use rustc_middle::mir;
use rustc_middle::ty::layout::HasTyCtxt;
use rustc_middle::ty::{self, Ty};
use std::borrow::{Borrow, Cow};
use std::collections::hash_map::Entry;
use std::hash::Hash;

use rustc_data_structures::fx::FxHashMap;

use rustc_ast::ast::Mutability;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::AssertMessage;
use rustc_span::symbol::Symbol;

use crate::interpret::{
    self, AllocId, Allocation, Frame, GlobalId, ImmTy, InterpCx, InterpResult, Memory, MemoryKind,
    OpTy, PlaceTy, Pointer, Scalar,
};

use super::error::*;

impl<'mir, 'tcx> InterpCx<'mir, 'tcx, CompileTimeInterpreter> {
    /// Evaluate a const function where all arguments (if any) are zero-sized types.
    /// The evaluation is memoized thanks to the query system.
    ///
    /// Returns `true` if the call has been evaluated.
    fn try_eval_const_fn_call(
        &mut self,
        instance: ty::Instance<'tcx>,
        ret: Option<(PlaceTy<'tcx>, mir::BasicBlock)>,
        args: &[OpTy<'tcx>],
    ) -> InterpResult<'tcx, bool> {
        trace!("try_eval_const_fn_call: {:?}", instance);
        // Because `#[track_caller]` adds an implicit non-ZST argument, we also cannot
        // perform this optimization on items tagged with it.
        if instance.def.requires_caller_location(self.tcx()) {
            return Ok(false);
        }
        // For the moment we only do this for functions which take no arguments
        // (or all arguments are ZSTs) so that we don't memoize too much.
        if args.iter().any(|a| !a.layout.is_zst()) {
            return Ok(false);
        }

        let dest = match ret {
            Some((dest, _)) => dest,
            // Don't memoize diverging function calls.
            None => return Ok(false),
        };

        let gid = GlobalId { instance, promoted: None };

        let place = self.const_eval_raw(gid)?;

        self.copy_op(place.into(), dest)?;

        self.return_to_block(ret.map(|r| r.1))?;
        self.dump_place(*dest);
        Ok(true)
    }

    /// "Intercept" a function call to a panic-related function
    /// because we have something special to do for it.
    /// If this returns successfully (`Ok`), the function should just be evaluated normally.
    fn hook_panic_fn(
        &mut self,
        instance: ty::Instance<'tcx>,
        args: &[OpTy<'tcx>],
    ) -> InterpResult<'tcx> {
        let def_id = instance.def_id();
        if Some(def_id) == self.tcx.lang_items().panic_fn()
            || Some(def_id) == self.tcx.lang_items().begin_panic_fn()
        {
            // &'static str
            assert!(args.len() == 1);

            let msg_place = self.deref_operand(args[0])?;
            let msg = Symbol::intern(self.read_str(msg_place)?);
            let span = self.find_closest_untracked_caller_location();
            let (file, line, col) = self.location_triple_for_span(span);
            Err(ConstEvalErrKind::Panic { msg, file, line, col }.into())
        } else {
            Ok(())
        }
    }
}

/// Extra machine state for CTFE, and the Machine instance
pub struct CompileTimeInterpreter {
    /// For now, the number of terminators that can be evaluated before we throw a resource
    /// exhuastion error.
    ///
    /// Setting this to `0` disables the limit and allows the interpreter to run forever.
    pub steps_remaining: usize,
}

#[derive(Copy, Clone, Debug)]
pub struct MemoryExtra {
    /// Whether this machine may read from statics
    pub(super) can_access_statics: bool,
}

impl CompileTimeInterpreter {
    pub(super) fn new(const_eval_limit: usize) -> Self {
        CompileTimeInterpreter { steps_remaining: const_eval_limit }
    }
}

impl<K: Hash + Eq, V> interpret::AllocMap<K, V> for FxHashMap<K, V> {
    #[inline(always)]
    fn contains_key<Q: ?Sized + Hash + Eq>(&mut self, k: &Q) -> bool
    where
        K: Borrow<Q>,
    {
        FxHashMap::contains_key(self, k)
    }

    #[inline(always)]
    fn insert(&mut self, k: K, v: V) -> Option<V> {
        FxHashMap::insert(self, k, v)
    }

    #[inline(always)]
    fn remove<Q: ?Sized + Hash + Eq>(&mut self, k: &Q) -> Option<V>
    where
        K: Borrow<Q>,
    {
        FxHashMap::remove(self, k)
    }

    #[inline(always)]
    fn filter_map_collect<T>(&self, mut f: impl FnMut(&K, &V) -> Option<T>) -> Vec<T> {
        self.iter().filter_map(move |(k, v)| f(k, &*v)).collect()
    }

    #[inline(always)]
    fn get_or<E>(&self, k: K, vacant: impl FnOnce() -> Result<V, E>) -> Result<&V, E> {
        match self.get(&k) {
            Some(v) => Ok(v),
            None => {
                vacant()?;
                bug!("The CTFE machine shouldn't ever need to extend the alloc_map when reading")
            }
        }
    }

    #[inline(always)]
    fn get_mut_or<E>(&mut self, k: K, vacant: impl FnOnce() -> Result<V, E>) -> Result<&mut V, E> {
        match self.entry(k) {
            Entry::Occupied(e) => Ok(e.into_mut()),
            Entry::Vacant(e) => {
                let v = vacant()?;
                Ok(e.insert(v))
            }
        }
    }
}

crate type CompileTimeEvalContext<'mir, 'tcx> = InterpCx<'mir, 'tcx, CompileTimeInterpreter>;

impl interpret::MayLeak for ! {
    #[inline(always)]
    fn may_leak(self) -> bool {
        // `self` is uninhabited
        self
    }
}

impl<'mir, 'tcx> interpret::Machine<'mir, 'tcx> for CompileTimeInterpreter {
    type MemoryKind = !;
    type PointerTag = ();
    type ExtraFnVal = !;

    type FrameExtra = ();
    type MemoryExtra = MemoryExtra;
    type AllocExtra = ();

    type MemoryMap = FxHashMap<AllocId, (MemoryKind<!>, Allocation)>;

    const GLOBAL_KIND: Option<!> = None; // no copying of globals from `tcx` to machine memory

    #[inline(always)]
    fn enforce_alignment(_memory_extra: &Self::MemoryExtra) -> bool {
        // We do not check for alignment to avoid having to carry an `Align`
        // in `ConstValue::ByRef`.
        false
    }

    #[inline(always)]
    fn enforce_validity(_ecx: &InterpCx<'mir, 'tcx, Self>) -> bool {
        false // for now, we don't enforce validity
    }

    fn find_mir_or_eval_fn(
        ecx: &mut InterpCx<'mir, 'tcx, Self>,
        instance: ty::Instance<'tcx>,
        args: &[OpTy<'tcx>],
        ret: Option<(PlaceTy<'tcx>, mir::BasicBlock)>,
        _unwind: Option<mir::BasicBlock>, // unwinding is not supported in consts
    ) -> InterpResult<'tcx, Option<&'mir mir::Body<'tcx>>> {
        debug!("find_mir_or_eval_fn: {:?}", instance);

        // Only check non-glue functions
        if let ty::InstanceDef::Item(def_id) = instance.def {
            // Execution might have wandered off into other crates, so we cannot do a stability-
            // sensitive check here.  But we can at least rule out functions that are not const
            // at all.
            if ecx.tcx.is_const_fn_raw(def_id) {
                // If this function is a `const fn` then under certain circumstances we
                // can evaluate call via the query system, thus memoizing all future calls.
                if ecx.try_eval_const_fn_call(instance, ret, args)? {
                    return Ok(None);
                }
            } else {
                // Some functions we support even if they are non-const -- but avoid testing
                // that for const fn!
                ecx.hook_panic_fn(instance, args)?;
                // We certainly do *not* want to actually call the fn
                // though, so be sure we return here.
                throw_unsup_format!("calling non-const function `{}`", instance)
            }
        }
        // This is a const fn. Call it.
        Ok(Some(match ecx.load_mir(instance.def, None) {
            Ok(body) => *body,
            Err(err) => {
                if let err_unsup!(NoMirFor(did)) = err.kind {
                    let path = ecx.tcx.def_path_str(did);
                    return Err(ConstEvalErrKind::NeedsRfc(format!(
                        "calling extern function `{}`",
                        path
                    ))
                    .into());
                }
                return Err(err);
            }
        }))
    }

    fn call_extra_fn(
        _ecx: &mut InterpCx<'mir, 'tcx, Self>,
        fn_val: !,
        _args: &[OpTy<'tcx>],
        _ret: Option<(PlaceTy<'tcx>, mir::BasicBlock)>,
        _unwind: Option<mir::BasicBlock>,
    ) -> InterpResult<'tcx> {
        match fn_val {}
    }

    fn call_intrinsic(
        ecx: &mut InterpCx<'mir, 'tcx, Self>,
        instance: ty::Instance<'tcx>,
        args: &[OpTy<'tcx>],
        ret: Option<(PlaceTy<'tcx>, mir::BasicBlock)>,
        _unwind: Option<mir::BasicBlock>,
    ) -> InterpResult<'tcx> {
        if ecx.emulate_intrinsic(instance, args, ret)? {
            return Ok(());
        }
        // An intrinsic that we do not support
        let intrinsic_name = ecx.tcx.item_name(instance.def_id());
        Err(ConstEvalErrKind::NeedsRfc(format!("calling intrinsic `{}`", intrinsic_name)).into())
    }

    fn assert_panic(
        ecx: &mut InterpCx<'mir, 'tcx, Self>,
        msg: &AssertMessage<'tcx>,
        _unwind: Option<mir::BasicBlock>,
    ) -> InterpResult<'tcx> {
        use rustc_middle::mir::AssertKind::*;
        // Convert `AssertKind<Operand>` to `AssertKind<u64>`.
        let err = match msg {
            BoundsCheck { ref len, ref index } => {
                let len = ecx
                    .read_immediate(ecx.eval_operand(len, None)?)
                    .expect("can't eval len")
                    .to_scalar()?
                    .to_machine_usize(&*ecx)?;
                let index = ecx
                    .read_immediate(ecx.eval_operand(index, None)?)
                    .expect("can't eval index")
                    .to_scalar()?
                    .to_machine_usize(&*ecx)?;
                BoundsCheck { len, index }
            }
            Overflow(op) => Overflow(*op),
            OverflowNeg => OverflowNeg,
            DivisionByZero => DivisionByZero,
            RemainderByZero => RemainderByZero,
            ResumedAfterReturn(generator_kind) => ResumedAfterReturn(*generator_kind),
            ResumedAfterPanic(generator_kind) => ResumedAfterPanic(*generator_kind),
        };
        Err(ConstEvalErrKind::AssertFailure(err).into())
    }

    fn ptr_to_int(_mem: &Memory<'mir, 'tcx, Self>, _ptr: Pointer) -> InterpResult<'tcx, u64> {
        Err(ConstEvalErrKind::NeedsRfc("pointer-to-integer cast".to_string()).into())
    }

    fn binary_ptr_op(
        _ecx: &InterpCx<'mir, 'tcx, Self>,
        _bin_op: mir::BinOp,
        _left: ImmTy<'tcx>,
        _right: ImmTy<'tcx>,
    ) -> InterpResult<'tcx, (Scalar, bool, Ty<'tcx>)> {
        Err(ConstEvalErrKind::NeedsRfc("pointer arithmetic or comparison".to_string()).into())
    }

    #[inline(always)]
    fn init_allocation_extra<'b>(
        _memory_extra: &MemoryExtra,
        _id: AllocId,
        alloc: Cow<'b, Allocation>,
        _kind: Option<MemoryKind<!>>,
    ) -> (Cow<'b, Allocation<Self::PointerTag>>, Self::PointerTag) {
        // We do not use a tag so we can just cheaply forward the allocation
        (alloc, ())
    }

    #[inline(always)]
    fn tag_global_base_pointer(_memory_extra: &MemoryExtra, _id: AllocId) -> Self::PointerTag {}

    fn box_alloc(
        _ecx: &mut InterpCx<'mir, 'tcx, Self>,
        _dest: PlaceTy<'tcx>,
    ) -> InterpResult<'tcx> {
        Err(ConstEvalErrKind::NeedsRfc("heap allocations via `box` keyword".to_string()).into())
    }

    fn before_terminator(ecx: &mut InterpCx<'mir, 'tcx, Self>) -> InterpResult<'tcx> {
        // The step limit has already been hit in a previous call to `before_terminator`.
        if ecx.machine.steps_remaining == 0 {
            return Ok(());
        }

        ecx.machine.steps_remaining -= 1;
        if ecx.machine.steps_remaining == 0 {
            throw_exhaust!(StepLimitReached)
        }

        Ok(())
    }

    #[inline(always)]
    fn init_frame_extra(
        _ecx: &mut InterpCx<'mir, 'tcx, Self>,
        frame: Frame<'mir, 'tcx>,
    ) -> InterpResult<'tcx, Frame<'mir, 'tcx>> {
        Ok(frame)
    }

    fn before_access_global(
        memory_extra: &MemoryExtra,
        alloc_id: AllocId,
        allocation: &Allocation,
        static_def_id: Option<DefId>,
        is_write: bool,
    ) -> InterpResult<'tcx> {
        if is_write {
            // Write access. These are never allowed, but we give a targeted error message.
            if allocation.mutability == Mutability::Not {
                Err(err_ub!(WriteToReadOnly(alloc_id)).into())
            } else {
                Err(ConstEvalErrKind::ModifiedGlobal.into())
            }
        } else {
            // Read access. These are usually allowed, with some exceptions.
            if memory_extra.can_access_statics {
                // Machine configuration allows us read from anything (e.g., `static` initializer).
                Ok(())
            } else if static_def_id.is_some() {
                // Machine configuration does not allow us to read statics
                // (e.g., `const` initializer).
                Err(ConstEvalErrKind::ConstAccessesStatic.into())
            } else {
                // Immutable global, this read is fine.
                // But make sure we never accept a read from something mutable, that would be
                // unsound. The reason is that as the content of this allocation may be different
                // now and at run-time, so if we permit reading now we might return the wrong value.
                assert_eq!(allocation.mutability, Mutability::Not);
                Ok(())
            }
        }
    }
}

// Please do not add any code below the above `Machine` trait impl. I (oli-obk) plan more cleanups
// so we can end up having a file with just that impl, but for now, let's keep the impl discoverable
// at the bottom of this file.
