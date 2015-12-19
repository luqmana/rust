// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This pass lowers any Call terminators which are intrinsics
//! to whatever statements or other calls as necessary.

use transform::MirPass;

use rustc::middle::const_eval;
use rustc::middle::infer;
use rustc::middle::subst;
use rustc::middle::ty;
use rustc::mir::repr::*;
use rustc::mir::repr::Terminator::Call;

use syntax::abi;
use syntax::parse::token;


pub struct LowerIntrinsics<'a, 'tcx: 'a> {
    tcx: &'a ty::ctxt<'tcx>
}

impl<'a, 'tcx: 'a> LowerIntrinsics<'a, 'tcx>  {
    pub fn new(tcx: &'a ty::ctxt<'tcx>) -> LowerIntrinsics<'a, 'tcx> {
        LowerIntrinsics { tcx: tcx }
    }
}

impl<'a, 'tcx> MirPass<'tcx> for LowerIntrinsics<'a, 'tcx> {
    fn run_on_mir(&mut self, mir: &mut Mir<'tcx>) {
        let mut bbs = vec![];

        for (i, basic_block) in mir.basic_blocks.iter_mut().enumerate() {
            match basic_block.terminator {
                Call { ref data, .. } if is_intrinsic_call(data) => bbs.push(BasicBlock::new(i)),
                _ => {}
            }
        }

        for bb in bbs {
            lower_intrinsic_in_basic_block(self.tcx, mir, bb);
        }
    }
}

fn is_intrinsic_call<'tcx>(call_data: &CallData<'tcx>) -> bool {
    if let Operand::Constant(Constant { ty, .. }) = call_data.func {
        match ty.sty {
            ty::TyBareFn(_, fty) if fty.abi == abi::RustIntrinsic => true,
            _ => false
        }
    } else {
        false
    }
}

fn lower_intrinsic_in_basic_block<'tcx>(tcx: &ty::ctxt<'tcx>,
                                        mir: &mut Mir<'tcx>,
                                        bb: BasicBlock) {

    let basic_block = mir.basic_block_data_mut(bb);

    let (call_data, targets) =
        if let Call { ref data, targets } = basic_block.terminator {
            ((*data).clone(), targets)
        } else {
            tcx.sess.bug("expected `Call` terminator to lower intrinsic")
        };
    let (def_id, span, fty, substs) = if let Operand::Constant(Constant {
        span, ty, literal: Literal::Item { def_id, substs, .. }
    }) = call_data.func {
        (def_id, span, ty, substs)
    } else {
        tcx.sess.bug("could not get literal item to lower intrinsic")
    };

    let sig = tcx.erase_late_bound_regions(&fty.fn_sig());
    let sig = infer::normalize_associated_type(tcx, &sig);
    let ret_ty = sig.output.unwrap_or(tcx.mk_nil());

    let name = &*tcx.item_name(def_id).as_str();

    if name == "transmute" {

        assert_eq!(call_data.args.len(), 1);

        // dest = transmute(foo)
        //   =>
        // Assign(dest, Cast(foo))
        basic_block.statements.push(Statement {
            span: span,
            kind: StatementKind::Assign(
                call_data.destination.clone(),
                Rvalue::Cast(CastKind::Transmute,
                             call_data.args[0].clone(),
                             ret_ty)
            )
        });

    } else if name == "move_val_init" {

        assert_eq!(call_data.args.len(), 2);

        if let Operand::Consume(dest) = call_data.args[0].clone() {
            // move_val_init(dest, src)
            //   =>
            // Assign(dest, src)
            basic_block.statements.push(Statement {
                span: span,
                kind: StatementKind::Assign(
                    dest,
                    Rvalue::Use(call_data.args[1].clone())
                )
            });
        } else {
            tcx.sess.span_bug(span, "destination argument not lvalue?");
        }

    } else if name == "size_of" {

        // dest = size_of<T>()
        //   =>
        // Assign(dest, SizeOf(T))
        basic_block.statements.push(Statement {
            span: span,
            kind: StatementKind::Assign(
                call_data.destination.clone(),
                Rvalue::SizeOf(*substs.types.get(subst::FnSpace, 0), None)
            )
        });

    } else if name == "size_of_val" {

        // dest = size_of_val<T>(x)
        //   =>
        // Assign(dest, SizeOf(T, x))
        basic_block.statements.push(Statement {
            span: span,
            kind: StatementKind::Assign(
                call_data.destination.clone(),
                Rvalue::SizeOf(*substs.types.get(subst::FnSpace, 0),
                               Some(call_data.args[0].clone()))
            )
        });

    } else if name == "type_name" {

        let tp_ty = *substs.types.get(subst::FnSpace, 0);
        let ty_name = token::intern_and_get_ident(&tp_ty.to_string());
        let name_op = Operand::Constant(Constant {
            span: span,
            ty: tcx.mk_static_str(),
            literal: Literal::Value {
                value: const_eval::ConstVal::Str(ty_name)
            }
        });

        // dest = type_name<T>()
        //   =>
        // Assign(dest, Use(<ty name>)
        basic_block.statements.push(Statement {
            span: span,
            kind: StatementKind::Assign(
                call_data.destination.clone(),
                Rvalue::Use(name_op)
            )
        });

    }

    // Since this is no longer a function call, replace the
    // terminator with a simple Goto
    basic_block.terminator = Terminator::Goto { target: targets.0 };
}
