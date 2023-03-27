use crate::ctxt::{InferType, InstTy, Subst};
use crate::defs::{BaseType, Lit, Predicate, PrimOp, Type};
use z3::ast::Ast;
use z3::{ast, AstKind};

pub fn z3_ast_to_pred(z3_ast: &ast::Dynamic) -> Predicate {
    match (z3_ast.kind(), &*z3_ast.children()) {
        (AstKind::Numeral, _) => Predicate::Lit(Lit::Int(
            z3_ast
                .as_int()
                .unwrap()
                .as_i64()
                .unwrap()
                .try_into()
                .unwrap(),
        )),
        (AstKind::App | AstKind::Var, []) => {
            let z3_ast_str = z3_ast.to_string();
            match &*z3_ast_str {
                "true" => Predicate::Lit(Lit::Bool(true)),
                "false" => Predicate::Lit(Lit::Bool(false)),
                _ => {
                    let (orig, _) = z3_ast_str.split_once("!").unwrap();
                    Predicate::Var(orig.into())
                }
            }
        }
        (AstKind::App, [v]) => {
            assert!(z3_ast.to_string().starts_with("(not"));
            Predicate::Not(Box::new([z3_ast_to_pred(v)]))
        }
        _ => panic!(),
    }
}

fn apply_subst_pred(pred: &Predicate, subst: &Subst) -> Predicate {
    match pred {
        Predicate::Res | Predicate::Lit(_) => pred.clone(),
        Predicate::Var(x) => subst.val.get(x).map(z3_ast_to_pred).unwrap_or(pred.clone()),
        Predicate::Op(box (op, pred1, pred2)) => Predicate::Op(Box::new((
            *op,
            apply_subst_pred(pred1, subst),
            apply_subst_pred(pred2, subst),
        ))),
        Predicate::Not(box [pred]) => Predicate::Not(Box::new([apply_subst_pred(pred, subst)])),
        Predicate::If(box [i, t, e]) => Predicate::If(Box::new([
            apply_subst_pred(i, subst),
            apply_subst_pred(t, subst),
            apply_subst_pred(e, subst),
        ])),
    }
}

pub fn apply_subst(ty: &Type, subst: &mut Subst) -> Type {
    match ty {
        Type::Refined(base, box pred) => {
            Type::Refined(base.clone(), Box::new(apply_subst_pred(pred, subst)))
        }
        Type::Fun(box (id, arg_ty, ret_ty)) => {
            let subst = &mut *subst.remove_v(id.clone());
            Type::Fun(Box::new((
                id.clone(),
                apply_subst(arg_ty, subst),
                apply_subst(ret_ty, subst),
            )))
        }
        Type::Forall(box (id, ty)) => {
            let subst = &mut *subst.remove_tp(id.clone());
            Type::Forall(Box::new((id.clone(), apply_subst(ty, subst))))
        }
        Type::Var(id) => match subst.ty.get(id) {
            None => ty.clone(),
            Some(InstTy::Fresh(id)) => Type::Var(format!("$T{id}").into()),
            Some(InstTy::Ty(ty)) => apply_subst(*ty, subst),
        },
    }
}

pub fn z3_ast_to_type(z3_ast: &ast::Dynamic, base: &BaseType) -> Type {
    let pred = z3_ast_to_pred(z3_ast);
    let pred = Predicate::Op(Box::new((PrimOp::Eq, Predicate::Res, pred)));
    Type::Refined(base.clone(), Box::new(pred))
}

pub fn infer_ty_to_ty(ty: &mut InferType) -> Type {
    match ty {
        InferType::Subst(subst, ty) => apply_subst(ty, subst),
        InferType::Selfify(z3_val, base) => z3_ast_to_type(z3_val, base),
    }
}
