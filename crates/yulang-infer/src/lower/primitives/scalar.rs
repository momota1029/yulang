use yulang_core_ir as core_ir;

use crate::ast::expr::TypedExpr;
use crate::lower::LowerState;
use crate::symbols::{ModuleId, Name};
use crate::types::{Neg, Pos};

use super::support::{named_path, named_runtime_path};

pub(super) fn install_bool_unary_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    install_unary_primitive(state, module, name, op, "bool", "bool");
}

pub(super) fn install_bool_binary_predicate_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    install_binary_predicate_primitive(state, module, name, op, "bool");
}

pub(super) fn install_int_binary_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let int_path = named_path("int");
    let pure_arg_eff = state.fresh_exact_pure_eff_tv();
    let pure_ret_eff = state.fresh_exact_pure_eff_tv();
    let inner_pure_arg_eff = state.fresh_exact_pure_eff_tv();
    let inner_pure_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(int_path.clone(), vec![]),
        Neg::Var(inner_pure_arg_eff),
        Pos::Var(inner_pure_ret_eff),
        state.pos_con(int_path.clone(), vec![]),
    );
    let pos_sig = state.pos_fun(
        state.neg_con(int_path.clone(), vec![]),
        Neg::Var(pure_arg_eff),
        Pos::Var(pure_ret_eff),
        pos_sig,
    );
    let neg_pure_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_pure_ret_eff = state.fresh_exact_pure_eff_tv();
    let inner_neg_pure_arg_eff = state.fresh_exact_pure_eff_tv();
    let inner_neg_pure_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(int_path.clone(), vec![]),
        Pos::Var(neg_pure_arg_eff),
        Neg::Var(neg_pure_ret_eff),
        state.neg_fun(
            state.pos_con(int_path.clone(), vec![]),
            Pos::Var(inner_neg_pure_arg_eff),
            Neg::Var(inner_neg_pure_ret_eff),
            state.neg_con(int_path.clone(), vec![]),
        ),
    );
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.principal_bodies.insert(def, body);
    state.runtime_export_schemes.insert(
        def,
        core_ir::Scheme {
            requirements: Vec::new(),
            body: binary_scheme_body("int"),
        },
    );
}

pub(super) fn install_float_binary_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let float_path = named_path("float");
    let pure_arg_eff = state.fresh_exact_pure_eff_tv();
    let pure_ret_eff = state.fresh_exact_pure_eff_tv();
    let inner_pure_arg_eff = state.fresh_exact_pure_eff_tv();
    let inner_pure_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(float_path.clone(), vec![]),
        Neg::Var(inner_pure_arg_eff),
        Pos::Var(inner_pure_ret_eff),
        state.pos_con(float_path.clone(), vec![]),
    );
    let pos_sig = state.pos_fun(
        state.neg_con(float_path.clone(), vec![]),
        Neg::Var(pure_arg_eff),
        Pos::Var(pure_ret_eff),
        pos_sig,
    );
    let neg_pure_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_pure_ret_eff = state.fresh_exact_pure_eff_tv();
    let inner_neg_pure_arg_eff = state.fresh_exact_pure_eff_tv();
    let inner_neg_pure_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(float_path.clone(), vec![]),
        Pos::Var(neg_pure_arg_eff),
        Neg::Var(neg_pure_ret_eff),
        state.neg_fun(
            state.pos_con(float_path.clone(), vec![]),
            Pos::Var(inner_neg_pure_arg_eff),
            Neg::Var(inner_neg_pure_ret_eff),
            state.neg_con(float_path.clone(), vec![]),
        ),
    );
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.principal_bodies.insert(def, body);
    state.runtime_export_schemes.insert(
        def,
        core_ir::Scheme {
            requirements: Vec::new(),
            body: binary_scheme_body("float"),
        },
    );
}

pub(super) fn install_string_binary_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    install_binary_primitive(state, module, name, op, "str");
}

pub(super) fn install_string_len_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    install_unary_primitive(state, module, name, op, "str", "int");
}

pub(super) fn install_string_index_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    install_binary_mixed_primitive(state, module, name, op, "str", "int", "str");
}

pub(super) fn install_string_index_range_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    install_binary_mixed_primitive(state, module, name, op, "str", "range", "str");
}

pub(super) fn install_string_index_range_raw_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    install_ternary_mixed_primitive(state, module, name, op, ["str", "int", "int"], "str");
}

pub(super) fn install_string_splice_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    install_ternary_mixed_primitive(state, module, name, op, ["str", "range", "str"], "str");
}

pub(super) fn install_string_splice_raw_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    install_quaternary_mixed_primitive(
        state,
        module,
        name,
        op,
        ["str", "int", "int", "str"],
        "str",
    );
}

pub(super) fn install_to_string_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
    param_name: &str,
) {
    install_unary_primitive(state, module, name, op, param_name, "str");
}

pub(super) fn install_int_binary_predicate_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    install_binary_predicate_primitive(state, module, name, op, "int");
}

pub(super) fn install_float_binary_predicate_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
) {
    install_binary_predicate_primitive(state, module, name, op, "float");
}

fn install_unary_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
    param_name: &str,
    ret_name: &str,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let param_path = named_path(param_name);
    let ret_path = named_path(ret_name);
    let pos_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(param_path.clone(), vec![]),
        Neg::Var(pos_arg_eff),
        Pos::Var(pos_ret_eff),
        state.pos_con(ret_path.clone(), vec![]),
    );
    let neg_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(param_path.clone(), vec![]),
        Pos::Var(neg_arg_eff),
        Neg::Var(neg_ret_eff),
        state.neg_con(ret_path.clone(), vec![]),
    );
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.principal_bodies.insert(def, body);
    state.runtime_export_schemes.insert(
        def,
        core_ir::Scheme {
            requirements: Vec::new(),
            body: unary_scheme_body(param_name, ret_name),
        },
    );
}

fn install_binary_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
    type_name: &str,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let type_path = named_path(type_name);
    let pure_arg_eff = state.fresh_exact_pure_eff_tv();
    let pure_ret_eff = state.fresh_exact_pure_eff_tv();
    let inner_pure_arg_eff = state.fresh_exact_pure_eff_tv();
    let inner_pure_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(type_path.clone(), vec![]),
        Neg::Var(inner_pure_arg_eff),
        Pos::Var(inner_pure_ret_eff),
        state.pos_con(type_path.clone(), vec![]),
    );
    let pos_sig = state.pos_fun(
        state.neg_con(type_path.clone(), vec![]),
        Neg::Var(pure_arg_eff),
        Pos::Var(pure_ret_eff),
        pos_sig,
    );
    let neg_pure_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_pure_ret_eff = state.fresh_exact_pure_eff_tv();
    let inner_neg_pure_arg_eff = state.fresh_exact_pure_eff_tv();
    let inner_neg_pure_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(type_path.clone(), vec![]),
        Pos::Var(neg_pure_arg_eff),
        Neg::Var(neg_pure_ret_eff),
        state.neg_fun(
            state.pos_con(type_path.clone(), vec![]),
            Pos::Var(inner_neg_pure_arg_eff),
            Neg::Var(inner_neg_pure_ret_eff),
            state.neg_con(type_path.clone(), vec![]),
        ),
    );
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.principal_bodies.insert(def, body);
    state.runtime_export_schemes.insert(
        def,
        core_ir::Scheme {
            requirements: Vec::new(),
            body: binary_scheme_body(type_name),
        },
    );
}

fn install_binary_mixed_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
    first_name: &str,
    second_name: &str,
    ret_name: &str,
) {
    install_mixed_primitive(
        state,
        module,
        name,
        op,
        &[first_name, second_name],
        ret_name,
    );
}

fn install_ternary_mixed_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
    params: [&str; 3],
    ret_name: &str,
) {
    install_mixed_primitive(state, module, name, op, &params, ret_name);
}

fn install_quaternary_mixed_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
    params: [&str; 4],
    ret_name: &str,
) {
    install_mixed_primitive(state, module, name, op, &params, ret_name);
}

fn install_mixed_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
    params: &[&str],
    ret_name: &str,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let pos_sig = mixed_pos_fun(state, params, ret_name);
    let neg_sig = mixed_neg_fun(state, params, ret_name);
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.principal_bodies.insert(def, body);
    state.runtime_export_schemes.insert(
        def,
        core_ir::Scheme {
            requirements: Vec::new(),
            body: mixed_scheme_body(params, ret_name),
        },
    );
}

fn mixed_pos_fun(state: &mut LowerState, params: &[&str], ret_name: &str) -> Pos {
    let Some((first, rest)) = params.split_first() else {
        return state.pos_con(named_path(ret_name), vec![]);
    };
    let arg_eff = state.fresh_exact_pure_eff_tv();
    let ret_eff = state.fresh_exact_pure_eff_tv();
    let ret = mixed_pos_fun(state, rest, ret_name);
    state.pos_fun(
        state.neg_con(named_path(first), vec![]),
        Neg::Var(arg_eff),
        Pos::Var(ret_eff),
        ret,
    )
}

fn mixed_neg_fun(state: &mut LowerState, params: &[&str], ret_name: &str) -> Neg {
    let Some((first, rest)) = params.split_first() else {
        return state.neg_con(named_path(ret_name), vec![]);
    };
    let arg_eff = state.fresh_exact_pure_eff_tv();
    let ret_eff = state.fresh_exact_pure_eff_tv();
    let ret = mixed_neg_fun(state, rest, ret_name);
    state.neg_fun(
        state.pos_con(named_path(first), vec![]),
        Pos::Var(arg_eff),
        Neg::Var(ret_eff),
        ret,
    )
}

fn install_binary_predicate_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: core_ir::PrimitiveOp,
    arg_name: &str,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let arg_path = named_path(arg_name);
    let bool_path = named_path("bool");
    let pos_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(arg_path.clone(), vec![]),
        Neg::Var(pos_outer_arg_eff),
        Pos::Var(pos_outer_ret_eff),
        state.pos_fun(
            state.neg_con(arg_path.clone(), vec![]),
            Neg::Var(pos_inner_arg_eff),
            Pos::Var(pos_inner_ret_eff),
            state.pos_con(bool_path.clone(), vec![]),
        ),
    );
    let neg_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(arg_path.clone(), vec![]),
        Pos::Var(neg_outer_arg_eff),
        Neg::Var(neg_outer_ret_eff),
        state.neg_fun(
            state.pos_con(arg_path.clone(), vec![]),
            Pos::Var(neg_inner_arg_eff),
            Neg::Var(neg_inner_ret_eff),
            state.neg_con(bool_path.clone(), vec![]),
        ),
    );
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.principal_bodies.insert(def, body);
    state.runtime_export_schemes.insert(
        def,
        core_ir::Scheme {
            requirements: Vec::new(),
            body: binary_predicate_scheme_body(arg_name),
        },
    );
}

fn binary_scheme_body(name: &str) -> core_ir::Type {
    let ty = core_ir::Type::Named {
        path: named_runtime_path(name),
        args: vec![],
    };
    core_ir::Type::Fun {
        param: Box::new(ty.clone()),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(core_ir::Type::Fun {
            param: Box::new(ty.clone()),
            param_effect: Box::new(core_ir::Type::Any),
            ret_effect: Box::new(core_ir::Type::Any),
            ret: Box::new(ty),
        }),
    }
}

fn unary_scheme_body(param_name: &str, ret_name: &str) -> core_ir::Type {
    let param = core_ir::Type::Named {
        path: named_runtime_path(param_name),
        args: vec![],
    };
    let ret = core_ir::Type::Named {
        path: named_runtime_path(ret_name),
        args: vec![],
    };
    core_ir::Type::Fun {
        param: Box::new(param),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(ret),
    }
}

fn mixed_scheme_body(params: &[&str], ret_name: &str) -> core_ir::Type {
    let ret = core_ir::Type::Named {
        path: named_runtime_path(ret_name),
        args: vec![],
    };
    params.iter().rev().fold(ret, |ret, param_name| {
        let param = core_ir::Type::Named {
            path: named_runtime_path(param_name),
            args: vec![],
        };
        core_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(core_ir::Type::Any),
            ret_effect: Box::new(core_ir::Type::Any),
            ret: Box::new(ret),
        }
    })
}

fn binary_predicate_scheme_body(name: &str) -> core_ir::Type {
    let ty = core_ir::Type::Named {
        path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
        args: vec![],
    };
    let bool_ty = core_ir::Type::Named {
        path: core_ir::Path::from_name(core_ir::Name("bool".to_string())),
        args: vec![],
    };
    core_ir::Type::Fun {
        param: Box::new(ty.clone()),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(core_ir::Type::Fun {
            param: Box::new(ty),
            param_effect: Box::new(core_ir::Type::Any),
            ret_effect: Box::new(core_ir::Type::Any),
            ret: Box::new(bool_ty),
        }),
    }
}
