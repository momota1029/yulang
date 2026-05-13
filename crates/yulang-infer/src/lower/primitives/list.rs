use yulang_typed_ir as typed_ir;

use crate::ast::expr::TypedExpr;
use crate::lower::LowerState;
use crate::symbols::{ModuleId, Name};
use crate::types::{Neg, Pos};

use super::support::{named_path, named_runtime_path};

fn store_list_primitive_scheme(
    state: &mut LowerState,
    def: crate::ids::DefId,
    principal: crate::ids::PosId,
    body: typed_ir::Type,
) {
    state.infer.store_frozen_scheme(
        def,
        crate::scheme::freeze_pos_scheme(&state.infer, principal),
    );
    state.runtime_export_schemes.insert(
        def,
        typed_ir::Scheme {
            requirements: Vec::new(),
            body,
        },
    );
}

fn store_list_runtime_scheme(state: &mut LowerState, def: crate::ids::DefId, body: typed_ir::Type) {
    state.runtime_export_schemes.insert(
        def,
        typed_ir::Scheme {
            requirements: Vec::new(),
            body,
        },
    );
}

pub(super) fn install_list_len_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: typed_ir::PrimitiveOp,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    let item_tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let list_path = named_path("list");
    let int_path = named_path("int");
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(list_path.clone(), list_args.clone()),
        Neg::Var(pos_arg_eff),
        Pos::Var(pos_ret_eff),
        state.pos_con(int_path.clone(), vec![]),
    );
    let neg_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(list_path.clone(), list_args),
        Pos::Var(neg_arg_eff),
        Neg::Var(neg_ret_eff),
        state.neg_con(int_path, vec![]),
    );
    let pos_sig = state.infer.alloc_pos(pos_sig);
    let neg_sig = state.infer.alloc_neg(neg_sig);
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.insert_principal_body(def, body);
    store_list_runtime_scheme(state, def, list_len_scheme_body());
}

pub(super) fn install_list_index_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: typed_ir::PrimitiveOp,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    let item_tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let list_path = named_path("list");
    let int_path = named_path("int");
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(list_path.clone(), list_args.clone()),
        Neg::Var(pos_outer_arg_eff),
        Pos::Var(pos_outer_ret_eff),
        state.pos_fun(
            state.neg_con(int_path.clone(), vec![]),
            Neg::Var(pos_inner_arg_eff),
            Pos::Var(pos_inner_ret_eff),
            Pos::Var(item_tv),
        ),
    );
    let neg_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(list_path, list_args),
        Pos::Var(neg_outer_arg_eff),
        Neg::Var(neg_outer_ret_eff),
        state.neg_fun(
            state.pos_con(int_path, vec![]),
            Pos::Var(neg_inner_arg_eff),
            Neg::Var(neg_inner_ret_eff),
            Neg::Var(item_tv),
        ),
    );
    let pos_sig = state.infer.alloc_pos(pos_sig);
    let neg_sig = state.infer.alloc_neg(neg_sig);
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.insert_principal_body(def, body);
    store_list_runtime_scheme(state, def, list_index_scheme_body());
}

pub(super) fn install_list_index_range_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: typed_ir::PrimitiveOp,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    let item_tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let list_path = named_path("list");
    let range_path = named_path("range");
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(list_path.clone(), list_args.clone()),
        Neg::Var(pos_outer_arg_eff),
        Pos::Var(pos_outer_ret_eff),
        state.pos_fun(
            state.neg_con(range_path.clone(), vec![]),
            Neg::Var(pos_inner_arg_eff),
            Pos::Var(pos_inner_ret_eff),
            state.pos_con(list_path.clone(), list_args.clone()),
        ),
    );
    let neg_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(list_path.clone(), list_args.clone()),
        Pos::Var(neg_outer_arg_eff),
        Neg::Var(neg_outer_ret_eff),
        state.neg_fun(
            state.pos_con(range_path, vec![]),
            Pos::Var(neg_inner_arg_eff),
            Neg::Var(neg_inner_ret_eff),
            state.neg_con(list_path, list_args),
        ),
    );
    let pos_sig = state.infer.alloc_pos(pos_sig);
    let neg_sig = state.infer.alloc_neg(neg_sig);
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.insert_principal_body(def, body);
    store_list_runtime_scheme(state, def, list_index_range_scheme_body());
}

pub(super) fn install_list_empty_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: typed_ir::PrimitiveOp,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    let item_tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let list_path = named_path("list");
    let unit_path = named_path("unit");
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(unit_path.clone(), vec![]),
        Neg::Var(pos_arg_eff),
        Pos::Var(pos_ret_eff),
        state.pos_con(list_path.clone(), list_args.clone()),
    );
    let neg_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(unit_path, vec![]),
        Pos::Var(neg_arg_eff),
        Neg::Var(neg_ret_eff),
        state.neg_con(list_path, list_args),
    );
    let pos_sig = state.infer.alloc_pos(pos_sig);
    let neg_sig = state.infer.alloc_neg(neg_sig);
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.insert_principal_body(def, body);
    store_list_runtime_scheme(state, def, list_empty_scheme_body());
}

pub(super) fn install_list_splice_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: typed_ir::PrimitiveOp,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    let item_tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let list_path = named_path("list");
    let range_path = named_path("range");
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_mid_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_mid_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(list_path.clone(), list_args.clone()),
        Neg::Var(pos_outer_arg_eff),
        Pos::Var(pos_outer_ret_eff),
        state.pos_fun(
            state.neg_con(range_path.clone(), vec![]),
            Neg::Var(pos_mid_arg_eff),
            Pos::Var(pos_mid_ret_eff),
            state.pos_fun(
                state.neg_con(list_path.clone(), list_args.clone()),
                Neg::Var(pos_inner_arg_eff),
                Pos::Var(pos_inner_ret_eff),
                state.pos_con(list_path.clone(), list_args.clone()),
            ),
        ),
    );
    let neg_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_mid_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_mid_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(list_path.clone(), list_args.clone()),
        Pos::Var(neg_outer_arg_eff),
        Neg::Var(neg_outer_ret_eff),
        state.neg_fun(
            state.pos_con(range_path, vec![]),
            Pos::Var(neg_mid_arg_eff),
            Neg::Var(neg_mid_ret_eff),
            state.neg_fun(
                state.pos_con(list_path, list_args.clone()),
                Pos::Var(neg_inner_arg_eff),
                Neg::Var(neg_inner_ret_eff),
                state.neg_con(
                    named_path("list"),
                    vec![(Pos::Var(item_tv), Neg::Var(item_tv))],
                ),
            ),
        ),
    );
    let pos_sig = state.infer.alloc_pos(pos_sig);
    let neg_sig = state.infer.alloc_neg(neg_sig);
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.insert_principal_body(def, body);
    store_list_runtime_scheme(state, def, list_splice_scheme_body());
}

pub(super) fn install_list_singleton_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: typed_ir::PrimitiveOp,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    let item_tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let list_path = named_path("list");
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        Neg::Var(item_tv),
        Neg::Var(pos_arg_eff),
        Pos::Var(pos_ret_eff),
        state.pos_con(list_path.clone(), list_args.clone()),
    );
    let neg_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        Pos::Var(item_tv),
        Pos::Var(neg_arg_eff),
        Neg::Var(neg_ret_eff),
        state.neg_con(list_path, list_args),
    );
    let pos_sig = state.infer.alloc_pos(pos_sig);
    let neg_sig = state.infer.alloc_neg(neg_sig);
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.insert_principal_body(def, body);
    store_list_runtime_scheme(state, def, list_singleton_scheme_body());
}

pub(super) fn install_list_merge_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: typed_ir::PrimitiveOp,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    let item_tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let list_path = named_path("list");
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(list_path.clone(), list_args.clone()),
        Neg::Var(pos_outer_arg_eff),
        Pos::Var(pos_outer_ret_eff),
        state.pos_fun(
            state.neg_con(list_path.clone(), list_args.clone()),
            Neg::Var(pos_inner_arg_eff),
            Pos::Var(pos_inner_ret_eff),
            state.pos_con(list_path.clone(), list_args.clone()),
        ),
    );
    let neg_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(list_path.clone(), list_args.clone()),
        Pos::Var(neg_outer_arg_eff),
        Neg::Var(neg_outer_ret_eff),
        state.neg_fun(
            state.pos_con(list_path, list_args),
            Pos::Var(neg_inner_arg_eff),
            Neg::Var(neg_inner_ret_eff),
            state.neg_con(
                named_path("list"),
                vec![(Pos::Var(item_tv), Neg::Var(item_tv))],
            ),
        ),
    );
    let pos_sig = state.infer.alloc_pos(pos_sig);
    let neg_sig = state.infer.alloc_neg(neg_sig);
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.insert_principal_body(def, body);
    store_list_runtime_scheme(state, def, list_merge_scheme_body());
}

pub(super) fn install_list_index_range_raw_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: typed_ir::PrimitiveOp,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    let item_tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let list_path = named_path("list");
    let int_path = named_path("int");
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_mid_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_mid_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(list_path.clone(), list_args.clone()),
        Neg::Var(pos_outer_arg_eff),
        Pos::Var(pos_outer_ret_eff),
        state.pos_fun(
            state.neg_con(int_path.clone(), vec![]),
            Neg::Var(pos_mid_arg_eff),
            Pos::Var(pos_mid_ret_eff),
            state.pos_fun(
                state.neg_con(int_path.clone(), vec![]),
                Neg::Var(pos_inner_arg_eff),
                Pos::Var(pos_inner_ret_eff),
                state.pos_con(list_path.clone(), list_args.clone()),
            ),
        ),
    );
    let neg_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_mid_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_mid_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_inner_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(list_path.clone(), list_args.clone()),
        Pos::Var(neg_outer_arg_eff),
        Neg::Var(neg_outer_ret_eff),
        state.neg_fun(
            state.pos_con(int_path.clone(), vec![]),
            Pos::Var(neg_mid_arg_eff),
            Neg::Var(neg_mid_ret_eff),
            state.neg_fun(
                state.pos_con(int_path, vec![]),
                Pos::Var(neg_inner_arg_eff),
                Neg::Var(neg_inner_ret_eff),
                state.neg_con(list_path, list_args),
            ),
        ),
    );
    let pos_sig = state.infer.alloc_pos(pos_sig);
    let neg_sig = state.infer.alloc_neg(neg_sig);
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.insert_principal_body(def, body);
    store_list_runtime_scheme(state, def, list_index_range_raw_scheme_body());
}

pub(super) fn install_list_splice_raw_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: typed_ir::PrimitiveOp,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    let item_tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let list_path = named_path("list");
    let int_path = named_path("int");
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_start_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_start_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_end_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_end_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_insert_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_insert_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(list_path.clone(), list_args.clone()),
        Neg::Var(pos_outer_arg_eff),
        Pos::Var(pos_outer_ret_eff),
        state.pos_fun(
            state.neg_con(int_path.clone(), vec![]),
            Neg::Var(pos_start_arg_eff),
            Pos::Var(pos_start_ret_eff),
            state.pos_fun(
                state.neg_con(int_path.clone(), vec![]),
                Neg::Var(pos_end_arg_eff),
                Pos::Var(pos_end_ret_eff),
                state.pos_fun(
                    state.neg_con(list_path.clone(), list_args.clone()),
                    Neg::Var(pos_insert_arg_eff),
                    Pos::Var(pos_insert_ret_eff),
                    state.pos_con(list_path.clone(), list_args.clone()),
                ),
            ),
        ),
    );
    let neg_outer_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_outer_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_start_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_start_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_end_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_end_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_insert_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_insert_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(list_path.clone(), list_args.clone()),
        Pos::Var(neg_outer_arg_eff),
        Neg::Var(neg_outer_ret_eff),
        state.neg_fun(
            state.pos_con(int_path.clone(), vec![]),
            Pos::Var(neg_start_arg_eff),
            Neg::Var(neg_start_ret_eff),
            state.neg_fun(
                state.pos_con(int_path, vec![]),
                Pos::Var(neg_end_arg_eff),
                Neg::Var(neg_end_ret_eff),
                state.neg_fun(
                    state.pos_con(list_path.clone(), list_args.clone()),
                    Pos::Var(neg_insert_arg_eff),
                    Neg::Var(neg_insert_ret_eff),
                    state.neg_con(list_path, list_args),
                ),
            ),
        ),
    );
    let pos_sig = state.infer.alloc_pos(pos_sig);
    let neg_sig = state.infer.alloc_neg(neg_sig);
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.insert_principal_body(def, body);
    store_list_runtime_scheme(state, def, list_splice_raw_scheme_body());
}

pub(super) fn install_list_view_raw_primitive(
    state: &mut LowerState,
    module: ModuleId,
    name: &str,
    op: typed_ir::PrimitiveOp,
) {
    let name = Name(name.to_string());
    if state.ctx.modules.node(module).values.contains_key(&name) {
        return;
    }

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    let item_tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let list_path = named_path("list");
    let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
    let pos_arg_eff = state.fresh_exact_pure_eff_tv();
    let pos_ret_eff = state.fresh_exact_pure_eff_tv();
    let pos_sig = state.pos_fun(
        state.neg_con(list_path.clone(), list_args.clone()),
        Neg::Var(pos_arg_eff),
        Pos::Var(pos_ret_eff),
        list_view_pos_type(state, item_tv),
    );
    let neg_arg_eff = state.fresh_exact_pure_eff_tv();
    let neg_ret_eff = state.fresh_exact_pure_eff_tv();
    let neg_sig = state.neg_fun(
        state.pos_con(list_path, list_args),
        Pos::Var(neg_arg_eff),
        Neg::Var(neg_ret_eff),
        list_view_neg_type(state, item_tv),
    );
    let pos_sig = state.infer.alloc_pos(pos_sig);
    let neg_sig = state.infer.alloc_neg(neg_sig);
    state.infer.constrain(pos_sig, Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_sig);

    let body = TypedExpr {
        tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: crate::ast::expr::ExprKind::PrimitiveOp(op),
    };
    state.insert_principal_body(def, body);
    store_list_primitive_scheme(state, def, pos_sig, list_view_scheme_body());
}

fn list_len_scheme_body() -> typed_ir::Type {
    let item = typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()));
    let list = typed_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![typed_ir::TypeArg::Type(item)],
    };
    let int_ty = typed_ir::Type::Named {
        path: named_runtime_path("int"),
        args: vec![],
    };
    typed_ir::Type::Fun {
        param: Box::new(list),
        param_effect: Box::new(typed_ir::Type::Any),
        ret_effect: Box::new(typed_ir::Type::Any),
        ret: Box::new(int_ty),
    }
}

fn list_empty_scheme_body() -> typed_ir::Type {
    let unit = typed_ir::Type::Named {
        path: named_runtime_path("unit"),
        args: vec![],
    };
    let item = typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()));
    let list = typed_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![typed_ir::TypeArg::Type(item)],
    };
    typed_ir::Type::Fun {
        param: Box::new(unit),
        param_effect: Box::new(typed_ir::Type::Any),
        ret_effect: Box::new(typed_ir::Type::Any),
        ret: Box::new(list),
    }
}

fn list_singleton_scheme_body() -> typed_ir::Type {
    let item = typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()));
    let list = typed_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![typed_ir::TypeArg::Type(item.clone())],
    };
    typed_ir::Type::Fun {
        param: Box::new(item),
        param_effect: Box::new(typed_ir::Type::Any),
        ret_effect: Box::new(typed_ir::Type::Any),
        ret: Box::new(list),
    }
}

fn list_index_scheme_body() -> typed_ir::Type {
    let item = typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()));
    let list = typed_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![typed_ir::TypeArg::Type(item.clone())],
    };
    let int_ty = typed_ir::Type::Named {
        path: named_runtime_path("int"),
        args: vec![],
    };
    typed_ir::Type::Fun {
        param: Box::new(list),
        param_effect: Box::new(typed_ir::Type::Any),
        ret_effect: Box::new(typed_ir::Type::Any),
        ret: Box::new(typed_ir::Type::Fun {
            param: Box::new(int_ty),
            param_effect: Box::new(typed_ir::Type::Any),
            ret_effect: Box::new(typed_ir::Type::Any),
            ret: Box::new(item),
        }),
    }
}

fn list_merge_scheme_body() -> typed_ir::Type {
    let item = typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()));
    let list = typed_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![typed_ir::TypeArg::Type(item.clone())],
    };
    typed_ir::Type::Fun {
        param: Box::new(list.clone()),
        param_effect: Box::new(typed_ir::Type::Any),
        ret_effect: Box::new(typed_ir::Type::Any),
        ret: Box::new(typed_ir::Type::Fun {
            param: Box::new(list.clone()),
            param_effect: Box::new(typed_ir::Type::Any),
            ret_effect: Box::new(typed_ir::Type::Any),
            ret: Box::new(list),
        }),
    }
}

fn list_index_range_raw_scheme_body() -> typed_ir::Type {
    let item = typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()));
    let list = typed_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![typed_ir::TypeArg::Type(item.clone())],
    };
    let int_ty = typed_ir::Type::Named {
        path: named_runtime_path("int"),
        args: vec![],
    };
    typed_ir::Type::Fun {
        param: Box::new(list.clone()),
        param_effect: Box::new(typed_ir::Type::Any),
        ret_effect: Box::new(typed_ir::Type::Any),
        ret: Box::new(typed_ir::Type::Fun {
            param: Box::new(int_ty.clone()),
            param_effect: Box::new(typed_ir::Type::Any),
            ret_effect: Box::new(typed_ir::Type::Any),
            ret: Box::new(typed_ir::Type::Fun {
                param: Box::new(int_ty),
                param_effect: Box::new(typed_ir::Type::Any),
                ret_effect: Box::new(typed_ir::Type::Any),
                ret: Box::new(list),
            }),
        }),
    }
}

fn list_index_range_scheme_body() -> typed_ir::Type {
    let item = typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()));
    let list = typed_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![typed_ir::TypeArg::Type(item.clone())],
    };
    let range = typed_ir::Type::Named {
        path: named_runtime_path("range"),
        args: vec![],
    };
    typed_ir::Type::Fun {
        param: Box::new(list.clone()),
        param_effect: Box::new(typed_ir::Type::Any),
        ret_effect: Box::new(typed_ir::Type::Any),
        ret: Box::new(typed_ir::Type::Fun {
            param: Box::new(range),
            param_effect: Box::new(typed_ir::Type::Any),
            ret_effect: Box::new(typed_ir::Type::Any),
            ret: Box::new(list),
        }),
    }
}

fn list_splice_scheme_body() -> typed_ir::Type {
    let item = typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()));
    let list = typed_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![typed_ir::TypeArg::Type(item.clone())],
    };
    let range = typed_ir::Type::Named {
        path: named_runtime_path("range"),
        args: vec![],
    };
    typed_ir::Type::Fun {
        param: Box::new(list.clone()),
        param_effect: Box::new(typed_ir::Type::Any),
        ret_effect: Box::new(typed_ir::Type::Any),
        ret: Box::new(typed_ir::Type::Fun {
            param: Box::new(range),
            param_effect: Box::new(typed_ir::Type::Any),
            ret_effect: Box::new(typed_ir::Type::Any),
            ret: Box::new(typed_ir::Type::Fun {
                param: Box::new(list.clone()),
                param_effect: Box::new(typed_ir::Type::Any),
                ret_effect: Box::new(typed_ir::Type::Any),
                ret: Box::new(list),
            }),
        }),
    }
}

fn list_splice_raw_scheme_body() -> typed_ir::Type {
    let item = typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()));
    let list = typed_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![typed_ir::TypeArg::Type(item.clone())],
    };
    let int_ty = typed_ir::Type::Named {
        path: named_runtime_path("int"),
        args: vec![],
    };
    typed_ir::Type::Fun {
        param: Box::new(list.clone()),
        param_effect: Box::new(typed_ir::Type::Any),
        ret_effect: Box::new(typed_ir::Type::Any),
        ret: Box::new(typed_ir::Type::Fun {
            param: Box::new(int_ty.clone()),
            param_effect: Box::new(typed_ir::Type::Any),
            ret_effect: Box::new(typed_ir::Type::Any),
            ret: Box::new(typed_ir::Type::Fun {
                param: Box::new(int_ty),
                param_effect: Box::new(typed_ir::Type::Any),
                ret_effect: Box::new(typed_ir::Type::Any),
                ret: Box::new(typed_ir::Type::Fun {
                    param: Box::new(list.clone()),
                    param_effect: Box::new(typed_ir::Type::Any),
                    ret_effect: Box::new(typed_ir::Type::Any),
                    ret: Box::new(list),
                }),
            }),
        }),
    }
}

fn list_view_scheme_body() -> typed_ir::Type {
    let item = typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()));
    let list = typed_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![typed_ir::TypeArg::Type(item.clone())],
    };
    let list_view = typed_ir::Type::Named {
        path: named_runtime_path("list_view"),
        args: vec![typed_ir::TypeArg::Type(item)],
    };
    typed_ir::Type::Fun {
        param: Box::new(list.clone()),
        param_effect: Box::new(typed_ir::Type::Any),
        ret_effect: Box::new(typed_ir::Type::Any),
        ret: Box::new(list_view),
    }
}

fn list_view_pos_type(state: &LowerState, item_tv: crate::ids::TypeVar) -> Pos {
    state.pos_con(
        named_path("list_view"),
        vec![(Pos::Var(item_tv), Neg::Var(item_tv))],
    )
}

fn list_view_neg_type(state: &LowerState, item_tv: crate::ids::TypeVar) -> Neg {
    state.neg_con(
        named_path("list_view"),
        vec![(Pos::Var(item_tv), Neg::Var(item_tv))],
    )
}
