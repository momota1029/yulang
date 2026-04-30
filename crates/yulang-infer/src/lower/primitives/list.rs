use yulang_core_ir as core_ir;

use crate::ast::expr::TypedExpr;
use crate::lower::LowerState;
use crate::symbols::{ModuleId, Name, Path};
use crate::types::{Neg, Pos};

use super::support::{named_path, named_runtime_path};

pub(super) fn install_list_len_primitive(
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
            body: list_len_scheme_body(),
        },
    );
}

pub(super) fn install_list_index_primitive(
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
            body: list_index_scheme_body(),
        },
    );
}

pub(super) fn install_list_index_range_primitive(
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
    let item_tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let list_path = named_path("list");
    let range_path = Path {
        segments: vec![
            Name("std".to_string()),
            Name("range".to_string()),
            Name("range".to_string()),
        ],
    };
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
            body: list_index_range_scheme_body(),
        },
    );
}

pub(super) fn install_list_empty_primitive(
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
            body: list_empty_scheme_body(),
        },
    );
}

pub(super) fn install_list_splice_primitive(
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
    let item_tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.register_def_name(def, name.clone());
    state.insert_value(module, name, def);

    let list_path = named_path("list");
    let range_path = Path {
        segments: vec![
            Name("std".to_string()),
            Name("range".to_string()),
            Name("range".to_string()),
        ],
    };
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
            body: list_splice_scheme_body(),
        },
    );
}

pub(super) fn install_list_singleton_primitive(
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
            body: list_singleton_scheme_body(),
        },
    );
}

pub(super) fn install_list_merge_primitive(
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
            body: list_merge_scheme_body(),
        },
    );
}

pub(super) fn install_list_index_range_raw_primitive(
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
            body: list_index_range_raw_scheme_body(),
        },
    );
}

pub(super) fn install_list_splice_raw_primitive(
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
            body: list_splice_raw_scheme_body(),
        },
    );
}

pub(super) fn install_list_view_raw_primitive(
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
            body: list_view_scheme_body(),
        },
    );
}

fn list_len_scheme_body() -> core_ir::Type {
    let item = core_ir::Type::Var(core_ir::TypeVar("a".to_string()));
    let list = core_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![core_ir::TypeArg::Type(item)],
    };
    let int_ty = core_ir::Type::Named {
        path: named_runtime_path("int"),
        args: vec![],
    };
    core_ir::Type::Fun {
        param: Box::new(list),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(int_ty),
    }
}

fn list_empty_scheme_body() -> core_ir::Type {
    let unit = core_ir::Type::Named {
        path: named_runtime_path("unit"),
        args: vec![],
    };
    let item = core_ir::Type::Var(core_ir::TypeVar("a".to_string()));
    let list = core_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![core_ir::TypeArg::Type(item)],
    };
    core_ir::Type::Fun {
        param: Box::new(unit),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(list),
    }
}

fn list_singleton_scheme_body() -> core_ir::Type {
    let item = core_ir::Type::Var(core_ir::TypeVar("a".to_string()));
    let list = core_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![core_ir::TypeArg::Type(item.clone())],
    };
    core_ir::Type::Fun {
        param: Box::new(item),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(list),
    }
}

fn list_index_scheme_body() -> core_ir::Type {
    let item = core_ir::Type::Var(core_ir::TypeVar("a".to_string()));
    let list = core_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![core_ir::TypeArg::Type(item.clone())],
    };
    let int_ty = core_ir::Type::Named {
        path: named_runtime_path("int"),
        args: vec![],
    };
    core_ir::Type::Fun {
        param: Box::new(list),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(core_ir::Type::Fun {
            param: Box::new(int_ty),
            param_effect: Box::new(core_ir::Type::Any),
            ret_effect: Box::new(core_ir::Type::Any),
            ret: Box::new(item),
        }),
    }
}

fn list_merge_scheme_body() -> core_ir::Type {
    let item = core_ir::Type::Var(core_ir::TypeVar("a".to_string()));
    let list = core_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![core_ir::TypeArg::Type(item.clone())],
    };
    core_ir::Type::Fun {
        param: Box::new(list.clone()),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(core_ir::Type::Fun {
            param: Box::new(list.clone()),
            param_effect: Box::new(core_ir::Type::Any),
            ret_effect: Box::new(core_ir::Type::Any),
            ret: Box::new(list),
        }),
    }
}

fn list_index_range_raw_scheme_body() -> core_ir::Type {
    let item = core_ir::Type::Var(core_ir::TypeVar("a".to_string()));
    let list = core_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![core_ir::TypeArg::Type(item.clone())],
    };
    let int_ty = core_ir::Type::Named {
        path: named_runtime_path("int"),
        args: vec![],
    };
    core_ir::Type::Fun {
        param: Box::new(list.clone()),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(core_ir::Type::Fun {
            param: Box::new(int_ty.clone()),
            param_effect: Box::new(core_ir::Type::Any),
            ret_effect: Box::new(core_ir::Type::Any),
            ret: Box::new(core_ir::Type::Fun {
                param: Box::new(int_ty),
                param_effect: Box::new(core_ir::Type::Any),
                ret_effect: Box::new(core_ir::Type::Any),
                ret: Box::new(list),
            }),
        }),
    }
}

fn list_index_range_scheme_body() -> core_ir::Type {
    let item = core_ir::Type::Var(core_ir::TypeVar("a".to_string()));
    let list = core_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![core_ir::TypeArg::Type(item.clone())],
    };
    let range = core_ir::Type::Named {
        path: named_runtime_path("range"),
        args: vec![],
    };
    core_ir::Type::Fun {
        param: Box::new(list.clone()),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(core_ir::Type::Fun {
            param: Box::new(range),
            param_effect: Box::new(core_ir::Type::Any),
            ret_effect: Box::new(core_ir::Type::Any),
            ret: Box::new(list),
        }),
    }
}

fn list_splice_scheme_body() -> core_ir::Type {
    let item = core_ir::Type::Var(core_ir::TypeVar("a".to_string()));
    let list = core_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![core_ir::TypeArg::Type(item.clone())],
    };
    let range = core_ir::Type::Named {
        path: named_runtime_path("range"),
        args: vec![],
    };
    core_ir::Type::Fun {
        param: Box::new(list.clone()),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(core_ir::Type::Fun {
            param: Box::new(range),
            param_effect: Box::new(core_ir::Type::Any),
            ret_effect: Box::new(core_ir::Type::Any),
            ret: Box::new(core_ir::Type::Fun {
                param: Box::new(list.clone()),
                param_effect: Box::new(core_ir::Type::Any),
                ret_effect: Box::new(core_ir::Type::Any),
                ret: Box::new(list),
            }),
        }),
    }
}

fn list_splice_raw_scheme_body() -> core_ir::Type {
    let item = core_ir::Type::Var(core_ir::TypeVar("a".to_string()));
    let list = core_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![core_ir::TypeArg::Type(item.clone())],
    };
    let int_ty = core_ir::Type::Named {
        path: named_runtime_path("int"),
        args: vec![],
    };
    core_ir::Type::Fun {
        param: Box::new(list.clone()),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(core_ir::Type::Fun {
            param: Box::new(int_ty.clone()),
            param_effect: Box::new(core_ir::Type::Any),
            ret_effect: Box::new(core_ir::Type::Any),
            ret: Box::new(core_ir::Type::Fun {
                param: Box::new(int_ty),
                param_effect: Box::new(core_ir::Type::Any),
                ret_effect: Box::new(core_ir::Type::Any),
                ret: Box::new(core_ir::Type::Fun {
                    param: Box::new(list.clone()),
                    param_effect: Box::new(core_ir::Type::Any),
                    ret_effect: Box::new(core_ir::Type::Any),
                    ret: Box::new(list),
                }),
            }),
        }),
    }
}

fn list_view_scheme_body() -> core_ir::Type {
    let item = core_ir::Type::Var(core_ir::TypeVar("a".to_string()));
    let list = core_ir::Type::Named {
        path: named_runtime_path("list"),
        args: vec![core_ir::TypeArg::Type(item.clone())],
    };
    let list_view = core_ir::Type::Named {
        path: core_ir::Path {
            segments: vec![
                core_ir::Name("std".to_string()),
                core_ir::Name("list".to_string()),
                core_ir::Name("list_view".to_string()),
            ],
        },
        args: vec![core_ir::TypeArg::Type(item)],
    };
    core_ir::Type::Fun {
        param: Box::new(list.clone()),
        param_effect: Box::new(core_ir::Type::Any),
        ret_effect: Box::new(core_ir::Type::Any),
        ret: Box::new(list_view),
    }
}

fn list_view_pos_type(state: &LowerState, item_tv: crate::ids::TypeVar) -> Pos {
    state.pos_con(
        Path {
            segments: vec![
                Name("std".to_string()),
                Name("list".to_string()),
                Name("list_view".to_string()),
            ],
        },
        vec![(Pos::Var(item_tv), Neg::Var(item_tv))],
    )
}

fn list_view_neg_type(state: &LowerState, item_tv: crate::ids::TypeVar) -> Neg {
    state.neg_con(
        Path {
            segments: vec![
                Name("std".to_string()),
                Name("list".to_string()),
                Name("list_view".to_string()),
            ],
        },
        vec![(Pos::Var(item_tv), Neg::Var(item_tv))],
    )
}
