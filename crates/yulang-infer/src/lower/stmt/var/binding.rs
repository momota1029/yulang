use crate::profile::ProfileClock as Instant;

use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{PatKind, TypedExpr, TypedPat, TypedStmt};
use crate::ids::{DefId, TypeVar};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

use super::sigil::VarBinding;

#[derive(Debug, Clone)]
struct PreparedVarBinding {
    binding: VarBinding,
    act: super::super::SyntheticActSpec,
    needs_ref_binding: bool,
    helper_source: Option<super::super::SyntheticActSource>,
}

#[derive(Debug, Clone, Copy, Default)]
struct VarBindingUsage {
    reads_reference: bool,
}

pub(crate) fn lower_var_binding_suffix(
    state: &mut LowerState,
    bindings: &[VarBinding],
    suffix_items: &[SyntaxNode],
    stmts: &mut Vec<TypedStmt>,
    tail: &mut Option<Box<TypedExpr>>,
) {
    let start = Instant::now();
    let prepared = prepare_var_bindings(state, bindings, suffix_items);

    for item in &prepared {
        materialize_var_act_helpers(state, &item.act, item.helper_source.as_ref());
    }

    for item in &prepared {
        if item.needs_ref_binding {
            if let Some(stmt) = lower_var_ref_binding(state, &item.binding, &item.act.name) {
                stmts.push(stmt);
            }
        } else {
            register_var_ref_alias(state, &item.binding, &item.act.name);
        }
    }

    let mut body = super::super::lower_block_expr_from_items(state, suffix_items);
    for item in prepared.iter().rev() {
        body = lower_var_run_expr(state, &item.act.name, &item.binding, body);
    }
    tail.replace(Box::new(body));
    state.lower_detail.lower_var_binding_suffix += start.elapsed();
}

fn prepare_var_bindings(
    state: &mut LowerState,
    bindings: &[VarBinding],
    suffix_items: &[SyntaxNode],
) -> Vec<PreparedVarBinding> {
    bindings
        .iter()
        .cloned()
        .map(|binding| {
            let usage = analyze_var_binding_usage(&binding, suffix_items);
            prepare_var_binding(state, binding, usage)
        })
        .collect()
}

fn analyze_var_binding_usage(binding: &VarBinding, suffix_items: &[SyntaxNode]) -> VarBindingUsage {
    VarBindingUsage {
        reads_reference: block_items_contain_reference_read(suffix_items, &binding.reference.0),
    }
}

fn block_items_contain_reference_read(items: &[SyntaxNode], text: &str) -> bool {
    items
        .iter()
        .any(|item| syntax_node_contains_reference_read(item, text))
}

fn syntax_node_contains_reference_read(node: &SyntaxNode, text: &str) -> bool {
    node.descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .any(|tok| {
            tok.kind() == SyntaxKind::SigilIdent
                && tok.text() == text
                && !sigil_token_is_assignment_target(&tok)
        })
}

fn sigil_token_is_assignment_target(
    token: &rowan::SyntaxToken<yulang_parser::sink::YulangLanguage>,
) -> bool {
    let mut node = token.parent();
    while let Some(parent) = node {
        let has_assign_suffix = parent
            .children()
            .any(|child| child.kind() == SyntaxKind::Assign);
        let projects_reference = parent
            .children()
            .any(|child| matches!(child.kind(), SyntaxKind::Field | SyntaxKind::Index));
        if has_assign_suffix && !projects_reference {
            return true;
        }
        node = parent.parent();
    }
    false
}

fn prepare_var_binding(
    state: &mut LowerState,
    binding: VarBinding,
    usage: VarBindingUsage,
) -> PreparedVarBinding {
    let act_name = scoped_var_act_name(&binding, state.current_owner);
    let init_def = ensure_var_init_binding(state, &binding.init);
    let act = super::super::unary_synthetic_act_spec(state, act_name);
    if let Some(&init_tv) = state.def_tvs.get(&init_def) {
        let act_tv = act.args[0].0;
        state.infer.constrain(Pos::Var(init_tv), Neg::Var(act_tv));
        state.infer.constrain(Pos::Var(act_tv), Neg::Var(init_tv));
    }
    super::super::register_synthetic_act_identity(state, &act);
    let helper_source = Some(std_var_synthetic_act_source(selected_var_helper_names(
        usage,
    )));
    PreparedVarBinding {
        binding,
        act,
        needs_ref_binding: usage.reads_reference,
        helper_source,
    }
}

fn register_var_ref_alias(state: &mut LowerState, binding: &VarBinding, act_name: &Name) {
    state
        .ctx
        .bind_var_ref_alias(binding.reference.clone(), act_name.clone());
}

fn lower_var_ref_binding(
    state: &mut LowerState,
    binding: &VarBinding,
    act_name: &Name,
) -> Option<TypedStmt> {
    let def = define_local_value(state, binding.reference.clone());
    state
        .ctx
        .bind_var_ref_alias(binding.reference.clone(), act_name.clone());
    state.var_ref_acts.insert(def, act_name.clone());
    let tv = state.def_tvs.get(&def).copied()?;
    let body = state.with_owner(def, |state| {
        let var_ref = crate::lower::expr::resolve_path_expr(
            state,
            vec![act_name.clone(), Name("var_ref".to_string())],
        );
        let unit = crate::lower::expr::unit_expr(state);
        crate::lower::expr::make_app(state, var_ref, unit)
    });
    state.infer.constrain(Pos::Var(body.tv), Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), Neg::Var(body.tv));
    constrain_var_ref_binding_to_init(state, tv, binding);
    Some(TypedStmt::Let(
        TypedPat {
            tv,
            kind: PatKind::UnresolvedName(binding.reference.clone()),
        },
        body,
    ))
}

fn constrain_var_ref_binding_to_init(
    state: &mut LowerState,
    ref_tv: TypeVar,
    binding: &VarBinding,
) {
    let Some(init_tv) = state
        .ctx
        .resolve_value(&binding.init)
        .and_then(|def| state.def_tvs.get(&def).copied())
    else {
        return;
    };
    let eff_tv = state.fresh_tv();
    let ref_args = invariant_ref_args(state, &[(eff_tv, eff_tv), (init_tv, init_tv)]);
    state
        .infer
        .constrain(Pos::Con(std_var_ref_path(), ref_args), Neg::Var(ref_tv));
}

fn lower_var_run_expr(
    state: &mut LowerState,
    act_name: &Name,
    binding: &VarBinding,
    body: TypedExpr,
) -> TypedExpr {
    let run = crate::lower::expr::resolve_path_expr(
        state,
        vec![act_name.clone(), Name("run".to_string())],
    );
    let init = crate::lower::expr::resolve_path_expr(state, vec![binding.init.clone()]);
    let run_with_init = crate::lower::expr::make_app(state, run, init);
    crate::lower::expr::make_app(state, run_with_init, body)
}

fn ensure_var_init_binding(state: &mut LowerState, name: &Name) -> DefId {
    state
        .ctx
        .resolve_value(name)
        .unwrap_or_else(|| define_local_value(state, name.clone()))
}

fn selected_var_helper_names(usage: VarBindingUsage) -> Vec<Name> {
    let mut names = vec![
        Name("run".to_string()),
        Name("get".to_string()),
        Name("set".to_string()),
    ];
    if usage.reads_reference {
        names.push(Name("var_ref".to_string()));
    }
    names
}

fn materialize_var_act_helpers(
    state: &mut LowerState,
    spec: &super::super::SyntheticActSpec,
    helper_source: Option<&super::super::SyntheticActSource>,
) {
    let Some(source) = helper_source else {
        return;
    };
    super::super::materialize_synthetic_act(state, spec, source);
}

fn std_var_synthetic_act_source(selected_names: Vec<Name>) -> super::super::SyntheticActSource {
    let source_path = Path {
        segments: vec![
            Name("std".to_string()),
            Name("var".to_string()),
            Name("var".to_string()),
        ],
    };
    super::super::SyntheticActSource {
        source_module_path: source_path.clone(),
        source_copy_path: source_path,
        selected_values: selected_names,
        selected_template_items: Vec::new(),
    }
}

fn define_local_value(state: &mut LowerState, name: Name) -> DefId {
    if let Some(def) = state.ctx.resolve_value(&name) {
        return def;
    }
    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.mark_let_bound_def(def);
    if let Some(owner) = state.current_owner {
        state.register_def_owner(def, owner);
    }
    state.register_def_name(def, name.clone());
    state.ctx.bind_local(name, def);
    def
}

fn scoped_var_act_name(binding: &VarBinding, owner: Option<DefId>) -> Name {
    let Some(owner) = owner else {
        return binding.reference.clone();
    };
    Name(format!("{}#{}", binding.reference.0, owner.0))
}

fn invariant_ref_args(
    state: &LowerState,
    tvs: &[(TypeVar, TypeVar)],
) -> Vec<(crate::ids::PosId, crate::ids::NegId)> {
    tvs.iter()
        .map(|&(lower, upper)| {
            (
                state.infer.alloc_pos(Pos::Var(lower)),
                state.infer.alloc_neg(Neg::Var(upper)),
            )
        })
        .collect()
}

fn std_var_ref_path() -> Path {
    Path {
        segments: vec![
            Name("std".to_string()),
            Name("var".to_string()),
            Name("ref".to_string()),
        ],
    }
}
