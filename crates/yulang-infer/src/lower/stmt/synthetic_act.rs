use crate::ids::TypeVar;
use crate::lower::LowerState;
use crate::symbols::{Name, Path};
use yulang_parser::lex::SyntaxKind;

#[derive(Debug, Clone)]
pub(crate) struct SyntheticActSpec {
    pub(crate) name: Name,
    pub(crate) effect_path: Path,
    pub(crate) args: Vec<(TypeVar, TypeVar)>,
}

#[derive(Debug, Clone)]
pub(crate) struct SyntheticActSource {
    pub(crate) source_module_path: Path,
    pub(crate) source_copy_path: Path,
    pub(crate) selected_values: Vec<Name>,
    pub(crate) selected_template_items: Vec<Name>,
}

pub(crate) fn nullary_synthetic_act_spec(name: Name) -> SyntheticActSpec {
    SyntheticActSpec {
        name: name.clone(),
        effect_path: Path {
            segments: vec![name],
        },
        args: Vec::new(),
    }
}

pub(crate) fn unary_synthetic_act_spec(state: &LowerState, name: Name) -> SyntheticActSpec {
    let tv = state.fresh_tv();
    SyntheticActSpec {
        name: name.clone(),
        effect_path: Path {
            segments: vec![name],
        },
        args: vec![(tv, tv)],
    }
}

pub(crate) fn register_synthetic_act_identity(state: &mut LowerState, spec: &SyntheticActSpec) {
    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    let mid = state.ctx.current_module;
    state.insert_type(mid, spec.name.clone(), def);
    state
        .effect_arities
        .insert(spec.effect_path.clone(), spec.args.len());
    state
        .effect_args
        .insert(spec.effect_path.clone(), spec.args.clone());
}

pub(crate) fn materialize_synthetic_act(
    state: &mut LowerState,
    spec: &SyntheticActSpec,
    source: &SyntheticActSource,
) {
    super::with_companion_module(state, spec.name.clone(), |state| {
        materialize_template_items(state, spec, source);
        materialize_value_helpers(state, spec, source);
    });
}

fn materialize_template_items(
    state: &mut LowerState,
    spec: &SyntheticActSpec,
    source: &SyntheticActSource,
) {
    if source.selected_template_items.is_empty() {
        return;
    }
    let Some(template) = source_template(state, source) else {
        return;
    };
    let source_names = crate::lower::signature::act_type_param_names(&template);
    if source_names.len() != spec.args.len() {
        return;
    }
    let source_scope = source_names
        .into_iter()
        .zip(spec.args.iter())
        .map(|(name, (pos, _))| (name, *pos))
        .collect::<std::collections::HashMap<_, _>>();
    let act_arg_tvs = spec.args.iter().map(|(pos, _)| *pos).collect::<Vec<_>>();
    let Some(body) = template.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    }) else {
        return;
    };
    super::lower_act_body(
        state,
        &body,
        spec.effect_path.clone(),
        &source_scope,
        &act_arg_tvs,
        Some(&source.selected_template_items),
    );
}

fn materialize_value_helpers(
    state: &mut LowerState,
    spec: &SyntheticActSpec,
    source: &SyntheticActSource,
) {
    if source.selected_values.is_empty() {
        return;
    }
    let Some(source_module) = state.ctx.resolve_module_path(&source.source_module_path) else {
        return;
    };
    let copy = super::ActCopy {
        source_path: state
            .ctx
            .canonical_current_type_path(&source.source_module_path),
        source_args: spec.args.clone(),
        source_module,
        selected_names: Some(source.selected_values.clone()),
    };
    super::lower_act_copy_body(state, copy, &spec.effect_path, &spec.args);
}

fn source_template(
    state: &LowerState,
    source: &SyntheticActSource,
) -> Option<crate::lower::SyntaxNode> {
    state
        .act_templates
        .get(&source.source_module_path)
        .cloned()
        .or_else(|| state.act_templates.get(&source.source_copy_path).cloned())
}
