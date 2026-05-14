use super::*;
use crate::types::EffectAtom;

mod throw;
mod up;
mod wrap;

pub(crate) use throw::lower_synthetic_error_throw;
pub(crate) use up::lower_synthetic_error_up;
pub(crate) use wrap::lower_synthetic_error_wrap;

#[derive(Debug, Clone)]
pub struct ErrorThrowVariant {
    pub(crate) payload_sig: Option<SigType>,
    pub(crate) constructor_def: crate::ids::DefId,
    pub(crate) operation_def: crate::ids::DefId,
}

#[derive(Debug, Clone)]
pub(crate) struct ErrorUpSource {
    pub(crate) source_sig: SigType,
    pub(crate) target_operation_def: crate::ids::DefId,
}

fn effect_atom_from_sig(
    state: &mut LowerState,
    sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) -> Option<EffectAtom> {
    match sig {
        SigType::Prim { path, .. } => Some(EffectAtom {
            path: path.clone(),
            args: Vec::new(),
        }),
        SigType::Apply { path, args, .. } => {
            let mut scope = impl_scope.clone();
            Some(EffectAtom {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| {
                        crate::lower::signature::lower_sig_effect_arg(state, arg, &mut scope)
                    })
                    .collect(),
            })
        }
        _ => None,
    }
}
fn effect_operation_surface_path(
    state: &LowerState,
    operation_def: crate::ids::DefId,
) -> Option<Path> {
    let mut path = state
        .ctx
        .canonical_value_paths()
        .get(&operation_def)
        .cloned()?;
    let last = path.segments.last_mut()?;
    if let Some(surface) = last.0.strip_suffix("#effect") {
        *last = Name(surface.to_string());
    }
    Some(path)
}

fn nominal_sig_effect_path(state: &LowerState, sig: &SigType) -> Option<Path> {
    match sig {
        SigType::Prim { path, .. } | SigType::Apply { path, .. } => {
            Some(state.ctx.canonical_current_type_path(path))
        }
        _ => None,
    }
}

fn never_sig(span: rowan::TextRange) -> SigType {
    SigType::Prim {
        path: Path {
            segments: vec![Name("never".to_string())],
        },
        span,
    }
}
