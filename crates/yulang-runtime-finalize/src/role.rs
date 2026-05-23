use yulang_typed_ir as typed_ir;

use crate::diagnostic::{FinalizeDiagnostic, FinalizeError, FinalizeResult};
use crate::types::{LowerSubstitutions, materialize_core_type, unify_core_types};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleContext {
    impls: Vec<typed_ir::RoleImplGraphNode>,
}

impl RoleContext {
    pub fn new(impls: impl IntoIterator<Item = typed_ir::RoleImplGraphNode>) -> Self {
        Self {
            impls: impls.into_iter().collect(),
        }
    }

    pub fn project_associated(
        &self,
        role: &typed_ir::Path,
        input_lowers: &[typed_ir::Type],
        associated_name: &typed_ir::Name,
    ) -> FinalizeResult<AssociatedProjection> {
        let mut matches = Vec::new();
        for impl_node in self
            .impls
            .iter()
            .filter(|impl_node| &impl_node.role == role)
        {
            let Some(substitutions) = match_impl_inputs(impl_node, input_lowers)? else {
                continue;
            };
            let Some(associated) = impl_node
                .associated_types
                .iter()
                .find(|field| &field.name == associated_name)
            else {
                continue;
            };
            let Some(lower) = associated.value.lower.as_ref() else {
                continue;
            };
            matches.push(materialize_core_type((**lower).clone(), &substitutions));
        }

        match matches.as_slice() {
            [] => Ok(AssociatedProjection {
                status: RoleProjectionStatus::Missing,
                ty: None,
            }),
            [ty] => Ok(AssociatedProjection {
                status: RoleProjectionStatus::Resolved,
                ty: Some(ty.clone()),
            }),
            _ => Ok(AssociatedProjection {
                status: RoleProjectionStatus::Ambiguous,
                ty: None,
            }),
        }
    }

    pub fn resolve_member(
        &self,
        role: &typed_ir::Path,
        input_lowers: &[typed_ir::Type],
        member_name: &typed_ir::Name,
    ) -> FinalizeResult<RoleMemberResolution> {
        let mut matches = Vec::new();
        for impl_node in self
            .impls
            .iter()
            .filter(|impl_node| &impl_node.role == role)
        {
            if !impl_inputs_accept(impl_node, input_lowers)? {
                continue;
            }
            let Some(member) = impl_node
                .members
                .iter()
                .find(|member| &member.name == member_name)
            else {
                continue;
            };
            matches.push(member.value.clone());
        }
        matches.sort_by_key(canonical_path);
        matches.dedup();

        match matches.as_slice() {
            [] => Ok(RoleMemberResolution {
                status: RoleProjectionStatus::Missing,
                binding: None,
            }),
            [binding] => Ok(RoleMemberResolution {
                status: RoleProjectionStatus::Resolved,
                binding: Some(binding.clone()),
            }),
            _ => Ok(RoleMemberResolution {
                status: RoleProjectionStatus::Ambiguous,
                binding: None,
            }),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssociatedProjection {
    pub status: RoleProjectionStatus,
    pub ty: Option<typed_ir::Type>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleMemberResolution {
    pub status: RoleProjectionStatus,
    pub binding: Option<typed_ir::Path>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoleProjectionStatus {
    Resolved,
    Missing,
    Ambiguous,
}

fn match_impl_inputs(
    impl_node: &typed_ir::RoleImplGraphNode,
    input_lowers: &[typed_ir::Type],
) -> FinalizeResult<Option<LowerSubstitutions>> {
    if impl_node.inputs.len() != input_lowers.len() {
        return Ok(None);
    }
    let mut substitutions = LowerSubstitutions::default();
    for (input, lower) in impl_node.inputs.iter().zip(input_lowers) {
        let Some(expected) = input.lower.as_ref() else {
            return Ok(None);
        };
        if let Err(err) = unify_core_types(&mut substitutions, expected, lower) {
            if matches!(
                err,
                FinalizeError::Diagnostic(FinalizeDiagnostic::ShapeMismatch { .. })
            ) {
                return Ok(None);
            }
            return Err(err);
        }
    }
    Ok(Some(substitutions))
}

fn impl_inputs_accept(
    impl_node: &typed_ir::RoleImplGraphNode,
    input_lowers: &[typed_ir::Type],
) -> FinalizeResult<bool> {
    if impl_node.inputs.is_empty() {
        return Ok(true);
    }
    match_impl_inputs(impl_node, input_lowers).map(|matched| matched.is_some())
}

pub(crate) fn role_method_parts(path: &typed_ir::Path) -> Option<(typed_ir::Path, typed_ir::Name)> {
    let (member_name, role_segments) = path.segments.split_last()?;
    if role_segments.is_empty() {
        return None;
    }
    Some((
        typed_ir::Path::new(role_segments.to_vec()),
        member_name.clone(),
    ))
}

fn canonical_path(path: &typed_ir::Path) -> Vec<String> {
    path.segments
        .iter()
        .map(|segment| segment.0.clone())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn role_context_projects_associated_type_from_input_lower() {
        let context = RoleContext::new([index_lines_impl()]);

        let projection = context
            .project_associated(
                &path(&["std", "index", "Index"]),
                &[lines_type(effect_var("fs"))],
                &typed_ir::Name("value".into()),
            )
            .unwrap();

        assert_eq!(projection.status, RoleProjectionStatus::Resolved);
        assert_eq!(projection.ty, Some(ref_str_type(effect_var("fs"))));
    }

    #[test]
    fn role_context_reports_missing_impl_without_synthesizing_type() {
        let context = RoleContext::new([index_lines_impl()]);

        let projection = context
            .project_associated(
                &path(&["std", "index", "Index"]),
                &[typed_ir::Type::Tuple(Vec::new())],
                &typed_ir::Name("value".into()),
            )
            .unwrap();

        assert_eq!(projection.status, RoleProjectionStatus::Missing);
        assert_eq!(projection.ty, None);
    }

    #[test]
    fn role_context_resolves_member_binding_from_input_lower() {
        let context = RoleContext::new([index_lines_impl()]);

        let resolution = context
            .resolve_member(
                &path(&["std", "index", "Index"]),
                &[lines_type(effect_var("fs"))],
                &typed_ir::Name("get".into()),
            )
            .unwrap();

        assert_eq!(resolution.status, RoleProjectionStatus::Resolved);
        assert_eq!(
            resolution.binding,
            Some(path(&["std", "index", "&impl#lines", "get"]))
        );
    }

    #[test]
    fn role_method_parts_splits_role_path_and_member_name() {
        assert_eq!(
            role_method_parts(&path(&["std", "index", "Index", "get"])),
            Some((
                path(&["std", "index", "Index"]),
                typed_ir::Name("get".into())
            ))
        );
        assert_eq!(role_method_parts(&path(&["get"])), None);
    }

    fn index_lines_impl() -> typed_ir::RoleImplGraphNode {
        typed_ir::RoleImplGraphNode {
            role: path(&["std", "index", "Index"]),
            inputs: vec![typed_ir::TypeBounds::lower(lines_type(
                typed_ir::Type::Var(typed_ir::TypeVar("e".into())),
            ))],
            associated_types: vec![typed_ir::RecordField {
                name: typed_ir::Name("value".into()),
                value: typed_ir::TypeBounds::lower(ref_str_type(typed_ir::Type::Var(
                    typed_ir::TypeVar("e".into()),
                ))),
                optional: false,
            }],
            members: vec![typed_ir::RecordField {
                name: typed_ir::Name("get".into()),
                value: path(&["std", "index", "&impl#lines", "get"]),
                optional: false,
            }],
        }
    }

    fn lines_type(effect: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "string", "Lines"]),
            args: vec![typed_ir::TypeArg::Type(effect)],
        }
    }

    fn ref_str_type(effect: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "var", "Ref"]),
            args: vec![
                typed_ir::TypeArg::Type(effect),
                typed_ir::TypeArg::Type(typed_ir::Type::Named {
                    path: path(&["std", "string", "Str"]),
                    args: Vec::new(),
                }),
            ],
        }
    }

    fn effect_var(name: &str) -> typed_ir::Type {
        typed_ir::Type::Var(typed_ir::TypeVar(name.into()))
    }

    fn path(segments: &[&str]) -> typed_ir::Path {
        typed_ir::Path::new(
            segments
                .iter()
                .map(|segment| typed_ir::Name((*segment).into()))
                .collect(),
        )
    }
}
