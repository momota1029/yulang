use std::collections::HashMap;

use crate::ids::{DefId, NegId, PosId, TypeVar};
use crate::simplify::compact::CompactType;
use crate::simplify::cooccur::CompactRoleConstraint;
use crate::symbols::{Name, Path};

pub(crate) fn role_method_info_for_path(
    role_methods: &HashMap<Name, RoleMethodInfo>,
    path: &Path,
) -> Option<RoleMethodInfo> {
    (path.segments.len() > 1).then_some(())?;
    let name = Name(path.segments.last()?.0.clone());
    let role_prefix = path.segments[..path.segments.len() - 1]
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>();
    role_methods
        .get(&name)
        .filter(|info| {
            role_prefix
                == info
                    .role
                    .segments
                    .iter()
                    .map(|segment| segment.0.as_str())
                    .collect::<Vec<_>>()
                || role_prefix.ends_with(
                    &info
                        .role
                        .segments
                        .iter()
                        .map(|segment| segment.0.as_str())
                        .collect::<Vec<_>>(),
                )
        })
        .cloned()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleConstraintArg {
    pub pos: PosId,
    pub neg: NegId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleConstraint {
    pub role: Path,
    pub args: Vec<RoleConstraintArg>,
}

#[derive(Debug, Clone)]
pub struct RoleMethodInfo {
    pub name: Name,
    pub def: DefId,
    pub role: Path,
    pub args: Vec<TypeVar>,
    pub sig: Option<crate::lower::signature::SigType>,
    pub has_receiver: bool,
    pub has_default_body: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleArgInfo {
    pub name: String,
    pub is_input: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleImplCandidate {
    pub role: Path,
    pub args: Vec<String>,
    pub compact_args: Vec<CompactType>,
    pub prerequisites: Vec<CompactRoleConstraint>,
    pub member_defs: HashMap<Name, DefId>,
}
