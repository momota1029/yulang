use std::collections::HashMap;

use crate::diagnostic::TypeOrigin;
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
    let role_prefix = &path.segments[..path.segments.len() - 1];
    role_methods
        .get(&name)
        .filter(|info| role_prefix == info.role.segments.as_slice())
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
    pub input_names: Vec<Option<String>>,
    pub output_name: Option<String>,
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
    pub origins: Vec<TypeOrigin>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedRoleMethodSelection {
    pub role: Path,
    pub member: DefId,
    pub impl_member: DefId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleMethodCallSelection {
    pub role: Path,
    pub member: DefId,
    pub recv_tv: TypeVar,
    pub arg_tvs: Vec<TypeVar>,
    pub result_tv: TypeVar,
}
