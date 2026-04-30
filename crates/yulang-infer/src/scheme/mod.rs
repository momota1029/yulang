use std::collections::HashSet;
use std::rc::Rc;

use smallvec::SmallVec;

use crate::ids::{PosId, TypeVar};
use crate::simplify::compact::CompactTypeScheme;
use crate::types::arena::TypeArena;

pub mod freeze;
pub mod instantiate;
pub mod view;

pub type SmallSubst = SmallVec<[(TypeVar, TypeVar); 8]>;
pub type FrozenArena = Rc<TypeArena>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scheme {
    pub arena: FrozenArena,
    pub compact: CompactTypeScheme,
    pub body: PosId,
    pub quantified: Vec<TypeVar>,
    pub quantified_sources: SmallSubst,
    pub through: HashSet<TypeVar>,
}

pub type FrozenScheme = Rc<Scheme>;

pub use freeze::{
    clone_neg_between_arenas, clone_pos_between_arenas, collect_neg_free_vars,
    collect_neg_free_vars_in_arena, collect_pos_free_vars, collect_pos_free_vars_in_arena,
    compact_scheme_from_pos_body, compact_scheme_from_pos_body_in_arena,
    freeze_compact_scheme_with_non_generic, freeze_pos_scheme, freeze_pos_scheme_with_non_generic,
    freeze_type_var, freeze_type_var_with_non_generic,
};
pub use instantiate::{
    InstantiateFrozenProfile, instantiate_as_view, instantiate_as_view_with_subst,
    instantiate_as_view_with_subst_profiled, instantiate_frozen_body,
    instantiate_frozen_body_with_subst, instantiate_frozen_body_with_subst_profiled,
    instantiate_frozen_scheme, instantiate_frozen_scheme_with_subst,
    instantiate_frozen_scheme_with_subst_profiled,
};
pub use view::{
    OwnedSchemeInstance, SchemeInstance, materialize_body, read_neg_with_subst, read_pos_with_subst,
};

pub(crate) use freeze::{
    collect_compact_role_constraint_free_vars, compact_pos_type,
    freeze_compact_scheme_owned_with_non_generic_and_extra_vars,
    freeze_compact_scheme_with_non_generic_and_extra_vars,
};
pub(crate) use instantiate::{subst_neg_id, subst_neg_id_map, subst_pos_id, subst_pos_id_map};
