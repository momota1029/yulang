//! Conservative eligibility check for the std-prefix cache boundary.
//!
//! A finalized prefix omits the live constraint topology that existed while it
//! was inferred. Programs whose suffix introduces prerequisite-bearing role
//! candidates may depend on that topology. This module rejects that combination
//! before warm lowering starts; the caller then follows the existing full-miss
//! path.

use std::collections::HashSet;

use parser::lex::SyntaxKind;
use parser::sink::YulangLanguage;
use poly::expr::Def;
use poly::roles::RoleImplCandidate;
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RolePredicateArg, Scheme, StackWeight, Subtractability,
    TypeArena, TypeVar,
};
use rowan::SyntaxNode;

use yulang::cache::CachedCompiledUnitArtifact;
use yulang::source::CollectedSource;

/// Return whether this program can safely use the finalized std prefix.
///
/// The prefix remains eligible unless both sides of the unsafe boundary are
/// present: the suffix builds live role-prerequisite relationships, and the
/// cached poly surface contains an interface that is not structurally closed.
pub(super) fn can_reuse_for_program(
    files: &[CollectedSource],
    prefix_file_indices: &[usize],
    prefix: &CachedCompiledUnitArtifact,
) -> bool {
    if !suffix_has_prerequisite_role_impl(files, prefix_file_indices, prefix) {
        return true;
    }

    !cached_surface_has_open_role_boundary(prefix)
}

fn suffix_has_prerequisite_role_impl(
    files: &[CollectedSource],
    prefix_file_indices: &[usize],
    prefix: &CachedCompiledUnitArtifact,
) -> bool {
    let prefix_files = prefix_file_indices.iter().copied().collect::<HashSet<_>>();
    let suffix = files
        .iter()
        .enumerate()
        .filter(|(index, _)| !prefix_files.contains(index))
        .map(|(_, file)| sources::SourceFile {
            module_path: file.module_path.clone(),
            source: file.source.clone(),
        })
        .collect::<Vec<_>>();
    let band_paths = files
        .iter()
        .enumerate()
        .filter(|(index, _)| !prefix_files.contains(index))
        .map(|(_, file)| file.band_path.clone())
        .collect::<Vec<_>>();
    let loaded =
        sources::load_suffix_with_syntax_prefix_and_band_paths(&prefix.syntax, suffix, band_paths);

    loaded.iter().any(|file| {
        let root = SyntaxNode::<YulangLanguage>::new_root(file.cst.clone());
        cst_has_prerequisite_role_impl(&root)
    })
}

fn cst_has_prerequisite_role_impl(root: &SyntaxNode<YulangLanguage>) -> bool {
    root.descendants()
        .filter(|node| node.kind() == SyntaxKind::ImplDecl)
        .any(|implementation| {
            implementation
                .descendants()
                .any(|node| node.kind() == SyntaxKind::WhereClause)
        })
}

fn cached_surface_has_open_role_boundary(prefix: &CachedCompiledUnitArtifact) -> bool {
    let arena = &prefix.runtime.arena.typ;
    prefix
        .runtime
        .arena
        .defs
        .iter()
        .filter_map(|(_, def)| match def {
            Def::Let {
                scheme: Some(scheme),
                ..
            } => Some(scheme),
            Def::Mod { .. } | Def::Let { .. } | Def::Arg => None,
        })
        .any(|scheme| scheme_has_open_boundary(arena, scheme))
        || prefix
            .runtime
            .arena
            .role_impls
            .iter()
            .any(|candidate| candidate_has_open_prerequisite(arena, candidate))
}

fn candidate_has_open_prerequisite(arena: &TypeArena, candidate: &RoleImplCandidate) -> bool {
    let head_vars = candidate.as_constraint().raw_vars(arena);
    candidate
        .prerequisites
        .iter()
        .any(|prerequisite| !prerequisite.raw_vars(arena).is_subset(&head_vars))
}

fn scheme_has_open_boundary(arena: &TypeArena, scheme: &Scheme) -> bool {
    let mut all = TypeVarScan::new(arena);
    all.pos(scheme.predicate);
    all.scheme_role_predicates(scheme);
    for bound in &scheme.recursive_bounds {
        all.vars.insert(bound.var);
        all.neu(bound.bounds);
    }

    let mut closed = scheme.quantifiers.iter().copied().collect::<HashSet<_>>();
    closed.extend(scheme.recursive_bounds.iter().map(|bound| bound.var));
    if !all.vars.is_subset(&closed) {
        return true;
    }

    if scheme.role_predicates.is_empty() {
        return false;
    }

    let mut role_vars = TypeVarScan::new(arena);
    role_vars.scheme_role_predicates(scheme);

    let mut anchors = TypeVarScan::new(arena);
    anchors.pos(scheme.predicate);
    for bound in &scheme.recursive_bounds {
        anchors.vars.insert(bound.var);
        anchors.neu(bound.bounds);
    }
    !role_vars.vars.is_subset(&anchors.vars)
}

struct TypeVarScan<'a> {
    arena: &'a TypeArena,
    vars: HashSet<TypeVar>,
    pos_seen: HashSet<PosId>,
    neg_seen: HashSet<NegId>,
    neu_seen: HashSet<NeuId>,
}

impl<'a> TypeVarScan<'a> {
    fn new(arena: &'a TypeArena) -> Self {
        Self {
            arena,
            vars: HashSet::new(),
            pos_seen: HashSet::new(),
            neg_seen: HashSet::new(),
            neu_seen: HashSet::new(),
        }
    }

    fn scheme_role_predicates(&mut self, scheme: &Scheme) {
        for predicate in &scheme.role_predicates {
            for input in &predicate.inputs {
                match input {
                    RolePredicateArg::Covariant(id) => self.pos(*id),
                    RolePredicateArg::Contravariant(id) => self.neg(*id),
                    RolePredicateArg::Invariant(id) => self.neu(*id),
                }
            }
            for associated in &predicate.associated {
                self.neu(associated.value);
            }
        }
    }

    fn pos(&mut self, id: PosId) {
        if !self.pos_seen.insert(id) {
            return;
        }
        match self.arena.pos(id) {
            Pos::Bot => {}
            Pos::Var(var) => {
                self.vars.insert(*var);
            }
            Pos::Con(_, args) => self.neu_slice(args),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.neg(*arg);
                self.neg(*arg_eff);
                self.pos(*ret_eff);
                self.pos(*ret);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.pos(field.value);
                }
            }
            Pos::RecordTailSpread { fields, tail } | Pos::RecordHeadSpread { tail, fields } => {
                for field in fields {
                    self.pos(field.value);
                }
                self.pos(*tail);
            }
            Pos::PolyVariant(variants) => {
                for (_, payloads) in variants {
                    for payload in payloads {
                        self.pos(*payload);
                    }
                }
            }
            Pos::Tuple(items) | Pos::Row(items) => {
                for item in items {
                    self.pos(*item);
                }
            }
            Pos::Stack { inner, weight } => {
                self.pos(*inner);
                self.stack_weight(weight);
            }
            Pos::NonSubtract(inner, weight) => {
                self.pos(*inner);
                self.stack_weight(weight);
            }
            Pos::Union(left, right) => {
                self.pos(*left);
                self.pos(*right);
            }
        }
    }

    fn neg(&mut self, id: NegId) {
        if !self.neg_seen.insert(id) {
            return;
        }
        match self.arena.neg(id) {
            Neg::Top | Neg::Bot => {}
            Neg::Var(var) => {
                self.vars.insert(*var);
            }
            Neg::Con(_, args) => self.neu_slice(args),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.pos(*arg);
                self.pos(*arg_eff);
                self.neg(*ret_eff);
                self.neg(*ret);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.neg(field.value);
                }
            }
            Neg::PolyVariant(variants) => {
                for (_, payloads) in variants {
                    for payload in payloads {
                        self.neg(*payload);
                    }
                }
            }
            Neg::Tuple(items) => {
                for item in items {
                    self.neg(*item);
                }
            }
            Neg::Row(items, tail) => {
                for item in items {
                    self.neg(*item);
                }
                self.neg(*tail);
            }
            Neg::Stack { inner, weight } => {
                self.neg(*inner);
                self.stack_weight(weight);
            }
            Neg::Intersection(left, right) => {
                self.neg(*left);
                self.neg(*right);
            }
        }
    }

    fn neu(&mut self, id: NeuId) {
        if !self.neu_seen.insert(id) {
            return;
        }
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                self.pos(*lower);
                self.neg(*upper);
            }
            Neu::Con(_, args) => self.neu_slice(args),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.neu(*arg);
                self.neu(*arg_eff);
                self.neu(*ret_eff);
                self.neu(*ret);
            }
            Neu::Record(fields) => {
                for field in fields {
                    self.neu(field.value);
                }
            }
            Neu::PolyVariant(variants) => {
                for (_, payloads) in variants {
                    for payload in payloads {
                        self.neu(*payload);
                    }
                }
            }
            Neu::Tuple(items) => self.neu_slice(items),
        }
    }

    fn neu_slice(&mut self, ids: &[NeuId]) {
        for id in ids {
            self.neu(*id);
        }
    }

    fn stack_weight(&mut self, weight: &StackWeight) {
        self.subtractability(weight.filter_set());
        for entry in weight.entries() {
            for bound in entry.floor.iter().chain(&entry.stack) {
                self.subtractability(bound);
            }
        }
    }

    fn subtractability(&mut self, bound: &Subtractability) {
        match bound {
            Subtractability::Empty | Subtractability::All => {}
            Subtractability::AllExcept(_, args) | Subtractability::Set(_, args) => {
                self.neu_slice(args);
            }
            Subtractability::AllExceptMany(families) | Subtractability::SetMany(families) => {
                for (_, args) in families {
                    self.neu_slice(args);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prerequisite_bearing_impl_is_a_live_role_boundary() {
        let cst = parser::parse_module_to_green(
            "impl (Box 'a): Render:\n    where 'a: Render\n    our value.render _ = value\n",
        );
        let root = SyntaxNode::<YulangLanguage>::new_root(cst);

        assert!(cst_has_prerequisite_role_impl(&root));
    }

    #[test]
    fn role_predicate_without_impl_prerequisite_is_not_rejected() {
        let cst = parser::parse_module_to_green(
            "my render(value: 'a): str =\n    where 'a: Render\n    value.render ()\n",
        );
        let root = SyntaxNode::<YulangLanguage>::new_root(cst);

        assert!(!cst_has_prerequisite_role_impl(&root));
    }

    #[test]
    fn scheme_with_unquantified_free_variable_has_open_boundary() {
        let mut arena = TypeArena::new();
        let predicate = arena.alloc_pos(Pos::Var(TypeVar(0)));
        let scheme = Scheme {
            quantifiers: Vec::new(),
            role_predicates: Vec::new(),
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
        };

        assert!(scheme_has_open_boundary(&arena, &scheme));
    }

    #[test]
    fn candidate_prerequisite_must_only_use_head_variables() {
        let mut arena = TypeArena::new();
        let head_var = TypeVar(0);
        let hidden_var = TypeVar(1);
        let head = poly::roles::RoleConstraintArg {
            lower: arena.alloc_pos(Pos::Var(head_var)),
            upper: arena.alloc_neg(Neg::Var(head_var)),
        };
        let hidden = poly::roles::RoleConstraintArg {
            lower: arena.alloc_pos(Pos::Var(hidden_var)),
            upper: arena.alloc_neg(Neg::Var(hidden_var)),
        };
        let mut candidate = RoleImplCandidate {
            impl_def: None,
            role: vec!["Outer".into()],
            inputs: vec![head],
            associated: Vec::new(),
            prerequisites: vec![poly::roles::RoleConstraint {
                role: vec!["Inner".into()],
                inputs: vec![hidden],
                associated: Vec::new(),
            }],
            methods: Vec::new(),
        };

        assert!(candidate_has_open_prerequisite(&arena, &candidate));

        candidate.prerequisites[0].inputs[0] = head;
        assert!(!candidate_has_open_prerequisite(&arena, &candidate));
    }

    #[test]
    fn role_variable_anchored_in_quantified_predicate_is_closed() {
        let mut arena = TypeArena::new();
        let variable = TypeVar(0);
        let predicate = arena.alloc_pos(Pos::Var(variable));
        let upper = arena.alloc_neg(Neg::Var(variable));
        let scheme = Scheme {
            quantifiers: vec![variable],
            role_predicates: vec![poly::types::RolePredicate {
                role: vec!["Role".into()],
                inputs: vec![RolePredicateArg::Contravariant(upper)],
                associated: Vec::new(),
            }],
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
        };

        assert!(!scheme_has_open_boundary(&arena, &scheme));
    }

    #[test]
    fn role_variable_not_anchored_in_predicate_has_open_boundary() {
        let mut arena = TypeArena::new();
        let predicate_var = TypeVar(0);
        let role_var = TypeVar(1);
        let predicate = arena.alloc_pos(Pos::Var(predicate_var));
        let upper = arena.alloc_neg(Neg::Var(role_var));
        let scheme = Scheme {
            quantifiers: vec![predicate_var, role_var],
            role_predicates: vec![poly::types::RolePredicate {
                role: vec!["Role".into()],
                inputs: vec![RolePredicateArg::Contravariant(upper)],
                associated: Vec::new(),
            }],
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
        };

        assert!(scheme_has_open_boundary(&arena, &scheme));
    }
}
