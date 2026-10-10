//! Exact structural context relation authority for the private candidate.
//! Derivations are a separate fiber: retaining another origin does not create
//! another semantic task or unfold a recursive identity derivation.
use crate::candidate_effect::BoundKey;
use crate::*;
use yu_hir::shadow::{SourceEffectId, SourceNodeKey};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct RelationId(pub u32);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct ContextId(u32);
const IDENTITY: ContextId = ContextId(0);
// A payload handle is independent of nominal members and boundary identities.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct LocalWeightId(u32);
#[derive(Debug)]
struct LocalWeight {
    left_word: [(); 0],
    allowed: Vec<SourceEffectId>,
    right_pops: [(); 0],
    boundary: u32,
    owner: DefinitionRootId,
    position: SourceNodeKey,
    attachment: Option<AttachmentSet>,
}
// The payload ID is the set identity; ordinals index its resolved allowed operands.
#[derive(Debug)]
struct AttachmentSet {
    composed_polarity: Polarity,
    lexical_scope: candidate_effect::AnnotationScope,
    member_ordinals: Vec<usize>,
    // Dormant source preparation only. The owning weight already retains the
    // exact resolved members; live zero-word/filter execution never reads this.
    unit_push: Option<SourceUnitPush>,
}
#[derive(Debug)]
struct SourceUnitPush;
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct AttachmentSource {
    pub composed_polarity: Polarity,
    pub lexical_scope: candidate_effect::AnnotationScope,
}
// These identities retain source construction only. They never enter a
// RelationKey, ContextExpr, executable View, or endpoint comparison.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) struct AttachmentBundleId(pub usize);
#[derive(Clone, Debug)]
#[cfg_attr(not(test), allow(dead_code, reason = "inert source provenance has no executable attachment consumer"))]
pub(super) struct EmptyAttachmentSet {
    pub owner: DefinitionRootId,
    pub position: SourceNodeKey,
    pub source: AttachmentSource,
}
#[derive(Clone, Debug)]
pub(super) struct AttachmentBundle {
    pub occurrence: ConstraintOccurrenceId,
    pub sets: Vec<EmptyAttachmentSet>,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct EntryCertificateId(u32);
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(
    not(test),
    allow(dead_code, reason = "context propagation is a later gate")
)]
enum ContextExpr {
    PrefixLeft {
        weight: LocalWeightId,
        input: ContextId,
    },
    SuffixRightPops {
        input: ContextId,
        weight: LocalWeightId,
    },
    Swap {
        input: ContextId,
    },
    BothFromRight {
        input: ContextId,
        certificate: EntryCertificateId,
    },
    Replay {
        lower: ContextId,
        upper: ContextId,
    },
    WithoutLeftFilter {
        input: ContextId,
    },
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct RelationKey {
    pair: TypedPairKey,
    context: ContextId,
}
#[derive(Clone, Copy, Debug)]
struct Relation {
    key: RelationKey,
    previous_on_pair: Option<RelationId>,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Dependency {
    Derived {
        child: RelationId,
        parent: RelationId,
    },
    // Parent order is lower then upper, independently of insertion direction.
    Replay {
        child: RelationId,
        lower: RelationId,
        upper: RelationId,
        lower_input: BoundKey,
        upper_input: BoundKey,
    },
    Transport {
        child: RelationId,
        parent: RelationId,
        use_origin: usize,
    },
}
#[derive(Debug)]
#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "source origin certificates are retained independently of semantic conflict traversal"
    )
)]
struct Origin {
    relation: RelationId,
    occurrence: ConstraintOccurrenceId,
}
#[derive(Clone, Copy, Debug)]
struct BundleIncidence {
    relation: RelationId,
    bundle: AttachmentBundleId,
    previous_on_relation: Option<usize>,
}
#[derive(Debug, Default)]
struct BundleTransports {
    heads: HashMap<RelationId, usize>,
    log: Vec<(RelationId, RelationId, Option<usize>)>,
}
impl BundleTransports {
    fn insert(&mut self, parent: RelationId, child: RelationId) -> Result<(), SolveAvailabilityError> {
        self.heads.try_reserve(1).map_err(|_| exhausted())?;
        self.log.try_reserve(1).map_err(|_| exhausted())?;
        let previous = self.heads.insert(parent, self.log.len());
        self.log.push((parent, child, previous));
        Ok(())
    }
    fn rollback(&mut self, length: usize) {
        for (parent, _, previous) in self.log.drain(length..).rev() {
            if let Some(previous) = previous { self.heads.insert(parent, previous); }
            else { self.heads.remove(&parent); }
        }
    }
    fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        self.heads.capacity().checked_mul(std::mem::size_of::<(RelationId, usize)>())
            .and_then(|n| n.checked_add(self.log.capacity().checked_mul(std::mem::size_of::<(RelationId, RelationId, Option<usize>)>())?)).ok_or_else(exhausted)
    }
}
#[derive(Debug, Default)]
pub(super) struct State {
    pub bundles: Vec<AttachmentBundle>,
    bundle_bytes: usize,
    source_bundles: HashMap<ConstraintOccurrenceId, AttachmentBundleId>,
    source_bundle_log: Vec<ConstraintOccurrenceId>,
    bundle_incidence: HashSet<(RelationId, AttachmentBundleId)>,
    bundle_incidence_log: Vec<BundleIncidence>,
    bundle_incidence_heads: HashMap<RelationId, usize>,
    bundle_transports: Option<BundleTransports>,
    #[cfg(test)]
    bundle_visits: usize,
    weights: Vec<LocalWeight>,
    weight_bytes: usize,
    contexts: Vec<ContextExpr>,
    context_keys: HashMap<ContextExpr, ContextId>,
    relations: Vec<Relation>,
    keys: HashMap<RelationKey, RelationId>,
    pair_heads: HashMap<TypedPairKey, RelationId>,
    dependencies: Vec<Dependency>,
    dependency_keys: HashSet<Dependency>,
    origins: Vec<Origin>,
    bounds: HashMap<BoundKey, usize>,
    bound_keys: Vec<(BoundKey, RelationId, Option<usize>)>,
    replay_heads: HashMap<(BoundKey, BoundKey), (Option<usize>, Option<usize>)>,
    replay_log: Vec<((BoundKey, BoundKey), Option<(Option<usize>, Option<usize>)>)>,
    uses: usize,
    edges: HashMap<RelationId, Vec<RelationId>>,
    edge_keys: HashSet<(RelationId, RelationId)>,
    edge_log: Vec<(RelationId, RelationId)>,
    edge_bytes: usize,
    pub processing: Option<RelationId>,
    discharged: HashSet<RelationId>,
    discharge_log: Vec<RelationId>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Checkpoint {
    bundles: usize,
    source_bundles: usize,
    bundle_incidence: usize,
    bundle_transports: Option<usize>,
    weights: usize,
    contexts: usize,
    relations: usize,
    dependencies: usize,
    origins: usize,
    bounds: usize,
    uses: usize,
    replay_log: usize,
    edges: usize,
    processing: Option<RelationId>,
    discharges: usize,
}
fn exhausted() -> SolveAvailabilityError {
    SolveAvailabilityError::IdentityExhausted
}
// Source correspondence: frozen constraints/directed_weight.rs and
// constraints/mod.rs:3566–3612, as mapped by the contextual-effect source note.
// Detached finite atom-set algebra: no source admission, parameterized/cofinite
// families, certificate authorization, residual construction, or filter discharge.
#[derive(Debug, Default, Eq, PartialEq)]
struct ExactCount(Vec<u32>);
impl ExactCount {
    fn from_u32(value: u32) -> Result<Self, SolveAvailabilityError> {
        let mut out = Self::default();
        if value != 0 { out.0.try_reserve(1).map_err(|_| exhausted())?; out.0.push(value); }
        Ok(out)
    }
    fn copy(&self) -> Result<Self, SolveAvailabilityError> {
        let mut out = Self::default();
        out.0.try_reserve(self.0.len()).map_err(|_| exhausted())?;
        out.0.extend_from_slice(&self.0);
        Ok(out)
    }
    fn is_zero(&self) -> bool { self.0.is_empty() }
    fn compare(&self, other: &Self) -> std::cmp::Ordering {
        self.0.len().cmp(&other.0.len()).then_with(|| self.0.iter().rev().cmp(other.0.iter().rev()))
    }
    fn add(&self, other: &Self) -> Result<Self, SolveAvailabilityError> {
        let length = self.0.len().max(other.0.len());
        let mut out = Self::default();
        out.0.try_reserve(length.checked_add(1).ok_or_else(exhausted)?).map_err(|_| exhausted())?;
        let mut carry = 0u64;
        for i in 0..length {
            let sum = self.0.get(i).copied().unwrap_or(0) as u64
                + other.0.get(i).copied().unwrap_or(0) as u64 + carry;
            out.0.push(sum as u32); carry = sum >> 32;
        }
        if carry != 0 { out.0.push(carry as u32); }
        Ok(out)
    }
    fn subtract(&self, other: &Self) -> Result<Self, SolveAvailabilityError> {
        if self.compare(other).is_lt() { return Err(exhausted()); }
        let mut out = self.copy()?;
        let mut borrow = 0u64;
        for (i, limb) in out.0.iter_mut().enumerate() {
            let sub = other.0.get(i).copied().unwrap_or(0) as u64 + borrow;
            let original = *limb as u64;
            *limb = if original < sub { original + (1u64 << 32) - sub } else { original - sub } as u32;
            borrow = u64::from(original < sub);
        }
        while out.0.last() == Some(&0) { out.0.pop(); }
        Ok(out)
    }
}
// PUSH payloads have finite resolved families. All belongs only to filters.
#[derive(Debug)]
struct DetachedPushFamily(Vec<SourceEffectId>);
impl PartialEq for DetachedPushFamily {
    fn eq(&self, other: &Self) -> bool {
        self.0.iter().all(|x| other.0.contains(x)) && other.0.iter().all(|x| self.0.contains(x))
    }
}
impl Eq for DetachedPushFamily {}
impl DetachedPushFamily {
    fn copy(&self) -> Result<Self, SolveAvailabilityError> {
        let mut out = Vec::new();
        out.try_reserve(self.0.len()).map_err(|_| exhausted())?;
        out.extend(self.0.iter().cloned());
        Ok(Self(out))
    }
}
#[derive(Debug)]
enum DetachedFilter { All, Finite(Vec<SourceEffectId>) }
impl PartialEq for DetachedFilter {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::All, Self::All) => true,
            (Self::Finite(a), Self::Finite(b)) => a.iter().all(|x| b.contains(x)) && b.iter().all(|x| a.contains(x)),
            _ => false,
        }
    }
}
impl Eq for DetachedFilter {}
impl DetachedFilter {
    fn copy(&self) -> Result<Self, SolveAvailabilityError> {
        match self {
            Self::All => Ok(Self::All),
            Self::Finite(atoms) => {
                let mut out = Vec::new(); out.try_reserve(atoms.len()).map_err(|_| exhausted())?;
                out.extend(atoms.iter().cloned()); Ok(Self::Finite(out))
            }
        }
    }
    fn intersect(&self, other: &Self) -> Result<Self, SolveAvailabilityError> {
        match (self, other) {
            (Self::All, family) | (family, Self::All) => family.copy(),
            (Self::Finite(a), Self::Finite(b)) => {
                let mut out = Vec::new(); out.try_reserve(a.len().min(b.len())).map_err(|_| exhausted())?;
                for atom in a { if b.contains(atom) && !out.contains(atom) { out.push(atom.clone()); } }
                Ok(Self::Finite(out))
            }
        }
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct DetachedAttachmentId(u32);
#[derive(Debug, Eq, PartialEq)]
struct DetachedLeftEntry {
    id: DetachedAttachmentId,
    pops: ExactCount,
    pushes: ExactCount,
    family: Option<DetachedPushFamily>,
}
impl DetachedLeftEntry {
    fn copy(&self) -> Result<Self, SolveAvailabilityError> {
        Ok(Self { id: self.id, pops: self.pops.copy()?, pushes: self.pushes.copy()?,
            family: self.family.as_ref().map(DetachedPushFamily::copy).transpose()? })
    }
}
#[derive(Debug, Eq, PartialEq)]
struct DetachedRightEntry { id: DetachedAttachmentId, pops: ExactCount }
#[derive(Debug, Eq, PartialEq)]
struct DetachedWeight {
    left: Vec<DetachedLeftEntry>,
    filter: DetachedFilter,
    right: Vec<DetachedRightEntry>,
}
impl DetachedWeight {
    fn identity() -> Self { Self { left: Vec::new(), filter: DetachedFilter::All, right: Vec::new() } }
    fn copy(&self) -> Result<Self, SolveAvailabilityError> {
        let mut out = Self::identity(); out.filter = self.filter.copy()?;
        out.left.try_reserve(self.left.len()).map_err(|_| exhausted())?;
        for entry in &self.left { out.left.push(entry.copy()?); }
        out.append_right(&self.right)?;
        Ok(out)
    }
    fn append_left(&mut self, entries: &[DetachedLeftEntry]) -> Result<(), SolveAvailabilityError> {
        for incoming in entries {
            if incoming.pushes.is_zero() != incoming.family.is_none() { return Err(exhausted()); }
            let Some(index) = self.left.iter().position(|entry| entry.id == incoming.id) else {
                if !incoming.pops.is_zero() || !incoming.pushes.is_zero() {
                    self.left.try_reserve(1).map_err(|_| exhausted())?;
                    self.left.push(incoming.copy()?); self.left.sort_unstable_by_key(|entry| entry.id.0);
                }
                continue;
            };
            let current = &self.left[index];
            if let (Some(a), Some(b)) = (&current.family, &incoming.family) {
                if a != b { return Err(exhausted()); }
            }
            let (pops, pushes) = if incoming.pops.compare(&current.pushes).is_le() {
                (current.pops.copy()?, current.pushes.subtract(&incoming.pops)?.add(&incoming.pushes)?)
            } else {
                (current.pops.add(&incoming.pops.subtract(&current.pushes)?)?, incoming.pushes.copy()?)
            };
            let family = if pushes.is_zero() { None } else {
                Some(current.family.as_ref().or(incoming.family.as_ref()).ok_or_else(exhausted)?.copy()?)
            };
            if pops.is_zero() && pushes.is_zero() { self.left.remove(index); }
            else { self.left[index] = DetachedLeftEntry { id: incoming.id, pops, pushes, family }; }
        }
        Ok(())
    }
    fn append_right(&mut self, entries: &[DetachedRightEntry]) -> Result<(), SolveAvailabilityError> {
        for incoming in entries {
            if incoming.pops.is_zero() { continue; }
            if let Some(current) = self.right.iter_mut().find(|entry| entry.id == incoming.id) {
                current.pops = current.pops.add(&incoming.pops)?;
            } else {
                self.right.try_reserve(1).map_err(|_| exhausted())?;
                self.right.push(DetachedRightEntry { id: incoming.id, pops: incoming.pops.copy()? });
                self.right.sort_unstable_by_key(|entry| entry.id.0);
            }
        }
        Ok(())
    }
    fn right_to_left(&mut self, entries: &[DetachedRightEntry]) -> Result<(), SolveAvailabilityError> {
        for entry in entries {
            self.append_left(&[DetachedLeftEntry { id: entry.id, pops: entry.pops.copy()?, pushes: ExactCount::default(), family: None }])?;
        }
        Ok(())
    }
    fn mix(mut self) -> Result<Self, SolveAvailabilityError> {
        if self.left.is_empty() || self.right.is_empty() { return Ok(self); }
        let right = std::mem::take(&mut self.right);
        for entry in right {
            let id = entry.id;
            self.right_to_left(&[entry])?;
            if let Some(index) = self.left.iter().position(|left| left.id == id) {
                if self.left[index].pushes.is_zero() {
                    let left = self.left.remove(index);
                    self.append_right(&[DetachedRightEntry { id, pops: left.pops }])?;
                }
            }
        }
        Ok(self)
    }
}
#[derive(Debug)]
#[cfg_attr(not(test), allow(dead_code, reason = "detached result has no live source consumer"))]
struct DetachedEvaluation {
    value: DetachedWeight,
    // One exact record per reachable node retains weight/certificate tokens.
    // Numeric equality never interns or rewrites construction records.
    nodes: Vec<(ContextId, Option<ContextExpr>)>,
}
fn reserve_rename_scratch<T>(
    storage: &mut Vec<T>, additional: usize, scratch_bytes: &mut usize, charge: &mut usize,
) -> Result<(), SolveAvailabilityError> {
    let before = storage.capacity();
    storage.try_reserve(additional).map_err(|_| exhausted())?;
    let growth = (storage.capacity() - before).checked_mul(std::mem::size_of::<T>()).ok_or_else(exhausted)?;
    let next_charge = charge.checked_add(growth).ok_or_else(exhausted)?;
    let next_scratch = scratch_bytes.checked_add(growth).ok_or_else(exhausted)?;
    *charge = next_charge;
    *scratch_bytes = next_scratch;
    Ok(())
}
impl State {
    // Detached per-use construction rename. Substitutions and the reusable map
    // belong to the caller's scratch lease; only traversal/journal storage is
    // charged here. Reuse the map only with unchanged substitutions and retained
    // nodes from this route/use; invalidate it when an outer route rolls back.
    // Certificates are opaque tokens, never entry authorization.
    #[cfg_attr(not(test), allow(dead_code, reason = "detached transport preparation has no live consumer"))]
    fn rename_contexts(
        &mut self,
        roots: &[ContextId],
        weights: &HashMap<LocalWeightId, LocalWeightId>,
        certificates: &HashMap<EntryCertificateId, EntryCertificateId>,
        remap: &mut HashMap<ContextId, ContextId>,
        scratch_bytes: &mut usize,
    ) -> Result<(), SolveAvailabilityError> {
        self.rename_contexts_impl(roots, weights, certificates, remap, scratch_bytes, false, &mut 0)
    }
    fn rename_contexts_impl(
        &mut self, roots: &[ContextId], weights: &HashMap<LocalWeightId, LocalWeightId>,
        certificates: &HashMap<EntryCertificateId, EntryCertificateId>,
        remap: &mut HashMap<ContextId, ContextId>, scratch_bytes: &mut usize,
        charge_map: bool, peak_bytes: &mut usize,
    ) -> Result<(), SolveAvailabilityError> {
        let checkpoint = self.checkpoint();
        let map_was_empty = remap.is_empty();
        let mut pending = Vec::<(ContextId, bool)>::new();
        let mut inserted = Vec::<ContextId>::new();
        let mut verified = HashSet::<ContextId>::new();
        let mut charge = 0usize;
        let result = (|| {
            for &root in roots {
                reserve_rename_scratch(&mut pending, 1, scratch_bytes, &mut charge)?;
                *peak_bytes = (*peak_bytes).max(*scratch_bytes);
                pending.push((root, false));
                while let Some((id, ready)) = pending.pop() {
                    if verified.contains(&id) { continue; }
                    // Newly interned outputs cannot make a malformed source
                    // handle valid partway through this rename.
                    if id.0 as usize > checkpoint.contexts { return Err(exhausted()); }
                    let expression = if id == IDENTITY { None } else {
                        Some(*self.contexts.get(id.0 as usize - 1).ok_or_else(exhausted)?)
                    };
                    let (children, count) = match expression {
                        None => ([IDENTITY, IDENTITY], 0),
                        Some(ContextExpr::Replay { lower, upper }) => ([lower, upper], 2),
                        Some(ContextExpr::PrefixLeft { input, .. }
                            | ContextExpr::SuffixRightPops { input, .. }
                            | ContextExpr::Swap { input }
                            | ContextExpr::BothFromRight { input, .. }
                            | ContextExpr::WithoutLeftFilter { input }) => ([input, IDENTITY], 1),
                    };
                    if children[..count].iter().any(|child| child.0 >= id.0) {
                        return Err(exhausted());
                    }
                    if !ready && count > 0 {
                        reserve_rename_scratch(&mut pending, count + 1, scratch_bytes, &mut charge)?;
                        *peak_bytes = (*peak_bytes).max(*scratch_bytes);
                        pending.push((id, true));
                        for &child in children[..count].iter().rev() {
                            if !verified.contains(&child) { pending.push((child, false)); }
                        }
                        continue;
                    }
                    let child = |input| remap.get(&input).copied().ok_or_else(exhausted);
                    let weight = |input: LocalWeightId| {
                        self.weights.get(input.0 as usize).ok_or_else(exhausted)?;
                        let copy = weights.get(&input).copied().ok_or_else(exhausted)?;
                        self.weights.get(copy.0 as usize).ok_or_else(exhausted)?;
                        Ok::<_, SolveAvailabilityError>(copy)
                    };
                    let renamed = match expression {
                        None => None,
                        Some(ContextExpr::PrefixLeft { weight: token, input }) =>
                            Some(ContextExpr::PrefixLeft { weight: weight(token)?, input: child(input)? }),
                        Some(ContextExpr::SuffixRightPops { input, weight: token }) =>
                            Some(ContextExpr::SuffixRightPops { input: child(input)?, weight: weight(token)? }),
                        Some(ContextExpr::Swap { input }) => Some(ContextExpr::Swap { input: child(input)? }),
                        Some(ContextExpr::BothFromRight { input, certificate }) => Some(ContextExpr::BothFromRight {
                            input: child(input)?, certificate: certificates.get(&certificate).copied().ok_or_else(exhausted)?,
                        }),
                        Some(ContextExpr::Replay { lower, upper }) =>
                            Some(ContextExpr::Replay { lower: child(lower)?, upper: child(upper)? }),
                        Some(ContextExpr::WithoutLeftFilter { input }) =>
                            Some(ContextExpr::WithoutLeftFilter { input: child(input)? }),
                    };
                    let old_capacity = verified.capacity();
                    verified.try_reserve(1).map_err(|_| exhausted())?;
                    let growth = (verified.capacity() - old_capacity).checked_mul(std::mem::size_of::<ContextId>()).ok_or_else(exhausted)?;
                    let next_charge = charge.checked_add(growth).ok_or_else(exhausted)?;
                    let next_scratch = scratch_bytes.checked_add(growth).ok_or_else(exhausted)?;
                    charge = next_charge;
                    *scratch_bytes = next_scratch;
                    *peak_bytes = (*peak_bytes).max(*scratch_bytes);
                    if let Some(&copy) = remap.get(&id) {
                        // Caller-seeded mappings are suggestions. Validate the
                        // exact reconstructed constructor before accepting one.
                        let actual = if copy == IDENTITY { None } else {
                            if copy.0 as usize > checkpoint.contexts { return Err(exhausted()); }
                            Some(*self.contexts.get(copy.0 as usize - 1).ok_or_else(exhausted)?)
                        };
                        if actual != renamed { return Err(exhausted()); }
                    } else {
                        // Reserve rollback storage before interning/publication.
                        reserve_rename_scratch(&mut inserted, 1, scratch_bytes, &mut charge)?;
                        let before = remap.capacity();
                        remap.try_reserve(1).map_err(|_| exhausted())?;
                        if charge_map {
                            // The caller retains this charge until its map drops,
                            // including a failed rename with retained capacity.
                            let growth = (remap.capacity() - before).checked_mul(std::mem::size_of::<(ContextId, ContextId)>()).ok_or_else(exhausted)?;
                            *scratch_bytes = scratch_bytes.checked_add(growth).ok_or_else(exhausted)?;
                        }
                        *peak_bytes = (*peak_bytes).max(*scratch_bytes);
                        let copy = match renamed { Some(node) => self.context(node)?, None => IDENTITY };
                        remap.insert(id, copy);
                        inserted.push(id);
                    }
                    verified.insert(id);
                }
            }
            Ok(())
        })();
        if result.is_err() {
            // A fresh-use map starts empty. Clear its deletion markers while
            // retaining the charged allocation for a supported retry.
            if charge_map && map_was_empty { remap.clear(); }
            else { for &id in &inserted { remap.remove(&id); } }
            self.rollback(checkpoint);
        }
        drop(pending);
        drop(inserted);
        drop(verified);
        *scratch_bytes -= charge;
        result
    }
    pub(super) fn rename_fresh_contexts(
        &mut self, roots: &[ContextId], weights: &HashMap<LocalWeightId, LocalWeightId>,
        remap: &mut HashMap<ContextId, ContextId>, scratch_bytes: &mut usize,
        peak_bytes: &mut usize,
    ) -> Result<(), SolveAvailabilityError> {
        self.rename_contexts_impl(roots, weights, &HashMap::new(), remap, scratch_bytes, true, peak_bytes)
    }
    pub(super) fn relation_context(&self, relation: RelationId) -> Result<ContextId, SolveAvailabilityError> {
        self.relations.get(relation.0 as usize).ok_or_else(exhausted)?;
        Ok(self.post_check_context(relation))
    }
    // Discovery follows construction edges once across all captured fibers.
    pub(super) fn context_payloads(
        &self, root: ContextId, visited: &mut HashSet<ContextId>,
        pending: &mut Vec<ContextId>, weights: &mut Vec<LocalWeightId>,
    ) -> Result<(), SolveAvailabilityError> {
        pending.try_reserve(1).map_err(|_| exhausted())?;
        pending.push(root);
        while let Some(id) = pending.pop() {
            if visited.contains(&id) { continue; }
            visited.try_reserve(1).map_err(|_| exhausted())?;
            visited.insert(id);
            if id == IDENTITY { continue; }
            let expression = *self.contexts.get(id.0 as usize - 1).ok_or_else(exhausted)?;
            let (children, count, weight) = match expression {
                ContextExpr::PrefixLeft { input, weight } | ContextExpr::SuffixRightPops { input, weight } => ([input, IDENTITY], 1, Some(weight)),
                ContextExpr::Replay { lower, upper } => ([lower, upper], 2, None),
                ContextExpr::Swap { input } | ContextExpr::WithoutLeftFilter { input } => ([input, IDENTITY], 1, None),
                // Fresh-use certificates require an authentic retained owner.
                ContextExpr::BothFromRight { .. } => return Err(exhausted()),
            };
            if children[..count].iter().any(|child| child.0 >= id.0) { return Err(exhausted()); }
            pending.try_reserve(count).map_err(|_| exhausted())?;
            pending.extend_from_slice(&children[..count]);
            if let Some(weight) = weight {
                self.weights.get(weight.0 as usize).ok_or_else(exhausted)?;
                weights.try_reserve(1).map_err(|_| exhausted())?;
                weights.push(weight);
            }
        }
        Ok(())
    }
    pub(super) fn payload_view(&self, weight: LocalWeightId) -> Result<u32, SolveAvailabilityError> {
        Ok(self.weights.get(weight.0 as usize).ok_or_else(exhausted)?.boundary)
    }
    pub(super) fn validate_payload_view(&self, weight: LocalWeightId, id: u32, view: &candidate_effect::View) -> Result<(), SolveAvailabilityError> {
        let payload = self.weights.get(weight.0 as usize).ok_or_else(exhausted)?;
        if payload.boundary != id || payload.owner != view.owner || payload.position != view.position
            || payload.allowed != view.allowed || view.source_weight != Some(weight)
            || view.closed_weight != view.tail.is_none().then_some(weight) { return Err(exhausted()); }
        Ok(())
    }
    // Detached postorder fold: the callback sees the exact construction token
    // and ordered children. No relation, source task, or certificate is consumed.
    #[cfg_attr(not(test), allow(dead_code, reason = "detached contextual evaluation gate"))]
    fn fold_context<T>(
        &self,
        root: ContextId,
        mut evaluate: impl FnMut(ContextId, Option<ContextExpr>, &[&T]) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| exhausted())?;
        pending.push((root, false));
        let mut results = HashMap::new();
        while let Some((id, ready)) = pending.pop() {
            if results.contains_key(&id) { continue; }
            let expression = if id == IDENTITY { None } else {
                Some(*self.contexts.get(id.0 as usize - 1).ok_or_else(exhausted)?)
            };
            let (children, count) = match expression {
                None => ([IDENTITY, IDENTITY], 0),
                Some(ContextExpr::Replay { lower, upper }) => ([lower, upper], 2),
                Some(ContextExpr::PrefixLeft { input, .. }
                    | ContextExpr::SuffixRightPops { input, .. }
                    | ContextExpr::Swap { input }
                    | ContextExpr::BothFromRight { input, .. }
                    | ContextExpr::WithoutLeftFilter { input }) => ([input, IDENTITY], 1),
            };
            // Construction only references already retained nodes. Validate
            // this invariant before descending, including malformed handles.
            if children[..count].iter().any(|child| child.0 >= id.0) {
                return Err(exhausted());
            }
            if !ready && count > 0 {
                pending.try_reserve(count + 1).map_err(|_| exhausted())?;
                pending.push((id, true));
                for &child in children[..count].iter().rev() {
                    if !results.contains_key(&child) { pending.push((child, false)); }
                }
                continue;
            }
            let result = match count {
                0 => evaluate(id, expression, &[])?,
                1 => evaluate(id, expression, &[&results[&children[0]]])?,
                2 => evaluate(id, expression, &[&results[&children[0]], &results[&children[1]]])?,
                _ => unreachable!(),
            };
            results.try_reserve(1).map_err(|_| exhausted())?;
            results.insert(id, result);
        }
        results.remove(&root).ok_or_else(exhausted)
    }
    #[cfg_attr(not(test), allow(dead_code, reason = "detached algebra has no source consumer"))]
    fn evaluate_context(&self, root: ContextId, weights: &[DetachedWeight]) -> Result<DetachedEvaluation, SolveAvailabilityError> {
        let mut nodes = Vec::new();
        let value = self.fold_context(root, |id, expression, children: &[&DetachedWeight]| {
            let value = match expression {
                None => DetachedWeight::identity(),
                Some(ContextExpr::PrefixLeft { weight, .. }) => {
                    let prefix = weights.get(weight.0 as usize).ok_or_else(exhausted)?;
                    let mut out = DetachedWeight::identity();
                    out.append_left(&prefix.left)?; out.append_left(&children[0].left)?;
                    out.filter = prefix.filter.intersect(&children[0].filter)?;
                    out.append_right(&children[0].right)?; out
                }
                Some(ContextExpr::SuffixRightPops { weight, .. }) => {
                    let suffix = weights.get(weight.0 as usize).ok_or_else(exhausted)?;
                    let mut out = children[0].copy()?;
                    out.right.clear();
                    // Oracle suffix uses only leading POPs of the wrapper.
                    for entry in &suffix.left {
                        out.append_right(&[DetachedRightEntry { id: entry.id, pops: entry.pops.copy()? }])?;
                    }
                    out.append_right(&children[0].right)?; out
                }
                Some(ContextExpr::Swap { .. }) => {
                    let mut out = DetachedWeight::identity(); out.right_to_left(&children[0].right)?;
                    for entry in &children[0].left {
                        out.append_right(&[DetachedRightEntry { id: entry.id, pops: entry.pops.copy()? }])?;
                    }
                    out
                }
                Some(ContextExpr::BothFromRight { .. }) => {
                    let mut out = DetachedWeight::identity(); out.right_to_left(&children[0].right)?;
                    out.append_right(&children[0].right)?; out
                }
                Some(ContextExpr::WithoutLeftFilter { .. }) => {
                    let mut out = children[0].copy()?; out.filter = DetachedFilter::All; out
                }
                Some(ContextExpr::Replay { .. }) => {
                    let mut out = children[0].copy()?; out.append_left(&children[1].left)?;
                    out.filter = children[0].filter.intersect(&children[1].filter)?;
                    out.right.clear(); out.append_right(&children[1].right)?;
                    out.append_right(&children[0].right)?; out.mix()?
                }
            };
            nodes.try_reserve(1).map_err(|_| exhausted())?; nodes.push((id, expression));
            Ok(value)
        })?;
        Ok(DetachedEvaluation { value, nodes })
    }
    pub fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            bundles: self.bundles.len(),
            source_bundles: self.source_bundle_log.len(),
            bundle_incidence: self.bundle_incidence_log.len(),
            bundle_transports: self.bundle_transports.as_ref().map(|index| index.log.len()),
            weights: self.weights.len(),
            contexts: self.contexts.len(),
            relations: self.relations.len(),
            dependencies: self.dependencies.len(),
            origins: self.origins.len(),
            bounds: self.bound_keys.len(),
            uses: self.uses,
            replay_log: self.replay_log.len(),
            edges: self.edge_log.len(),
            processing: self.processing,
            discharges: self.discharge_log.len(),
        }
    }
    pub fn rollback(&mut self, checkpoint: Checkpoint) {
        for bundle in self.bundles.drain(checkpoint.bundles..) {
            self.bundle_bytes -= bundle.sets.capacity() * std::mem::size_of::<EmptyAttachmentSet>();
        }
        for origin in self.source_bundle_log.drain(checkpoint.source_bundles..) { self.source_bundles.remove(&origin); }
        for incidence in self.bundle_incidence_log.drain(checkpoint.bundle_incidence..).rev() {
            self.bundle_incidence.remove(&(incidence.relation, incidence.bundle));
            if let Some(previous) = incidence.previous_on_relation { self.bundle_incidence_heads.insert(incidence.relation, previous); }
            else { self.bundle_incidence_heads.remove(&incidence.relation); }
        }
        if let Some(length) = checkpoint.bundle_transports { self.bundle_transports.as_mut().unwrap().rollback(length); }
        else { self.bundle_transports = None; }
        for weight in self.weights.drain(checkpoint.weights..) {
            self.weight_bytes -= weight.allowed.capacity() * std::mem::size_of::<SourceEffectId>()
                + weight.attachment.as_ref().map_or(0, |set| set.member_ordinals.capacity() * std::mem::size_of::<usize>());
        }
        for (key, previous) in self.replay_log.drain(checkpoint.replay_log..).rev() {
            if let Some(previous) = previous { self.replay_heads.insert(key, previous); }
            else { self.replay_heads.remove(&key); }
        }
        for relation in self.discharge_log.drain(checkpoint.discharges..) {
            self.discharged.remove(&relation);
        }
        for context in self.contexts.drain(checkpoint.contexts..) {
            self.context_keys.remove(&context);
        }
        for relation in self.relations.drain(checkpoint.relations..).rev() {
            self.keys.remove(&relation.key);
            if let Some(previous) = relation.previous_on_pair {
                self.pair_heads.insert(relation.key.pair, previous);
            } else {
                self.pair_heads.remove(&relation.key.pair);
            }
        }
        for dependency in self.dependencies.drain(checkpoint.dependencies..) {
            self.dependency_keys.remove(&dependency);
        }
        for (bound, _, previous) in self.bound_keys.drain(checkpoint.bounds..).rev() {
            if let Some(previous) = previous { self.bounds.insert(bound, previous); }
            else { self.bounds.remove(&bound); }
        }
        self.origins.truncate(checkpoint.origins);
        self.uses = checkpoint.uses;
        self.processing = checkpoint.processing;
        for (parent, child) in self.edge_log.drain(checkpoint.edges..).rev() {
            self.edge_keys.remove(&(parent, child));
            let entries = self.edges.get_mut(&parent).unwrap();
            assert_eq!(entries.pop(), Some(child));
            if entries.is_empty() {
                self.edge_bytes -= self.edges.remove(&parent).unwrap().capacity()
                    * std::mem::size_of::<RelationId>();
            }
        }
    }
    pub fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
        let parts = [
            Some(self.bundle_bytes),
            self.bundles.capacity().checked_mul(std::mem::size_of::<AttachmentBundle>()),
            self.source_bundles.capacity().checked_mul(std::mem::size_of::<(ConstraintOccurrenceId, AttachmentBundleId)>()),
            self.source_bundle_log.capacity().checked_mul(std::mem::size_of::<ConstraintOccurrenceId>()),
            self.bundle_incidence.capacity().checked_mul(std::mem::size_of::<(RelationId, AttachmentBundleId)>()),
            self.bundle_incidence_log.capacity().checked_mul(std::mem::size_of::<BundleIncidence>()),
            self.bundle_incidence_heads.capacity().checked_mul(std::mem::size_of::<(RelationId, usize)>()),
            Some(self.bundle_transports.as_ref().map_or(Ok(0), BundleTransports::bytes)?),
            Some(self.weight_bytes),
            self.weights.capacity().checked_mul(std::mem::size_of::<LocalWeight>()),
            self.replay_heads.capacity().checked_mul(std::mem::size_of::<((BoundKey, BoundKey), (Option<usize>, Option<usize>))>()),
            self.replay_log.capacity().checked_mul(std::mem::size_of::<((BoundKey, BoundKey), Option<(Option<usize>, Option<usize>)>)>()),
            self.discharged.capacity().checked_mul(std::mem::size_of::<RelationId>()),
            self.discharge_log.capacity().checked_mul(std::mem::size_of::<RelationId>()),
            self.contexts
                .capacity()
                .checked_mul(std::mem::size_of::<ContextExpr>()),
            self.context_keys
                .capacity()
                .checked_mul(std::mem::size_of::<(ContextExpr, ContextId)>()),
            self.relations
                .capacity()
                .checked_mul(std::mem::size_of::<Relation>()),
            self.keys
                .capacity()
                .checked_mul(std::mem::size_of::<(RelationKey, RelationId)>()),
            self.pair_heads
                .capacity()
                .checked_mul(std::mem::size_of::<(TypedPairKey, RelationId)>()),
            self.dependencies
                .capacity()
                .checked_mul(std::mem::size_of::<Dependency>()),
            self.dependency_keys
                .capacity()
                .checked_mul(std::mem::size_of::<Dependency>()),
            self.origins
                .capacity()
                .checked_mul(std::mem::size_of::<Origin>()),
            self.bounds
                .capacity()
                .checked_mul(std::mem::size_of::<(BoundKey, usize)>()),
            self.bound_keys
                .capacity()
                .checked_mul(std::mem::size_of::<(BoundKey, RelationId, Option<usize>)>()),
        ];
        let owned = parts.into_iter().try_fold(0usize, |n, part| {
            n.checked_add(part.ok_or_else(exhausted)?)
                .ok_or_else(exhausted)
        })?;
        owned
            .checked_add(
                self.edges
                    .capacity()
                    .checked_mul(std::mem::size_of::<(RelationId, Vec<RelationId>)>())
                    .ok_or_else(exhausted)?,
            )
            .and_then(|n| {
                n.checked_add(
                    self.edge_keys
                        .capacity()
                        .checked_mul(std::mem::size_of::<(RelationId, RelationId)>())?,
                )
            })
            .and_then(|n| {
                n.checked_add(
                    self.edge_log
                        .capacity()
                        .checked_mul(std::mem::size_of::<(RelationId, RelationId)>())?,
                )
            })
            .and_then(|n| n.checked_add(self.edge_bytes))
            .ok_or_else(exhausted)
    }
    #[cfg(test)]
    pub fn enumerated_bytes(&self) -> usize {
        let adjacency_bytes = self
            .edges
            .values()
            .map(|entries| entries.capacity() * std::mem::size_of::<RelationId>())
            .sum::<usize>();
        assert_eq!(self.edge_bytes, adjacency_bytes);
        self.bundles.capacity() * std::mem::size_of::<AttachmentBundle>()
            + self.bundles.iter().map(|bundle| bundle.sets.capacity() * std::mem::size_of::<EmptyAttachmentSet>()).sum::<usize>()
            + self.source_bundles.capacity() * std::mem::size_of::<(ConstraintOccurrenceId, AttachmentBundleId)>()
            + self.source_bundle_log.capacity() * std::mem::size_of::<ConstraintOccurrenceId>()
            + self.bundle_incidence.capacity() * std::mem::size_of::<(RelationId, AttachmentBundleId)>()
            + self.bundle_incidence_log.capacity() * std::mem::size_of::<BundleIncidence>()
            + self.bundle_incidence_heads.capacity() * std::mem::size_of::<(RelationId, usize)>()
            + self.bundle_transports.as_ref().map_or(0, |index| index.heads.capacity() * std::mem::size_of::<(RelationId, usize)>()
                + index.log.capacity() * std::mem::size_of::<(RelationId, RelationId, Option<usize>)>())
            + self.weights.capacity() * std::mem::size_of::<LocalWeight>()
            + self.weights.iter().map(|w| w.allowed.capacity() * std::mem::size_of::<SourceEffectId>()
                + w.attachment.as_ref().map_or(0, |set| set.member_ordinals.capacity() * std::mem::size_of::<usize>())).sum::<usize>()
            + self.replay_heads.capacity() * std::mem::size_of::<((BoundKey, BoundKey), (Option<usize>, Option<usize>))>()
            + self.replay_log.capacity() * std::mem::size_of::<((BoundKey, BoundKey), Option<(Option<usize>, Option<usize>)>)>()
            + self.discharged.capacity() * std::mem::size_of::<RelationId>()
            + self.discharge_log.capacity() * std::mem::size_of::<RelationId>()
            + self.contexts.capacity() * std::mem::size_of::<ContextExpr>()
            + self.context_keys.capacity() * std::mem::size_of::<(ContextExpr, ContextId)>()
            + self.relations.capacity() * std::mem::size_of::<Relation>()
            + self.keys.capacity() * std::mem::size_of::<(RelationKey, RelationId)>()
            + self.pair_heads.capacity() * std::mem::size_of::<(TypedPairKey, RelationId)>()
            + self.dependencies.capacity() * std::mem::size_of::<Dependency>()
            + self.dependency_keys.capacity() * std::mem::size_of::<Dependency>()
            + self.origins.capacity() * std::mem::size_of::<Origin>()
            + self.bounds.capacity() * std::mem::size_of::<(BoundKey, usize)>()
            + self.bound_keys.capacity() * std::mem::size_of::<(BoundKey, RelationId, Option<usize>)>()
            + self.edges.capacity() * std::mem::size_of::<(RelationId, Vec<RelationId>)>()
            + self.edge_keys.capacity() * std::mem::size_of::<(RelationId, RelationId)>()
            + self.edge_log.capacity() * std::mem::size_of::<(RelationId, RelationId)>()
            + adjacency_bytes
    }
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "context propagation is a later gate")
    )]
    fn context(&mut self, expression: ContextExpr) -> Result<ContextId, SolveAvailabilityError> {
        match expression {
            ContextExpr::PrefixLeft { input, .. }
            | ContextExpr::SuffixRightPops { input, .. }
            | ContextExpr::Swap { input }
            | ContextExpr::BothFromRight { input, .. }
            | ContextExpr::WithoutLeftFilter { input } => self.assert_context(input),
            ContextExpr::Replay { lower, upper } => {
                self.assert_context(lower);
                self.assert_context(upper);
            }
        }
        if let Some(&id) = self.context_keys.get(&expression) {
            return Ok(id);
        }
        let id = ContextId(
            u32::try_from(self.contexts.len())
                .map_err(|_| exhausted())?
                .checked_add(1)
                .ok_or_else(exhausted)?,
        );
        self.contexts.try_reserve(1).map_err(|_| exhausted())?;
        self.context_keys.try_reserve(1).map_err(|_| exhausted())?;
        self.contexts.push(expression);
        self.context_keys.insert(expression, id);
        Ok(id)
    }
    pub fn retain_bundle(&mut self, bundle: AttachmentBundle, source: bool) -> Result<AttachmentBundleId, SolveAvailabilityError> {
        let identity = AttachmentBundleId(self.bundles.len());
        let bytes = bundle.sets.capacity().checked_mul(std::mem::size_of::<EmptyAttachmentSet>()).ok_or_else(exhausted)?;
        let total = self.bundle_bytes.checked_add(bytes).ok_or_else(exhausted)?;
        self.bundles.try_reserve(1).map_err(|_| exhausted())?;
        if source {
            assert!(!self.source_bundles.contains_key(&bundle.occurrence));
            self.source_bundles.try_reserve(1).map_err(|_| exhausted())?;
            self.source_bundle_log.try_reserve(1).map_err(|_| exhausted())?;
            self.source_bundles.insert(bundle.occurrence.clone(), identity);
            self.source_bundle_log.push(bundle.occurrence.clone());
        }
        self.bundles.push(bundle);
        self.bundle_bytes = total;
        Ok(identity)
    }
    pub fn relation_bundles(&self, relation: RelationId) -> impl Iterator<Item = AttachmentBundleId> + '_ {
        std::iter::successors(self.bundle_incidence_heads.get(&relation).copied(), |&index| {
            self.bundle_incidence_log[index].previous_on_relation
        }).map(|index| self.bundle_incidence_log[index].bundle)
    }
    fn activate_bundle_transports(&mut self) -> Result<(), SolveAvailabilityError> {
        if self.bundle_transports.is_some() { return Ok(()); }
        // This one scan is paid only by sessions using bundle provenance.
        let mut index = BundleTransports::default();
        for dependency in &self.dependencies {
            if let Dependency::Transport { parent, child, use_origin: 0 } = *dependency { index.insert(parent, child)?; }
        }
        self.bundle_transports = Some(index);
        Ok(())
    }
    fn bundle_incidence_insert(&mut self, relation: RelationId, bundle: AttachmentBundleId) -> Result<(), SolveAvailabilityError> {
        if self.bundle_incidence.contains(&(relation, bundle)) { return Ok(()); }
        self.bundle_incidence.try_reserve(1).map_err(|_| exhausted())?;
        self.bundle_incidence_log.try_reserve(1).map_err(|_| exhausted())?;
        self.bundle_incidence_heads.try_reserve(1).map_err(|_| exhausted())?;
        let previous_on_relation = self.bundle_incidence_heads.insert(relation, self.bundle_incidence_log.len());
        self.bundle_incidence.insert((relation, bundle));
        self.bundle_incidence_log.push(BundleIncidence { relation, bundle, previous_on_relation });
        Ok(())
    }
    fn bundle_link(&mut self, relation: RelationId, bundle: AttachmentBundleId) -> Result<(), SolveAvailabilityError> {
        if self.bundle_incidence.contains(&(relation, bundle)) { return Ok(()); }
        self.activate_bundle_transports()?;
        let mut cursor = self.bundle_incidence_log.len();
        self.bundle_incidence_insert(relation, bundle)?;
        // The append log is an iterative queue. Each new incidence visits only
        // diagnostic successors and the sparse zero-use transport chain.
        while cursor < self.bundle_incidence_log.len() {
            let BundleIncidence { relation: parent, bundle, .. } = self.bundle_incidence_log[cursor];
            cursor += 1;
            let count = self.edges.get(&parent).map_or(0, Vec::len);
            for index in 0..count {
                let child = self.edges[&parent][index];
                #[cfg(test)] { self.bundle_visits += 1; }
                self.bundle_incidence_insert(child, bundle)?;
            }
            let mut next = self.bundle_transports.as_ref().unwrap().heads.get(&parent).copied();
            while let Some(index) = next {
                let (_, child, previous) = self.bundle_transports.as_ref().unwrap().log[index];
                next = previous;
                #[cfg(test)] { self.bundle_visits += 1; }
                self.bundle_incidence_insert(child, bundle)?;
            }
        }
        Ok(())
    }
    fn bundle_edge(&mut self, parent: RelationId, child: RelationId) -> Result<(), SolveAvailabilityError> {
        let mut next = self.bundle_incidence_heads.get(&parent).copied();
        while let Some(index) = next {
            let incidence = self.bundle_incidence_log[index];
            next = incidence.previous_on_relation;
            #[cfg(test)] { self.bundle_visits += 1; }
            self.bundle_link(child, incidence.bundle)?;
        }
        Ok(())
    }
    pub fn source_weight(&mut self, boundary: u32, owner: &DefinitionRootId, position: &SourceNodeKey, allowed: &[SourceEffectId], source: Option<AttachmentSource>) -> Result<LocalWeightId, SolveAvailabilityError> {
        let id = LocalWeightId(u32::try_from(self.weights.len()).map_err(|_| exhausted())?);
        let mut members = Vec::new();
        members.try_reserve_exact(allowed.len()).map_err(|_| exhausted())?;
        members.extend_from_slice(allowed);
        let attachment = source.map(|source| {
            let mut member_ordinals = Vec::new();
            member_ordinals.try_reserve_exact(allowed.len()).map_err(|_| exhausted())?;
            member_ordinals.extend(0..allowed.len());
            Ok::<_, SolveAvailabilityError>(AttachmentSet {
                composed_polarity: source.composed_polarity,
                lexical_scope: source.lexical_scope,
                member_ordinals,
                unit_push: (source.composed_polarity == Polarity::Positive && !allowed.is_empty()).then_some(SourceUnitPush),
            })
        }).transpose()?;
        let ordinal_bytes = attachment.as_ref().map_or(Some(0), |set| set.member_ordinals.capacity().checked_mul(std::mem::size_of::<usize>())).ok_or_else(exhausted)?;
        let weight_bytes = self.weight_bytes.checked_add(ordinal_bytes).and_then(|n| n.checked_add(members.capacity().checked_mul(std::mem::size_of::<SourceEffectId>())?)).ok_or_else(exhausted)?;
        self.weights.try_reserve(1).map_err(|_| exhausted())?;
        self.weights.push(LocalWeight { left_word: [], allowed: members, right_pops: [], boundary, owner: owner.clone(), position: position.clone(), attachment });
        self.weight_bytes = weight_bytes;
        Ok(id)
    }
    // The adapter is private and detached. It does not produce a live
    // ContextExpr, relation, bound, registration, or executable local word.
    #[cfg_attr(not(test), allow(dead_code, reason = "source PUSH preparation has no live consumer"))]
    fn materialize_unit_push(&self, weight: LocalWeightId) -> Result<Option<DetachedWeight>, SolveAvailabilityError> {
        let payload = self.weights.get(weight.0 as usize).ok_or_else(exhausted)?;
        let Some(set) = &payload.attachment else { return Ok(None); };
        if set.unit_push.is_none() { return Ok(None); }
        let mut atoms = Vec::new();
        atoms.try_reserve_exact(payload.allowed.len()).map_err(|_| exhausted())?;
        atoms.extend(payload.allowed.iter().cloned());
        let mut out = DetachedWeight::identity();
        out.left.try_reserve_exact(1).map_err(|_| exhausted())?;
        out.left.push(DetachedLeftEntry {
            id: DetachedAttachmentId(weight.0),
            pops: ExactCount::default(),
            pushes: ExactCount::from_u32(1)?,
            family: Some(DetachedPushFamily(atoms)),
        });
        Ok(Some(out))
    }
    pub fn attachment_source(&self, weight: LocalWeightId) -> Option<AttachmentSource> {
        self.weights[weight.0 as usize].attachment.as_ref().map(|set| AttachmentSource {
            composed_polarity: set.composed_polarity,
            lexical_scope: set.lexical_scope.clone(),
        })
    }
    pub fn allowed(&self, weight: LocalWeightId) -> &[SourceEffectId] {
        &self.weights[weight.0 as usize].allowed
    }
    fn assert_context(&self, context: ContextId) {
        assert!(
            context == IDENTITY || context.0 as usize <= self.contexts.len(),
            "context must be identity or an already interned node"
        );
    }
    fn relation(
        &mut self,
        pair: TypedPairKey,
        context: ContextId,
    ) -> Result<RelationId, SolveAvailabilityError> {
        self.assert_context(context);
        let key = RelationKey { pair, context };
        if let Some(&id) = self.keys.get(&key) {
            return Ok(id);
        }
        let id = RelationId(u32::try_from(self.relations.len()).map_err(|_| exhausted())?);
        self.relations.try_reserve(1).map_err(|_| exhausted())?;
        self.keys.try_reserve(1).map_err(|_| exhausted())?;
        self.pair_heads.try_reserve(1).map_err(|_| exhausted())?;
        let previous_on_pair = self.pair_heads.insert(pair, id);
        self.relations.push(Relation { key, previous_on_pair });
        self.keys.insert(key, id);
        Ok(id)
    }
    pub fn begin_use(&mut self) -> Result<usize, SolveAvailabilityError> {
        self.uses = self.uses.checked_add(1).ok_or_else(exhausted)?;
        Ok(self.uses)
    }
    #[cfg(test)]
    pub fn contains(&self, pair: TypedPairKey) -> bool {
        self.pair_heads.contains_key(&pair)
    }
    fn dependency(&mut self, dependency: Dependency) -> Result<(), SolveAvailabilityError> {
        if self.dependency_keys.contains(&dependency) {
            return Ok(());
        }
        self.dependencies.try_reserve(1).map_err(|_| exhausted())?;
        self.dependency_keys
            .try_reserve(1)
            .map_err(|_| exhausted())?;
        match dependency {
            Dependency::Derived { child, parent } => self.edge(parent, child)?,
            // Transport retains provenance across instantiation and row
            // lifecycle changes; it is not a constraint from the template to
            // a fresh use and must not replay that use's conflicts upstream.
            Dependency::Transport { .. } => {}
            Dependency::Replay {
                child,
                lower,
                upper,
                ..
            } => {
                self.edge(lower, child)?;
                self.edge(upper, child)?;
            }
        }
        if let Dependency::Transport { child, parent, use_origin: 0 } = dependency {
            if let Some(index) = &mut self.bundle_transports {
                index.insert(parent, child)?;
                self.bundle_edge(parent, child)?;
            }
        }
        self.dependencies.push(dependency);
        self.dependency_keys.insert(dependency);
        Ok(())
    }
    fn edge(
        &mut self,
        parent: RelationId,
        child: RelationId,
    ) -> Result<(), SolveAvailabilityError> {
        if self.edge_keys.contains(&(parent, child)) {
            return Ok(());
        }
        self.edges.try_reserve(1).map_err(|_| exhausted())?;
        self.edge_keys.try_reserve(1).map_err(|_| exhausted())?;
        self.edge_log.try_reserve(1).map_err(|_| exhausted())?;
        let new = !self.edges.contains_key(&parent);
        let mut fresh = Vec::new();
        let entries = if new {
            &mut fresh
        } else {
            self.edges.get_mut(&parent).unwrap()
        };
        let old = entries.capacity();
        entries.try_reserve(1).map_err(|_| exhausted())?;
        self.edge_bytes = self
            .edge_bytes
            .checked_add(
                (entries.capacity() - old)
                    .checked_mul(std::mem::size_of::<RelationId>())
                    .ok_or_else(exhausted)?,
            )
            .ok_or_else(exhausted)?;
        entries.push(child);
        if new {
            self.edges.insert(parent, fresh);
        }
        self.edge_keys.insert((parent, child));
        self.edge_log.push((parent, child));
        self.bundle_edge(parent, child)
    }
    pub fn children(&self, pair: TypedPairKey) -> impl Iterator<Item = TypedPairKey> + '_ {
        std::iter::successors(self.pair_heads.get(&pair).copied(), |id| {
            self.relations[id.0 as usize].previous_on_pair
        })
        .filter_map(|id| self.edges.get(&id))
        .flatten()
        .map(|id| self.relations[id.0 as usize].key.pair)
    }
    #[cfg(test)]
    pub fn bound(&self, key: BoundKey) -> Option<RelationId> {
        self.bound_relations(key).next()
    }
    pub fn bound_relations(&self, key: BoundKey) -> impl Iterator<Item = RelationId> + '_ {
        std::iter::successors(self.bounds.get(&key).copied(), |&index| {
            self.bound_keys[index].2
        }).map(|index| self.bound_keys[index].1)
    }
    pub fn bound_cursor(&self, key: BoundKey) -> Option<usize> {
        self.bounds.get(&key).copied()
    }
    pub fn bound_entry(&self, index: usize) -> (RelationId, Option<usize>) {
        let (_, relation, next) = self.bound_keys[index];
        (relation, next)
    }
    fn replay_progress(&mut self, key: (BoundKey, BoundKey), heads: (Option<usize>, Option<usize>)) -> Result<(), SolveAvailabilityError> {
        self.replay_heads.try_reserve(1).map_err(|_| exhausted())?;
        self.replay_log.try_reserve(1).map_err(|_| exhausted())?;
        let previous = self.replay_heads.insert(key, heads);
        self.replay_log.push((key, previous));
        Ok(())
    }
    fn attach(
        &mut self,
        key: BoundKey,
        relation: RelationId,
    ) -> Result<(), SolveAvailabilityError> {
        if self.bound_relations(key).any(|existing| existing == relation) {
            return Ok(());
        }
        self.bounds.try_reserve(1).map_err(|_| exhausted())?;
        self.bound_keys.try_reserve(1).map_err(|_| exhausted())?;
        let previous = self.bounds.insert(key, self.bound_keys.len());
        self.bound_keys.push((key, relation, previous));
        Ok(())
    }
    fn post_check_context(&self, relation: RelationId) -> ContextId {
        let context = self.relations[relation.0 as usize].key.context;
        if context != IDENTITY && matches!(self.contexts[context.0 as usize - 1],
            ContextExpr::PrefixLeft { input: IDENTITY, .. }) {
            // This executable filter is consumed at insertion; its bound and
            // derivation retain the current/future obligations.
            IDENTITY
        } else { context }
    }

}
pub(super) fn task_pair(task: LiveConstraintTask) -> TypedPairKey {
    match task {
        LiveConstraintTask::Value(pair) => TypedPairKey::Value(pair),
        LiveConstraintTask::Effect(lower, upper) => TypedPairKey::Effect { lower, upper },
    }
}
pub(super) fn bound_pair(BoundKey(owner, side, item): BoundKey) -> TypedPairKey {
    let (lower, upper) = if side == Polarity::Positive {
        (item, owner)
    } else {
        (owner, item)
    };
    match (lower, upper) {
        (ExtrusionEndpoint::Value(lower), ExtrusionEndpoint::Value(upper)) => {
            TypedPairKey::Value(CanonicalValuePairKey { lower, upper })
        }
        (ExtrusionEndpoint::Effect(lower), ExtrusionEndpoint::Effect(upper)) => {
            TypedPairKey::Effect { lower, upper }
        }
        _ => unreachable!("bound component kind"),
    }
}
impl InferenceSession {
    pub(super) fn candidate_context_pair(&self, pair: TypedPairKey) -> TypedPairKey {
        match pair {
            TypedPairKey::Value(pair) => TypedPairKey::Value(CanonicalValuePairKey {
                lower: self.canonical_value(pair.lower),
                upper: self.canonical_value(pair.upper),
            }),
            TypedPairKey::Effect { lower, upper } => TypedPairKey::Effect {
                lower: self.canonical_effect(lower),
                upper: self.canonical_effect(upper),
            },
        }
    }
    fn candidate_closed_allowance(&self, pair: TypedPairKey) -> Option<LocalWeightId> {
        let TypedPairKey::Effect { upper: EffectEndpointKey::Allowance(view), .. } = pair else { return None; };
        let view_data = &self.candidate_graph.as_ref()?.intrusion.effect_algebra.views[view as usize];
        view_data.closed_weight
    }
    fn candidate_context_source(&mut self, pair: TypedPairKey) -> Result<ContextId, SolveAvailabilityError> {
        let weight = self.candidate_closed_allowance(pair);
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        match weight {
            Some(weight) => state.context(ContextExpr::PrefixLeft { weight, input: IDENTITY }),
            None => Ok(IDENTITY),
        }
    }
    pub(super) fn candidate_context_seed(
        &mut self,
        task: LiveConstraintTask,
        occurrence: &ConstraintOccurrenceId,
    ) -> Result<(), SolveAvailabilityError> {
        if self.candidate_graph.is_none() {
            return Ok(());
        }
        let pair = self.candidate_context_pair(task_pair(task));
        let context = self.candidate_context_source(pair)?;
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let relation = state.relation(pair, context)?;
        let bundle_slot = match occurrence.local_slot() {
            40 | 41 => Some(41),
            45 | 46 => Some(46),
            _ => None,
        };
        if let Some(slot) = bundle_slot {
            let anchor = ConstraintOccurrenceId::new(occurrence.occurrence().clone(), slot);
            if let Some(&bundle) = state.source_bundles.get(&anchor) { state.bundle_link(relation, bundle)?; }
        }
        state.origins.try_reserve(1).map_err(|_| exhausted())?;
        state.origins.push(Origin {
            relation,
            occurrence: occurrence.clone(),
        });
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    pub(super) fn candidate_context_admit(
        &mut self,
        task: LiveConstraintTask,
    ) -> Result<Option<RelationId>, SolveAvailabilityError> {
        let Some(graph) = &self.candidate_graph else { return Ok(None); };
        let retained_parent = graph.intrusion.effect_algebra.context.processing;
        let parent = graph.intrusion.effect_algebra.processing
            .map(|p| self.candidate_context_pair(p));
        let pair = self.candidate_context_pair(task_pair(task));
        let context = self.candidate_context_source(pair)?;
        let parent_context = parent.map(|pair| self.candidate_context_source(pair)).transpose()?;
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let child = state.relation(pair, context)?;
        if let Some(parent) = parent {
            let parent = match retained_parent {
                Some(id) if state.relations[id.0 as usize].key.pair == parent => id,
                _ => state.relation(parent, parent_context.unwrap())?,
            };
            state.dependency(Dependency::Derived { child, parent })?;
        }
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(Some(child))
    }
    // Admission checks run before endpoint memoization and equality handling.
    // Once consumed, the normal Allowance bound retains current/future-lower
    // obligations. Children use the discharged context, not a repeated filter.
    pub(super) fn candidate_context_execute(
        &mut self,
        task: LiveConstraintTask,
        relation: Option<RelationId>,
    ) -> Result<bool, SolveAvailabilityError> {
        let Some(relation) = relation else { return Ok(false); };
        let state = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
        let key = state.relations[relation.0 as usize].key;
        assert_eq!(key.pair, self.candidate_context_pair(task_pair(task)), "task retains its relation endpoints");
        if key.context == IDENTITY { return Ok(false); }
        if state.discharged.contains(&relation) { return Ok(true); }
        let ContextExpr::PrefixLeft { weight, input: IDENTITY } = state.contexts[key.context.0 as usize - 1] else {
            // Only closed source filters have an executable consumer in this
            // slice. Other ContextExpr constructors are not admitted here.
            return Err(exhausted());
        };
        let payload = state.weights.get(weight.0 as usize).ok_or_else(exhausted)?;
        let view = payload.boundary;
        let boundary = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.views[view as usize];
        assert_eq!((&payload.owner, &payload.position), (&boundary.owner, &boundary.position));
        assert!(payload.left_word.is_empty() && payload.right_pops.is_empty());
        let lower = match task {
            LiveConstraintTask::Effect(lower, _) => lower,
            LiveConstraintTask::Value(_) => return Err(exhausted()),
        };
        let upper = EffectEndpointKey::Allowance(view);
        let registered = match self.canonical_effect(lower) {
            EffectEndpointKey::EffectRow(row) => self.effect_bounds[row as usize].exact_non_variable_uppers.contains(&upper),
            _ => false,
        };
        if registered {
            // The allowance already owns its executable bound, but this
            // source occurrence still needs an edge to that bound. Otherwise
            // a conflict recorded before this relation was admitted cannot
            // be replayed at this occurrence.
            let EffectEndpointKey::EffectRow(row) = self.canonical_effect(lower) else { unreachable!() };
            self.candidate_bound_origin(
                BoundKey(
                    ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)),
                    Polarity::Negative,
                    ExtrusionEndpoint::Effect(upper),
                ),
                Some(task_pair(task)),
            )?;
            self.candidate_replay_bound(
                ExtrusionEndpoint::Effect(EffectEndpointKey::EffectRow(row)),
                Polarity::Negative,
                ExtrusionEndpoint::Effect(upper),
                None,
            )?;
        } else {
            self.candidate_apply_effect(lower, upper)?;
        }
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        state.discharged.try_reserve(1).map_err(|_| exhausted())?;
        state.discharge_log.try_reserve(1).map_err(|_| exhausted())?;
        state.discharged.insert(relation);
        state.discharge_log.push(relation);
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(true)
    }
    pub(super) fn candidate_context_bound(
        &mut self,
        bound: BoundKey,
        origin: TypedPairKey,
    ) -> Result<(), SolveAvailabilityError> {
        let pair = self.candidate_context_pair(bound_pair(bound));
        let origin = self.candidate_context_pair(origin);
        let origin_context = self.candidate_context_source(origin)?;
        let retained_parent = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.processing;
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let parent = match retained_parent {
            Some(id) if state.relations[id.0 as usize].key.pair == origin => id,
            _ => state.relation(origin, origin_context)?,
        };
        let child = state.relation(pair, state.post_check_context(parent))?;
        state.dependency(Dependency::Derived { child, parent })?;
        state.attach(bound, child)
    }
    pub(super) fn candidate_context_replay<T>(
        &mut self,
        lower_input: BoundKey,
        upper_input: BoundKey,
        task: LiveConstraintTask,
        publish: impl FnOnce(&mut Self, &[RelationId]) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        self.candidate_context_replay_impl(lower_input, upper_input, task, false, publish)
    }
    pub(super) fn candidate_context_restore_replay<T>(
        &mut self,
        lower_input: BoundKey,
        upper_input: BoundKey,
        task: LiveConstraintTask,
        publish: impl FnOnce(&mut Self, &[RelationId]) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        self.candidate_context_replay_impl(lower_input, upper_input, task, true, publish)
    }
    fn candidate_context_replay_impl<T>(
        &mut self,
        lower_input: BoundKey,
        upper_input: BoundKey,
        task: LiveConstraintTask,
        incoming_use: bool,
        publish: impl FnOnce(&mut Self, &[RelationId]) -> Result<T, SolveAvailabilityError>,
    ) -> Result<T, SolveAvailabilityError> {
        let pair = self.candidate_context_pair(task_pair(task));
        let mut replay = Vec::new();
        let mut charge = 0;
        let result = (|| {
            let state = &self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context;
            let heads = (state.bound_cursor(lower_input), state.bound_cursor(upper_input));
            let recorded = state.replay_heads.get(&(lower_input, upper_input)).copied().unwrap_or((None, None));
            // Every incoming scheme use owns diagnostic replay, even when
            // ordinary propagation already admitted these exact dependencies.
            let old = if incoming_use { (None, None) } else { recorded };
            if !incoming_use && heads == old { return publish(self, &replay); }
            // Each newly retained fiber meets the opposite fibers once. Older
            // lower fibers meet only new uppers; the new/new quadrant is owned
            // by the first loop.
            for (start, stop, upper_start, upper_stop) in [
                (heads.0, old.0, heads.1, None),
                (old.0, None, heads.1, old.1),
            ] {
                if upper_start == upper_stop { continue; }
                let mut lower_cursor = start;
                while lower_cursor != stop {
                    let Some(index) = lower_cursor else { break; };
                    let (lower, next) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_entry(index);
                    lower_cursor = next;
                    let mut upper_cursor = upper_start;
                    while upper_cursor != upper_stop {
                        let Some(index) = upper_cursor else { break; };
                        let (upper, next) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_entry(index);
                        upper_cursor = next;
                        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                        let lower_context = state.relations[lower.0 as usize].key.context;
                        let upper_context = state.relations[upper.0 as usize].key.context;
                        // Empty-weight directed mix is identity; its ordered
                        // derivation remains in the dependency certificate.
                        let context = if lower_context == IDENTITY && upper_context == IDENTITY { IDENTITY }
                            else { state.context(ContextExpr::Replay { lower: lower_context, upper: upper_context })? };
                        let child = state.relation(pair, context)?;
                        let dependency = Dependency::Replay { child, lower, upper, lower_input, upper_input };
                        if !incoming_use && state.dependency_keys.contains(&dependency) { continue; }
                        state.dependency(dependency)?;
                        let old_capacity = replay.capacity();
                        replay.try_reserve(1).map_err(|_| exhausted())?;
                        self.candidate_scratch_growth(&mut charge,
                            (replay.capacity() - old_capacity).checked_mul(std::mem::size_of::<RelationId>()).ok_or_else(exhausted)?)?;
                        replay.push(child);
                    }
                }
            }
            if heads != recorded {
                self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.replay_progress((lower_input, upper_input), heads)?;
            }
            self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
            publish(self, &replay)
        })();
        drop(replay);
        self.candidate_graph.as_mut().unwrap().scratch_bytes -= charge;
        result
    }
    pub(super) fn candidate_context_canonicalize_bounds(&mut self) -> Result<(), SolveAvailabilityError> {
        // Representative changes affect third-owner incidence as well as the
        // merged row's outgoing bounds. Preserve the original fiber/provenance
        // and transport it to the canonical bound key before any replay.
        let count = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_keys.len();
        for index in 0..count {
            let (from, parent, _) = self.candidate_graph.as_ref().unwrap().intrusion.effect_algebra.context.bound_keys[index];
            let to = BoundKey(self.canonical_extrusion(from.0), from.1, self.canonical_extrusion(from.2));
            if to != from {
                self.candidate_context_transport(parent, to, 0)?;
                let pair = self.candidate_context_pair(bound_pair(to));
                let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
                let child = state.relation(pair, state.post_check_context(parent))?;
                // Equality transport remains within this owner, unlike fresh
                // scheme uses: conflicts must retain the original derivation.
                state.dependency(Dependency::Derived { child, parent })?;
            }
        }
        Ok(())
    }
    pub(super) fn candidate_context_fresh_transport(
        &mut self, parent: RelationId, to: BoundKey, use_origin: usize,
        context: ContextId,
    ) -> Result<RelationId, SolveAvailabilityError> {
        let pair = self.candidate_context_pair(bound_pair(to));
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let child = state.relation(pair, context)?;
        state.dependency(Dependency::Transport { child, parent, use_origin })?;
        state.attach(to, child)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)?;
        Ok(child)
    }
    pub(super) fn candidate_context_fresh_bundle(
        &mut self, child: RelationId, bundle: AttachmentBundleId,
    ) -> Result<(), SolveAvailabilityError> {
        self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context.bundle_link(child, bundle)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    #[allow(dead_code, reason = "equality bundle transport is distinct from fresh-use reconstruction")]
    pub(super) fn candidate_context_transport_bundle(
        &mut self, parent: RelationId, to: BoundKey, bundle: AttachmentBundleId,
    ) -> Result<(), SolveAvailabilityError> {
        let pair = self.candidate_context_pair(bound_pair(to));
        let state = &mut self.candidate_graph.as_mut().unwrap().intrusion.effect_algebra.context;
        let child = state.relation(pair, state.post_check_context(parent))?;
        state.bundle_link(child, bundle)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
    pub(super) fn candidate_context_transport(
        &mut self,
        parent: RelationId,
        to: BoundKey,
        use_origin: usize,
    ) -> Result<(), SolveAvailabilityError> {
        let pair = self.candidate_context_pair(bound_pair(to));
        let state = &mut self
            .candidate_graph
            .as_mut()
            .unwrap()
            .intrusion
            .effect_algebra
            .context;
        let child = state.relation(pair, state.post_check_context(parent))?;
        state.dependency(Dependency::Transport {
            child,
            parent,
            use_origin,
        })?;
        state.attach(to, child)?;
        self.sample_f4_resources(ResourceBoundary::IncomingRoute)
    }
}
#[cfg(test)]
#[path = "candidate_context_tests.rs"]
mod tests;
