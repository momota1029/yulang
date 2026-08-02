//! Factorized replay claim-parent storage.
//!
//! This module is the staged RCPF-A model. It deliberately has no admission or consumer wiring
//! yet; keeping the model isolated makes that later cutover explicit.

#![allow(dead_code)]

use std::marker::PhantomData;

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use super::*;

const MAX_PARENT_SET_DEPTH: u16 = 32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct ReplayOccurrenceId(pub(super) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct ParentSetVersionId(pub(super) u32);

impl ParentSetVersionId {
    const EMPTY: Self = Self(0);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct ParentSetChunkId(pub(super) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct ReplayParentAttachmentBatchId(pub(super) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct ReplayParentDraftId(pub(super) u32);

impl ReplayParentDraftId {
    /// The shared empty draft is represented by the sentinel rather than a plan allocation.
    pub(super) const EMPTY: Self = Self(0);
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct ReplayParentDraft {
    /// Legacy admission order. Losers are intentionally plan-local.
    pub(super) claims: Box<[UpperReplayClaimId]>,
}

type BoundReplayActions = SmallVec<[BoundReplayAction; 4]>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct BoundReplayAction {
    pub(super) constraint: SubtypeConstraintKey,
    pub(super) derivation: BinaryReplayDerivation,
    pub(super) lower_parents: ReplayParentDraftId,
    pub(super) upper_parents: ReplayParentDraftId,
    pub(super) canonicalization_disposition: Option<ConstraintCanonicalizationDisposition>,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub(super) struct BoundReplayPlan {
    pub(super) parent_drafts: Vec<ReplayParentDraft>,
    pub(super) input_count: usize,
    pub(super) generated: usize,
    pub(super) var_var: usize,
    pub(super) prefiltered: usize,
    pub(super) prefilter_duplicate: ReplayDuplicateProfile,
    pub(super) stats: BoundReplayApplyStats,
    pub(super) actions: BoundReplayActions,
    pub(super) evidence_actions: BoundReplayActions,
    pub(super) duplicate_actions: BoundReplayActions,
    pub(super) trivial_actions: BoundReplayActions,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct BoundReplayApplyStats {
    pub(super) accepted: usize,
    pub(super) duplicate: usize,
    pub(super) trivial: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct ParentSetEntry {
    pub(super) coverage_root: UpperReplayClaimId,
    pub(super) representative_claim: UpperReplayClaimId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ParentSetVersionRecord {
    pub(super) base: Option<ParentSetVersionId>,
    pub(super) delta: ParentSetChunkId,
    pub(super) len: u32,
    pub(super) depth: u16,
    pub(super) fingerprint: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ParentSetChunk {
    /// Canonical entry order; `coverage_root` is unique within the chunk.
    pub(super) entries: Box<[ParentSetEntry]>,
}

/// A bounded base/delta chain with content interning.
///
/// Normal extension stores only its accepted delta. Once a chain reaches the fixed depth bound,
/// an internal canonical checkpoint restores bounded membership lookup without changing logical
/// identity or iterator order.
#[derive(Debug)]
pub(super) struct ParentSetArena {
    versions: Vec<ParentSetVersionRecord>,
    chunks: Vec<ParentSetChunk>,
    chunks_by_fingerprint: FxHashMap<(u32, u64), Vec<ParentSetChunkId>>,
    versions_by_fingerprint: FxHashMap<(u32, u64), Vec<ParentSetVersionId>>,
}

impl Default for ParentSetArena {
    fn default() -> Self {
        let empty_chunk = ParentSetChunk {
            entries: Box::default(),
        };
        let empty_version = ParentSetVersionRecord {
            base: None,
            delta: ParentSetChunkId(0),
            len: 0,
            depth: 0,
            fingerprint: 0,
        };
        let mut chunks_by_fingerprint = FxHashMap::default();
        chunks_by_fingerprint.insert((0, 0), vec![ParentSetChunkId(0)]);
        let mut versions_by_fingerprint = FxHashMap::default();
        versions_by_fingerprint.insert((0, 0), vec![ParentSetVersionId::EMPTY]);
        Self {
            versions: vec![empty_version],
            chunks: vec![empty_chunk],
            chunks_by_fingerprint,
            versions_by_fingerprint,
        }
    }
}

impl ParentSetArena {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn empty_version(&self) -> ParentSetVersionId {
        ParentSetVersionId::EMPTY
    }

    pub(super) fn preflight_extend<'draft>(
        &self,
        base: ParentSetVersionId,
        draft: &'draft ReplayParentDraft,
        bounds: &TypeBounds,
    ) -> ParentSetExtensionPlan<'draft> {
        self.version_record(base);

        let mut accepted_roots = FxHashSet::default();
        let mut accepted_entries = Vec::new();
        for &claim in &draft.claims {
            let root = bounds
                .canonical_coverage_root(claim)
                .expect("replay parent draft contains an unknown claim");
            if self.contains(base, root) || !accepted_roots.insert(root) {
                continue;
            }
            accepted_entries.push(ParentSetEntry {
                coverage_root: root,
                representative_claim: claim,
            });
        }
        canonicalize_entries(&mut accepted_entries);

        ParentSetExtensionPlan {
            base,
            accepted_entries: accepted_entries.into_boxed_slice(),
            draft: PhantomData,
        }
    }

    pub(super) fn commit_extend(&mut self, plan: ParentSetExtensionPlan<'_>) -> ParentSetExtension {
        if plan.accepted_entries.is_empty() {
            return ParentSetExtension {
                version: plan.base,
                accepted_delta: ParentSetVersionId::EMPTY,
                changed: false,
            };
        }

        let accepted_len = u32::try_from(plan.accepted_entries.len())
            .expect("parent-set accepted delta length overflow");
        let accepted_fingerprint = entries_fingerprint(&plan.accepted_entries);
        let accepted_chunk = self.intern_chunk(plan.accepted_entries);
        let accepted_delta = self.intern_version_description(
            None,
            accepted_chunk,
            accepted_len,
            0,
            accepted_fingerprint,
        );

        let base_record = *self.version_record(plan.base);
        let len = base_record
            .len
            .checked_add(accepted_len)
            .expect("parent-set version length overflow");
        let fingerprint = base_record.fingerprint ^ accepted_fingerprint;
        let next_depth = base_record
            .depth
            .checked_add(1)
            .expect("parent-set version depth overflow");

        let version = if next_depth <= MAX_PARENT_SET_DEPTH {
            self.intern_version_description(
                Some(plan.base),
                accepted_chunk,
                len,
                next_depth,
                fingerprint,
            )
        } else {
            let mut checkpoint_entries = self.iter(plan.base).collect::<Vec<_>>();
            checkpoint_entries.extend_from_slice(&self.chunk(accepted_chunk).entries);
            canonicalize_entries(&mut checkpoint_entries);
            let checkpoint_chunk = self.intern_chunk(checkpoint_entries.into_boxed_slice());
            self.intern_version_description(None, checkpoint_chunk, len, 0, fingerprint)
        };

        ParentSetExtension {
            version,
            accepted_delta,
            changed: true,
        }
    }

    pub(super) fn contains(&self, version: ParentSetVersionId, root: UpperReplayClaimId) -> bool {
        self.representative_claim(version, root).is_some()
    }

    pub(super) fn representative_claim(
        &self,
        version: ParentSetVersionId,
        root: UpperReplayClaimId,
    ) -> Option<UpperReplayClaimId> {
        let mut cursor = Some(version);
        while let Some(version) = cursor {
            let record = self.version_record(version);
            if let Some(entry) = find_entry(&self.chunk(record.delta).entries, root) {
                return Some(entry.representative_claim);
            }
            cursor = record.base;
        }
        None
    }

    pub(super) fn iter(&self, version: ParentSetVersionId) -> impl Iterator<Item = ParentSetEntry> {
        let expected_len = self.version_record(version).len as usize;
        let mut entries = Vec::with_capacity(expected_len);
        let mut cursor = Some(version);
        while let Some(version) = cursor {
            let record = self.version_record(version);
            entries.extend_from_slice(&self.chunk(record.delta).entries);
            cursor = record.base;
        }
        debug_assert_eq!(entries.len(), expected_len);
        canonicalize_entries(&mut entries);
        entries.into_iter()
    }

    fn intern_chunk(&mut self, entries: Box<[ParentSetEntry]>) -> ParentSetChunkId {
        debug_assert!(
            entries
                .windows(2)
                .all(|pair| { canonical_entry_key(pair[0]) < canonical_entry_key(pair[1]) })
        );
        let key = (
            u32::try_from(entries.len()).expect("parent-set chunk length overflow"),
            entries_fingerprint(&entries),
        );
        if let Some(candidates) = self.chunks_by_fingerprint.get(&key) {
            for &candidate in candidates {
                if self.chunk(candidate).entries == entries {
                    return candidate;
                }
            }
        }

        let id = ParentSetChunkId(
            u32::try_from(self.chunks.len()).expect("parent-set chunk ID overflow"),
        );
        self.chunks.push(ParentSetChunk { entries });
        self.chunks_by_fingerprint.entry(key).or_default().push(id);
        id
    }

    fn intern_version_description(
        &mut self,
        base: Option<ParentSetVersionId>,
        delta: ParentSetChunkId,
        len: u32,
        depth: u16,
        fingerprint: u64,
    ) -> ParentSetVersionId {
        let key = (len, fingerprint);
        if let Some(candidates) = self.versions_by_fingerprint.get(&key) {
            for &candidate in candidates {
                if self.version_matches_description(candidate, base, delta) {
                    return candidate;
                }
            }
        }

        let id = ParentSetVersionId(
            u32::try_from(self.versions.len()).expect("parent-set version ID overflow"),
        );
        self.versions.push(ParentSetVersionRecord {
            base,
            delta,
            len,
            depth,
            fingerprint,
        });
        self.versions_by_fingerprint
            .entry(key)
            .or_default()
            .push(id);
        id
    }

    fn version_matches_description(
        &self,
        candidate: ParentSetVersionId,
        base: Option<ParentSetVersionId>,
        delta: ParentSetChunkId,
    ) -> bool {
        let mut cursor = Some(candidate);
        while let Some(version) = cursor {
            let record = self.version_record(version);
            for &entry in &self.chunk(record.delta).entries {
                if self.description_representative_claim(base, delta, entry.coverage_root)
                    != Some(entry.representative_claim)
                {
                    return false;
                }
            }
            cursor = record.base;
        }
        true
    }

    fn description_representative_claim(
        &self,
        base: Option<ParentSetVersionId>,
        delta: ParentSetChunkId,
        root: UpperReplayClaimId,
    ) -> Option<UpperReplayClaimId> {
        find_entry(&self.chunk(delta).entries, root)
            .map(|entry| entry.representative_claim)
            .or_else(|| base.and_then(|base| self.representative_claim(base, root)))
    }

    fn version_record(&self, id: ParentSetVersionId) -> &ParentSetVersionRecord {
        self.versions
            .get(id.0 as usize)
            .expect("unknown parent-set version")
    }

    fn chunk(&self, id: ParentSetChunkId) -> &ParentSetChunk {
        self.chunks
            .get(id.0 as usize)
            .expect("unknown parent-set chunk")
    }
}

#[derive(Debug)]
pub(super) struct ParentSetExtensionPlan<'draft> {
    base: ParentSetVersionId,
    accepted_entries: Box<[ParentSetEntry]>,
    draft: PhantomData<&'draft ReplayParentDraft>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ParentSetExtension {
    pub(super) version: ParentSetVersionId,
    pub(super) accepted_delta: ParentSetVersionId,
    pub(super) changed: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct ReplayOccurrenceKey {
    pub(super) result: ConstraintRecordId,
    pub(super) carrier: BinaryReplayDerivation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ReplayOccurrence {
    pub(super) id: ReplayOccurrenceId,
    pub(super) result: ConstraintRecordId,
    pub(super) carrier: BinaryReplayDerivation,
    pub(super) lower_parents: ParentSetVersionId,
    pub(super) upper_parents: ParentSetVersionId,
    pub(super) first_admission_ordinal: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ReplayParentAttachmentBatch {
    pub(super) id: ReplayParentAttachmentBatchId,
    pub(super) admission_ordinal: u64,
    pub(super) side: ReplayClaimParentSide,
    pub(super) occurrences: Box<[ReplayOccurrenceId]>,
    pub(super) accepted_delta: ParentSetVersionId,
}

impl ReplayParentAttachmentBatch {
    pub(super) fn order_key(&self) -> (u64, ReplayParentAttachmentBatchId) {
        (self.admission_ordinal, self.id)
    }
}

#[derive(Debug, Default)]
pub(super) struct ReplayOccurrenceStore {
    pub(super) occurrences: Vec<ReplayOccurrence>,
    pub(super) by_key: FxHashMap<ReplayOccurrenceKey, ReplayOccurrenceId>,
    pub(super) by_result: FxHashMap<ConstraintRecordId, Vec<ReplayOccurrenceId>>,
    pub(super) attachment_batches: Vec<ReplayParentAttachmentBatch>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct FirstReplayParentWitness {
    pub(super) occurrence: ReplayOccurrenceId,
    pub(super) parent_side: ReplayClaimParentSide,
    pub(super) parent_claim: UpperReplayClaimId,
    pub(super) admission_ordinal: u64,
}

#[derive(Debug, Default)]
pub(super) struct ReplayResultSummary {
    pub(super) first_parent_by_root:
        FxHashMap<(ConstraintRecordId, UpperReplayClaimId), FirstReplayParentWitness>,
    pub(super) projected_parent_versions: FxHashSet<(
        ConstraintRecordId,
        ReplayClaimParentSide,
        ParentSetVersionId,
    )>,
}

#[derive(Debug, Default)]
pub(super) struct ReplayClauseProjection {
    pub(super) clause_by_record_and_occurrence:
        FxHashMap<(BoundRecordId, ReplayOccurrenceId), RecordProofClauseId>,
    pub(super) attributed_claim_supports: FxHashSet<(BoundRecordId, UpperReplayClaimId)>,
}

fn canonicalize_entries(entries: &mut [ParentSetEntry]) {
    entries.sort_unstable_by_key(|&entry| canonical_entry_key(entry));
}

fn canonical_entry_key(entry: ParentSetEntry) -> (u32, u32) {
    (entry.coverage_root.0, entry.representative_claim.0)
}

fn find_entry(entries: &[ParentSetEntry], root: UpperReplayClaimId) -> Option<ParentSetEntry> {
    entries
        .binary_search_by_key(&root.0, |entry| entry.coverage_root.0)
        .ok()
        .map(|index| entries[index])
}

fn entries_fingerprint(entries: &[ParentSetEntry]) -> u64 {
    entries.iter().fold(0, |fingerprint, &entry| {
        fingerprint ^ entry_fingerprint(entry)
    })
}

fn entry_fingerprint(entry: ParentSetEntry) -> u64 {
    let key = ((entry.coverage_root.0 as u64) << 32) | entry.representative_claim.0 as u64;
    splitmix64(key ^ 0x5250_4346_5041_5245)
}

fn splitmix64(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

#[cfg(test)]
mod tests {
    use poly::types::{NegId, TypeVar};

    use super::*;

    #[test]
    fn extends_an_empty_arena_in_canonical_order() {
        let bounds = bounds_with_roots(&[0, 1]);
        let mut arena = ParentSetArena::new();
        let extension = extend(&mut arena, ParentSetVersionId::EMPTY, &[1, 0], &bounds);

        assert!(extension.changed);
        assert_eq!(
            arena.iter(extension.version).collect::<Vec<_>>(),
            vec![entry(0, 0), entry(1, 1)]
        );
        assert_eq!(
            arena.iter(extension.accepted_delta).collect::<Vec<_>>(),
            vec![entry(0, 0), entry(1, 1)]
        );
    }

    #[test]
    fn repeated_extension_of_the_same_roots_preserves_existing_winners() {
        let bounds = bounds_with_roots(&[0, 0, 0, 3, 3, 3]);
        let mut arena = ParentSetArena::new();
        let first = extend(&mut arena, ParentSetVersionId::EMPTY, &[1, 4], &bounds);
        let version_count = arena.versions.len();
        let chunk_count = arena.chunks.len();
        let repeated = extend(&mut arena, first.version, &[2, 5], &bounds);

        assert!(!repeated.changed);
        assert_eq!(repeated.version, first.version);
        assert_eq!(repeated.accepted_delta, arena.empty_version());
        assert_eq!(arena.versions.len(), version_count);
        assert_eq!(arena.chunks.len(), chunk_count);
        assert_eq!(
            arena.representative_claim(repeated.version, UpperReplayClaimId(0)),
            Some(UpperReplayClaimId(1))
        );
        assert_eq!(
            arena.representative_claim(repeated.version, UpperReplayClaimId(3)),
            Some(UpperReplayClaimId(4))
        );
    }

    #[test]
    fn entry_permutations_intern_and_iterate_as_the_same_logical_map() {
        let bounds = bounds_with_roots(&[0, 1]);
        let mut arena = ParentSetArena::new();
        let left = extend(&mut arena, ParentSetVersionId::EMPTY, &[1, 0], &bounds);
        let right = extend(&mut arena, ParentSetVersionId::EMPTY, &[0, 1], &bounds);

        assert_eq!(left.version, right.version);
        assert_eq!(
            arena.iter(left.version).collect::<Vec<_>>(),
            arena.iter(right.version).collect::<Vec<_>>()
        );
        assert_eq!(
            arena.iter(right.version).collect::<Vec<_>>(),
            vec![entry(0, 0), entry(1, 1)]
        );
    }

    #[test]
    fn representative_claim_is_first_wins_before_delta_canonicalization() {
        let bounds = bounds_with_roots(&[0, 0, 0]);
        let mut arena = ParentSetArena::new();
        let first = extend(&mut arena, ParentSetVersionId::EMPTY, &[2, 1], &bounds);
        let later = extend(&mut arena, first.version, &[1], &bounds);

        assert_eq!(
            arena.iter(first.version).collect::<Vec<_>>(),
            vec![entry(0, 2)]
        );
        assert_eq!(
            arena.representative_claim(later.version, UpperReplayClaimId(0)),
            Some(UpperReplayClaimId(2))
        );
        assert!(!later.changed);
    }

    fn extend(
        arena: &mut ParentSetArena,
        base: ParentSetVersionId,
        claims: &[u32],
        bounds: &TypeBounds,
    ) -> ParentSetExtension {
        let draft = ReplayParentDraft {
            claims: claims
                .iter()
                .copied()
                .map(UpperReplayClaimId)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        };
        let plan = arena.preflight_extend(base, &draft, bounds);
        arena.commit_extend(plan)
    }

    fn bounds_with_roots(roots: &[u32]) -> TypeBounds {
        let mut bounds = TypeBounds::new();
        bounds.upper_replay_claims = roots
            .iter()
            .copied()
            .enumerate()
            .map(|(index, root)| {
                let id = UpperReplayClaimId(index as u32);
                UpperReplayClaim {
                    id,
                    source: TypeVar(0),
                    endpoint: NegId(0),
                    weights: ConstraintWeights::default(),
                    producer_constraint: ConstraintRecordId(index as u32),
                    kind: UpperReplayClaimKind::Direct,
                    current_record: BoundRecordId(0),
                    coverage_root: UpperReplayClaimId(root),
                    lineage: UpperReplayClaimLineage::Original,
                }
            })
            .collect();
        bounds
    }

    fn entry(root: u32, representative: u32) -> ParentSetEntry {
        ParentSetEntry {
            coverage_root: UpperReplayClaimId(root),
            representative_claim: UpperReplayClaimId(representative),
        }
    }
}
