//! Factorized replay claim-parent storage.
//!
//! This module is the staged RCPF-A model. It deliberately has no admission or consumer wiring
//! yet; keeping the model isolated makes that later cutover explicit.

#![allow(dead_code)]

use std::marker::PhantomData;

use rustc_hash::{FxHashMap, FxHashSet};

use super::*;

const MAX_PARENT_SET_DEPTH: u16 = 32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ReplayOccurrenceId(pub(super) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ParentSetVersionId(pub(super) u32);

impl ParentSetVersionId {
    const EMPTY: Self = Self(0);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ParentSetChunkId(pub(super) u32);

impl ParentSetChunkId {
    const EMPTY: Self = Self(0);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct ReplayParentAttachmentBatchId(pub(super) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ReplayParentDraftId(pub(super) u32);

impl ReplayParentDraftId {
    /// The shared empty draft is represented by the sentinel rather than a plan allocation.
    pub(super) const EMPTY: Self = Self(0);
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(super) struct ReplayParentDraft {
    /// Legacy admission order. Losers are intentionally plan-local.
    pub(super) claims: Box<[UpperReplayClaimId]>,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplayFactoredShadowFailure {
    AllocationFailed,
    ReplayOccurrenceIdOverflow,
    ReplayAdmissionOrdinalOverflow,
    ParentSetLengthOverflow,
    ParentSetDepthOverflow,
    ParentSetVersionIdOverflow,
    ParentSetChunkIdOverflow,
    UnknownParentSetVersion(ParentSetVersionId),
    UnknownParentSetChunk(ParentSetChunkId),
    UnknownReplayParentClaim(UpperReplayClaimId),
    UnknownReplayParentDraft(ReplayParentDraftId),
    ReplayParentDraftMismatch(ReplayClaimParentSide),
    #[cfg(any(test, debug_assertions))]
    OracleMismatch(ReplayFactoredOracleMismatch),
    UnknownReplayOccurrence(ReplayOccurrenceId),
    InvalidReplayParentCoverageRoot {
        claim: UpperReplayClaimId,
        root: UpperReplayClaimId,
    },
    NonCanonicalParentSetChunk,
    CorruptParentSetVersionLength {
        version: ParentSetVersionId,
        expected: u32,
        actual: usize,
    },
    CorruptParentSetIndex,
    CorruptReplayOccurrenceIndex,
}

#[cfg(any(test, debug_assertions))]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplayFactoredOracleMismatch {
    ExactParentRelation,
    QualifiedReplayCarriers,
    ClauseMapping,
    ExactClauseLinks,
    AttributedRoots,
    ClaimedAttributionUnion,
    ReplayDependencyEdges,
    DerivedReplayLineage,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) enum ReplayFactoredShadowStatus {
    #[default]
    Active,
    Failed(ReplayFactoredShadowFailure),
}

pub(super) type ReplayFactoredResult<T> = Result<T, ReplayFactoredShadowFailure>;

const EMPTY_PARENT_SET_VERSION: ParentSetVersionRecord = ParentSetVersionRecord {
    base: None,
    delta: ParentSetChunkId::EMPTY,
    len: 0,
    depth: 0,
    fingerprint: 0,
};

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
    #[cfg(test)]
    fail_next_reservation: bool,
}

impl Default for ParentSetArena {
    fn default() -> Self {
        Self {
            versions: Vec::new(),
            chunks: Vec::new(),
            chunks_by_fingerprint: FxHashMap::default(),
            versions_by_fingerprint: FxHashMap::default(),
            #[cfg(test)]
            fail_next_reservation: false,
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
    ) -> ReplayFactoredResult<ParentSetExtensionPlan<'draft>> {
        self.version_record(base)?;

        let mut accepted_roots = FxHashSet::default();
        let mut accepted_entries = Vec::new();
        let mut storage_reserved = false;
        for &claim in &draft.claims {
            let root = replay_parent_coverage_root(bounds, claim)?;
            if self.contains(base, root)? {
                continue;
            }
            if !storage_reserved {
                accepted_roots
                    .try_reserve(draft.claims.len())
                    .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
                accepted_entries
                    .try_reserve(draft.claims.len())
                    .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
                storage_reserved = true;
            }
            if !accepted_roots.insert(root) {
                continue;
            }
            accepted_entries.push(ParentSetEntry {
                coverage_root: root,
                representative_claim: claim,
            });
        }
        canonicalize_entries(&mut accepted_entries);

        Ok(ParentSetExtensionPlan {
            base,
            accepted_entries: accepted_entries.into_boxed_slice(),
            draft: PhantomData,
        })
    }

    pub(super) fn commit_extend(
        &mut self,
        plan: ParentSetExtensionPlan<'_>,
    ) -> ReplayFactoredResult<ParentSetExtension> {
        if plan.accepted_entries.is_empty() {
            return Ok(ParentSetExtension {
                version: plan.base,
                accepted_delta: ParentSetVersionId::EMPTY,
                changed: false,
            });
        }

        let accepted_len = u32::try_from(plan.accepted_entries.len())
            .map_err(|_| ReplayFactoredShadowFailure::ParentSetLengthOverflow)?;
        let accepted_fingerprint = entries_fingerprint(&plan.accepted_entries);
        let accepted_chunk = self.intern_chunk(plan.accepted_entries)?;
        let accepted_delta = self.intern_version_description(
            None,
            accepted_chunk,
            accepted_len,
            0,
            accepted_fingerprint,
        )?;

        let base_record = *self.version_record(plan.base)?;
        let len = base_record
            .len
            .checked_add(accepted_len)
            .ok_or(ReplayFactoredShadowFailure::ParentSetLengthOverflow)?;
        let fingerprint = base_record.fingerprint ^ accepted_fingerprint;
        let next_depth = base_record
            .depth
            .checked_add(1)
            .ok_or(ReplayFactoredShadowFailure::ParentSetDepthOverflow)?;

        let version = if next_depth <= MAX_PARENT_SET_DEPTH {
            self.intern_version_description(
                Some(plan.base),
                accepted_chunk,
                len,
                next_depth,
                fingerprint,
            )?
        } else {
            let mut checkpoint_entries = self.iter(plan.base)?.collect::<Vec<_>>();
            let accepted_entries = self.chunk_entries(accepted_chunk)?;
            checkpoint_entries
                .try_reserve(accepted_entries.len())
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            checkpoint_entries.extend_from_slice(accepted_entries);
            canonicalize_entries(&mut checkpoint_entries);
            let checkpoint_chunk = self.intern_chunk(checkpoint_entries.into_boxed_slice())?;
            self.intern_version_description(None, checkpoint_chunk, len, 0, fingerprint)?
        };

        Ok(ParentSetExtension {
            version,
            accepted_delta,
            changed: true,
        })
    }

    pub(super) fn contains(
        &self,
        version: ParentSetVersionId,
        root: UpperReplayClaimId,
    ) -> ReplayFactoredResult<bool> {
        Ok(self.representative_claim(version, root)?.is_some())
    }

    pub(super) fn representative_claim(
        &self,
        version: ParentSetVersionId,
        root: UpperReplayClaimId,
    ) -> ReplayFactoredResult<Option<UpperReplayClaimId>> {
        let mut cursor = Some(version);
        while let Some(version) = cursor {
            let record = self.version_record(version)?;
            if let Some(entry) = find_entry(self.chunk_entries(record.delta)?, root) {
                return Ok(Some(entry.representative_claim));
            }
            cursor = record.base;
        }
        Ok(None)
    }

    pub(super) fn iter(
        &self,
        version: ParentSetVersionId,
    ) -> ReplayFactoredResult<std::vec::IntoIter<ParentSetEntry>> {
        let expected_len = self.version_record(version)?.len;
        let mut entries = Vec::new();
        entries
            .try_reserve(expected_len as usize)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        let mut cursor = Some(version);
        while let Some(version) = cursor {
            let record = self.version_record(version)?;
            let delta = self.chunk_entries(record.delta)?;
            entries
                .try_reserve(delta.len())
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            entries.extend_from_slice(delta);
            cursor = record.base;
        }
        if entries.len() != expected_len as usize {
            return Err(ReplayFactoredShadowFailure::CorruptParentSetVersionLength {
                version,
                expected: expected_len,
                actual: entries.len(),
            });
        }
        canonicalize_entries(&mut entries);
        Ok(entries.into_iter())
    }

    #[cfg(test)]
    pub(super) fn storage_census(
        &self,
    ) -> (usize, usize, usize, usize, usize, usize, usize, usize) {
        (
            self.versions.len(),
            self.versions.capacity(),
            self.chunks.len(),
            self.chunks.capacity(),
            self.versions_by_fingerprint.len(),
            self.versions_by_fingerprint.capacity(),
            self.chunks_by_fingerprint.len(),
            self.chunks_by_fingerprint.capacity(),
        )
    }

    fn intern_chunk(
        &mut self,
        entries: Box<[ParentSetEntry]>,
    ) -> ReplayFactoredResult<ParentSetChunkId> {
        if !entries.windows(2).all(|pair| {
            canonical_entry_key(pair[0]) < canonical_entry_key(pair[1])
                && pair[0].coverage_root != pair[1].coverage_root
        }) {
            return Err(ReplayFactoredShadowFailure::NonCanonicalParentSetChunk);
        }
        let key = (
            u32::try_from(entries.len())
                .map_err(|_| ReplayFactoredShadowFailure::ParentSetLengthOverflow)?,
            entries_fingerprint(&entries),
        );
        if let Some(candidates) = self.chunks_by_fingerprint.get(&key) {
            for &candidate in candidates {
                if self.chunk_entries(candidate)? == entries.as_ref() {
                    return Ok(candidate);
                }
            }
        }

        let id = self.next_chunk_id()?;
        self.try_reserve_chunks(1)?;
        let existing_key = self.chunks_by_fingerprint.contains_key(&key);
        let mut new_candidates = if existing_key {
            self.chunks_by_fingerprint
                .get_mut(&key)
                .ok_or(ReplayFactoredShadowFailure::CorruptParentSetIndex)?
                .try_reserve(1)
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            None
        } else {
            self.try_reserve_chunk_index(1)?;
            let mut candidates = Vec::new();
            candidates
                .try_reserve(1)
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            Some(candidates)
        };

        self.chunks.push(ParentSetChunk { entries });
        if let Some(candidates) = &mut new_candidates {
            candidates.push(id);
        } else if let Some(candidates) = self.chunks_by_fingerprint.get_mut(&key) {
            candidates.push(id);
        } else {
            return Err(ReplayFactoredShadowFailure::CorruptParentSetIndex);
        }
        if let Some(candidates) = new_candidates {
            self.chunks_by_fingerprint.insert(key, candidates);
        }
        Ok(id)
    }

    fn intern_version_description(
        &mut self,
        base: Option<ParentSetVersionId>,
        delta: ParentSetChunkId,
        len: u32,
        depth: u16,
        fingerprint: u64,
    ) -> ReplayFactoredResult<ParentSetVersionId> {
        let key = (len, fingerprint);
        if let Some(candidates) = self.versions_by_fingerprint.get(&key) {
            for &candidate in candidates {
                if self.version_matches_description(candidate, base, delta)? {
                    return Ok(candidate);
                }
            }
        }

        let id = self.next_version_id()?;
        self.try_reserve_versions(1)?;
        let existing_key = self.versions_by_fingerprint.contains_key(&key);
        let mut new_candidates = if existing_key {
            self.versions_by_fingerprint
                .get_mut(&key)
                .ok_or(ReplayFactoredShadowFailure::CorruptParentSetIndex)?
                .try_reserve(1)
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            None
        } else {
            self.try_reserve_version_index(1)?;
            let mut candidates = Vec::new();
            candidates
                .try_reserve(1)
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            Some(candidates)
        };

        self.versions.push(ParentSetVersionRecord {
            base,
            delta,
            len,
            depth,
            fingerprint,
        });
        if let Some(candidates) = &mut new_candidates {
            candidates.push(id);
        } else if let Some(candidates) = self.versions_by_fingerprint.get_mut(&key) {
            candidates.push(id);
        } else {
            return Err(ReplayFactoredShadowFailure::CorruptParentSetIndex);
        }
        if let Some(candidates) = new_candidates {
            self.versions_by_fingerprint.insert(key, candidates);
        }
        Ok(id)
    }

    fn version_matches_description(
        &self,
        candidate: ParentSetVersionId,
        base: Option<ParentSetVersionId>,
        delta: ParentSetChunkId,
    ) -> ReplayFactoredResult<bool> {
        let mut cursor = Some(candidate);
        while let Some(version) = cursor {
            let record = self.version_record(version)?;
            for &entry in self.chunk_entries(record.delta)? {
                if self.description_representative_claim(base, delta, entry.coverage_root)?
                    != Some(entry.representative_claim)
                {
                    return Ok(false);
                }
            }
            cursor = record.base;
        }
        Ok(true)
    }

    fn description_representative_claim(
        &self,
        base: Option<ParentSetVersionId>,
        delta: ParentSetChunkId,
        root: UpperReplayClaimId,
    ) -> ReplayFactoredResult<Option<UpperReplayClaimId>> {
        if let Some(entry) = find_entry(self.chunk_entries(delta)?, root) {
            return Ok(Some(entry.representative_claim));
        }
        match base {
            Some(base) => self.representative_claim(base, root),
            None => Ok(None),
        }
    }

    fn version_record(
        &self,
        id: ParentSetVersionId,
    ) -> ReplayFactoredResult<&ParentSetVersionRecord> {
        if id == ParentSetVersionId::EMPTY {
            return Ok(&EMPTY_PARENT_SET_VERSION);
        }
        let index =
            id.0.checked_sub(1)
                .ok_or(ReplayFactoredShadowFailure::UnknownParentSetVersion(id))?;
        self.versions
            .get(index as usize)
            .ok_or(ReplayFactoredShadowFailure::UnknownParentSetVersion(id))
    }

    fn chunk_entries(&self, id: ParentSetChunkId) -> ReplayFactoredResult<&[ParentSetEntry]> {
        if id == ParentSetChunkId::EMPTY {
            return Ok(&[]);
        }
        let index =
            id.0.checked_sub(1)
                .ok_or(ReplayFactoredShadowFailure::UnknownParentSetChunk(id))?;
        self.chunks
            .get(index as usize)
            .map(|chunk| chunk.entries.as_ref())
            .ok_or(ReplayFactoredShadowFailure::UnknownParentSetChunk(id))
    }

    fn next_version_id(&self) -> ReplayFactoredResult<ParentSetVersionId> {
        let index = u32::try_from(self.versions.len())
            .map_err(|_| ReplayFactoredShadowFailure::ParentSetVersionIdOverflow)?;
        index
            .checked_add(1)
            .map(ParentSetVersionId)
            .ok_or(ReplayFactoredShadowFailure::ParentSetVersionIdOverflow)
    }

    fn next_chunk_id(&self) -> ReplayFactoredResult<ParentSetChunkId> {
        let index = u32::try_from(self.chunks.len())
            .map_err(|_| ReplayFactoredShadowFailure::ParentSetChunkIdOverflow)?;
        index
            .checked_add(1)
            .map(ParentSetChunkId)
            .ok_or(ReplayFactoredShadowFailure::ParentSetChunkIdOverflow)
    }

    fn try_reserve_versions(&mut self, additional: usize) -> ReplayFactoredResult<()> {
        self.maybe_fail_reservation()?;
        self.versions
            .try_reserve(additional)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)
    }

    fn try_reserve_chunks(&mut self, additional: usize) -> ReplayFactoredResult<()> {
        self.maybe_fail_reservation()?;
        self.chunks
            .try_reserve(additional)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)
    }

    fn try_reserve_version_index(&mut self, additional: usize) -> ReplayFactoredResult<()> {
        self.maybe_fail_reservation()?;
        self.versions_by_fingerprint
            .try_reserve(additional)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)
    }

    fn try_reserve_chunk_index(&mut self, additional: usize) -> ReplayFactoredResult<()> {
        self.maybe_fail_reservation()?;
        self.chunks_by_fingerprint
            .try_reserve(additional)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)
    }

    fn maybe_fail_reservation(&mut self) -> ReplayFactoredResult<()> {
        #[cfg(test)]
        if std::mem::take(&mut self.fail_next_reservation) {
            super::mark_next_replay_soak_failure_as_intentional();
            return Err(ReplayFactoredShadowFailure::AllocationFailed);
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn fail_next_reservation(&mut self) {
        self.fail_next_reservation = true;
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
    next_admission_ordinal: u64,
}

impl ReplayOccurrenceStore {
    pub(super) fn claim_admission_ordinal(&mut self) -> ReplayFactoredResult<u64> {
        let ordinal = self.next_admission_ordinal;
        self.next_admission_ordinal = ordinal
            .checked_add(1)
            .ok_or(ReplayFactoredShadowFailure::ReplayAdmissionOrdinalOverflow)?;
        Ok(ordinal)
    }

    pub(super) fn occurrence_id(&self, key: ReplayOccurrenceKey) -> Option<ReplayOccurrenceId> {
        self.by_key.get(&key).copied()
    }

    pub(super) fn occurrence(
        &self,
        id: ReplayOccurrenceId,
    ) -> ReplayFactoredResult<&ReplayOccurrence> {
        self.occurrences
            .get(id.0 as usize)
            .ok_or(ReplayFactoredShadowFailure::UnknownReplayOccurrence(id))
    }

    pub(super) fn update_parent_versions(
        &mut self,
        id: ReplayOccurrenceId,
        lower_parents: ParentSetVersionId,
        upper_parents: ParentSetVersionId,
    ) -> ReplayFactoredResult<()> {
        let occurrence = self
            .occurrences
            .get_mut(id.0 as usize)
            .ok_or(ReplayFactoredShadowFailure::UnknownReplayOccurrence(id))?;
        occurrence.lower_parents = lower_parents;
        occurrence.upper_parents = upper_parents;
        Ok(())
    }

    pub(super) fn try_insert(
        &mut self,
        key: ReplayOccurrenceKey,
        lower_parents: ParentSetVersionId,
        upper_parents: ParentSetVersionId,
        first_admission_ordinal: u64,
    ) -> ReplayFactoredResult<ReplayOccurrenceId> {
        if self.by_key.contains_key(&key) {
            return Err(ReplayFactoredShadowFailure::CorruptReplayOccurrenceIndex);
        }
        let raw_id = u32::try_from(self.occurrences.len())
            .map_err(|_| ReplayFactoredShadowFailure::ReplayOccurrenceIdOverflow)?;
        let id = ReplayOccurrenceId(raw_id);

        self.occurrences
            .try_reserve(1)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        self.by_key
            .try_reserve(1)
            .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
        let result_already_indexed = self.by_result.contains_key(&key.result);
        let mut new_result_occurrences = if result_already_indexed {
            self.by_result
                .get_mut(&key.result)
                .ok_or(ReplayFactoredShadowFailure::CorruptReplayOccurrenceIndex)?
                .try_reserve(1)
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            None
        } else {
            self.by_result
                .try_reserve(1)
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            let mut occurrences = Vec::new();
            occurrences
                .try_reserve(1)
                .map_err(|_| ReplayFactoredShadowFailure::AllocationFailed)?;
            Some(occurrences)
        };

        self.occurrences.push(ReplayOccurrence {
            id,
            result: key.result,
            carrier: key.carrier,
            lower_parents,
            upper_parents,
            first_admission_ordinal,
        });
        self.by_key.insert(key, id);
        if let Some(occurrences) = &mut new_result_occurrences {
            occurrences.push(id);
        } else if let Some(occurrences) = self.by_result.get_mut(&key.result) {
            occurrences.push(id);
        } else {
            return Err(ReplayFactoredShadowFailure::CorruptReplayOccurrenceIndex);
        }
        if let Some(occurrences) = new_result_occurrences {
            self.by_result.insert(key.result, occurrences);
        }
        Ok(id)
    }
}

/// Read-side RCPF boundary. The facade names the two queries from the design while reusing the
/// existing occurrence vector and `by_result` index without adding another projection.
impl ConstraintMachine {
    pub(super) fn replay_occurrences_for_result(
        &self,
        result: ConstraintRecordId,
    ) -> impl Iterator<Item = ReplayOccurrenceId> + '_ {
        self.replay_occurrences
            .by_result
            .get(&result)
            .into_iter()
            .flat_map(|occurrences| occurrences.iter().copied())
    }

    pub(super) fn replay_occurrence(
        &self,
        id: ReplayOccurrenceId,
    ) -> ReplayFactoredResult<&ReplayOccurrence> {
        self.replay_occurrences.occurrence(id)
    }
}

fn replay_parent_coverage_root(
    bounds: &TypeBounds,
    claim: UpperReplayClaimId,
) -> ReplayFactoredResult<UpperReplayClaimId> {
    let claim_record = bounds
        .upper_replay_claims
        .get(claim.0 as usize)
        .ok_or(ReplayFactoredShadowFailure::UnknownReplayParentClaim(claim))?;
    let root = claim_record.coverage_root;
    let root_record = bounds
        .upper_replay_claims
        .get(root.0 as usize)
        .ok_or(ReplayFactoredShadowFailure::InvalidReplayParentCoverageRoot { claim, root })?;
    if root_record.coverage_root != root {
        return Err(ReplayFactoredShadowFailure::InvalidReplayParentCoverageRoot { claim, root });
    }
    Ok(root)
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
        .and_then(|index| entries.get(index).copied())
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
    fn virtual_empty_arena_has_zero_allocation_and_stays_virtual_on_empty_extend() {
        let bounds = TypeBounds::new();
        let draft = ReplayParentDraft::default();
        let mut arena = ParentSetArena::new();

        assert_arena_storage_is_unallocated(&arena);
        assert!(
            !arena
                .contains(ParentSetVersionId::EMPTY, UpperReplayClaimId(0))
                .unwrap()
        );
        assert_eq!(
            arena
                .representative_claim(ParentSetVersionId::EMPTY, UpperReplayClaimId(0))
                .unwrap(),
            None
        );
        assert_eq!(entries(&arena, ParentSetVersionId::EMPTY), Vec::new());

        let plan = arena
            .preflight_extend(ParentSetVersionId::EMPTY, &draft, &bounds)
            .unwrap();
        let extension = arena.commit_extend(plan).unwrap();
        assert_eq!(
            extension,
            ParentSetExtension {
                version: ParentSetVersionId::EMPTY,
                accepted_delta: ParentSetVersionId::EMPTY,
                changed: false,
            }
        );
        assert_arena_storage_is_unallocated(&arena);
    }

    #[test]
    fn extends_an_empty_arena_in_canonical_order() {
        let bounds = bounds_with_roots(&[0, 1]);
        let mut arena = ParentSetArena::new();
        let extension = extend(&mut arena, ParentSetVersionId::EMPTY, &[1, 0], &bounds);

        assert!(extension.changed);
        assert_eq!(
            entries(&arena, extension.version),
            vec![entry(0, 0), entry(1, 1)]
        );
        assert_eq!(
            entries(&arena, extension.accepted_delta),
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
            arena
                .representative_claim(repeated.version, UpperReplayClaimId(0))
                .unwrap(),
            Some(UpperReplayClaimId(1))
        );
        assert_eq!(
            arena
                .representative_claim(repeated.version, UpperReplayClaimId(3))
                .unwrap(),
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
            entries(&arena, left.version),
            entries(&arena, right.version)
        );
        assert_eq!(
            entries(&arena, right.version),
            vec![entry(0, 0), entry(1, 1)]
        );
    }

    #[test]
    fn representative_claim_is_first_wins_before_delta_canonicalization() {
        let bounds = bounds_with_roots(&[0, 0, 0]);
        let mut arena = ParentSetArena::new();
        let first = extend(&mut arena, ParentSetVersionId::EMPTY, &[2, 1], &bounds);
        let later = extend(&mut arena, first.version, &[1], &bounds);

        assert_eq!(entries(&arena, first.version), vec![entry(0, 2)]);
        assert_eq!(
            arena
                .representative_claim(later.version, UpperReplayClaimId(0))
                .unwrap(),
            Some(UpperReplayClaimId(2))
        );
        assert!(!later.changed);
    }

    #[test]
    fn invalid_ids_and_claims_return_errors() {
        let arena = ParentSetArena::new();
        let bounds = TypeBounds::new();
        let invalid_root_bounds = bounds_with_roots(&[1, 0]);
        let unknown_version = ParentSetVersionId(1);
        let unknown_chunk = ParentSetChunkId(1);
        let draft = ReplayParentDraft {
            claims: Box::new([UpperReplayClaimId(0)]),
        };

        assert_eq!(
            arena.contains(unknown_version, UpperReplayClaimId(0)),
            Err(ReplayFactoredShadowFailure::UnknownParentSetVersion(
                unknown_version
            ))
        );
        assert!(matches!(
            arena.iter(unknown_version),
            Err(ReplayFactoredShadowFailure::UnknownParentSetVersion(
                version
            )) if version == unknown_version
        ));
        assert_eq!(
            arena.chunk_entries(unknown_chunk),
            Err(ReplayFactoredShadowFailure::UnknownParentSetChunk(
                unknown_chunk
            ))
        );
        assert!(matches!(
            arena.preflight_extend(ParentSetVersionId::EMPTY, &draft, &bounds),
            Err(ReplayFactoredShadowFailure::UnknownReplayParentClaim(
                UpperReplayClaimId(0)
            ))
        ));
        assert!(matches!(
            arena.preflight_extend(
                ParentSetVersionId::EMPTY,
                &draft,
                &invalid_root_bounds
            ),
            Err(
                ReplayFactoredShadowFailure::InvalidReplayParentCoverageRoot {
                    claim,
                    root,
                }
            ) if claim == UpperReplayClaimId(0) && root == UpperReplayClaimId(1)
        ));
    }

    #[test]
    fn reservation_failure_returns_error_without_committing_storage() {
        let bounds = bounds_with_roots(&[0]);
        let draft = ReplayParentDraft {
            claims: Box::new([UpperReplayClaimId(0)]),
        };
        let mut arena = ParentSetArena::new();
        let plan = arena
            .preflight_extend(ParentSetVersionId::EMPTY, &draft, &bounds)
            .unwrap();
        arena.fail_next_reservation();

        assert_eq!(
            arena.commit_extend(plan),
            Err(ReplayFactoredShadowFailure::AllocationFailed)
        );
        assert_arena_storage_is_unallocated(&arena);
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
        let plan = arena.preflight_extend(base, &draft, bounds).unwrap();
        arena.commit_extend(plan).unwrap()
    }

    fn entries(arena: &ParentSetArena, version: ParentSetVersionId) -> Vec<ParentSetEntry> {
        arena.iter(version).unwrap().collect()
    }

    fn assert_arena_storage_is_unallocated(arena: &ParentSetArena) {
        assert_eq!(arena.versions.len(), 0);
        assert_eq!(arena.versions.capacity(), 0);
        assert_eq!(arena.chunks.len(), 0);
        assert_eq!(arena.chunks.capacity(), 0);
        assert_eq!(arena.versions_by_fingerprint.len(), 0);
        assert_eq!(arena.versions_by_fingerprint.capacity(), 0);
        assert_eq!(arena.chunks_by_fingerprint.len(), 0);
        assert_eq!(arena.chunks_by_fingerprint.capacity(), 0);
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
