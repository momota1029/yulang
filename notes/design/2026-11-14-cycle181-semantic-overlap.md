# Cycle 181: semantic readback compatibility

Status: Draft proof-engineering note, 2026-11-14.

## Target and scope

The target remains I-30's `B4SkeletonV5.EvidenceNode
(GeneralNominalCenteredGroundBoundary.groundBoundary roles)`. This cycle does
not change that boundary, its notion of selection, or the other three fields
owned by Astra. Fresh integration is `bf6bc0d16263e9b418f0cfcea7c8f9ce621920b9`.

Cycle 180's arbitrary-origin extension fixes exact center values; its
source-origin specialization already needs only semantic equivalence. The
next local step removes that unnecessary exactness for general finite origins,
and connects the existing overlap-compatible linear nominal readback to a
complete candidate plan model. No old proof file is rewritten.

The full old raw and centered footprint is preserved. A fixed previous model
can extend across an overlapping binder only when its old value agrees with
the new observed nominal value. This is a local compatibility condition, not
a claim that the source language rejects the candidate or that no other model
exists. The eventual producer must still establish the required conditions
for reachable selected candidates rather than assume them.

## Verification plan

Use an isolated one-worker Lean cache and focused dependency closure. Audit
all new declarations with trust zero and warning-as-error. Do not run the
full repository build. Preserve historical imports and published files while
incorporating the pending upstream class-local work without modifying it.

## Checkpoint results

- `GeneralNominalSemanticCompatibility181`: arbitrary finite nominal origins,
  shared centers and old overlaps require `Equivalent`, not representative equality.
- `GeneralNominalObservationExtension181.extension_iff`: eliminates chosen
  representatives; observation existence, bounds, pairwise center coherence and
  overlap compatibility are necessary and sufficient for fixed-footprint extension.
- `GeneralDictionaryCenteredOverlapExact181.joint_iff`: actual finite linear
  nominal leaf plans have exactly the nonpoint overlap condition, with point
  input names and a fixed previous model.
- `GeneralNominalBinderIdentity181`: same-seed allocated binder collisions expose
  invocation, declaration and binder identity; registered actual uses give readback.
- `GeneralDictionaryCenteredProvenance181`: a syntactic registered-use coverage
  certificate supplies overlap compatibility, a joint model and, with separate
  raw-installation/value-support assumptions, a stable Instance.
- `GeneralNominalSemanticCollisionExample181`: two unequal chosen types, top and
  union(top,top), share one fresh center. Semantic extension succeeds; simultaneous
  exact assignment is impossible. This is a finite-family regression, not a
  source Candidate or reachable-boundary counterexample.

General G EvidenceNode remains OPEN (0 newly closed fields). Coverage has not
been derived for all full-footprint overlaps in reachable states. In particular,
raw-source freshness alone does not classify historical plan/site sources, and
old registered origins still need transport to the refreshed current candidate.
Astra's class-local obstruction concerns another boundary and is not transferred
to G. No semantic design decision is made here.
