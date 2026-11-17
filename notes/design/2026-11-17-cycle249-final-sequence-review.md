# Read-only review: materialized owner-frame sequences

Reviewed MaterializedDomain249, MaterializedOwnerFrame249,
MaterializedSequence249 and MaterializedSequenceModels249 against their actual
statements. No logical weakening or missing intermediate witness condition was
found in this review. The parent's strict build/audit remains the verification
source for those parent-authored modules; the review did not rebuild them.

## What is established

- Materialized is a provenance predicate, not an assumed Stable law. Its base
  constructor is actual Journal243.compile of a state satisfying LegacyEmpty,
  with any expression mapping. Reachability is NOT required by that constructor.
  Reachable mixed/point states can supply LegacyEmpty through the earlier
  actual theorems, but the converse is not asserted. Finite substitutions retain
  provenance. Existing actual congruence plus read_compatible proves recovery.
- Owner-frame rebase rewrites all stored journal fields and ordinary consumers,
  then replaces the ordered block. Forward/backward models use one common
  assignment each, not unrelated witnesses for different metadata components.
- run is structural recursion over an explicitly supplied FINITE list of
  blocks. For nonempty runs whose blocks have targets inside the INITIAL
  block's domain, metadata and consumer syntax equal the first rewrite
  literally. The final definition block is still the last supplied block.
- run_models_iff requires initial Formed, SafeOrder for every supplied block,
  target inclusion in the INITIAL domain, and public coordinates outside that
  initial domain. It is pointwise in the same public boundary assignment.
  Initial-domain support closure automatically supplies the protection needed
  at every step. Consecutive block domains need not shrink monotonically:
  shrink then re-expand is permitted inside the initial domain.

## What must not be inferred

This is neither unconditional Acc nor a source scheduler Step. The finite list
is an input, not a generated sequence proved finite by a decreasing measure.
Repeatedly changing definitions can still continue indefinitely; their RHS
sizes and values are not bounded here. Metadata is fixed apart from the stated
substitutions: appending new observations, packets, effects or consumer atoms
is outside metadata_fixed/consumers_fixed. The all-field claim concerns the
actual materialized Journal243 representation, not any future enlarged state.

Formed alone does not guarantee model preservation for an arbitrary rebase:
fresh safety and support/public protection are also needed. The same-initial-
domain sequence theorem derives those protection premises, but does not
produce safe source blocks or certify actual owner allocation. Public privacy
cannot be obtained merely by renaming a promoted source address private.
Targets beyond the initial domain require the separate expansion-support
certificate; the sequence theorem does not silently admit them.

Finally, a reachable source's compilation provenance does not show that every
new materialized owner-frame corresponds to a reachable source state. The
operational correspondence, remaining B4 laws, unconditional EvidenceNode and
old source-regression transfers are still separate obligations. No new source
acceptance restriction is justified by a failed sufficient support check.

## Old-definition extraction: precise additional boundary

JournalExpansion begins from actual Journal.Models AND satisfaction of its
chosen old definition block. That extra conjunct must not be silently dropped.
Formed only supplies provenance and SafeOrder; it asserts neither model
existence nor source eligibility. In particular, stable Definitions241 entries
come from the legacy allocation primitive, so they cannot automatically be
identified with the actual versioned source journal's recorded equations.
ActiveMerge's reserved-slot examples execute propagate primitives, not an
established source-scheduler reachability path.

There is, however, a concrete historical versioned-block route, now connected
by the parent in VersionedPreparedHistory249 and reported strictPASS. The review
read its completed source. Existing
HistoryEquations237.descending gives a strict Nat rank for all actual mixed
ledger entries; typed_reads_subset gives the 247 sort rank premise. Existing
HistoryNormalization238.historical_equations derives every historical entry
equation from actual Journal.Models. Recorded supplies coherence for duplicate
removal and is supplied by actual mixed reachability. Preparation success
itself needs rank, not Recorded; converting prepared-block models to/from the
original ledger uses coherence. The claim that ALL actual old-block extraction is missing is now
withdrawn: it remains missing for an arbitrary chosen stable-owner block, not
for the prepared actual historical versioned ledger. This does not produce new
stable-owner refresh entries or justify retaining version growth as the I47
successor design.


Verified-parent update: source_public_models_iff in
GeneralNominalVersionedPreparedHistory249 starts on the left from actual mixed
reachable Journal.Models, arbitrary consumer All, and public Agrees, with NO
extra old-block conjunct. Actual history preparation supplies that conjunct
inside the proof. Prepare success is still an explicit theorem parameter, but
prepares proves existence for every state using the concrete strict Nat rank.
Recorded/coherence comes from reachability, and LegacyEmpty does too. Fresh
SafeOrder, support protection and public-coordinate privacy remain explicit.
The historical ledger is the actual versioned ledger, not stable241 entries.
