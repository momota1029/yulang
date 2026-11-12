# Cycle148 module guide and general bridge connection

## Direct proof chain

- `GeneralNominalSharedCaptureFacts`: arbitrary finite maps `Fin n -> Nat`, without
  injectivity. `Coherent` requires equivalent actual observations only at equal
  binder names. Projection implies this coherence, and source models plus
  coherence derive projection and cross-bound compatibility. Source models,
  coherence and actual allocation equations give an exact branch residual.
- `GeneralNominalSharedMaterializationFacts`: same-head terminal singleton
  associated output materialization is derived for all finite sharing patterns;
  it is no longer an assumed semantic residual. Source models, coherence and
  allocation equations remain independent inputs.
- `GeneralNominalSharedJournalFacts`: a recorded earlier packet and actual
  support history recover coherence in every final-state model. Projection may
  be recomputed after interval changes and binder renaming when the current
  equal-name relation is contained in the previous one.
- `GeneralNominalMergeCongruence`: arbitrary finite ordered bindings with equal
  names and equivalent endpoint denotations preserve merge equations, including
  zero, one, and arbitrarily many occurrences of each binder. It does not assume
  the equations at the new endpoints.
- `GeneralNominalSharedHistoricalBranch`: combines these results into same-model
  BranchModels for arbitrary finite sharing at a recorded same-head terminal
  declaration. Covers point-to-point histories with changing endpoint IDs, and
  source-ID-preserving histories with arbitrary interval width. Historical
  packet membership, actual support path, current model, matching head source
  and name, allocation seed, query/output shapes and declaration checks remain
  explicit. Neither coherence, merge equations, materialization, BranchModels,
  Joint nor Installable is an additional premise of the final branch theorems.

`GeneralNominalRepeatedMaterializationFacts`, `RepeatedJournalFacts`,
`RepeatedMergeTransport`, and `RepeatedHistoricalBranch` give the corresponding
binary single-repeated-binder proof chain. The later Shared modules extend that
chain to arbitrary finite repeated-name maps; the binary chain remains useful
as an explicit small interface. No existing file or target is replaced.

## Connection to the actual V5 EvidenceNode residual

No new conditional adapter is necessary. Given a current selected judgment,
its `unique.1` supplies the actual Survivor. With checked registry, visible
checked declaration, key match and actual argument lookup, the existing
`GeneralDictionaryRecursiveEvidence.survivor_instance_of_branch` turns the
history-derived BranchModels into Instance at the SAME caller assignment.
`evidence_node_of_branch` then uses All₂ child Evidence in that same model and
context. It does not replace that evidence by graph generation or stability.

The unrestricted residual `GeneralDictionarySameModelComposition.
SameModelBranchAtSelected` quantifies over EVERY relevant reachable stable
selected focus and EVERY caller model. We have not proved every such focus has
one of the structural histories above. This missing coverage is not removed by
quantifying over arbitrary finite arities or arbitrary lengths of covered paths.
General V5 remains 6/14 supplied, 8/14 unresolved. GeneratedChildren also remains
separate: Instance/Evidence adapters do not create historical graph edges.

## Operational diagnostic chain

`GeneralDictionarySupportRevisionStability` proves the cycle147 emission-gap
endpoint nonstable by an actual second reobservation. It reaches a point-closed
modeled state while the syntactic-emission/historical-generation discrepancy
remains. `GeneralDictionarySupportPointRefresh` proves that second endpoint
nonstable too, by a further exact journal-justified refresh. The historical child
then has an actual rejected support frontier. `GeneralDictionarySupportRootRejection`
proves the root rejected, and not selected for any key/children, at each of these
three particular snapshots. No theorem here claims rejection at every future
state or global stability of the last snapshot. The original gap therefore
fails both required premises of a proposed stable-selected V5 counterexample.

`GeneralDictionarySupportConstraintTrace` records only actual generated-focus
support steps. For every caller assignment it gives an exact final-model iff
initial-model plus all emitted installation/merge constraints, and localizes a
first rejecting edge if that assignment is lost. This is distinct from loss of
all models. Event permutation compares two already-existing traces with the
same event multiset; it does not establish arbitrary schedule existence or
unrestricted order independence.
