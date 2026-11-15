# I34 selected evidence: role defaults and legacy explicit-body guard

## First proposal: delay the legacy evidence target

Keep the actual default semantics and V6/V7 classification unchanged. Delay a
claim of the current Alloc `SelectedEvidenceNode` / V7 `EvidenceNode` until the
source evidence judgment can express role-default provenance. Do not add an
explicit-body premise silently and do not label such a restricted theorem I34.

## Closed refutations (cycle202)

`GeneralDictionaryAllocDefaultCounterexample202.not_selected_evidenceNode`
refutes the exact I34 quantifier/premise order defined in
`GeneralDictionarySelectedInterface202.SelectedEvidenceNode`.
`not_v7_evidenceNode` separately refutes the integrated B4SkeletonV7 field.

The registry has one checked terminal declaration, key37, Int head, no where
clauses and no explicit associated equations. The role declares output0 with
positional default argument0. Root100 has input(source1,source1) and requests
output0 at source1. The source fixes source1 to Int. The initial journal has an
actual model, is reachable and stable, and selects key37 with exactly []
children. Its actual total packet is true in every current model, so the
terminal plan is already Committed without needing an installation. There is
no OutputConflict; initially no aliases, hence no MergedOutputConflict either.
`actual_default` proves the lookup, default body interpretation and total packet
at the concrete model. Thus there is no absent dictionary-child premise.

The failure is confined to the inherited evidence representation:
Alloc.remaining.Evidence → GeneralDictionaryFeedbackEvidence.evidence →
GeneralDictionaryRecursiveEvidence.Instance → RequestReady → RootDefined.
RootDefined requires an explicit associated equation for every root output.
This declaration intentionally uses its legal role default and has none.
`no_instance` rejects all candidate child lists, for every assignment; the
selected-only node premise is instantiated at the concrete model.

## Possible repair, requiring target guidance

Introduce a new source evidence judgment retaining the selected explicit/default
body and interpret both through total expressions, then supply a boundary using
that judgment and prove the intended dictionary-soundness bridge. Preserve the
old partial inspection certificate unchanged. An alternative explicit-only
fragment would be narrower than I34 and must be named/reported as such.

No semantic decision or owner boundary/target change was made in this cycle.
