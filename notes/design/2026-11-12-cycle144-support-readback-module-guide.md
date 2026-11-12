# Cycle144: actual support snapshot readback

## Design and ownership

Fresh integration `6cff680c`, I25 support-aware boundary; cycle143 source retained.
Do not alter Astra-owned state/Step/Stable/Generated, Audit.lean or README.md.
Use new small modules and a small cycle audit. No runtime/language feature is added.

SupportReadback supplies a missing assembly step: cycle143 required a completed
Classify dictionary. Here finite Classify is constructed by accessibility of the
independent current Local child relation, preserving child list order and repeats.
It then yields a single payload whose Evidence holds for every final model.
Premises are actual Reachable, Stable, local selection at every generated demand,
Joint at those selected demands, and independent where accessibility. Neither
Classify nor Evidence nor a ready-made output is an input. Root Joint also proves
this model class is inhabited. This remains conditional, not general V5 completion.

Parallel investigations: complete the actual recursive example's final Local /
Classify / Stable as far as proved; and derive journal coherence for structural
early-merge schedules rather than assuming cross-class key equality. Both are
explicitly scoped, and will not be counted as general V5 bridges.

## Verified first slice

`lake build Yulang.GeneralDictionarySupportReadback --wfail`: initial two public
theorems passed (668 jobs). Final audit and final expanded build are recorded in
the cycle report. General V5 remains six unconditional fields / eight open.

## EarlyMergeChoices and regression

`UncommittedClass` means no installed packet belongs to an alias class. `Early`
allows merging if at least one side is uncommitted. The actual-transition trace
`Scheduled` adds only this structural restriction at merges; administrative
steps (including certified reobservation) and enabled installs are unchanged.
`scheduled_formed` embeds it in actual SourceFormed, `scheduled_coherent` proves
journal-key consistency, and `recorded_choices` obtains the key half of Joint
for a recorded root. No key equality or Current assumption is supplied.
The first regression is an inhabited nonempty installation/reobservation trace,
showing Coherent does not imply Current. It has no merge and is not offered as
evidence of the unrestricted executor's merge ordering.
