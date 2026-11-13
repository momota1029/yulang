# Cycle 161: certified reachable nonterminal evidence

`GeneralDictionaryNonterminalCertifiedEvidence` adapts the positive full
nonterminal fixture to the existing certified source, whose ordinary atoms
include both `1 ≤ 2` and `2 ≤ 1`. It uses the same extended registry
(parent 31 and terminal variable leaf 32), associated-output root, model, and
current context throughout.

The universal certificate is inherited from `NonpointCertified.raw_models`:
for every source assignment, the ordinary endpoint equality justifies replacing
the outer interval descriptor by its point descriptor. It is not inferred from
one positive model. Both `Certified revision` and `Improves revision` are
proved, and an actual `GeneralNominalValueSteps.Step` yields `SourceFormed` and
`B4TargetV5.Reachable` for the Value boundary.

At the exact reached context `after.current.context`, the canonical child list
is a singleton and its input locates slots `(3,4)`, interpreted as bottom/int.
The checked terminal variable leaf gives child Instance/Evidence. The checked
parent, actual child list, completion guards, and private BranchModels give full
Evidence `node 31 [node 32 []]`. Parent requests include the nonempty
associated-root schema. `reachable_nonterminal_evidence` packages the checked
registry, actual step, reachable/formed result, current model, nonempty
requirement/schema, distinct semantic endpoints, and this full Evidence.

The private materialization component reduces variable-only where requests to
root requests, so it can reuse the existing certified terminal fixture's
private branch component. This is not reuse of terminal Evidence as nonterminal
Evidence: the actual child evidence and parent Instance are constructed here.

## Limits

No old child Evidence is asserted; old private merged endpoints need not be
located source slots. No selected candidate, installed associated output,
Stable or final dictionary correctness theorem is asserted. The reachable
witness uses the existing Value boundary, not a new theorem unifying all V5
boundaries or completing general nonterminal replay.

## Verification

Direct Lean 4.35.0 `--trust=0` compile succeeds without warnings.
`Audit/Cycle161NonterminalCertified.lean` audits all 23 public theorems under
`--trust=0`, exit 0, only `propext`, `Classical.choice`, `Quot.sound`.
No full build or executable language CLI result is claimed.
