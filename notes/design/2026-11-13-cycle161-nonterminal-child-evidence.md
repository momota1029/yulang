# Cycle 161: current nonterminal child evidence

Builds on `GeneralDictionaryNonterminalNonpointExample` and its checked role-1
parent, associated-root request, and old/current private BranchModels.

## General terminal interval fact

`GeneralDictionaryVariableIntervalLeaf.instance_of_interval` constructs a
terminal source Instance for one bare variable query at a located interval.
It assumes the declaration is visible and checked, its sole input name matches
the query, requirements and demanded outputs are empty, role and metadata match,
the source model is valid, and the lower endpoint is a subtype of the upper.
It does not require the endpoints to coincide. The proof computes the actual
inspection report, uses singleton capture propagation (no generated merge
equation), checks both interval self-checks, and discharges the empty schema.

## Concrete full current evidence

`GeneralDictionaryNonterminalChildEvidence` extends the fixture registry with
checked declaration 32, role 0, head `var 8`, no requirements or outputs.
It computes the actual canonical singleton child of parent 31 / clause 51.
After collapse the sole capture is `(7,3,4)` and the child's input is located at
source slots `(3,4)`, whose model values are bottom and int, respectively.
The interval theorem gives the actual child's Instance and Evidence. The
existing parent private branch, completion guards, and this exact child list
then construct the parent's Instance and full source Evidence:
`node 31 [node 32 []]`. The associated-root schema is nonempty.

No old child Evidence is asserted: the old captured bounds refer to privately
allocated identifiers, not necessarily located current source slots. This
example does not supply candidate selection, freshness, installed outputs,
operational reachability, Stable, or a certified revision. In particular a
finite source Evidence derivation alone does not settle full V5.

## Verification

Both new modules compile directly with Lean 4.35.0 `--trust=0`, exit 0, no
warnings. `Audit/Cycle161NonterminalChild.lean` prints all 16 new public theorem
axioms under `--trust=0`: only `propext`, `Classical.choice`, `Quot.sound`.
No sorry, new axiom, native_decide, unsafe, or opaque implementation added.
No full build or executable language CLI validation is claimed.
