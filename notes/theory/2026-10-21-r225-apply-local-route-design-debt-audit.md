# R225 — Apply/LocalFreshRoute design-debt audit

Status: audit closed; implementation packet required before attempting another provider/formal reconstruction.
Baseline: `031ad45f6` on `research/simple-sub-intrusion`.
Parent computation-forwarding theorem, R71 and R72 remain OPEN.

## Result

Classification: **D — reconstruction debt at the source-origin owner boundary**.

The exact source Apply for `repeat loop q` does carry the actual callback argument into the expected function type. The missing edge is downstream attribution from that expected callback function to the formal registration for `f` used by `f z`. The evidence does not indicate a semantic or ordinary-inference failure, and it does not justify adding a theorem premise.

## Owner-qualified evidence

The focused test is `r225_local_apply_relation_map_ownership` in `crates/yu-solver/src/candidate_scheme.rs`. It runs the exact R221 source through ordinary candidate mode, without scoped experiment.

- Provider Apply occurrence 26 is source-origin relation 357. Replay relation 358 joins its callee function (relation 234, positive function Term 381) to the Apply demand (negative function Term 456).
- Relation 358's swapped Argument port is relation 362. Its replay child 363 compares the actual LocalFreshRoute function Term 413 with expected callback function Term 377. The provider callee's argument port is Term 377.
- This comparison decomposes into an owner-qualified result-effect edge: relation 368, `EffectRow(69) <= EffectRow(54)`, under the argument comparison. It preserves the actual `loop` route's slot-4 result-effect image through the provider Apply context.
- Callback-body Apply occurrence 19 is source-origin relation 146, with pair `ValueRow(31) <= NegativeFunction(Term 340)`. Its source-origin lineage records the occurrence, but has no formal registration (`formal_present=false` in the context lineage). No FunctionPort dependency is owned by relation 146.
- In ordinary candidate mode, both LocalFreshRoute copies have an empty `retained.scoped_relations` map. Their context remaps and route terms exist, but they do not retain a relation-to-formal-use bridge. The provider expected function Term 377 is distinct from both the repeat callback route term Term 386 and callback consumer demand Term 340.

These owner-qualified relation and route facts establish the Apply-to-expected-function comparison. They do not establish expected-function-to-formal-use attribution. Term inequality alone is not the conclusion; it is corroborated by the absent formal metadata and absent consumer-owned relation edge.

## First missing owner fact

The first missing fact is the callback formal registration identity on the source-origin/relation record for the callback-body use. The source collection layer has this fact: the exact callback SourceCall for `f z` exposes a formal registration, as checked in the R222 source observation. The provider SourceCall `repeat loop` correctly has no formal registration because `repeat` is an ordinary local function. When the callback Apply enters candidate context as relation 146, only occurrence/local-slot provenance remains; the formal registration identity is not retained for later LocalFreshRoute reconstruction.

This places the debt at the existing source-origin/candidate-call to candidate-context provenance seam. It does not show that a new inference relation is needed. The next implementation packet should first test whether preserving the existing formal registration identity through this seam is sufficient to construct an owner-qualified use-to-route bridge, then prove that bridge against the original obligation before changing production behavior.

## Classification falsifier

This D classification is falsified if the existing relation/use owners already retain a formal registration identity for relation 146, or if an existing canonical LocalFreshUseMap/context path joins Term 377 to the callback formal route and WorkBound demand without relying on equal IDs, generic leaves, or solver acceptance. In that case, the audit should be revised to identify the specific existing path and its missed reconstruction step. The R225 probe found neither path.

## Scope and status

No production relation, public API, language rule, or theorem premise changed. This audit does not close the parent theorem, R71, or R72. It authorizes a bounded implementation packet to preserve existing source ownership metadata and retry the correspondence with an independent proof/review gate.
