# R233 — Cross-owner search over inference-playground examples

Status: finite source-corpus result; no independent review. R71/R72 and the parent theorem remain OPEN.

## Corpus and candidate admission

The observer reads all 20 checked-in `.yu` examples under `tools/inference-playground/examples/` by exact `include_str!` paths. It parses and lowers each source, runs ordinary `CandidateInference::solve`, and retains complete forest/WorkBound histories for cleanly accepted cases.

Eighteen examples were candidate-accepted with no solver errors or candidate conflicts. `conditional-conflict.yu` and `type-error.yu` each produced the expected candidate conflict and were kept out of the accepted schedule set. No structural recovery or lowering failure occurred.

The 18 accepted cases produced 18 WorkBound events total. Seventeen had no effect-row merge. `nested-recursion.yu` had the only two effect-row merges, ordered `Effect(10) -> Effect(6)` and `Effect(11) -> Effect(9)`. Its single WorkBound was `BoundKey(EffectRow(6), Positive, BottomPositive)` with physical owner `EffectRow(10)`. The copied item is an atom, so the two row merges do not alias its item. The complete ordered prefix search reported no third-owner post-alias WorkBound hit in any accepted example.

The trace checker applies the merge prefix in order before examining each raw WorkBound key. It requires a changed row item representative and an owner outside that representative class. The forest log is complete, and each effect-row parent write has a matching ordered trace event.

## Limits and next evidence

The two rejected diagnostic sources are not accepted executions; their existing CLI tests cover their intended rejection behavior. The 18 positive examples show candidate source acceptance, not general source reachability. A finite miss cannot establish that arbitrary Yulang source lacks the target schedule.

The checked-in corpus contains no accepted effect-row alias followed by a WorkBound on that changed row item. The remaining search should target constructors that can combine effectful handlers with recursive/callback computation rows, while retaining exact source and consumer ownership. R71/R72 and the original theorem remain OPEN; no production/sample code changed.
