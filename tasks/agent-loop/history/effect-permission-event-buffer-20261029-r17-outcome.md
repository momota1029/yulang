# R17 outcome: event-buffer lifecycle

Status: **CLOSED_COMPLETE_CONDITIONAL** under the unchanged inference/executor soundness goal. This closes only the fixed event-buffer model packet; no source/native or production gate is closed.

## Delivered result

`YulangClosure.FormalPermissionEventBuffer` models the six-slot `Option` array and its separate length. Its 17 new public roots prove occupied-prefix/empty-suffix preservation through bounded pushes, physical indexed writes, exact full-array flattening, and whole-buffer drain/reset. It also proves the selected R16 suffix fits from empty and that selected wrapper composition preserves empty entry only under the explicit no-intervening-mutation equality.

Artifact SHA-256: `1886b763ebd493721cd6cb7d03f32ff3c43555587a53ccf4e0ee3c351c450b57`. Proof handoff SHA-256: `9d214366594818412205ec46741faa223b18b153aebe20ba8db18815deb5faeb`. Source handoff SHA-256: `0324a286e294ce711c6f09fba0371a041032c4d25c7d66f3319d66a89a40ae08`.

Primary Audit 1 passed Lean 4.35.0 over all 73 roots: 56 inherited roots plus 17 R17 roots, with complete printed theorem types and transitive axiom reports. Exit 0, empty stderr, 9.093 seconds, maximum RSS 1,013,120 KiB. The new roots use only `propext` and `Quot.sound`. Raw audit receipts are preserved under `/tmp/yulang-effect-permission-event-buffer-20261029-r17/attempt-1/` and authenticated by the evidence record `tasks/agent-loop/evidence/effect-permission-event-buffer-20261029-r17.json` (SHA-256 `9e8dbe3fdff9fb3356dbc130aa2e0d79d7835c6eb9169b69948acffa31042613`).

Fresh independent compiler-referee review: **PASS**, no findings. The reviewer authenticated all 197 manifest entries, 19 copied project entries, all 73 ordered theorem/type/axiom blocks, source mapping and audit receipts. The read-only reviewer returned its report through its final message; no review file was written or claimed.

The source inspection found four production append sites in `term.rs`; `intern_structure` has two writer branches outside R16's selected protocol. `with_term_events` drains before sampling or mapping and the sampler writes separate counters. The model does not prove an overall six-event limit for structural constructors. R17 also does not authenticate actual execution/Input/Appends correspondence, arbitrary initial-buffer provenance, primitive reserve/snapshot outcomes, page identity, sampler availability/execution, or absence of interleaving on an actual call path.

## Remaining gates

The complete recursive caller, source/native correspondence, original parent, effect hygiene, consumer residual, soundness, principality, termination and production remain **OPEN**. Constructor panic before drain is distinct from normal `Result::Err`; arbitrary prefixes, interleaved writers and the structural event maximum remain outside the proved claim.

No source edits, tests, Cargo, runtime instrumentation or Git staging/commit/push were performed. Existing quarantines and deferred Git disposition remain in force.

## Next bounded action

The sprint-end selector found a concrete source-grounded obstruction candidate: `intern_structure` invokes `intern` and then appends a structural-owner event on success. If the selected R16 path has already produced six events, this seventh push reaches the assertion before `with_term_events` can drain. The tuple path through `candidate_formal_value_pair → positive_tuple → intern_tuple → intern_structure → intern/push` is a source candidate, not yet an authenticated native counterexample.

R18 should trace this path into either a checked conditional seven-event/assertion-failure witness with explicit primitive availability and capacity premises, or a source invariant that excludes the trace. It must not use an arbitrary seven-element list or infer Rust reachability from independent Boolean choices. Preserve successful-reserve assumptions separately from actual allocation evidence. The selector authorized no production change, tests, Cargo or instrumentation. Consultations and packet limits are recorded in the R18 contract.
