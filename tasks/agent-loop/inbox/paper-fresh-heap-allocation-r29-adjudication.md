# R29 primary adjudication — bounded finite heap payload allocation

Sprint: `FULL-PAPER-TYPE-SUBSTITUTION-20261026/r29`, contract r1.

## Decision

**ACCEPTED as a bounded intermediate proof only.** This does not close the paper's recursive allocation/graph-extension theorem, any original A/B obligation, source/native correspondence, inference/executor preservation or production authority. Guardedness remains OPEN.

## Frozen evidence

- Contract `tasks/agent-loop/sprints/paper-fresh-heap-allocation-r29-r1.md`: SHA-256 `1859d9a005b9bfbff2fd98de5bf7e2d984b48f890cd42ca37b5909f5439d8c70`.
- Candidate `notes/theory/lean/YulangClosure/PaperFreshHeapAllocation.lean`: SHA-256 `7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925`.
- Worker handoff `tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29.md`: SHA-256 `ea88664ab5f3a70864a713a47e19036df8b097fa7adc77775a2978f8a8f02846`.
- Worker checks `tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-worker-checks.txt`: SHA-256 `ec4283642d9431019043a0024eab0372babb2ed4b4f89b4558968946c364284c`.
- Primary verification `tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-primary-verification.txt`: SHA-256 `1301b818fd5d3f68c3162ab468112ad50b7a0af1436e2bb582827083a51d2899`.
- Independent review `tasks/agent-loop/inbox/paper-fresh-heap-allocation-r29-review.md`: SHA-256 `2611315d23588db8b02f8644bc9d8c495e388566659037e59f3b3501b49e25b1`.
- Lean pin: Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; primary's two pinned version preflight calls passed before worker launch. Worker and primary used the isolated checkout `/tmp/yulang-r29-fresh-heap`.
- Worker cache: 72 files; canonical manifest SHA-256 `4d5f44291a2bf8f60c6c3eccf08c5b2d1da6e846e8c4d42f69962cb60f2ed10b`, matched at primary handoff.

## Primary checker and axiom evidence

After the worker STOP receipt, primary used exactly its two remaining checker calls:

1. `lake build +YulangClosure.PaperFreshHeapAllocation` — exit 0, 0.145146 seconds.
2. `lake env lean -j1 -M1024 .lake/R29Audit.lean` — exit 0, 4.299852 seconds.

The audit prints complete `#check @...` types and `#print axioms` for every public declaration in the module: 10 definitions/abbreviations and 21 theorems. All 62 ordered audit markers are present. Seven declarations use no axioms, two use only `propext`, and 22 use `propext, Quot.sound`. None uses `Classical.choice`, `sorryAx`, a project axiom or another unsupported axiom. The nine-module imported source cone scan found no `sorry`, `admit`, `axiom`, `debug.skipKernelTC` or `native_decide` matches.

The worker's three failed checker invocations triggered its mandatory STOP. Its successful focused build (#3) and all failures remain in the original log. Primary's independent focused build and full declaration audit both passed, so the worker's earlier audit-path error is preserved as a worker failure and does not describe the final primary audit result.

## Reviewed theorem boundary

The accepted statement is over an explicit finite input block `List (Nat × Ty × Value)` in de Bruijn order and a new auxiliary finite `HeapPayloadTyped` relation. From unique/disjoint IDs, typed original RHSs, one shared typed substitution and old payload typing, `finite_allocation` proves graph lookup preservation and exact new lookups, success of the actual same whole-list Option substitution, exact node length and new-prefix/old-suffix heap layout, new and old lookup behavior, and payload typing of every updated node. It applies R27 weakening to old payloads and R28 substitution to each block RHS.

The concrete duplicate/collision/zip/order/sequential-substitution discriminators are checked. A self-alias block has payload typing and an actual self-edge lookup, which correctly shows the auxiliary relation omits guardedness. The new theorem does not establish real source formal order, a source `rec` correspondence, the manuscript heap judgment, graph guardedness, native allocation or full preservation. These are the next premises, not assumed conclusions.

Fresh independent M1 review: **CLEAN**, no blocking, major or minor finding. Reviewer used source and the supplied complete primary receipt only; zero checker/cache/Git calls. The review report was persisted by primary because the review role is read-only.

## Cessation and integration

R29 proof worker STOPPED after four calls (27.421 checker seconds, three failures); no checker processes or descendants remained and writes stopped. Independent reviewer STOPPED after source-only review; no file writes. Primary checker budget is fully spent for R29. Candidate and evidence paths are frozen for this adjudication. No Rust files, tests, runtime probes, source expectations or semantic behavior changed. No check beyond the contract's focused Lean build/audit and required static state validation was run.

Next source-side premises remain the real-program block/formal-order correspondence and the graph-guard preservation theorem after allocation. The full manuscript source domain and all stated parent obligations remain OPEN.
