# R145 outcome — FreshUse shared-map support

- Sprint: `EFFECT-PERMISSION-FRESH-MAP-SUPPORT/20261102-R145`
- Baseline: `f634b2f426b6aef3e2dd602dab0a6dce3e1ad0dd` (HEAD and upstream at admission)
- Outcome: **CLOSED_REVIEWED_CONDITIONAL_UNCHECKED**. The fresh independent reviewer accepts this as a conditional research checkpoint. Source application, source/native refinement, original H/A/B, whole-language soundness and production remain OPEN.
- No Rust production code changed. No Rust, Cargo, test, build, Lean or Lake invocation ran. No environment, worktree, scratch or cache was created.

## Frozen artifacts

| Artifact | SHA-256 | Evidence class |
| --- | --- | --- |
| Sprint contract | `283bf739e6eab63c2ab2a538137bc8114e3e1613d7565a353925d63eb63beb32` | Fixed scope and limits |
| Admission | `36880c318413883251f8baa1ccc8968818cec73a9e3406a40e8739586b7aabd5` | Dispatch, assignments, review amendment |
| Rust source handoff | `e543b1cd4c6d98d6fdaf912f228a8cd53e407fe72edf3338b2f1c9fca295ffba` | Immutable-source trace |
| Lean proof handoff | `da15341b46d3b7adef8cb1bd90d02bfe6dd27fc594a5fb96520f5cf84f82dcea` | Conditional proof map; unchecked |
| Lean candidate | `d47da744694beb04abfcf3b06137b5a04b241f568490af5fbf59147933a2db57` | Seven unchecked theorem candidates |
| First review deviation | `3c35bd548637eb5c8792c5da0b6607540aeb029ca28acdc011645c6b09ab9adf` | NO_VERDICT; excluded from acceptance |
| Fresh independent review R2 | `d8607ef81d8a6cecd331171a8886a71d50fa9800298e1d018d98daae5f46e06e` | ACCEPT conditional checkpoint; kernel unchecked |

## Rust source result

The committed `prepare_candidate_fresh_use` path makes one scope/input `ScopeRemap` before reconstructing the FreshUse. It reuses that same map for each distinct incoming transformer and the demand's output scope/input; the demand root uses the term map. Repeated bounds for one parent reuse the retained mapped flow. Later replay composes existing transformers without allocating another scope map; later FreshUse calls allocate from later inventory lengths. Baseline-qualified search found two production callers.

`ScopeInventory::fresh` appends new scope/input IDs from the inventory lengths at the successful allocation cut. `ScopeTransformer::remap` only checks collisions on transformer-local support, while identity fallback leaves coordinates outside this FreshUse's copied domain unchanged. The source trace does not authenticate the complete transformer, demand and incoming-state support below the same pre-copy counts, nor does it show a general incoming `NativeScopeTransformer.State` being renamed by that same map.

Therefore the first open owner is the allocator/support and incoming-state source/native bridge. No reachable source collision or concrete production defect was established. The equality of `scope_origins` is not used as an injectivity premise. Fallible preparation can advance private inventory/use identities before an error; this packet does not certify retry or full rollback behavior.

## Proof and review

The Lean candidate states finite-support versions for the transformer and the incoming state, then specializes injection to fresh allocation with explicit pre-copy bounds. The proof lane identifies seven candidate theorem statements, including repeated copy keys. They are **UNCHECKED**: no Lean/Lake run, inferred theorem types or axiom audit exists. The candidate does not assume the Rust support premises, and the source handoff does not establish them.

The independent reviewer notes that copied-key uniqueness is unnecessary for the allocation lemma's injectivity on old identifiers; repeated-key overwrite is already covered by the native fresh-allocation law. Ownership/iteration correspondence remains a separate source concern where needed.

The first reviewer used `rg` on dirty working-tree `candidate_scheme.rs` before reading the contract. That reviewer stopped and froze the NO_VERDICT deviation receipt; its search output and conclusions are excluded entirely. A fresh reviewer read the amended contract first, matched all six frozen input hashes before source inspection, and used baseline-qualified committed Git objects only. Its verdict accepts the checkpoint as an honest conditional research artifact. It identifies two blocking premises for source application: authenticated same-map incoming-state correspondence and joint pre-copy support bounds. It also notes that copied-key uniqueness is not needed by the local injectivity lemma, though ownership/iteration correspondence may remain a distinct source obligation.

The reviewer returned its complete receipt in the final runtime message because its role is read-only. After the reviewer stopped, the primary transcribed that text into the leased review record without changing its verdict or findings.

At review time, the admission hash was `d4995672266e83f15adac2cb396a11d2b2987ee7d78425ea983627a9f6978d7e`, as recorded in the reviewer receipt. After review completed, the primary added only the receipt-serialization note; the final admission file hash is `36880c318413883251f8baa1ccc8968818cec73a9e3406a40e8739586b7aabd5`.

## Gates and checkpoint

No source repair is justified by this result. Do not promote the conditional theorem to a FreshUse source theorem. Keep the authentic incoming-state consumer, complete support bound, source/native correspondence, original Simple-sub A/B and production gates OPEN.

The dispatcher approved closing and pushing this exact reviewed checkpoint. Its next proposed packet is R146: identify the real incoming-state consumer and prove or refute the allocator/support invariant across source producers, composition/replay, earlier copies and failures. No Rust fix is authorized until a reachable production defect is found.

The exact coherent checkpoint is this outcome, contract/admission, source/proof handoffs, unchecked Lean candidate, both review records, and compact current-state disposition. Only these explicit R145 paths may be staged; all unrelated dirty/quarantined paths remain untouched. Normal fast-forward push only.
