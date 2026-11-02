# Sprint R250 — ordinary typed-drain progress

Status: ADMITTED under the unchanged goal: Yulang inference soundness and its Rust implementation. Preserve the original parent theorem, Simple-sub A/B claims, all source forms, arbitrary independent satisfying assignment and semantic choices. Parent delta is zero until a justified result is applied at its original edge.

## Fixed outcome

R249's reviewed successful-history storage result preserves prior operation/child identity, restoration cursors and Running/Ready barriers. `R70-DRAIN-1` remains open: it is not yet shown that actual typed-drain work advances through termination, diagnosis, acknowledgement and ReturnReady without losing or regenerating work indefinitely.

Trace the current production path through Transport → Context → Dispatch → settlement → Diagnostics → Acknowledgements → ReturnReady. Derive a well-founded progress measure and apply it to the R70 drain obligation, or freeze the first precise producer/consumer equation and accepted route that prevents such a measure. Count work added by genuine representative merges/generation changes, root reopening, bound replay and diagnostic processing. A decreasing local cursor alone is insufficient if later phases add work; resource exhaustion is not normal completion. Do not restate R143's conditional "finite successful return implies completed work" result as global progress.

Method: construct the producer/consumer dependency graph and test a size-change, lexicographic, or multiset-founded measure over actual current states. Charge every created/consumed item to a finite source structure, a strict representative merge, or a finite unprocessed evidence set, with exact owners and transitions. Falsifier: an accepted non-test route permits uncharged regeneration, nonterminating revisits, diagnostic-created unprocessed work after the supposed terminal point, or a lost acknowledgement. Hand-built cycles and test-only paths are not falsifiers.

Keep R71 raw-slot/fiber, evidence authenticity/origin/fiber, F1/FK1, foreign continuation and full source/evaluator soundness separate. No code repair is authorized absent a concrete reachable production defect. Implementation lane remains NO_SAFE_CODE_SLICE.

## Assignment, exact leases, pins and limits

One registered `prover`, Sol/high, no descendants. Exact write leases:

- `notes/theory/2026-11-02-ordinary-drain-progress-r250.md`
- `tasks/agent-loop/inbox/ordinary-drain-progress-r250.md`

Maximum 2,400 active seconds. Fresh independent `compiler_referee` review after freeze, maximum 300 seconds. No production edits, Lean, builds, tests, probes, Cargo, scratch/cache outputs, runtime/quarantined paths or Git. A new required owner must be returned to Luna with exact path/hash before its body is read or cited.

Baseline HEAD: `f8124eba4827e89c596016bdc28019011cd1887d`.

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `crates/yu-solver/src/candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md` | `648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7` |
| `tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md` | `4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf` |
| `tasks/agent-loop/inbox/20261019-r70-proof.md` | `25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db` |
| `tasks/agent-loop/inbox/20261019-r70-closeout.md` | `ff2c149bd71c783f874c150404bf199084858df631c21899d3abf53a258655bb` |
| `notes/progress/2026-10-19-r70-closeout.md` | `a93b2e5d38c03511c768dd704e57f3b616a1dafc591fe62a4155d64a06bbf4d8` |
| `notes/theory/2026-11-02-prior-replay-owner-lifetime-r249.md` | `615121840e60fe86b493a3e9b9236783770cc8bbd002cea6c4e41b29d60e90e9` |
| `tasks/agent-loop/inbox/prior-replay-owner-lifetime-r249.md` | `381d7d65f8de903611e9896fc56498a4ce005b551c08d073b63e9c891657a246` |
| `crates/yu-solver/src/candidate_scope.rs` | `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03` |

Verify every hash before citing. Record actual producer/consumer transitions, measure or exact obstruction, residual R71/ack/evidence obligations, outputs/dependencies, resource receipt and STOPPED-writing status. Do not claim parent-theorem closure from a local drain result.
