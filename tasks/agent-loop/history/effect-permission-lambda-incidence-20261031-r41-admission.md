# R41 admission receipt

Primary admission for `EFFECT-PERMISSION-LAMBDA-INCIDENCE/20261031-R41`,
contract revision 1.

- Contract: `tasks/agent-loop/sprints/effect-permission-lambda-incidence-20261031-r41.md`; SHA-256 `20b446aa3ad63eeccbda603e4b054ccd76e87e492c8f64d7a5cab6aacd112ed8`.
- Baseline and `origin/yulang3`: `41a446c9e37d1cb9a4f88f7d8832f831d76cfd40`.
- R40 report and independent PASS are consumed exactly as pinned by the contract; no R40 source absence claim is widened.
- Live roster synchronized immediately before admission with `collaboration.list_agents`: `/root` running; all previously dispatched children terminal/completed. No capacity override, path-lease release, or UNKNOWN/quarantine change was applied.
- Exact source writes: `/root/r41_rust` owns only `lib.rs`, `candidate_context.rs`, and `candidate_scheme.rs` within contract slices plus the Rust handoff. Exact proof writes: `/root/r41_proof` owns only the R41 Lean module and proof handoff. The Rust and Lean writers do not share paths. A fresh reviewer lease is added only after both outputs freeze.
- Requested routes: Luna/high `implementer` and registered `lean_prover`; observed model/effort remain UNKNOWN until actual runtime evidence exists.
- Reservation: 4,800 seconds total, Rust 1,400; Lean 1,400; independent review 1,000; primary 1,000 including at most 500 for integration. No Astra, carryover, builds, tests, environments, worktrees, or caches.
- Pre-admission compaction receipt: `tasks/agent-loop/history/effect-permission-source-inventory-20261031-r37-compact.md`, SHA-256 `c1e8a86491793cd9634343484be2e55f67795850636854f04f87c1ca3c0a5f97`. Only resolved R37 frozen artifact rows and the reviewed/stopped R40 reader/report rows were archived. The R37 source lease, every UNKNOWN row and its quarantined/held paths, all 32 pending items, and unrelated frozen leases remain.
- No source or proof result is yet claimed. Git integration remains primary-only and the pinned dirty `candidate_scheme.rs` baseline must be isolated from any outbound delta.
