# Sprint R244 — ordinary extrusion entry construction

Status: ADMITTED for one bounded Sol-owned constructor-preservation proof
attempt. The full objective remains Yulang inference soundness and its Rust
implementation. The unchanged original inference theorem and Simple-sub A/B
domain remain in force; this packet targets only the open implementation edge
`R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`.

## Fixed outcome and exact parent edge

R70's reviewed conditional result establishes entry-to-return behavior of the
two production `candidate_extrude` calls **assuming** entry invariant `W`.
R70-ENTRY-WF-1 remains open: derive every applicable conjunct of `W` from
actual production-reachable constructor/transport/merge histories before those
calls, or identify the first exact constructor that cannot preserve it.

Begin at ordinary solver initialization and follow the relevant row/term/view,
FreshUse, source-bound, merge, rollback, transport and typed-drain constructors
in their actual creation order. Prove preservation of W by induction over
reachable histories, not from a hand-built state or a test setup. Apply every
derived W conjunct to both production call sites and then to the frozen R70
entry-to-return implication. Classify each W conjunct as constructor-derived,
conditional on a named prior invariant, or still open with exact owner.

Keep separate: (a) R71 raw-slot/canonical-fiber coverage after merges, (b)
R70-DRAIN-1 later queue acknowledgement/settlement, (c) source/evaluator
soundness, and (d) the unchanged parent theorem. Do not claim any of those from
W or local extrusion return. Parent delta is zero until a checked source/native
result is actually justified at its original parent edge.

Required falsifier: an accepted production-reachable constructor prefix
creates an out-of-range/wrong-kind row, invalid Function term/view/member/
incidence/evidence reference, bad polarity, or stale owner/head at an actual
call. Hand-built states and test-only call paths are not falsifiers.

## Sol assignment and exact read dependencies

Registered `prover`, requested Sol/high, no descendants. The exact outputs are:

- `notes/theory/2026-11-02-ordinary-extrusion-entry-construction-r244.md`
- `tasks/agent-loop/inbox/ordinary-extrusion-entry-construction-r244.md`

The assignment is read-only over these frozen dependencies:

| Path | SHA-256 |
|---|---|
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/theory/2026-10-19-r70-ordinary-extrusion-invariant.md` | `648b594fdf1cd989e7399db00f396c65ec82cc1b4d3585bcb68ce21b316021e7` |
| `tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md` | `4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf` |
| `tasks/agent-loop/inbox/20261019-r70-proof.md` | `25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db` |
| `tasks/agent-loop/inbox/20261019-r70-closeout.md` | `ff2c149bd71c783f874c150404bf199084858df631c21899d3abf53a258655bb` |
| `notes/progress/2026-10-19-r70-closeout.md` | `a93b2e5d38c03511c768dd704e57f3b616a1dafc591fe62a4155d64a06bbf4d8` |
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_scope.rs` | `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03` |
| `crates/yu-solver/src/candidate_value_graph.rs` | `aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf` |
| `crates/yu-solver/src/candidate_receiver.rs` | `5ca308e7b890e57a8458a151554ece55585d762565204d39c520c4b534e44ade` |

If any dependency hash differs at assignment start, stop before citing that
file and return the mismatch to Luna. No production writes, tests, builds,
probes, Cargo, runtime/quarantined paths, scratch/cache files, Git, or external
contact are authorized. The implementation lane remains NO_SAFE_CODE_SLICE
unless this proof produces an exact source-level falsifier that supports a
separately admitted repair.

## Review and resources

Maximum 1,800 active seconds for Sol; zero Astra, zero descendants, zero builds
or tests. Freeze a single constructor-by-constructor note and a single handoff
with source/hash receipts, every W conjunct, the actual two call-site
applications, R71/R70-DRAIN-1 exclusions, exact remaining premise, and
STOPPED-writing receipt. A fresh `compiler_referee` reviews the frozen source
argument within 300 seconds. Luna owns intake, adjudication and any later
verification/Git. No prior R70 time is reset or carried into this grant.

Stop when W is derived at both calls, a production-reachable exact
counterexample is established, the first precise W owner remains unprovable,
the budget ends, or user STOP arrives. Record unobserved model/runtime as
UNKNOWN. Do not widen sources, semantics, leases or claims without returning
to Luna.
