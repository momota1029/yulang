# Sprint R246 — production error propagation and retained-reference lifetime

Status: ADMITTED under the unchanged goal of Yulang inference soundness and its Rust implementation. R245's reviewed local native equation and conditional return trace are preserved as source evidence only; the original parent theorem, all source forms, arbitrary independent assignment and semantics remain unchanged. Parent delta is zero unless a justified source/native result is applied at its parent edge.

## Fixed question and outcome

R245 leaves `R245-RETAINED-REF-1` open: do captured row/term/view/relation/replay/context references that survive a rollback remain valid along production-reachable histories that later continue to an ordinary-extrusion call?

First trace every production route transaction from its actual entry to the consuming caller and then through `execute`, `run`, or `run_candidate`. Classify each availability-error route as either:

1. the failed private attempt returns out of the same session and no later extrusion call can reuse its rolled-back references; or
2. a non-test consumer absorbs the error and the same session can reach another real extrusion call, in which case derive the retained-owner/journal survivor equation over that exact path and apply it to the R245 entry-W premises.

Do not infer (1) from `Err` alone. Enumerate actual production call sites and caller propagation/catch behavior, including candidate local routing, retained resume and source schedule consumers. Keep test-only pause/failure injection separate. Successful lookup alone does not prove owner identity. Identify any non-test error absorption followed by a same-session actual extrusion call as a falsifier of (1).

The proof/source result must state which R245 retained-reference obligations are discharged, excluded only because the failed attempt cannot continue, or still open on an actual continuation. R71 raw-slot/fiber coverage and later queue acknowledgement/settlement remain independent. No Rust edit is authorized; absent a reachable production defect, implementation lane stays NO_SAFE_CODE_SLICE.

## Sol assignment, exact leases and inputs

One registered `prover`, Sol/high, no descendants. Exact write leases:

- `notes/theory/2026-11-02-production-error-lifetime-r246.md`
- `tasks/agent-loop/inbox/production-error-lifetime-r246.md`

Active time maximum 1,800 seconds. No Lean, build, test, probe, Cargo, scratch/cache output, runtime/quarantined path, production edit or Git. Freeze the source account and handoff with all call-site/caller cases, exact success/error transitions, constructor/consumer owner links, dependency and artifact hashes, residual R245 lifetime premises, and STOPPED-writing receipt. Fresh independent `compiler_referee` review is capped at 300 seconds.

Baseline HEAD: `64dcbc150aec64f7a17abb08171f4cea48c84ce8`.

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `crates/yu-solver/src/candidate_scheme.rs` | `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e` |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `crates/yu-solver/src/candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r3.md` | `104720837d86a40efafe1676bf23d756042ce78355d0bfc84c69918aa7676956` |
| `notes/theory/2026-11-02-ordinary-extrusion-native-entry-and-return-r245.md` | `7ef7ca1bb40fbe18370691b064edc3b24d9818076dbb63738fdb3d6b6f72101e` |
| `tasks/agent-loop/inbox/ordinary-extrusion-native-entry-and-return-r245.md` | `647860bfec8b9b7b7b1809ace66c24181e1c9ad8c7b3f7616c7100acdb439322` |

If a pinned dependency differs, stop before citing it and report the exact mismatch. Do not widen source domain, lease or semantics without returning to Luna.
