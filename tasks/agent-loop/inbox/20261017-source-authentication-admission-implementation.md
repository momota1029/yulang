# Frozen implementation handoff: source-authentication admission

- Sprint / contract: `source-authentication-admission-20261017`, revision 2, SHA-256 `aad68de68506f3857b11d72404bd424b7ea686a22121a31cb68cdb1207d201c9`.
- Assignment / handoff: `assignment-source-authentication-admission-implementation-20261017`, revision 1.
- Parent: `CHOOSE-SOURCE-2 / RESEARCH-FIXTURE`; exact newly authored 357-byte fixture only. Historical source identity, `R_e`, complete choose semantics, F1/FK1/First-Result, principality, F5, source export, and production remain OPEN.
- Baseline: `cba9d794d1f0498262b3668f9d5cc055c16749e9`; no Git operation.
- Worker: `/root/source_authentication_admission_implementation`; requested `gpt-6-luna` / high; observed model, effort, and session UNKNOWN in this runtime context.
- Direct authority: all 16 rev2 contract pins matched before edit; contract bytes and Luna's pre-edit snapshot also matched their assigned hashes. The proof artifact and handoff are frozen direct dependencies.
- Exact write leases: `crates/yu-solver/examples/research_source_registration.rs` and this handoff. No descendants, scratch, generated outputs, tests, builds, Cargo, compiler runs, or Git.

## Result and correspondence

Removed only the harness's unconditional early stop on nonempty `hir.errors()`. It still prints the complete HIR error vector and retains the fixture-byte comparison, parse recovery check, source/HIR identity and root inventory, declaration-key checks, LocalSource ownership and source-key checks, resolved-operation identity checks, ordinary `CandidateInference::solve(hir.clone())`, conflict checks, and success-gated export of the same `f0` definition root.

The frozen source-to-owner argument predicts declaration `UnsupportedItem` via its exact declaration placeholder identity; `f0`'s `UnsupportedExpression` via its LocalSource preflight then retained Lambda-to-Error ID; and `receive`'s `UnsupportedExpression` stopping at its own LocalSource preflight because of its negative nested concrete effect row. The proof explicitly marks reconstructed numeric HIR error IDs and raw branded identities as not runtime-observed. The harness edit now permits the owning normal solve/preflight path to decide; it does not establish the predicted refusal, a pass, or export success. Luna owns the one contracted post-freeze Cargo run and the exact first-refusal/pass receipt.

Reused the pinned proof/source correspondence, the original receive/choose owner map, and the prior lowering/diagnostic summaries. The r2 receipt withdraws the old “HIR incompatibility” conclusion and reports that solve/export were never reached; no earlier refusal/pass is treated as evidence. Read existing solve/preflight refusal examples only as owner-path context; no test was run or changed.

## Diff, checks, and boundary

- Focused diff against Luna's pre-edit snapshot contains exactly the three-line removal of the `if !hir.errors().is_empty()` refusal.
- Confirmed by source inspection that diagnostic printing, ordinary solve, and success-gated export remain present. No tests, builds, Cargo, or execution were performed; these are prohibited for this assignment.
- Artifact SHA-256: `10ea5f2c6db7c9d093d86780dbeb217d7eca11332e99a4d1ec40f4753f544e7c`.
- Work used 5 of 5 stages; exact active seconds were not instrumented, within the 360-second assignment cap. No extra sprint resources used.
- New paths: exactly the two leased outputs above. Disposable scratch: none. Writes stopped after freezing and hashing.
- Outcome class: implementation, execution pending. This harness correction is not compiler behavior or semantic evidence. Candidate admission/source-native and mathematical parent gates remain separate and open pending Luna's run and independent review.
- Next related in-envelope step: Luna performs the single <=120-second Cargo run on the frozen output, then records solve's exact refusal/pass and any export result. No author writes remain.

Handoff SHA-256 is returned separately to avoid a self-hash cycle.
