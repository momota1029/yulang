# NPAIR fixed-c r8 implementation handoff

Sprint: `npair-fixed-c-interpretation-and-native-path-20261018-r8`
Contract SHA-256: `529fe913b9cf2645399a7e8ce135b5535bc26fc7d0336e5dbf27ef582e64f8e9`
Assignment: `NPAIR-FIXED-C-R8-IMPL-20261018`, handoff revision 1
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` (OPEN; closure 0)
Baseline commit: `e2469125777d8a88356ab15522e8506b35107f97`

## Worker and authority

- Role: Luna implementation lane; worker identity `/root/npair_fixed_c_r8_impl`.
- Requested model/effort: Luna/high. Observed model/effort: UNKNOWN.
- Exact source leases: one E0308 dereference in the named lineage test in
  `crates/yu-solver/src/candidate_scheme.rs`; the two synthetic test `Graph`
  initializers in `crates/yu-solver/src/shadow_apply.rs`.
- Exact handoff lease: this file only.
- No descendants. Writes stopped after this frozen handoff. No Cargo, build,
  test, runtime, formatter, or Git mutation was run.

## Pin intake and outcome

At lease start the contract and direct source pins matched:

- Contract: `529fe913b9cf2645399a7e8ce135b5535bc26fc7d0336e5dbf27ef582e64f8e9`
- `candidate_scheme.rs` before edit:
  `17ec98c43ca211a60f4f99c873186788e3d0ee0788fab4cfad95078769281eac`
- `shadow_apply.rs` before edit:
  `6508a3f39a6d3742110ca1f33e927fa26bd3b112c3f378fc345294675b7f69e3`
- Candidate context pin from contract:
  `42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca`

Applied only the three authorized compile-blocker corrections:

1. In `replay_constructor_lineage_observes_rejected_cross_route_authentication`,
   compare `emission.admission` with `*admission_id`, dereferencing the selected
   borrowed `BoundAdmissionId`.
2. Added `capture_rows: Vec::new()` to each of the two synthetic `Graph`
   literals in `shadow_apply.rs`. These deliberately empty graphs now initialize
   the `#[cfg(test)]` row-observation vector consistently with their empty rows.

The relation-wide uniqueness assertion, full identity checks, authentication,
source specimen, expected output, and production code were not edited by this
lease. Existing dirty r7 source changes were present at the pinned intake; the
full Git diff therefore includes those earlier changes. The lease delta is
limited to the three edits above.

## Frozen artifacts and checks

- `crates/yu-solver/src/candidate_scheme.rs` SHA-256 after edit:
  `25ce531aa10d5f2ab85f363248f6d7ff0c062b93c70389e3d25f4a1b67e608bb`
- `crates/yu-solver/src/shadow_apply.rs` SHA-256 after edit:
  `eb0b9dcd8529e067ec8778c7888f3595ad8df466e1be4243b1d2104c853952d7`
- Static scoped inspection confirmed the dereference and exactly two test
  initializer fields at the leased sites. No tests or compiler checks were run,
  as required before freeze.
- This worker's command/work interval was under 240 seconds; precise runtime
  model and active-time receipt are unavailable (UNKNOWN).

## Parent and source/native status

This removes the three compile blockers from the already established path:
source Apply -> candidate graph and generated constraints -> retained Replay
rows / relation-keyed admission and readback observations -> authentication
classification and test consumer. It makes that exact native test compilable in
principle, but execution is not yet observed. The source/native evidence remains
provisional until the independent compiler referee is CLEAN and Luna performs
the single exact r8 command. A successful test would show this specimen's
source/native behavior only; it does not close the original fixed-c theorem.

The original fixed `c`, quantifiers, source domain, R/W/Z cases, and semantics
are unchanged. The proof lane still owns the unresolved source supplier at the
actual complete `A_decl` output, full dependent `rho_u`, and actual residual
consumer. Proof remains OPEN / closure 0; production remains unauthorized.

## Next in-envelope step and stop boundary

Fresh independent `compiler_referee` review of the frozen exact delta is next.
Only if CLEAN, Luna may run once, with the contract's 120-second cap, the exact
command:

```sh
timeout 120s cargo test --offline -p yu-solver --features shadow-apply-candidate candidate_scheme::authentic_demand_capture_tests::replay_constructor_lineage_observes_rejected_cross_route_authentication --lib -- --exact --nocapture
```

The runtime paths belong to Luna and remain absent at this handoff:
`tasks/agent-loop/runtime/20261018-replay-constructor-r8.stdout.log`,
`tasks/agent-loop/runtime/20261018-replay-constructor-r8.stderr.log`, and
`tasks/agent-loop/runtime/20261018-replay-constructor-r8.meta.json`. Stop on a
review finding, pin mismatch, compile/test failure, or runtime cap; no retry or
test expansion is authorized. Luna owns runtime recording, adjudication, state,
and Git integration.
