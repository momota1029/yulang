# R117 outcome — CLOSED_BOUNDED_PASS_RESEARCH_ONLY

Contract: `tasks/agent-loop/sprints/effect-permission-native-decoder-20261102-r117.md` (SHA-256 `8eca5d0db24a42521706016e90175c5073e8f02146396ac0db964f0f7e08215c`). Admission: `tasks/agent-loop/history/effect-permission-native-decoder-20261102-r117-admission.md`.

## Result

A concrete candidate now authenticates the selected native provider member against the retained permission in the same private source/internal projection and carries that evidence into the existing `InventoryCatchRequest` and `internal_root_view_from` consumer. The final revision is accepted only as a **research patch candidate**. It remains unapplied and uncompiled; ordinary inference and suppression behavior were not changed or executed.

Patch `tasks/agent-loop/artifacts/effect-permission-native-decoder-r117.patch`, SHA-256 `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1`. Rust handoff revision 2, SHA-256 `6557b368fb1f092d5c4151cb54d74c7dd61c92153105e8720b17189c1efd128e`. It targets only pinned `candidate_receiver.rs` blob `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` at base `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`. The other dependency pins are recorded in the contract and handoff. All six hunk counts were independently checked against their bodies. The patch has not been applied.

The first independent review rejected revision 1: its hunk counts were malformed, `ptr::eq` compared mismatched reference levels, and it conflated packed permission storage position with formal registration. The author made a sequential revision 2 fixing those findings. Fresh independent review accepted revision 2 with no BLOCKING/major/minor compiler-correctness finding in scope. Review receipts:

- Rejected revision 1: `tasks/agent-loop/inbox/effect-permission-native-decoder-r117-review.md`, SHA-256 `7e5e51c512c0fe13a3ab58c4abfc49f76011dabb3159e498a8bfbd3f2c1196fd`.
- Accepted revision 2: `tasks/agent-loop/inbox/effect-permission-native-decoder-r117-review2.md`, SHA-256 `a47cfe5a54cc2d22b3fcd2834bed3f3c959ba85cfcb28cf38ed095db06488664`.

The final join selects uniquely by `permission.registration`; the packed inventory position remains a separate value and is checked against the same retained record pointer at consumption. The reviewed static counterexample has registration 0 with no nonempty permission and registration 1 stored at slot 0. The provider family is decoded from the exact owner view's `allowed[member]`. Same operation identity, source owner and provider origin checks remain explicit. Projection failure returns through the existing private optional-observation failure path and does not add a solver or suppression rule.

## Proof map and remaining gates

`tasks/agent-loop/inbox/effect-permission-native-decoder-r117-proof.md`, SHA-256 `0d5d17927a9b1cd2c7c72fb8b1ba0f7be44c146f7057cd1730b1b31dfcd32e53`, maps the R116 theorem inputs to source owners and names the missing Rust-to-Lean interpretation. Its candidate field descriptions were provisional at its freeze; the R117 revision 2 Rust handoff and independent review provide the final field/consumer mapping. No Lean theorem, checker result or complete axiom audit was added.

Open: Rust type/borrow checking and application; executable unequal-index and rejection controls; authenticated successful Rust suppression into R39/R45/R54 model inputs; R116 kernel acceptance; R114 admission transport; original source/native correspondence; inference soundness, all-language effect hygiene, principality, termination and production authority. No parent proof or production gate is closed.

## Execution and Git scope

The contract prohibited patch application, Rust source edits, Cargo/compiler/build/test, Lean/Lake/checker, formatter, scratch paths, caches, worktrees and environment/resource experiments. None were run or created. The static patch count check and repository agent-state consistency check are not compiler evidence. Existing dirty source and quarantined paths were not staged or included.

This bounded research result was committed as `c15c2beb3bfc6baa24dda34b439b673c9cfc9b4a` and pushed to `origin/yulang3`. The outbound range contained only the nine listed R117 checkpoint files; dirty Rust/Lean and quarantined paths were excluded. Production integration remains gated on an authorized execution envelope and the open source/proof obligations above.

## Next bounded step

At the R117 boundary, the dispatcher selected R118: construct the R116 permission/provider/endpoint inputs from the reviewed decoder success conditions while keeping registration and packed storage position distinct. The proof lane must name any R39/R45/native premise the Rust candidate still does not supply. No additional Rust slice is currently authorized by that selection; the candidate remains frozen and execution-gated.
