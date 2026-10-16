# Receive/choose source example API repair receipt

Sprint: `authentic-source-and-forward-handler-20261017`, contract revision 3, SHA-256 `05907fe8f146f3c86b134b250d0fcb68302bc310e712497161e23e47b8d74252`.

The frozen source-authentication author output was preserved before repair:

- Original example snapshot: `tasks/agent-loop/snapshots/20261017-research-source-registration-pre-repair.rs`, SHA-256 `2a58996b1085ca892dcb9a79465054fad9ac0ddfce4b02eb02c51aa9d464bfe1`.
- Repair: changed only `lower_module_with_local_source(&identity, ...)` to pass the owned `identity`, matching the public owner signature in `crates/yu-hir/src/shadow.rs`.
- Repaired example: `crates/yu-solver/examples/research_source_registration.rs`, SHA-256 `60592afdafd8b545ef0f4410a693bcc5815ce929d2ae64c8b527ec28bdf0643c`.
- Fixture and original author handoff remain unchanged at their rev1 hashes recorded in `tasks/agent-loop/current.json`.

Execution used the single additional primary-authorized attempt, with offline dependencies and an isolated target directory:

```text
timeout 120s env CARGO_TARGET_DIR=/tmp/yulang-research-source-authentication-20261017 cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
```

Exit code: `2` (the process completed in about two seconds; below the 120-second cap). The first attempt, recorded in current state, stopped at compile E0308 because `ModuleIdentity` was borrowed instead of passed by value. The one-line repair fixed that compile error. This second and final authorized attempt compiled and launched the example. It reported `source.bytes=357`, `SourceRevision(0)`, and `parse.structural_recoveries=[]`, then stopped at the explicit `hir-errors` guard. Lowering reported three errors:

- direct root item range `80..130`: `UnsupportedItem`;
- `f0` range `147..162`: `UnsupportedExpression`;
- `receive` range `328..356`: `UnsupportedExpression`.

Candidate solve and export did not run. The actual HIR/source/candidate authentication outcome is therefore **REFUSED AT HIR ERRORS**, not a successful source-to-candidate trace. No third run, fixture edit, test, production change, or source-domain expansion is authorized by this receipt.

Budget: primary repair, snapshot and receipt fit within the rev3 maximum allocation of 180 seconds from reserve. The first Cargo process took about 14 seconds; the second completed in about two seconds. No proof budget transfer. The proof author stopped at stage 3/8 with no writes; post-rev2 incremental reasoning was not instrumented, so Luna reserved its entire remaining 720 seconds pending separate reconciliation.

Claim boundary: these results concern only the newly authored fixture. Historical source identity, phase-root `R_e`, complete choose contracts, original F1/FK1/First-Result obligations, principality, source-Generalize, F5 and production all remain OPEN. The fixture's parser acceptance does not cure its HIR incompatibility or authenticate a candidate root.

No tests were run. One primary Cargo example command was run after the author's frozen output; no compiler source/API behavior was changed. The only code delta is the one-line example API correction recorded above.
