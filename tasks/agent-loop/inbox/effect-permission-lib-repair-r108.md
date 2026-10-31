# R108 exact `lib.rs` repair reconstruction

Status: FROZEN CANDIDATE; source not materialized; compile gate blocked.

## Assignment and parent

- Sprint-ID / contract revision: `effect-permission-rust-lib-repair-and-lean-module-validation-20261101-r108`, revision 1.
- Contract SHA-256: `e7e024562d59624a9b52a3fb71700156027aa582fb09599cf40816d3c8106658`.
- Assignment-ID / handoff revision: `effect-permission-lib-repair-r108` / 1.
- Parent: Simple-sub/effect-hygiene and source/native obligations remain OPEN. This reconstruction closes no theorem, semantic gate, or production gate.
- Baseline: R107 commit `070cc8d2fc8ae519fa9f3eb2d1b872bcb485fba8`; exact `lib.rs` source commit `68770fb2e55aef28f6a2b6793e1150db4ec031cd`, SHA-256 `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`.
- Requested role/model/effort: implementer, Luna / high. Observed model and effort: UNKNOWN (runtime metadata unavailable in this worker view).
- Actual worker: `/root/r108_lib_repair`. Session: `effect-permission-rust-lib-repair-and-lean-module-validation-20261101-r108`. Runtime launch receipt: unavailable in this worker view.
- Sole write lease used: this handoff. Source path `crates/yu-solver/src/lib.rs` stayed read-only. No descendants.

## Exact in-memory reconstruction

Three unique one-line replacements against the pinned baseline:

```diff
--- a/crates/yu-solver/src/lib.rs
+++ b/crates/yu-solver/src/lib.rs
@@ -11763 +11763 @@
-            let entry = match self.store.term_view(argument_effect).map_err(|_| exhausted())? {
+            let entry = match self.store.term_view(argument_effect).map_err(|_| SolveAvailabilityError::IdentityExhausted)? {
@@ -11770 +11770 @@
-                .ok_or_else(exhausted)?
+                .ok_or(SolveAvailabilityError::IdentityExhausted)?
@@ -18372 +18372 @@
-                    candidate_source::SourceRootId::Definition(root) if root == &target_owner.root)
+                    SourceRootId::Definition(root) if root == &target_owner.root)
```

Exact old-pattern counts in the pinned baseline, before each replacement: 1, 1, 1. No additional match was accepted. Reconstructing these three replacements in memory yielded SHA-256 `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`, exactly the R98 target. Line comparison yields exactly three one-line changed hunks and 36,685 unchanged lines out of 36,688; all bytes outside those three replacement spans are preserved. This confirms the candidate hash but is not independent review.

## Direct source/API dependencies

- `SolveAvailabilityError::IdentityExhausted` is an existing variant in the same `lib.rs`; baseline hash above. It is the established availability classification used elsewhere in that file.
- `self.store.term_view` is defined in the same `lib.rs`; its `TermView` and `TermLookupError` API is from `crates/yu-solver/src/term.rs`, R107 SHA-256 `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`.
- `SourceRootId` is already imported at the `lib.rs` crate scope from `yu_hir`; the exact type definition is in `crates/yu-hir/src/module.rs`, R107 SHA-256 `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`. The inaccessible `candidate_source` name was a private import, while the predicate remains identical.
- Feature graph evidence: R107 `crates/yu-solver/src/candidate_source.rs` SHA-256 `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`; root `Cargo.toml` `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`; `Cargo.lock` `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`; `crates/yu-solver/Cargo.toml` `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`.

## Compile boundary

`NO_SAFE_COMPILE_SLICE`. First obstruction: the authorized feature build compiles `candidate_effect.rs`, but its current dirty bytes are untrusted and do not match the R107 baseline (`candidate_effect.rs` R107 SHA-256 `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`; live dirty SHA-256 `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`). The feature-build target also reaches other dirty owner modules. This worker has no lease to materialize an isolated reviewed source state, and the contract makes source materialization and execution Luna-owned. Therefore no compile command was run or proposed as safe. The first obstruction is enough; no build/test was attempted.

## Scope, checks, and stop receipt

- Parent/source/native correspondence: no new source-to-constraints-to-propagation-to-execution behavior was implemented. This is byte-level reconstruction only; all parent, source/native, effect-hygiene, A/B, semantic and production gates remain OPEN.
- Prior evidence reused: R98-v2 diagnostic map and target hash; R107 compiler-referee reconstruction result recorded in the R107 outcome. No earlier R98 test or review is treated as approval of source integration. The untrusted dirty observer candidate was excluded from reconstruction and compile evidence.
- Checks: read-only Git/source inspection, exact baseline SHA verification, three unique replacement counts, in-memory resulting SHA verification, and unchanged-line comparison. No Cargo/build/test, scratch, environment change, source edit, Git mutation, or other write occurred.
- Resource use: within the 300-second assignment cap; exact active seconds unavailable. Cargo calls: 0. Worker writes to the sole handoff are now stopped; no descendant leases or generated outputs.
- Next related step within the fixed sprint: fresh independent compiler-referee review must validate the frozen patch/hash/dependency closure and adjudicate the compile boundary. If it confirms `NO_SAFE_COMPILE_SLICE`, Luna can continue the independent Lean lane; any isolated-source compile would require a Luna-owned reviewed materialization and the exact contract gate.
- Mutual TODO: parent/source owner must supply authenticated source-constructor to generated-constraint to propagated endpoint to consumer/native correspondence, with an explicit falsifier. This handoff does not supply that evidence.
- Commit-ready: no. Source is not materialized; independent review and Luna adjudication remain pending.
