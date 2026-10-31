# R111 baseline-derived compile repair candidate

## Assignment and parent

- Sprint / contract: `effect-permission-baseline-compile-repair-20261101-r111`; contract SHA-256 at author freeze `7d7f58e59c790b5512950bc0f679a15e4e27fd027ae22d2fdb543d13e4a24489`; Luna corrections rev2 and rev3 are identified below.
- Assignment / handoff: `r111_baseline_compile_repair` / revision 1.
- Baseline source commit: `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`.
- Parent: Simple-sub/effect hygiene, original A/B claims, source/native correspondence, semantics, and production remain OPEN. This handoff records a compile-repair candidate only; no source-to-constraints-to-propagation-to-execution contribution was executed or established.
- Requested role/model/effort: implementer, Luna / high. Observed model/effort: UNKNOWN in this worker view.
- Worker: `/root/r111_compile_repair`; runtime launch receipt unavailable here. Assignment bound: 300 seconds; exact active seconds unavailable.
- Sole write lease: this handoff. No descendants.

## Immutable baseline and exact reconstructed candidate

All source bytes below were read with `git show <baseline>:<path>` and changed only in memory. No live dirty source file was inspected. SHA-256 covers complete bytes.

| Path | Baseline SHA-256 | Reconstructed candidate SHA-256 | Candidate bytes |
| --- | --- | --- | ---: |
| `crates/yu-solver/src/lib.rs` | `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df` | `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f` | 1,660,798 |
| `crates/yu-solver/src/candidate_receiver.rs` | `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` | `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf` | 291,827 |
| `crates/yu-solver/src/candidate_effect.rs` | `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41` | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` | 301,873 |

The lib and receiver hashes exactly reproduce the R98 targets independently reconstructed in R107. The effect target is the new baseline plus only the R98 `RowKey` import; it intentionally does not reproduce the R98 observer/test file.

Exact candidate hunks:

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

```diff
--- a/crates/yu-solver/src/candidate_receiver.rs
+++ b/crates/yu-solver/src/candidate_receiver.rs
@@ -4186 +4186 @@
-            || choice_recipe.occurrence != permission.occurrence
+            || choice_recipe.occurrence != *permission.occurrence
@@ -4385 +4385 @@
-            || choice.recipe.occurrence != incidence.permission.occurrence
+            || choice.recipe.occurrence != *incidence.permission.occurrence
@@ -4433,4 +4433 @@
-            let root_is_owned = match &registration.owner {
-                SourceRootId::Definition(root) => local_source.hir.owns_definition_root(root),
-                SourceRootId::Expression(root) => local_source.hir.owns_expression_root(root),
-            };
+            let root_is_owned = local_source.hir.owns_source_root(&registration.owner);
@@ -4628 +4625 @@
-            if expression.occurrence != call.checking.occurrence()
+            if expression.occurrence != *call.checking.occurrence()
```

```diff
--- a/crates/yu-solver/src/candidate_effect.rs
+++ b/crates/yu-solver/src/candidate_effect.rs
@@ -2,0 +3 @@
+use crate::candidate_scheme::RowKey;
```

Each of the seven old patterns matched exactly once. Full-file SHA-256 checks after the in-memory replacements matched all three declared candidate hashes. Receiver reconstruction also exactly matches R98's pinned four-hunk candidate, including the later Member-owner correction; no other bytes change.

## Member-owner behavior and source/API pins

The replacement calls the existing `HirModule::owns_source_root` implementation in the immutable baseline `crates/yu-hir/src/module.rs`, SHA-256 `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`. Its `Definition` and `Expression` arms delegate to the prior ownership predicates. Its `Member` arm requires pointer identity of the HIR artifact, matching module identity, and ownership of both declaration and member source keys by the parsed source. Thus the new arm accepts only a member root belonging to this exact HIR artifact/module and preserves the previous Definition/Expression checks. The receiver code then continues to validate the registered lambda, occurrence, parameter and source-owner correspondence; this change does not bypass those checks.

Relevant manifest and tool inputs from the baseline:

- Root `Cargo.toml`: `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`.
- `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5` (lock format 4; 99 packages, 87 registry packages across the whole workspace).
- `.cargo/config.toml`: `c185a2b859850d94af015a9672c1568e1ef73b12612d820f596ef967b835f637` (alias only).
- `crates/yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`; edition 2024, feature `shadow-apply-candidate` enables `shadow-f5`, direct local dependencies `yu-hir`, `yu-syntax`, `yu-types`, and test dependency `yu-core` with `shadow`.
- Transitive local package manifests: `yu-core` `2be9f92dbb92013436311b696b4020d10bc99a965a82a25181d8957fc5e1b08d`; `yu-hir` `a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1`; `yu-syntax` `567b705fabf7558250dbfa59e833d4ff04cb3041db8ed742311865d8cf3081d3`; `yu-types` `1fae5cab6325fc575ff586f665460592c3c66d9fb03310d060d5d018cb251a9c`; `chasa-recover` `ff7ef8af10850ac4b1de7822f4897ed483810b61e9a118bd1db3d296cb2ec903`.
- `yu-syntax` external manifest requirements include `chasa = 0.5.0`, `reborrow-generic = 0.1.2`, `rowan = 0.15` (lock resolves 0.15.17), and `unicode-ident = 1.0`; `chasa-recover` enables the `derive` feature of `reborrow-generic`.
- No `rust-toolchain` or `rust-toolchain.toml` exists in the baseline tree; the Rust toolchain version is therefore not repository-pinned by these inputs.

The six path-dependency package closure initially counted 322 tracked blobs / 13,847,118 bytes. Independent review found that the immutable root workspace declares twelve members, all of whose manifests Cargo may load before `-p yu-solver` selection. Conservative inclusion of all twelve workspace member directories gives 420 tracked blobs / 14,980,299 bytes. Root `Cargo.toml`, `Cargo.lock`, `.cargo/config.toml`, the three repairs and all source paths must be included and counted separately in the final ≤64 MiB workspace-loading view.

The independent reviewer verified all 87 cached registry archives against Cargo.lock checksums and a conservative selected lock traversal of 25 packages, 727 archive members / 6,707,242 bytes, against existing extracted source files. No `.cargo-checksum.json` files were present, so materialization must use the verified `.crate` archives in a temporary CARGO_HOME inside the capped tmpfs; no persistent cache writes. Cargo.lock package sources and total selected archive bytes must be recorded in the final execution receipt. The repository does not pin a Rust toolchain; record installed cargo/rustc/clang/mold executable identities and versions before launch. These inputs are now part of the fresh review gate. The contract requires stopping if any dependency is unavailable or the capped storage cannot be enforced.

## Prior evidence reused and rejected

- Reused R98's diagnostic map: its first feature compilation found the missing `RowKey` import, three owned/reference occurrence comparisons, two unavailable `exhausted` references and a private `SourceRootId` path. R98's later final invocation still failed on the missing `SourceRootId::Member` arm. These are historical failure receipts, not evidence that this candidate compiles.
- Reused R107's exact reconstruction and classification: lib and receiver byte targets were reproduced from the immutable baseline, and the complete live effect observer file was classified as uncertain.
- Reused R108's independent reconstruction result for the exact three-line `lib.rs` repair and its source-isolation blocker. R108 did not compile this source combination.
- Reused R109's authenticated effect baseline blob and R110's negative snapshot-recovery result. No pre-R106 dirty snapshot was reconstructed or guessed. This candidate starts from the committed baseline and contains only the import repair.
- R99 reviewed the ownership expression positively but rejected its larger five-file test candidate for separate protected-test failures. That rejection is not passed test or compile evidence for this three-file candidate.
- No withdrawn Simple-sub bypass, semantic change, test expectation/diagnostic/source-domain edit, or production claim is included.

## Checks, boundaries, and next step

Checks performed: immutable Git-blob reads; SHA-256 of three base and three reconstructed complete files; unique match counts for all seven replacements; full diff rendering; immutable `module.rs` ownership-branch inspection; transitive local path-dependency traversal from package manifests; and aggregate tracked-blob byte count for the six local packages. No live dirty source path was read. No Cargo, compiler, build, test, source materialization, scratch/cache/environment setup, worktree/copy, Git mutation, or staging occurred.

No source-to-generated-constraint-to-propagation-to-consumer/native behavior was run or proved. This candidate only addresses name/type/ownership compile blockers; actual compilation and the parent source/native correspondence remain open. Tests and original claims/quantifiers are unchanged.

Fresh independent review must verify corrected rev3 contract and workspace closure, the cache-checksum report above, actual cache paths/archives and installed executable pins. The private hard-capped tmpfs remains unproven. No compiler call is authorized before that PASS and Luna's storage/cessation gate. If registry sources or toolchain cannot be verified inside the contract, stop without materialization or compilation. Do not broaden this lease or use the dirty live files.

Changed path: this sole handoff. Known disposable scratch/generated outputs: none. Worker writes stopped after freezing revision 1. No source integration or commit-ready claim.


Luna correction, revision 2: the contract initially listed the R98 three-dereference intermediate SHA as the full receiver candidate. The four-repair candidate reconstructed here is the R107 full receiver SHA `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`; the three-repair intermediate is `03553455bb3b0a4cb0f0ad2fb04b1b8dbf8fac00982547323fe8b6439edbb34d`. Candidate hunks and bytes are unchanged.


Luna correction, revision 3: the workspace source closure includes all twelve root-manifest members, not only the six local package dependencies. The six-package 13,847,118-byte figure is retained as a subset; the conservative all-member figure is 14,980,299 bytes. The final view also includes counted root Cargo inputs and only lock-selected, checksum-verified registry archives in temporary CARGO_HOME. No candidate source bytes or patches changed.
