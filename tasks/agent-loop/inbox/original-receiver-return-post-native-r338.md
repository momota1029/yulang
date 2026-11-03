# R338 post-native ReceiverReturn handoff — revision 1

Sprint: `R338`, contract `tasks/agent-loop/sprints/actual-source-union-r338.md`, baseline `8e7d98d7e`.
Assignment: `R338-IMPLEMENTATION`, post-native ReceiverReturn observation.
Parent/goal: unchanged source Union / result-world relation and its application to `YulangClosure.SourceAppAdmissionR159.app_admission_iff`; this handoff supplies finite native evidence only. Contract does not authorize semantic changes or production behavior changes.

## Runtime and ownership

Author/worker: `/root/r338_impl`; no descendants. Exact leased repository outputs: `tools/inference-playground/src/runtime/machine.rs` and this handoff. Exact scratch directory: `/tmp/yulang-r338-native/`.
Requested model/effort: `gpt-6-luna` / `high` (implementation lane requirement). Observed model/effort: `UNKNOWN` (runtime model metadata was not exposed to this worker). The primary reserved and then released the single heavy Cargo checker slot before these commands.
Assignment budget: 3000 seconds, no renewal. Exact active elapsed was not instrumented; the work remained within the finite assignment window.

## Outcome and parent application

Outcome class: `source-native-evidence`, finite and test-only.

Before: R335 retained the `Frame::ReceiverReturn` tuple immediately before `leave_owner`; R337 showed that this cannot be treated as the successful post-exit world. R335's selected Call, response/Hole, pre-exit receiver tuple and selected-definition result had no actual post-exit active-stack / invocation-table readout.

After: `machine.rs` captures a bounded `#[cfg(test)]` receipt only after the actual `leave_owner(...)?` succeeds. It retains the exact incoming `ReceivedValue`, the Value-normalized outgoing tuple, current owner, complete native active-receiver vector, and complete invocation table (indexed call site, provider site and active bit), immediately before and after the transition. It joins the receipt to the existing R335 run, activation, source Call/provider, outgoing tuple, and selected result in the R323 test exporter. The checks enforce the actual finite transition shape: native active vector loses its top activation; only that invocation's `active` bit flips; every invocation's call/provider and every other active bit remain the same; current owner restores to `previous`; step does not advance inside `leave_owner`.

The R323 artifact emits finite data fields including `selectedReceiverPostExitNativeActiveReceiversBefore/After`, `selectedReceiverPostExitInvocationTableBefore/After`, `selectedReceiverPostExitIncoming`, the normalized return tuple, owners, source sites, activation and steps. The native receiver vector is serialized in its actual outer-to-inner order; R337's `Control.active` is described as the reverse order, so a future proof bridge must perform and justify that conversion.

This does **not** construct `Inputs.execute`, `checkedObservation`, `traceForm`, an original Event/World, semantic provider ownership, lawful whole actions, universal response domains, independent Union arms, EI, or R159 admission. R335/R337 parent premises remain open. The output is not a theorem and does not establish Rust-to-Lean equivalence.

## Source/native correspondence, coverage and falsifier

The instrumentation is in the actual `Frame::ReceiverReturn` path. `incoming` is the received argument before interface normalization; `received` is the existing outgoing value with unchanged value/view/dispatch and `ParameterRole::Value`. The existing R335 receipt is compared against this outgoing tuple. The post snapshot is placed after the fallible owner leave, so a failed/partially mutated leave cannot be exported as successful post-exit evidence.

The focused test covers the actual source Call and same parsed HIR used by the accepted runtime, checks emitted R323 data, then rejects an altered activation, a pre-exit control snapshot supplied as post-exit, a changed post-exit view, and a post-exit record from a second run over the same HIR. It also injects a failed `leave_owner` path after the activation has become inactive; the active stack is partially popped, `return_value` fails, and no post-exit receipt is appended.

Falsifiers: a successful return whose active receiver top is not the returning activation; a registered target invocation absent or inactive pre-exit; any unrelated invocation row/call/provider/active bit changing across `leave_owner`; outgoing value/view/dispatch differing from the R335 return; outgoing interface not Value; owner/step not restored/preserved; second activation/run/Call/provider being accepted; or an erroring leave producing a post-exit receipt. No such failure occurred in the focused test.

## Prior evidence reused / rejected

Reused the R335 revision-2 native observation and review, including the same-run response/Hole and receiver-return to selected-definition tuple join; R335 handoff SHA-256 `b33d1cff2e58c880ede67fd32c75e71858438ea96b4460cbef9cfbefcfa53a3c`. Reused R337's unchanged `SourceIdentityWorld.Control.leave` / `returnOwned` fields, `leave_shape`, and `return_owned_fields`; R337 handoff SHA-256 `c0e99ea3d24778881533fdbab7e99289323a3a16cb9958448eb5b866544b4a4d`, and source SHA-256 `b6d524a13d74184d7b76e77c03be08ad3ed2183f21b958ee0c6d453a4e0be462`. R337 remains a conditional original consumer, not a native-state isomorphism.

Rejected identifying the R335 pre-exit snapshot with the post-exit result, treating a finite test observation as an arbitrary-world interpretation, reversing the active stack without explicit proof, or calling this complete source/native correspondence.

## Changes and checks

Changed only `tools/inference-playground/src/runtime/machine.rs` and this handoff under the repository lease. No Cargo manifest, dependency, expected output, diagnostic, source domain, or production semantics changed. The code hash is `1832020d095134dd69637bb1eb8f9eea70499037124c0654417190d6dba78803`.

Final checks, offline and sequential:

- `cargo check --manifest-path tools/inference-playground/Cargo.toml --lib --offline` — exit 0. It verifies the ordinary non-test library build, including that the added observation state and its initializers are consistently `#[cfg(test)]`.
- `cargo test --manifest-path tools/inference-playground/Cargo.toml --lib --offline r313_accepted_source_callee_returns_after_request_and_observes_value_name` — exit 0; 1 passed, 94 filtered.

Logs: `/tmp/yulang-r338-native/cargo-check.log` SHA-256 `fad2a5808774c64d38c6beca073ef351062a264ad09acb778369192e9c0418e9`; `/tmp/yulang-r338-native/focused-test.log` SHA-256 `083a61ddaf379334ea5ba92a5b52edc5c33416bd3cb12c3281a014151d033074`.

A broader `cargo test --manifest-path tools/inference-playground/Cargo.toml --offline r313_accepted_source_callee_returns_after_request_and_observes_value_name` invocation without `--lib` exited 101 before test execution. It attempted package binaries and reported `HirAvailabilityError: std::error::Error` conversion failures in the unleased `tools/inference-playground/src/bin/inline_authentic_extraction.rs` at lines 191:29, 199:78, 205:45, and 262:44 (`lower(&parsed)?`, `definition_source_key(...)?`, `local_source_for(...)?`, and `lower(&foreign_parse)?`). That source's observed SHA-256 is `1ab6f3ed86d6bfc6d8f73baa40e5e46d5e3d451922af06fc1092a93ca29a39c0`; no write to it occurred. Baseline reproducibility is **NOT VERIFIED**: this worker did not use Git or create a baseline checkout. To verify, an independent reviewer should materialize the frozen `8e7d98d7e` tree in an isolated directory with a separate clean target, confirm the binary source hash/content from that tree, then run the same broad Cargo command. The failure above only establishes the current observed tree's all-binary failure and is not evidence about the frozen baseline. An earlier test compile caught an `assert_eq!` requiring `RuntimeUnavailable: PartialEq`; the test was corrected to `matches!` before the successful focused run. An exact-name `-- --exact` attempt selected zero tests and is not counted as verification.

Cargo used the repository's shared `target/` build cache. No cleanup or Git operation was performed. This generated/cache path is reported for primary-only hygiene; whether its files predated this assignment was not measured. No other scratch path was created beyond the two log files under `/tmp/yulang-r338-native/`.

## Hashes, remaining premises and next step

- R338 contract SHA-256: `b416b1731da2bd1bd9e83d34fcee300237ca06b21a48634ebfec139092458215`.
- Pre-change `machine.rs` SHA-256 recorded before edits: `3727e1f4f32b9bed251a30224bd63b87a575d9ef84b97564f95e5774800a11c5`.
- Final `machine.rs` SHA-256: `1832020d095134dd69637bb1eb8f9eea70499037124c0654417190d6dba78803`.
- `tools/inference-playground/Cargo.toml` SHA-256 (read-only dependency input): `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56`.

Open source/native premises: map every `SourceSite` in the finite native invocation table to the Lean `Site` expected by R337; translate native outer-to-inner activation vectors to the model's reverse list; relate the captured finite transition to the original semantic configuration only under actual supplied laws. R337 additionally leaves original execution interpretation, current-world semantics and universal source domains open.

Provisional boundary: reversible test-only instrumentation; production cutover is not authorized. Cleanup owner: Luna. Next related in-envelope step: formal lane consumes these exact fields to assess whether one actual successful return can instantiate R337's existing `Control.leave`/`returnOwned` projection without claiming arbitrary EI or R159 closure; any missing site/control translation becomes an exact source-owner TODO.

Worker writes stopped after freezing this revision. No proof/native theorem closure, independent review, integration or Git checkpoint is claimed.
