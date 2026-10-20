# R149 primary source checkpoint, revision 2

Status: provisional source-owner evidence; independent delta review pending.
This is a new immutable revision correcting rev1's host-resolution and
nullfix-owner boundaries. It does not establish either exact sample's failure.

## Authority and provenance

Goal: proof-backed Yulang inference/evaluation and broad unchanged Yulang2 Web
example compatibility. Types and Console remain the current finite target, not
an upper bound. R149 is provisionally adopted by the user. Governing contract:
`tasks/agent-loop/sprints/yulang2-types-console-20261020-r149-rev10.md`,
SHA-256 `31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9`.
Predecessor contract rev9 SHA-256:
`fba7059b283049ee6401f23b84e9800ea31be3a2f0fce62ffddb28ff70cb5e32`.

Predecessor note rev1 remains frozen at SHA-256
`6c5885c4f963071424a01070f6e92c197bd93bbdeef004667eac561a5fe16e17`; its
inbox remains frozen at
`72d2c97c00ceb688be6f4a3fbafa1f5ea4661b8c72b9ae68a5a3955d1b1efe3e`.
The independent review of those bytes found one major runtime boundary and two
minor record defects. This revision supersedes the affected statements only;
rev1 remains preserved.

Oracle source was read from immutable Git commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`, not the dirty oracle worktree.

## Root and nullfix facts

The prior checkpoint's collection and binding claims remain valid:

- `crates/infer/src/module_map/mod.rs`, blob
  `0e20fedcfef410b647b3fc90e70afa3fc0cb73e6`, sorts `LoadedFileCst` by module
  path depth and key (1818–1824). `body/mod.rs`, blob
  `f33bdfb5525ddcee02eba9bcd8c181acd1f9ea99`, lowers loaded files in that
  stored order (726–753).
- `crates/infer/src/lowering/body/methods.rs`, blob
  `086d42bc63f1c12414a42898671dda22c8ac1084`, emits `RuntimeRoot::ComputedDef`
  only when `BindingFetch::runs_computation()` and `publish_runtime_root` are
  both true (358–399).
- The actual nullfix thunk owner is
  `crates/infer/src/lowering/expr/tail.rs`, blob
  `8289bfdc6a17b2469ae168ac7939d34813fda474`, lines 455–476. It constructs a
  unit lambda and returns `Computation::value`; the earlier worker message said
  only `tail.rs`, while rev1 incorrectly attributed a nonexistent
  `body/tail.rs` path. `body/mod.rs` lines 2525–2536 selects this thunk only for
  `info.nullfix`. This establishes a delayed lambda body, not the behavior of
  every imported initializer.
- `crates/specialize/src/lib_support/specializer.rs`, blob
  `4dfffee1d68b89ea311dd9218bd56d8ab75a42d5`, maps a computed definition root
  to `Root::EvalInstance` (55–70).

## Runtime host-request boundary

`crates/mono-runtime/src/runtime/engine.rs`, blob
`d920a498c226383776ff265d5d8efddd06d06779`, has distinct root branches in
`run_with_host` (23–40):

1. `Root::Instance` and `Root::EvalInstance` call `eval_instance` first and
   wrap its returned `Value`; only after that does the common code call
   `resolve_host_requests`.
2. `Root::Expr` calls `eval_expr` directly, so an `EvalResult::Request` reaches
   `resolve_host_requests` and can invoke the supplied host.
3. `eval_instance` evaluates its body and calls `expect_eval_value` before
   returning (67–92). In `crates/mono-runtime/src/lib.rs`, blob
   `cb2b4cc1fb563934567a9cdcbaf8f803510372bc`, `expect_eval_value` maps a
   `Request` directly to `RuntimeError::UnhandledEffect` (1219–1223). That
   error propagates out of the root branch before `resolve_host_requests` can
   handle it. Successful instance values are cached only after evaluation
   succeeds; recursive re-entry is rejected (engine.rs 67–92).

Therefore, a runtime initializer whose instance body produces a host request
cannot use the `run_with_host` handler through this path. This is a conditional
control-flow obstruction to R149's desired host-write behavior, not evidence
that either unchanged example fails: this checkpoint has not connected a
required imported initializer in either sample's exact graph to that
request-producing branch. Keep that source-to-effect premise OPEN. A source
root-vector order fact is also not a substitute for the independent
initializer census/order across module composition and cycles.

The predecessor's `LoadedFileCst` and runtime-root facts establish a finite
producer-to-consumer slice only. The exact imported initializer set/order,
visible Add/Display candidate/prerequisite graph, selected implementation
identities, and Y3 source-to-selector carriers remain OPEN. No compiler/code
lease or production permission follows. Simple-sub/evaluator A/B, R70/R71,
source/native generality, soundness and principality remain OPEN.

Falsifier for the conditional obstruction: pinned evidence showing the exact
initializer path carries `Request` through `eval_instance` to the host handler
without `expect_eval_value` rejecting it. Falsifier for sample impact: no
required initializer on the exact Types/Console source graph reaches this
request-producing branch. No tests, builds, or runtime executions were run.
