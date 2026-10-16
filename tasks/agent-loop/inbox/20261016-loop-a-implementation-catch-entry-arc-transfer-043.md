# I32 Catch-entry Code Arc transfer receipt

- Request: `20261016-loop-a-implementation-catch-entry-arc-transfer-043`
- Revision: 1
- Baseline HEAD: `55af6349c7a1a37291d88782ac97616526fa1ee4`
- Requested/configured implementer: Luna/high
- Observed runtime settings: UNKNOWN
- Authority: approved G4/runtime correspondence, existing Catch ownership
  contracts and inference efficiency principle §2. No handler-rule or
  semantic change.
- Claim: remove one temporary Code Arc clone/drop pair at Catch entry only; no
  proof, semantic, or production-cutover gate is closed.

## Frozen ten-pin manifest

All ten inputs matched at launch and freeze:

| Input | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `c8fd76cd161f6fa433b1167aa417830f7df014ac3b25671eb5022507f8494891` |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| `tools/inference-playground/tests/runtime_module_expressions.rs` | `8eaad5f05b2592ce068f6ed2ed2e7934eaad68e368f4f60b8e3a60e59cf9ff1f` |
| `tools/inference-playground/tests/runtime_receiving.rs` | `f82399766a012383f12e7190744c397ce10d11b9730241d6f724fa254c9d06bf` |
| `tools/inference-playground/tests/runtime_resume.rs` | `1c1a4f402c87088454bf31eee2c1eee8d5ff9ec716fe2282ed4fe421b6469859` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/tests/candidate_catch_value_source.rs` | `449e254d4ea61a14e2713c2434734cb317f4da34dff0515b65090e37d0d3f60f` |
| `notes/design/2026-10-16-module-expression-source-owner.md` | `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5` |
| `notes/theory/2026-10-16-runtime-module-expression-roots.md` | `915f99eb5cbd9734c3d1e4e0b778682bf1dbb3a8044ea21d5d77cee9d7250694` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

## Implementation and checks

In the `Machine::evaluate` Catch arm, the scrutinee label is copied before
frame construction, and the already-owned `code` Arc is moved into
`Frame::CatchReturn.handler`. Handler-counter overflow checks, installation
owner, environment and frame fields, the shallow boundary, evidence checks,
captured continuations, errors, transitions, and all other required clones are
unchanged.

The three assigned commands ran serially:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_module_expressions primitive_direct_expression_handler_has_module_run_permission -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 17 filtered out`.

2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_receiving selected_operation_arm_runs_outside_its_shallow_handler -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 17 filtered out`.

3. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_resume forwarded_handler_reentry_runs_its_normal_value_arm_before_parent_completion -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 12 filtered out`.

No failure, warning, pin mismatch, extra test, or scope expansion occurred. No
benchmark was run.

## Complete literal baseline diff

```diff
diff --git a/tools/inference-playground/src/runtime/machine.rs b/tools/inference-playground/src/runtime/machine.rs
index 0a07a3186..20d847d16 100644
--- a/tools/inference-playground/src/runtime/machine.rs
+++ b/tools/inference-playground/src/runtime/machine.rs
@@ -543,6 +543,7 @@ impl Machine {
                 self.data(site, RuntimeValueKind::Operation(resolution.clone()), None)
             }
             Instruction::Catch { scrutinee, .. } => {
+                let scrutinee = *scrutinee;
                 let occurrence = self.next_handler;
                 self.next_handler = occurrence
                     .checked_add(1)
@@ -552,12 +553,12 @@ impl Machine {
                     owner: self.current_execution_owner(),
                 };
                 self.frames.push(Frame::CatchReturn {
-                    handler: code.clone(),
+                    handler: code,
                     environment,
                     installation,
                 });
                 self.state = State::Evaluate {
-                    code: *scrutinee,
+                    code: scrutinee,
                     environment,
                 };
             }
```

## Frozen outputs and limits

- `tools/inference-playground/src/runtime/machine.rs` SHA-256:
  `b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82`
- This receipt SHA-256: recorded by the primary after freeze.

This is a focused ownership optimization and runtime regression result only.
It makes no broader handler-semantics, proof, inference-soundness or
production-cutover claim.
