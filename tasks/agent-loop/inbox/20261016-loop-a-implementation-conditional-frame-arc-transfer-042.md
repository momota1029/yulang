# I31 conditional-frame Code Arc transfer receipt

- Request: `20261016-loop-a-implementation-conditional-frame-arc-transfer-042`
- Revision: 1
- Baseline HEAD: `5f3c6f6e64c67a1854ed4d39f2e8721d06bf43f5`
- Requested/configured implementer: Luna/high
- Observed runtime settings: UNKNOWN
- Authority: approved G4 runtime handoff, reviewed runtime correspondence §10,
  selected conditional behavior contracts, and efficiency principle §2.
- Claim: internal conditional-frame ownership transfer only; no semantic or
  proof-gate change and no measured-speed claim.

## Frozen nine-pin manifest

All nine inputs matched at launch and freeze:

| Input | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `ce3ee56589b55b56344e877bd7566105f5ef9458a6c466534b3d45eaf63d6ea5` |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| `tools/inference-playground/tests/runtime.rs` | `c285ab9f8609134adfb2e61820fdc08f3148dbb1d6dae292fd9488a90182498e` |
| `tools/inference-playground/tests/runtime_module_expressions.rs` | `8eaad5f05b2592ce068f6ed2ed2e7934eaad68e368f4f60b8e3a60e59cf9ff1f` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/tests/candidate_conditionals.rs` | `b404eacf20e30a59affb2ac49afab2d489d50ce25510bfd93b90352e4379ed3c` |
| `notes/design/2026-10-16-module-expression-source-owner.md` | `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5` |
| `notes/theory/2026-10-16-runtime-module-expression-roots.md` | `915f99eb5cbd9734c3d1e4e0b778682bf1dbb3a8044ea21d5d77cee9d7250694` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

## Implementation and behavior coverage

In `Machine::evaluate`, the first test label is copied before the owned
conditional `Code` is moved into the first `Frame::Condition`. In
`return_value`, the next test label is copied before the owned conditional is
moved into the replacement frame. No other ownership path changed.

The new `multi_arm_conditionals_preserve_selected_values_and_unit` test checks
the five assigned `my main = ...` cases: first arm returns `11`, a later true
arm returns `7`, else returns `9`, and omitted-else cases return Unit. This
preserves the existing Boolean condition error behavior and selected-result
contracts without asserting any unassigned behavior. Existing test assertions
were preserved.

## Exact checks

The two assigned commands ran serially:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime multi_arm_conditionals_preserve_selected_values_and_unit -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 18 filtered out`.

2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_module_expressions conditional_expression_results_are_discarded_before_selection -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 17 filtered out`.

No failure, warning, pin mismatch, extra check, benchmark, or scope expansion
occurred. No proof or production-cutover gate is claimed closed.

## Complete literal baseline diff

```diff
diff --git a/tools/inference-playground/src/runtime/machine.rs b/tools/inference-playground/src/runtime/machine.rs
index 83dd7fbb8..0a07a3186 100644
--- a/tools/inference-playground/src/runtime/machine.rs
+++ b/tools/inference-playground/src/runtime/machine.rs
@@ -520,13 +520,14 @@ impl Machine {
             Instruction::Block { .. } => self.begin_local(code, 0, environment)?,
             Instruction::If { arms, else_branch } => {
                 if let Some((test, _)) = arms.first() {
+                    let test = *test;
                     self.frames.push(Frame::Condition {
-                        conditional: code.clone(),
+                        conditional: code,
                         arm: 0,
                         environment,
                     });
                     self.state = State::Evaluate {
-                        code: *test,
+                        code: test,
                         environment,
                     };
@@ -884,12 +885,13 @@ impl Machine {
                         environment,
                     };
                 } else if let Some((test, _)) = arms.get(arm + 1) {
+                    let test = *test;
                     self.state = State::Evaluate {
-                        code: *test,
+                        code: test,
                         environment,
                     };
                     self.frames.push(Frame::Condition {
-                        conditional: conditional.clone(),
+                        conditional,
                         arm: arm + 1,
                         environment,
                     });
diff --git a/tools/inference-playground/tests/runtime.rs b/tools/inference-playground/tests/runtime.rs
index 79267a127..b5bf00c35 100644
--- a/tools/inference-playground/tests/runtime.rs
+++ b/tools/inference-playground/tests/runtime.rs
@@ -62,6 +62,20 @@ fn explicit_else_returns_the_selected_branch_value() {
     assert_eq!(run("my main = if false: 7 else: 9").unwrap(), "9\n");
 }
 
+#[test]
+fn multi_arm_conditionals_preserve_selected_values_and_unit() {
+    for (body, expected) in [
+        ("if true: 11 elsif true: 13 else: 9", "11\n"),
+        ("if false: 11 elsif false: 13 elsif true: 7 else: 9", "7\n"),
+        ("if false: 11 elsif false: 13 elsif false: 7 else: 9", "9\n"),
+        ("if false: 11 elsif true: 7", "()\n"),
+        ("if false: 11 elsif false: 7", "()\n"),
+    ] {
+        let source = format!("my main = {body}");
+        assert_eq!(run(&source).unwrap(), expected, "{source}");
+    }
+}
+
 #[test]
 fn positive_integer_display_preserves_arbitrary_precision() {
```

## Frozen outputs and limits

- `tools/inference-playground/src/runtime/machine.rs` SHA-256:
  `c8fd76cd161f6fa433b1167aa417830f7df014ac3b25671eb5022507f8494891`
- `tools/inference-playground/tests/runtime.rs` SHA-256:
  `f8bebfd4eb4571e2814b83ea8473c035b429fe1eed4e07d26942a096143306ec`
- This receipt SHA-256: recorded by the primary after freeze.

The changed paths remove conditional Code Arc clone/drop pairs while keeping
test/body order, arm indices, environments, Boolean-error behavior, else
selection, omitted-else discard/Unit behavior, and transitions. No runtime
speed measurement, general theorem, or production cutover claim is made.
