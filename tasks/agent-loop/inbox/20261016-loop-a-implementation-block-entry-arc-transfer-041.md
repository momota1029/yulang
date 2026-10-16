# I30 block-entry Code Arc transfer receipt

- Request: `20261016-loop-a-implementation-block-entry-arc-transfer-041`
- Revision: 1
- Baseline HEAD: `3c521cc8a3569cb89b99e875c6d2dd5713f174de`
- Requested/configured implementer: Luna/high
- Observed runtime settings: UNKNOWN
- Authority: approved G4 runtime handoff, reviewed runtime correspondence §10,
  local-binding ownership behavior from I27, and inference efficiency
  principle §2.
- Claim: one temporary Code Arc clone/drop pair removed at local Block entry;
  no semantic or proof-gate change, no measured-speed claim.

## Frozen seven-pin manifest

All seven inputs matched before editing and at freeze:

| Input | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `ce8a58b934591a0898487c5ea93f821a23054fdc68fdaf02f6d003754e665ce6` |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| `tools/inference-playground/tests/runtime.rs` | `c285ab9f8609134adfb2e61820fdc08f3148dbb1d6dae292fd9488a90182498e` |
| `tools/inference-playground/tests/runtime_module_expressions.rs` | `8eaad5f05b2592ce068f6ed2ed2e7934eaad68e368f4f60b8e3a60e59cf9ff1f` |
| `notes/design/2026-10-16-module-expression-source-owner.md` | `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5` |
| `notes/theory/2026-10-16-runtime-module-expression-roots.md` | `915f99eb5cbd9734c3d1e4e0b778682bf1dbb3a8044ea21d5d77cee9d7250694` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

## Exact checks

The two assigned commands ran serially:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime returned_closure_retains_its_lexical_capture -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 17 filtered out`.

2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_module_expressions recursive_expression_completion_precedes_selected_definition -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 17 filtered out`.

No failure, warning, pin mismatch, extra test, or scope expansion occurred.
No benchmark was run.

## Complete literal baseline diff

```diff
diff --git a/tools/inference-playground/src/runtime/machine.rs b/tools/inference-playground/src/runtime/machine.rs
index 9aa85fb9c..83dd7fbb8 100644
--- a/tools/inference-playground/src/runtime/machine.rs
+++ b/tools/inference-playground/src/runtime/machine.rs
@@ -517,7 +517,7 @@ impl Machine {
                     environment,
                 };
             }
-            Instruction::Block { .. } => self.begin_local(code.clone(), 0, environment)?,
+            Instruction::Block { .. } => self.begin_local(code, 0, environment)?,
             Instruction::If { arms, else_branch } => {
                 if let Some((test, _)) = arms.first() {
                     self.frames.push(Frame::Condition {
```

## Frozen output and limits

- `tools/inference-playground/src/runtime/machine.rs` SHA-256:
  `ce3ee56589b55b56344e877bd7566105f5ef9458a6c466534b3d45eaf63d6ea5`
- This receipt SHA-256: recorded by the primary after freeze.

The exact change transfers the existing owned `Code` Arc into `begin_local`.
Its local-frame storage/ownership and all other evaluate arms are unchanged.
Focused tests verify lexical capture and Expression completion paths only; no
general runtime, inference, proof, or production-cutover theorem is claimed.
