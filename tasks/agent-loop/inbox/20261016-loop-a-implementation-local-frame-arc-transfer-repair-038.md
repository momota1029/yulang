# I27-R1 local-frame Arc transfer repair receipt

- Request: `20261016-loop-a-implementation-local-frame-arc-transfer-repair-038`
- Revision: 1
- Baseline HEAD: `4137f234fefd7a15e4c13d36569eb113c695c0db`
- Requested/configured implementer: Luna/high
- Observed model/effort: UNKNOWN (not exposed by the runtime)
- R40 finding: MINOR — the first implementation cloned the binding ID
  unconditionally, even for nonrecursive local bindings. The baseline only
  performs that clone in the recursive environment-extension branch.
- Disposition: remove the unconditional clone and restore the conditional
  `binding.id.clone()` directly inside `if recursive`. Keep copied initializer
  and recursion flag, moved block, cell allocation, frame fields, and all
  transitions unchanged.
- No change to or rewrite of receipt037.

## Frozen seven-pin manifest

All seven dependency pins matched before and after repair:

| Input | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` (I27 source before R1) | `3d8e507f318088b354ba10c282523fd03d272756acb630f0345001b49c7d5305` |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| `tools/inference-playground/tests/runtime.rs` | `c285ab9f8609134adfb2e61820fdc08f3148dbb1d6dae292fd9488a90182498e` |
| `tools/inference-playground/tests/runtime_module_expressions.rs` | `057030165810710cf0f883e320f2f08a05990bc4ccfae12ac8ae7c1e8ba2432c` |
| `notes/design/2026-10-16-module-expression-source-owner.md` | `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5` |
| `notes/theory/2026-10-16-runtime-module-expression-roots.md` | `915f99eb5cbd9734c3d1e4e0b778682bf1dbb3a8044ea21d5d77cee9d7250694` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

Receipt037 remains byte-identical at SHA-256
`027dc4ecd4e834d0527c6279c2396916952882f1c83f2f33a2bf0a388cf7d851` and
records the original I27 implementation and R40 finding context.

## Exact checks

The two original focused commands ran serially:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime returned_closure_retains_its_lexical_capture -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 17 filtered out`.

2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_module_expressions recursive_expression_completion_precedes_selected_definition -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 16 filtered out`.

No warning, timeout, dependency mismatch, extra test, benchmark, or scope
expansion occurred. Benchmark budget was 0 processes / 0 samples.

## Repair diff against the frozen I27 output

```diff
-            let binding_id = binding.id.clone();
             let cell = self.cells.len();
             self.cells.push(None);
             if recursive {
-                environment = self.extend(environment, Binder::Local(binding_id), cell);
+                environment = self.extend(environment, Binder::Local(binding.id.clone()), cell);
```

## Complete final baseline diff

```diff
diff --git a/tools/inference-playground/src/runtime/machine.rs b/tools/inference-playground/src/runtime/machine.rs
index 5bbf8024c..9aa85fb9c 100644
--- a/tools/inference-playground/src/runtime/machine.rs
+++ b/tools/inference-playground/src/runtime/machine.rs
@@ -1549,20 +1549,22 @@ impl Machine {
             return Err(RuntimeUnavailable::InvalidSourceReference);
         };
         if let Some(binding) = bindings.get(ordinal) {
+            let initializer = binding.initializer;
+            let recursive = binding.recursive;
             let cell = self.cells.len();
             self.cells.push(None);
-            if binding.recursive {
+            if recursive {
                 environment = self.extend(environment, Binder::Local(binding.id.clone()), cell);
             }
             self.frames.push(Frame::Local {
-                block: block.clone(),
+                block,
                 next: ordinal + 1,
                 environment,
                 cell,
-                recursive: binding.recursive,
+                recursive,
             });
             self.state = State::Evaluate {
-                code: binding.initializer,
+                code: initializer,
                 environment,
             };
         } else {
```

## Frozen outputs and limits

- `tools/inference-playground/src/runtime/machine.rs` SHA-256:
  `ce8a58b934591a0898487c5ea93f821a23054fdc68fdaf02f6d003754e665ce6`
- This receipt SHA-256: recorded in the primary handoff after freeze.

The final implementation removes one temporary Arc clone/drop pair per local
initializer while preserving the baseline conditional clone of a binding ID
for recursive bindings. The tests provide focused regression evidence only;
they establish no general runtime or inference theorem and close no production
gate.
