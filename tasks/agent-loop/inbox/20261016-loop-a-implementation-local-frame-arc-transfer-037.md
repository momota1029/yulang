# I27 local-frame Arc transfer receipt

- Request: `20261016-loop-a-implementation-local-frame-arc-transfer-037`
- Revision: 1
- Baseline HEAD: `4137f234fefd7a15e4c13d36569eb113c695c0db`
- Requested/configured implementer: Luna/high
- Observed model/effort: UNKNOWN (not exposed by the runtime)
- Authority: approved G4 runtime handoff, reviewed §10 correspondence, existing
  local-binding contract, and efficiency principle §2.
- Claim class: bounded internal ownership-transfer optimization; behavior/API
  unchanged. No measured-speed or proof-closure claim.

## Frozen input manifest

All seven dispatcher pins matched at launch:

| Input | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `910e583843d6afa1b06530cc52f83a59708fd3d22bdf384a16d03a99931078cc` |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| `tools/inference-playground/tests/runtime.rs` | `c285ab9f8609134adfb2e61820fdc08f3148dbb1d6dae292fd9488a90182498e` |
| `tools/inference-playground/tests/runtime_module_expressions.rs` | `057030165810710cf0f883e320f2f08a05990bc4ccfae12ac8ae7c1e8ba2432c` |
| `notes/design/2026-10-16-module-expression-source-owner.md` | `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5` |
| `notes/theory/2026-10-16-runtime-module-expression-roots.md` | `915f99eb5cbd9734c3d1e4e0b778682bf1dbb3a8044ea21d5d77cee9d7250694` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

## Change and checks

Only `Machine::begin_local` changed. It copies the initializer `Arc<Code>` and
recursion flag and makes the required owned binding-ID clone before frame
construction. Recursive environment extension uses that ID. `Frame::Local`
takes ownership of `block` rather than cloning its Arc; its other fields,
environment extension, cell allocation, initializer choice, error behavior,
and transitions are unchanged. This removes one temporary Arc clone/drop pair
per local initializer while preserving retained ownership and asymptotic work.
No speed measurement was made.

The two assigned commands ran serially:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime returned_closure_retains_its_lexical_capture -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 17 filtered out`.

2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_module_expressions recursive_expression_completion_precedes_selected_definition -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 16 filtered out`.

No warning, timeout, dependency mismatch, extra test, benchmark, or scope
expansion was observed. Benchmark budget was 0 processes / 0 samples.

## Complete literal baseline diff

```diff
diff --git a/tools/inference-playground/src/runtime/machine.rs b/tools/inference-playground/src/runtime/machine.rs
index 5bbf8024c..5d5cf825a 100644
--- a/tools/inference-playground/src/runtime/machine.rs
+++ b/tools/inference-playground/src/runtime/machine.rs
@@ -1549,20 +1549,23 @@ impl Machine {
             return Err(RuntimeUnavailable::InvalidSourceReference);
         };
         if let Some(binding) = bindings.get(ordinal) {
+            let initializer = binding.initializer;
+            let recursive = binding.recursive;
+            let binding_id = binding.id.clone();
             let cell = self.cells.len();
             self.cells.push(None);
-            if binding.recursive {
-                environment = self.extend(environment, Binder::Local(binding.id.clone()), cell);
+            if recursive {
+                environment = self.extend(environment, Binder::Local(binding_id), cell);
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

## Frozen outputs and remaining limits

- `tools/inference-playground/src/runtime/machine.rs` SHA-256:
  `3d8e507f318088b354ba10c282523fd03d272756acb630f0345001b49c7d5305`
- This receipt SHA-256: recorded by the primary after freeze.

No test or proof artifact changed. Focused tests verify the selected local
closure capture and recursive Expression completion paths; they do not prove
general runtime correctness, inference adequacy, or any open parent theorem.
The exact owned implementation and verification scope remains limited to this
`begin_local` Arc transfer.
