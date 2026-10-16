# I25 captured local expression regression receipt

- Request: `20261016-loop-a-implementation-captured-local-expression-034`
- Revision: 1
- Baseline HEAD: `49beeebd2bfde5e8d19634cd8d1ba300f2ab9592`
- Requested/configured implementation role: Luna/high (`gpt-6-luna`, high)
- Observed model/effort: UNKNOWN (not exposed by the runtime)
- Claim: focused accepted-behavior regression evidence only; no proof or
  production-gate closure.
- Governing authority: approved G3/G4 module-expression ownership and ordinary
  inference/runtime handoff; top-level inference principles §2; current capture,
  generalization boundary and supported Bool-condition contracts.

## Frozen input manifest

All eleven packet hashes matched before editing:

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/tests/ordinary_expression_source.rs` | `819268e265e9afa03a3cfdebf867876de3f40dbadc159d9248814615dd2ce81c` |
| `tools/inference-playground/tests/runtime.rs` | `2a263b532a1db0fceafb2787e5783461b3a6684f5a7a74c45995943ec2060e90` |
| `crates/yu-solver/src/candidate_scheme.rs` | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `tools/inference-playground/src/runtime/machine.rs` | `910e583843d6afa1b06530cc52f83a59708fd3d22bdf384a16d03a99931078cc` |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| `tools/inference-playground/src/lib.rs` | `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb` |
| `crates/yu-solver/tests/candidate_annotated_primitive_formals.rs` | `137b51c32f14ada552954648171c091526d8b26e786f3c36cddf3c134830281d` |
| `notes/design/2026-10-16-module-expression-source-owner.md` | `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

## Implementation and evidence

Added the native test `captured_local_expression_values_keep_original_constraints`
and runtime test `captured_local_expression_conflicts_withhold_execution` for
the exact packet fixture with `CAPTURE` equal to `true`, `false`, and `1`. The
native test verifies one module binding (`main`), one authentic Expression root,
genuine local `outer`/`keep`/`first` bindings, both local `keep` resolutions,
the original captured `x` Parameter resolution, and three authentic Apply/Call
occurrence correspondences under the same Expression owner. For the Boolean
variants it checks each original local `keep` Name's own FreshUse route and
nonempty local Value and Effect images. It does not require captured route rows
to be pairwise disjoint. For integer capture it confirms a nonempty conflict
whose occurrence is in this LocalSource and requests no FreshUse after conflict.
The runtime test confirms both Boolean variants return exactly `7\n` and the
integer capture is rejected under the existing candidate type conflict category
without an Unsupported result.

Exact commands, run serially as assigned:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --test ordinary_expression_source captured_local_expression_values_keep_original_constraints -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 11 filtered out`.

2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime captured_local_expression_conflicts_withhold_execution -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 17 filtered out`.

No warning, timeout, owner mismatch, route mismatch or dependency/pin change was
observed. No benchmark was run (budget 0 processes / 0 samples). No rejected
program was executed.

## Reused and adapted evidence

- Reused the accepted I22 conditional-expression source mapping pattern for
  authentic original Apply-to-Call occurrence correspondence.
- Reused I23's genuine local scheme/FreshUse route pattern for the two `keep`
  occurrences and local Value/Effect image checks.
- Adapted I23's row assertions: captured rows can correlate, so this regression
  asserts each route's required local images but deliberately does not claim
  pairwise row disjointness.
- Reused the existing `run` helper and candidate-conflict result category in
  the public runtime regression.
- Rejected numeric solver-ID assumptions, synthetic IDs/source variants,
  Unsupported-result expectations, post-conflict FreshUse queries, and any
  effect-order or executed-branch claim. No superseded Simple-sub bypass was
  recreated.

Earlier evidence is available at I22 receipt
`20261016-loop-a-implementation-conditional-expression-freshuse-031` and I23
receipt `20261016-loop-a-implementation-local-expression-freshuse-032`.

## Complete literal baseline diff

```diff
diff --git a/crates/yu-solver/tests/ordinary_expression_source.rs b/crates/yu-solver/tests/ordinary_expression_source.rs
index fbdc788dd..fd7657753 100644
--- a/crates/yu-solver/tests/ordinary_expression_source.rs
+++ b/crates/yu-solver/tests/ordinary_expression_source.rs
@@ -386,6 +386,145 @@ fn local_scheme_expression_uses_keep_distinct_fresh_instances() {
     }
 }
 
+#[test]
+fn captured_local_expression_values_keep_original_constraints() {
+    let template = r#"{ my outer x = { my keep ignored = x; my first = keep 1; if keep "str": 11 else: 13 }; outer CAPTURE }; my main = 7"#;
+
+    for (capture, expect_conflict) in [("true", false), ("false", false), ("1", true)] {
+        let text = template.replace("CAPTURE", capture);
+        let hir = module(&text);
+        let candidate = CandidateInference::solve(hir.clone())
+            .unwrap_or_else(|error| panic!("{text}: {error:?}"));
+
+        let module_bindings: Vec<_> = hir
+            .items()
+            .iter()
+            .filter_map(|item| match item {
+                HirItem::Binding(binding) => Some(binding),
+                _ => None,
+            })
+            .collect();
+        assert_eq!(module_bindings.len(), 1, "no synthetic module binding: {text}");
+        assert_eq!(module_bindings[0].name().spelling(), "main");
+
+        let expressions: Vec<_> = hir
+            .items()
+            .iter()
+            .filter_map(|item| match item {
+                HirItem::Expression(expression) => Some(expression),
+                _ => None,
+            })
+            .collect();
+        let [expression] = expressions.as_slice() else {
+            panic!("the block remains one original Expression root: {text}");
+        };
+        let root = hir
+            .expression_root(expression.occurrence())
+            .unwrap()
+            .expect("the original block expression root");
+        let owner = SourceRootId::Expression(root.clone());
+        let local = hir
+            .local_source_for(&owner)
+            .unwrap()
+            .expect("the authentic expression root retains LocalSource");
+        assert_eq!(root.occurrence(), expression.occurrence());
+
+        let outer = local
+            .bindings()
+            .iter()
+            .find(|binding| binding.spelling.as_ref() == "outer")
+            .expect("the genuine local outer binding");
+        let keep = local
+            .bindings()
+            .iter()
+            .find(|binding| binding.spelling.as_ref() == "keep")
+            .expect("the genuine local keep binding");
+        assert!(local.bindings().iter().any(|binding| binding.spelling.as_ref() == "first"));
+        let parameter = outer
+            .parameters
+            .iter()
+            .find(|parameter| parameter.spelling.as_ref() == "x")
+            .expect("the genuine outer parameter x");
+        assert!(local.expressions().iter().any(|source_expression| matches!(
+            &source_expression.form,
+            LocalSourceForm::Name {
+                spelling,
+                resolution: LocalSourceResolution::Parameter(resolved),
+            } if spelling.as_ref() == "x" && resolved == &parameter.id
+        )), "the captured x Name keeps its original Parameter identity: {text}");
+
+        let keep_names: Vec<_> = local
+            .expressions()
+            .iter()
+            .filter(|source_expression| matches!(
+                &source_expression.form,
+                LocalSourceForm::Name {
+                    spelling,
+                    resolution: LocalSourceResolution::Local(resolved),
+                } if spelling.as_ref() == "keep" && resolved == &keep.id
+            ))
+            .collect();
+        assert_eq!(keep_names.len(), 2, "both original keep Names resolve locally: {text}");
+        assert_ne!(keep_names[0].occurrence, keep_names[1].occurrence);
+
+        let applications: Vec<_> = local
+            .expressions()
+            .iter()
+            .filter(|source_expression| matches!(&source_expression.form, LocalSourceForm::Apply { .. }))
+            .collect();
+        assert_eq!(applications.len(), 3, "the source retains all actual applications: {text}");
+        assert_eq!(candidate.source_call_count(), 3, "all three Calls are retained: {text}");
+        let calls: Vec<_> = (0..candidate.source_call_count())
+            .map(|index| candidate.source_call(index).unwrap())
+            .collect();
+        assert!(calls.iter().all(|call| call.owner() == &owner));
+        for application in &applications {
+            assert!(calls.iter().any(|call| {
+                &call.source().occurrence == &application.occurrence
+            }), "each Call retains its authentic Apply occurrence: {text}");
+            let LocalSourceForm::Apply { callee, .. } = &application.form else {
+                unreachable!();
+            };
+            let callee = &local.expressions()[callee.ordinal() as usize];
+            assert!(matches!(
+                &callee.form,
+                LocalSourceForm::Name {
+                    spelling,
+                    resolution: LocalSourceResolution::Local(resolved),
+                } if (spelling.as_ref() == "keep" && resolved == &keep.id)
+                    || (spelling.as_ref() == "outer" && resolved == &outer.id)
+            ), "each actual Apply follows an authentic local callee: {text}");
+        }
+
+        if expect_conflict {
+            assert!(!candidate.candidate_conflicts().is_empty(), "integer capture must conflict: {text}");
+            assert!(candidate.candidate_conflicts().iter().any(|conflict| {
+                local.expressions().iter().any(|source_expression| {
+                    conflict.occurrence().occurrence() == &source_expression.occurrence
+                })
+            }), "a conflict is owned by the original expression LocalSource: {text}");
+            continue;
+        }
+
+        assert!(candidate.candidate_conflicts().is_empty(), "boolean capture must solve: {text}");
+        for name in keep_names {
+            let fresh_use = candidate
+                .fresh_use(&name.occurrence)
+                .expect("each original local keep Name retains its FreshUse route");
+            assert_eq!(fresh_use.occurrence(), &name.occurrence);
+            let local_rows: Vec<_> = fresh_use
+                .rows()
+                .filter(|row| row.source_row().is_local())
+                .collect();
+            assert!(!local_rows.is_empty(), "each FreshUse retains local rows: {text}");
+            for kind in [ComponentKind::Value, ComponentKind::Effect] {
+                assert!(local_rows.iter().any(|row| row.kind() == kind),
+                    "each local FreshUse image contains a {kind:?} row: {text}");
+            }
+        }
+    }
+}
+
 #[test]
 fn forward_alias_expression_uses_keep_distinct_fresh_instances() {
     let hir = module(r"alias 1; alias (\x -> x); my alias = id; my id x = x; my main = 7");
diff --git a/tools/inference-playground/tests/runtime.rs b/tools/inference-playground/tests/runtime.rs
index 191aca33c..79267a127 100644
--- a/tools/inference-playground/tests/runtime.rs
+++ b/tools/inference-playground/tests/runtime.rs
@@ -162,6 +162,23 @@ fn discarded_expression_type_conflicts_keep_source_locations() {
     }
 }
 
+#[test]
+fn captured_local_expression_conflicts_withhold_execution() {
+    let template = r#"{ my outer x = { my keep ignored = x; my first = keep 1; if keep "str": 11 else: 13 }; outer CAPTURE }; my main = 7"#;
+    for capture in ["true", "false"] {
+        let source = template.replace("CAPTURE", capture);
+        assert_eq!(run(&source).unwrap(), "7\n", "{source}");
+    }
+
+    let source = template.replace("CAPTURE", "1");
+    let error = run(&source).expect_err("the integer capture must be rejected before execution");
+    assert!(
+        error.starts_with("candidate type conflicts"),
+        "unexpected error category: {error}"
+    );
+    assert!(!error.contains("unsupported source"), "{error}");
+}

 #[test]
 fn cli_resource_exhaustion_withholds_runtime_output() {
     let source = "my main = { my loop x = loop x; my ignore x = 7; ignore (loop ()) }";
```

## Output hashes and remaining gates

At freeze:

- `crates/yu-solver/tests/ordinary_expression_source.rs` SHA-256:
  `2e789678e57131e8a73b18ebcd216e0a6e75b4a45c211161a5949a288fa79410`
- `tools/inference-playground/tests/runtime.rs` SHA-256:
  `c285ab9f8609134adfb2e61820fdc08f3148dbb1d6dae292fd9488a90182498e`

The only packet-owned outputs are those two test files and this receipt. Existing
unrelated dirty board/question/inbox paths were left untouched. The open
source/ResultBind/MODEL/exact-U/A-B/F1/FK1 parent gates remain open; this test
pair is not evidence for their closure, effect-order adequacy, or generalization
proof. Suggested successor: primary-consulted I25 result review, with the
board-proposed single M1 regression auditor R38 if the dispatcher retains that
selection.
