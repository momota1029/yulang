# I23 implementation result — local-scheme expression FreshUse regressions

Request-ID: `20261016-loop-a-implementation-local-expression-freshuse-032`
Revision: 1 (frozen)
Baseline: `d02c2225845d44ff1fe14867014812c60bb1d98e`
Requested role/model: implementer, Luna/high
Observed runtime model/effort: UNKNOWN (runtime metadata unavailable)

## Authority and scope

Authority: Authoritative module-expression source-owner G3/G4 and top-level inference principles §2, with the existing local FreshUse contracts. This packet adds only the two specified regressions. It changes no production source, inference behavior, runtime behavior, prior expectations, or public API. The tests establish observations for this fixed source only; they prove no general theorem and close no F5, source-adequacy, or production gate.

Exact fixture in both tests:

`{ my id x = x; my first = id 1; id "str" }; my main = 7`

## Earlier evidence reused / adapted / rejected

- Reused `expression_origin_uses_freshen_one_definition_at_distinct_value_shapes` in `crates/yu-solver/tests/ordinary_expression_source.rs` (commit `342f27633`, “test: cover polymorphic expression-root freshening and execution”) and `forward_alias_expression_uses_keep_distinct_fresh_instances` (commit `6ab6882e0`, “test: cover forward alias inference and runtime”). Those cover two uses across distinct expression roots, not two uses within one local expression-root owner.
- Reused `local_fresh_uses_transport_both_captured_branch_literals` from `crates/yu-solver/tests/candidate_conditionals.rs` and `binder_callable_alias_and_local_fresh_uses_keep_the_original_value` from `crates/yu-solver/tests/candidate_catch_value_source.rs` for the existing FreshUse local-row/identity assertions. They exercise the Definition-root consumer; I22 separately covered ModuleDef Name routes.
- Adapted the same local Value/Effect and `same_identity` checks to two distinct local `id` Name occurrences in one authentic Expression root. Each Apply's real typed callee index leads to the actual local Name, and each route is queried by that occurrence. The test matches Call records to actual Apply occurrences without relying on order or solver numeric IDs.
- Reused the runtime test's existing `assert_selected` helper and its 30,000-step bound. No new helper or runtime rule was added.
- No previous behavior or expectation was rejected or changed. No production path, theorem, receiving-context rule, or source profile was broadened.

## Full literal baseline diffs

Exactly two test files changed. Full literal diffs from the pinned baseline:

```diff
diff --git a/crates/yu-solver/tests/ordinary_expression_source.rs b/crates/yu-solver/tests/ordinary_expression_source.rs
index 9378a3a64..fbdc788dd 100644
--- a/crates/yu-solver/tests/ordinary_expression_source.rs
+++ b/crates/yu-solver/tests/ordinary_expression_source.rs
@@ -263,6 +263,129 @@ fn conditional_expression_branches_keep_distinct_fresh_instances() {
     }
 }
 
+#[test]
+fn local_scheme_expression_uses_keep_distinct_fresh_instances() {
+    let text = r#"{ my id x = x; my first = id 1; id "str" }; my main = 7"#;
+    let hir = module(text);
+    let candidate = CandidateInference::solve(hir.clone())
+        .unwrap_or_else(|error| panic!("{text}: {error:?}"));
+    assert!(candidate.candidate_conflicts().is_empty(), "{text}");
+
+    let module_bindings: Vec<_> = hir
+        .items()
+        .iter()
+        .filter_map(|item| match item {
+            HirItem::Binding(binding) => Some(binding),
+            _ => None,
+        })
+        .collect();
+    assert_eq!(module_bindings.len(), 1, "no synthetic module definition");
+    assert_eq!(module_bindings[0].name().spelling(), "main");
+
+    let expressions: Vec<_> = hir
+        .items()
+        .iter()
+        .filter_map(|item| match item {
+            HirItem::Expression(expression) => Some(expression),
+            _ => None,
+        })
+        .collect();
+    let [expression] = expressions.as_slice() else {
+        panic!("the block remains one original Expression root");
+    };
+    let root = hir
+        .expression_root(expression.occurrence())
+        .unwrap()
+        .expect("the original block expression root");
+    let owner = SourceRootId::Expression(root.clone());
+    let local = hir
+        .local_source_for(&owner)
+        .unwrap()
+        .expect("the authentic expression root retains its LocalSource");
+    assert_eq!(root.occurrence(), expression.occurrence());
+
+    let local_id = local
+        .bindings()
+        .iter()
+        .find(|binding| binding.spelling.as_ref() == "id")
+        .expect("the genuine local id binding");
+    let name_uses: Vec<_> = local
+        .expressions()
+        .iter()
+        .filter(|expression| matches!(
+            &expression.form,
+            LocalSourceForm::Name {
+                spelling,
+                resolution: LocalSourceResolution::Local(resolved),
+            } if spelling.as_ref() == "id" && resolved == &local_id.id
+        ))
+        .collect();
+    assert_eq!(name_uses.len(), 2, "both original local id uses are retained");
+    assert_ne!(name_uses[0].occurrence, name_uses[1].occurrence);
+
+    let applications: Vec<_> = local
+        .expressions()
+        .iter()
+        .filter(|expression| matches!(&expression.form, LocalSourceForm::Apply { .. }))
+        .collect();
+    assert_eq!(applications.len(), 2);
+    assert_eq!(candidate.source_call_count(), 2);
+    let calls: Vec<_> = (0..candidate.source_call_count())
+        .map(|index| candidate.source_call(index).unwrap())
+        .collect();
+    assert!(calls.iter().all(|call| call.owner() == &owner));
+    for application in &applications {
+        assert!(calls.iter().any(|call| {
+            &call.source().occurrence == &application.occurrence
+        }), "each Apply Call retains its authentic source occurrence");
+    }
+
+    let mut fresh_rows_by_use = Vec::with_capacity(2);
+    for application in applications {
+        let LocalSourceForm::Apply { callee, .. } = &application.form else {
+            unreachable!();
+        };
+        let callee = &local.expressions()[callee.ordinal() as usize];
+        assert!(name_uses.iter().any(|name| name.occurrence == callee.occurrence));
+        let LocalSourceForm::Name {
+            spelling,
+            resolution: LocalSourceResolution::Local(resolved),
+        } = &callee.form
+        else {
+            panic!("each actual Apply callee is a local Name");
+        };
+        assert_eq!(spelling.as_ref(), "id");
+        assert_eq!(resolved, &local_id.id);
+
+        let fresh_use = candidate
+            .fresh_use(&callee.occurrence)
+            .expect("each original local Name occurrence has its FreshUse route");
+        assert_eq!(fresh_use.occurrence(), &callee.occurrence);
+        let local_rows: Vec<_> = fresh_use
+            .rows()
+            .filter(|row| row.source_row().is_local())
+            .collect();
+        assert!(!local_rows.is_empty(), "each FreshUse has a local row image");
+        for kind in [ComponentKind::Value, ComponentKind::Effect] {
+            assert!(
+                local_rows.iter().any(|row| row.kind() == kind),
+                "each local FreshUse image contains a {kind:?} row"
+            );
+        }
+        fresh_rows_by_use.push(local_rows);
+    }
+
+    let [first, second] = fresh_rows_by_use.as_slice() else {
+        panic!("the two local Name occurrences have distinct FreshUse images");
+    };
+    for row in first {
+        assert!(
+            second.iter().all(|other| !row.same_identity(other)),
+            "independent local Name uses do not share local row identity"
+        );
+    }
+}
+
 #[test]
 fn forward_alias_expression_uses_keep_distinct_fresh_instances() {
     let hir = module(r"alias 1; alias (\x -> x); my alias = id; my id x = x; my main = 7");
diff --git a/tools/inference-playground/tests/runtime_module_expressions.rs b/tools/inference-playground/tests/runtime_module_expressions.rs
index f8759b4ea..4c2a261ad 100644
--- a/tools/inference-playground/tests/runtime_module_expressions.rs
+++ b/tools/inference-playground/tests/runtime_module_expressions.rs
@@ -147,6 +147,11 @@ fn conditional_expression_results_are_discarded_before_selection() {
     }
 }
 
+#[test]
+fn local_scheme_expression_results_are_discarded_before_selection() {
+    assert_selected(r#"{ my id x = x; my first = id 1; id "str" }; my main = 7"#, "7");
+}
+
 #[test]
 fn forward_alias_expression_calls_discard_results_before_selection() {
*** End Patch
```

## Exact verification results

Ran exactly the two listed commands, serially. Both passed, exit 0, with exactly one test discovered and passed each:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --test ordinary_expression_source local_scheme_expression_uses_keep_distinct_fresh_instances -- --exact --test-threads=1`
   - `1 passed; 0 failed; 0 ignored; 0 measured; 10 filtered out`.
2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_module_expressions local_scheme_expression_results_are_discarded_before_selection -- --exact --test-threads=1`
   - `1 passed; 0 failed; 0 ignored; 0 measured; 15 filtered out`.

No other test/build/probe/benchmark/stress command was run; benchmark budget was 0 processes / 0 samples. No Git/index operation, delegation, production edit, or cleanup was performed.

## Frozen eleven-input manifest and output hashes

All eleven pinned inputs matched before editing. Frozen changed-file hashes:

- `crates/yu-solver/tests/ordinary_expression_source.rs` baseline `2fc93916edaf2f5b479020eae6cdd38fa2a8d2d35f8bf6b1ab54100dfeed72f3`; frozen output SHA-256 `819268e265e9afa03a3cfdebf867876de3f40dbadc159d9248814615dd2ce81c`.
- `tools/inference-playground/tests/runtime_module_expressions.rs` baseline `485551b31825d53a8e6c27fdf7359f452e0690f35b6b9d4f5e57eb44659c07fc`; frozen output SHA-256 `f1693e49067f9bbfcd354ee3b87094cddef3736b324ca6c2551f70582368afa6`.
- `crates/yu-solver/src/shadow_apply.rs`: `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`.
- `crates/yu-solver/src/candidate_scheme.rs`: `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`.
- `crates/yu-solver/src/candidate_source.rs`: `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`.
- `crates/yu-solver/tests/candidate_conditionals.rs`: `b404eacf20e30a59affb2ac49afab2d489d50ce25510bfd93b90352e4379ed3c`.
- `crates/yu-solver/tests/candidate_catch_value_source.rs`: `449e254d4ea61a14e2713c2434734cb317f4da34dff0515b65090e37d0d3f60f`.
- `tools/inference-playground/src/runtime/machine.rs`: `d9a8e14bd3eda8f5c40641beabac0ad862a4c04fc1173359934376681b731e77`.
- `tools/inference-playground/src/runtime/program.rs`: `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748`.
- `notes/design/2026-10-16-module-expression-source-owner.md`: `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`.
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- `tasks/agent-loop/inbox/20261016-loop-a-implementation-local-expression-freshuse-032.md`: final receipt SHA-256 is reported separately to Luna.

## What the tests observed and what remains open

Native lowering retained one module binding named `main`, one original Expression root with authentic `SourceRootId::Expression`, a local `id` binding and exactly two matching original local Name uses resolving to that same `HirLocalId`. Solving had no conflicts. The two actual Apply Call records were owned by that Expression root and matched the two authentic Apply occurrences. Following each Apply's typed callee index reached one of those Name occurrences; each had a matching FreshUse route and local Value/Effect rows, and the two local row images shared no local row identity. The local `first` binding remains within the expression root.

The runtime test called the existing `assert_selected` helper once on the same fixture and observed selected integer `7` within its 30,000-step cap. This only observes successful evaluation/discard for this fixture; it is not a general effect-order or source-adequacy theorem.

No refusal, missing route, empty image, shared local identity, pin change, or dependency change was observed. No new proof TODO was exposed. Original source/F5/production gates remain OPEN/BLOCKED. No disposable outputs were created or identified. Requested role/model was Luna/high; observed model/effort is UNKNOWN.
