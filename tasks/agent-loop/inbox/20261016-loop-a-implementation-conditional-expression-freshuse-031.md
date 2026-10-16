# I22 implementation result — same-root conditional FreshUse regressions

Packet: I22, dispatcher-selected bounded regression packet
Revision: 1 (frozen)
Baseline: `7eb2fe938b6075f0ebcd957024ef659c2ec6d6ff`
Requested role/model: Luna/high implementation
Observed runtime model/effort: UNKNOWN (runtime metadata unavailable)

## Authority and limits

Authority: approved module-expression source-owner G3 ordinary Name FreshUse/G4 mixed roots and top-level inference principles §1.1, which explicitly retains constraints from both conditional branches regardless of constant conditions.

This packet adds only tests. It makes no production change and establishes no general proof, principal-type claim, source-adequacy claim, or F5/production closure. Full Call/T/image and soundness/F5 parent gates remain independently OPEN/BLOCKED.

## Earlier evidence reused / adapted / rejected

- Reused the existing `expression_origin_uses_freshen_one_definition_at_distinct_value_shapes` test in `crates/yu-solver/tests/ordinary_expression_source.rs` (introduced by `342f27633`, “test: cover polymorphic expression-root freshening and execution”). It already asserts local Value and Effect rows and pairwise distinct FreshUse row identities for two uses under separate expression roots.
- Reused the `forward_alias_expression_uses_keep_distinct_fresh_instances` test in the same file (introduced by `6ab6882e0`, “test: cover forward alias inference and runtime”) as an existing separate-root/forward-target case. Those tests do not distinguish per-Name-use freshening from a hypothetical per-expression-root cache because each expression has a different root.
- Adapted the existing local-row assertions to two differently shaped Calls inside one authentic conditional expression root. The new test follows each actual branch Apply's callee source index to the actual resolved `id` Name, looks up FreshUse by that authentic Name occurrence, and compares local row identity across the two uses. It matches Calls to branch Apply occurrences without relying on Call order.
- Reused the existing runtime `assert_selected` helper, which creates one machine and applies the existing 30,000-step cap. The runtime regression calls it once for each condition.
- Rejected no prior accepted behavior and changed no existing assertion or production path. No inference/receiver rule, cache layer, ID, or source ordinal was invented.

## Exact frozen diffs from baseline

Only the two assigned test files and this inbox changed. Full literal baseline diffs:

```diff
diff --git a/crates/yu-solver/tests/ordinary_expression_source.rs b/crates/yu-solver/tests/ordinary_expression_source.rs
index 4e04a7af1..9378a3a64 100644
--- a/crates/yu-solver/tests/ordinary_expression_source.rs
+++ b/crates/yu-solver/tests/ordinary_expression_source.rs
@@ -136,6 +136,133 @@ fn expression_origin_uses_freshen_one_definition_at_distinct_value_shapes() {
     }
 }
 
+#[test]
+fn conditional_expression_branches_keep_distinct_fresh_instances() {
+    for condition in ["true", "false"] {
+        let text = format!(
+            r"my id x = x; if {condition}: id 1 else: id (\y -> y); my main = 7"
+        );
+        let hir = module(&text);
+        let candidate = CandidateInference::solve(hir.clone())
+            .unwrap_or_else(|error| panic!("{text}: {error:?}"));
+        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
+
+        let bindings: Vec<_> = hir
+            .items()
+            .iter()
+            .filter_map(|item| match item {
+                HirItem::Binding(binding) => Some(binding),
+                _ => None,
+            })
+            .collect();
+        assert_eq!(bindings.len(), 2, "no synthetic definitions: {text}");
+        let definition = bindings
+            .iter()
+            .find(|binding| binding.name().spelling() == "id")
+            .expect("the genuine id definition");
+        assert!(bindings.iter().any(|binding| binding.name().spelling() == "main"));
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
+            panic!("the conditional is one genuine expression root: {text}");
+        };
+        let root = hir
+            .expression_root(expression.occurrence())
+            .unwrap()
+            .expect("the original conditional expression root");
+        let owner = SourceRootId::Expression(root.clone());
+        let local = hir
+            .local_source_for(&owner)
+            .unwrap()
+            .expect("the authentic expression root retains its local source");
+        assert_eq!(root.occurrence(), expression.occurrence());
+
+        let conditionals: Vec<_> = local
+            .expressions()
+            .iter()
+            .filter(|expression| matches!(&expression.form, LocalSourceForm::If { .. }))
+            .collect();
+        let [conditional] = conditionals.as_slice() else {
+            panic!("one original conditional is retained: {text}");
+        };
+        let LocalSourceForm::If { arms, else_branch } = &conditional.form else {
+            unreachable!();
+        };
+        assert_eq!(arms.len(), 1);
+        assert!(else_branch.is_some());
+
+        let applications: Vec<_> = local
+            .expressions()
+            .iter()
+            .filter(|expression| matches!(&expression.form, LocalSourceForm::Apply { .. }))
+            .collect();
+        assert_eq!(applications.len(), 2, "both constant branches are retained: {text}");
+        assert_eq!(candidate.source_call_count(), 2, "both branch Calls are retained: {text}");
+        let calls: Vec<_> = (0..candidate.source_call_count())
+            .map(|index| candidate.source_call(index).unwrap())
+            .collect();
+        assert!(calls.iter().all(|call| call.owner() == &owner));
+        for application in &applications {
+            assert!(calls.iter().any(|call| {
+                &call.source().occurrence == &application.occurrence
+            }), "each Call keeps its actual branch Apply occurrence");
+        }
+
+        let mut name_occurrences = Vec::with_capacity(2);
+        let mut local_rows_by_use = Vec::with_capacity(2);
+        for application in applications {
+            let LocalSourceForm::Apply { callee, .. } = &application.form else {
+                unreachable!();
+            };
+            let callee = &local.expressions()[callee.ordinal() as usize];
+            let LocalSourceForm::Name {
+                spelling,
+                resolution: LocalSourceResolution::ModuleDef(resolved),
+            } = &callee.form
+            else {
+                panic!("each branch Call follows its actual callee to a resolved Name");
+            };
+            assert_eq!(spelling.as_ref(), "id");
+            assert_eq!(resolved, definition.id());
+
+            let fresh_use = candidate
+                .fresh_use(&callee.occurrence)
+                .expect("the original branch Name occurrence has a FreshUse route");
+            assert_eq!(fresh_use.occurrence(), &callee.occurrence);
+            name_occurrences.push(callee.occurrence.clone());
+
+            let local_rows: Vec<_> = fresh_use
+                .rows()
+                .filter(|row| row.source_row().is_local())
+                .collect();
+            for kind in [ComponentKind::Value, ComponentKind::Effect] {
+                assert!(
+                    local_rows.iter().any(|row| row.kind() == kind),
+                    "each branch FreshUse retains a local {kind:?} row"
+                );
+            }
+            local_rows_by_use.push(local_rows);
+        }
+        assert_ne!(name_occurrences[0], name_occurrences[1]);
+        let [first, second] = local_rows_by_use.as_slice() else {
+            panic!("the two authentic branch Name uses have separate FreshUse routes");
+        };
+        for row in first {
+            assert!(
+                second.iter().all(|other| !row.same_identity(other)),
+                "distinct branch FreshUse images do not share local row identity"
+            );
+        }
+    }
+}
+
 #[test]
 fn forward_alias_expression_uses_keep_distinct_fresh_instances() {
     let hir = module(r"alias 1; alias (\x -> x); my alias = id; my id x = x; my main = 7");
diff --git a/tools/inference-playground/tests/runtime_module_expressions.rs b/tools/inference-playground/tests/runtime_module_expressions.rs
index 4b4bade37..f8759b4ea 100644
--- a/tools/inference-playground/tests/runtime_module_expressions.rs
+++ b/tools/inference-playground/tests/runtime_module_expressions.rs
@@ -137,6 +137,16 @@ fn polymorphic_expression_results_are_discarded_before_selected_definition() {
     );
 }
 
+#[test]
+fn conditional_expression_results_are_discarded_before_selection() {
+    for condition in ["true", "false"] {
+        let source = format!(
+            r"my id x = x; if {condition}: id 1 else: id (\y -> y); my main = 7"
+        );
+        assert_selected(&source, "7");
+    }
+}
+
 #[test]
 fn forward_alias_expression_calls_discard_results_before_selection() {
*** End Patch
```

## Verification and exact results

Ran exactly the two assigned commands serially. Both passed, exit 0, one test passed each (each test internally checks `true` and `false`):

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --test ordinary_expression_source conditional_expression_branches_keep_distinct_fresh_instances -- --exact --test-threads=1`
   - `1 passed; 0 failed; 0 ignored; 0 measured; 9 filtered out`.
2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_module_expressions conditional_expression_results_are_discarded_before_selection -- --exact --test-threads=1`
   - `1 passed; 0 failed; 0 ignored; 0 measured; 14 filtered out`.

No other test, build, probe, benchmark, or random/source stress was run. No production files, existing assertions, expected outputs, board, shared records, or other inboxes were changed. No Git/index operation or delegation was performed.

## Frozen nine-input manifest

All nine packet pins matched at the pinned baseline:

- `crates/yu-solver/tests/ordinary_expression_source.rs` baseline: `7a5bb43ca530a507d65c5679d1a4a19eafb3127ae28f787c761a479266505ef0`; frozen output SHA-256: `2fc93916edaf2f5b479020eae6cdd38fa2a8d2d35f8bf6b1ab54100dfeed72f3`.
- `tools/inference-playground/tests/runtime_module_expressions.rs` baseline: `e86c45f917b6e0242d952223f839f6f1b07368e3ad69f8e0001bf91ea9d69176`; frozen output SHA-256: `485551b31825d53a8e6c27fdf7359f452e0690f35b6b9d4f5e57eb44659c07fc`.
- `crates/yu-solver/src/candidate_source.rs`: `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`.
- `crates/yu-solver/src/shadow_apply.rs`: `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`.
- `crates/yu-solver/src/lib.rs`: `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`.
- `tools/inference-playground/src/runtime/machine.rs`: `d9a8e14bd3eda8f5c40641beabac0ad862a4c04fc1173359934376681b731e77`.
- `tools/inference-playground/src/runtime/program.rs`: `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748`.
- `notes/design/2026-10-16-module-expression-source-owner.md`: `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`.
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- `tasks/agent-loop/inbox/20261016-loop-a-implementation-conditional-expression-freshuse-031.md`: this frozen receipt; its final SHA-256 is reported separately to Luna.

## Invariant, static evidence, and limits

The paired native fixture is the exact approved source:

`my id x = x; if CONDITION: id 1 else: id (\y -> y); my main = 7`

For both constant conditions, the passing regression observed no candidate conflicts, exactly the genuine `id`/`main` bindings, one authentic expression root with one `If` and two `Apply` nodes, two retained Calls owned by the same expression root, Call source occurrences matching the actual two branch Apply occurrences, and distinct original Name occurrences resolving to the genuine `id` definition. Each Name occurrence had a FreshUse route with local Value and Effect rows, and pairwise comparison found no shared local row identity between the two uses. This is executable observation only, not a theorem proof or principal-type claim.

The runtime regression ran exactly two machines through the existing `assert_selected` helper, one for each condition, with the existing 30,000-step bound per machine; each selected `main` as integer `7`. This fixture-specific completion check does not prove which branch executed or whole source adequacy.

No new TODO or proof dependency was exposed. The existing original theorem/F5/production gates remain open. No disposable output was created or identified for cleanup. Requested implementation setting was Luna/high; observed runtime setting remains UNKNOWN. Suggested successor is the board-selected single M1 R35 regression review, with the frozen artifact and this receipt as its inputs.
