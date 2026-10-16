# I26 recursive Expression owner implementation receipt

- Request: `20261016-loop-a-implementation-recursive-expression-owner-035`
- Revision: 1
- Baseline HEAD: `a4ec01a4c873c727d658a3314d8804e7e4d87d90`
- Requested/configured implementation role: Luna/high
- Observed model/effort: UNKNOWN (not exposed by the runtime)
- Claim: partial regression attempt stopped at the first prescribed test failure;
  no accepted-behavior result is claimed.
- Authority: approved module-expression G3/G4 and existing local-recursion
  contract. No production or proof change was made.

## Inputs, outputs, and stop

The primary's assignment states that all ten frozen input hashes were verified
against the dispatcher packet before launch. That packet's ten individual path
and hash entries were not included in the received task payload and were not
present in the current visible board, so this worker cannot reproduce the full
ten-entry manifest here. The two directly owned source-file pre-edit hashes
observed at launch were:

- `crates/yu-solver/tests/ordinary_expression_source.rs`:
  `2e789678e57131e8a73b18ebcd216e0a6e75b4a45c211161a5949a288fa79410`
- `tools/inference-playground/tests/runtime_module_expressions.rs`:
  `f1693e49067f9bbfcd354ee3b87094cddef3736b324ca6c2551f70582368afa6`

The receipt and source output hashes at freeze are:

- `crates/yu-solver/tests/ordinary_expression_source.rs`:
  `911c1764862002433a090795fdd8404c05d3c50d00a3d32a14a5134f0f6682ac`
- `tools/inference-playground/tests/runtime_module_expressions.rs`:
  `057030165810710cf0f883e320f2f08a05990bc4ccfae12ac8ae7c1e8ba2432c`
- this receipt: hash to be recorded by the primary after intake/freeze

The first assigned command was run exactly:

```text
timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --test ordinary_expression_source recursive_expression_uses_open_initializer_then_fresh_scheme -- --exact --test-threads=1
```

It exited 101. One test ran and failed, with 12 filtered out. Panic:

```text
the local loop initializer is the original conditional: { my loop condition = if condition: loop false else: 11; loop true }; my main = 7
```

The assumption that `loop_binding.initializer` directly indexes an `If` was
false. This was an assertion in the new test, not a solver error. Per the
packet's stop-at-first-failure condition, the second assigned runtime command
was NOT run. No retries, diagnosis probes, extra tests, or benchmarks were
performed. The test was not weakened or repaired after failure.

## Earlier evidence reused/adapted and remaining work

- Reused the existing `candidate_local_self_recursion` evidence that recursive
  initializer occurrences remain open while later nonrecursive local uses may
  have a FreshUse route. Adapted it to the original module Expression owner and
  actual Apply/Call occurrences.
- Reused I25's original Expression-root lookup pattern and runtime module
  `assert_selected` helper. The I25 integration is present at the supplied
  baseline and was not edited.
- The attempted typed-index path starts at the authentic Expression occurrence
  and block final-expression index. It needs the correct LocalSource index
  relationship for the local binding initializer before the test can establish
  the assigned contract.
- No source-adequacy, proof-closure, new semantics, or runtime execution-order
  claim is made. The runtime regression's result remains unverified.

## Complete literal baseline diff

```diff
diff --git a/crates/yu-solver/tests/ordinary_expression_source.rs b/crates/yu-solver/tests/ordinary_expression_source.rs
index fd7657753..9670c71fa 100644
--- a/crates/yu-solver/tests/ordinary_expression_source.rs
+++ b/crates/yu-solver/tests/ordinary_expression_source.rs
@@ -525,6 +525,124 @@ fn captured_local_expression_values_keep_original_constraints() {
     }
 }
 
+#[test]
+fn recursive_expression_uses_open_initializer_then_fresh_scheme() {
+    let template = "{ my loop condition = if condition: loop false else: 11; loop START }; my main = 7";
+
+    for start in ["true", "false"] {
+        let text = template.replace("START", start);
+        let hir = module(&text);
+        let candidate = CandidateInference::solve(hir.clone())
+            .unwrap_or_else(|error| panic!("{text}: {error:?}"));
+        assert!(candidate.candidate_conflicts().is_empty(), "{text}");
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
+            panic!("the recursive block remains one original Expression root: {text}");
+        };
+        let root = hir
+            .expression_root(expression.occurrence())
+            .unwrap()
+            .expect("the original recursive expression root");
+        let owner = SourceRootId::Expression(root.clone());
+        let local = hir
+            .local_source_for(&owner)
+            .unwrap()
+            .expect("the expression root retains its authentic LocalSource");
+        assert_eq!(root.occurrence(), expression.occurrence());
+
+        let loop_binding = local
+            .bindings()
+            .iter()
+            .find(|binding| binding.spelling.as_ref() == "loop")
+            .expect("the genuine local recursive loop binding");
+        let source_root = local
+            .expressions()
+            .iter()
+            .find(|source_expression| &source_expression.occurrence == expression.occurrence())
+            .expect("the LocalSource retains the original root occurrence");
+        let LocalSourceForm::Block { bindings, final_expression } =
+            &source_root.form
+        else {
+            panic!("the original expression source is a block: {text}");
+        };
+        assert_eq!(bindings.len(), 1, "the source block has its one local binding: {text}");
+        let LocalSourceForm::If { arms, .. } = &local.expressions()[loop_binding.initializer.ordinal() as usize].form
+        else {
+            panic!("the local loop initializer is the original conditional: {text}");
+        };
+        let [(_, recursive_call_index)] = arms.as_slice() else {
+            panic!("the initializer has its one authentic true arm: {text}");
+        };
+        let recursive_call = &local.expressions()[recursive_call_index.ordinal() as usize];
+        let final_call = &local.expressions()[final_expression.ordinal() as usize];
+        let LocalSourceForm::Apply { callee: recursive_callee_index, .. } = &recursive_call.form else {
+            panic!("the recursive branch retains its Apply: {text}");
+        };
+        let LocalSourceForm::Apply { callee: final_callee_index, .. } = &final_call.form else {
+            panic!("the block-final use retains its Apply: {text}");
+        };
+        let recursive_callee = &local.expressions()[recursive_callee_index.ordinal() as usize];
+        let final_callee = &local.expressions()[final_callee_index.ordinal() as usize];
+        for callee in [recursive_callee, final_callee] {
+            assert!(matches!(
+                &callee.form,
+                LocalSourceForm::Name {
+                    spelling,
+                    resolution: LocalSourceResolution::Local(resolved),
+                } if spelling.as_ref() == "loop" && resolved == &loop_binding.id
+            ), "both original callee Names resolve to the genuine local loop: {text}");
+        }
+
+        assert_eq!(candidate.source_call_count(), 2, "both original Calls are retained: {text}");
+        let calls: Vec<_> = (0..candidate.source_call_count())
+            .map(|index| candidate.source_call(index).unwrap())
+            .collect();
+        assert!(calls.iter().all(|call| call.owner() == &owner));
+        for application in [recursive_call, final_call] {
+            assert!(calls.iter().any(|call| {
+                &call.source().occurrence == &application.occurrence
+            }), "each authentic Apply occurrence has its Call: {text}");
+        }
+
+        assert!(
+            candidate.fresh_use(&recursive_callee.occurrence).is_none(),
+            "the recursive initializer Name remains open: {text}"
+        );
+        let fresh_use = candidate
+            .fresh_use(&final_callee.occurrence)
+            .expect("the later block-final Name uses the completed local scheme");
+        assert_eq!(fresh_use.occurrence(), &final_callee.occurrence);
+        let local_rows: Vec<_> = fresh_use
+            .rows()
+            .filter(|row| row.source_row().is_local())
+            .collect();
+        assert!(!local_rows.is_empty(), "the later FreshUse has local rows: {text}");
+        for kind in [ComponentKind::Value, ComponentKind::Effect] {
+            assert!(local_rows.iter().any(|row| row.kind() == kind),
+                "the later FreshUse has a local {kind:?} row: {text}");
+        }
+    }
+}
+
 #[test]
 fn forward_alias_expression_uses_keep_distinct_fresh_instances() {
     let hir = module(r"alias 1; alias (\x -> x); my alias = id; my id x = x; my main = 7");
diff --git a/tools/inference-playground/tests/runtime_module_expressions.rs b/tools/inference-playground/tests/runtime_module_expressions.rs
index 4c2a261ad..2c3b88a9c 100644
--- a/tools/inference-playground/tests/runtime_module_expressions.rs
+++ b/tools/inference-playground/tests/runtime_module_expressions.rs
@@ -152,6 +152,16 @@ fn local_scheme_expression_results_are_discarded_before_selection() {
     assert_selected(r#"{ my id x = x; my first = id 1; id "str" }; my main = 7"#, "7");
 }
 
+#[test]
+fn recursive_expression_completion_precedes_selected_definition() {
+    for start in ["true", "false"] {
+        let source = format!(
+            "{{ my loop condition = if condition: loop false else: 11; loop {start} }}; my main = 7"
+        );
+        assert_selected(&source, "7");
+    }
+}
+
 #[test]
 fn forward_alias_expression_calls_discard_results_before_selection() {
     assert_selected(
```

Primary follow-up: provide the exact ten-entry input manifest with the revised
dispatched repair/continuation packet. This worker does not repair the failed
test or infer the missing LocalSource ownership/index relationship. The write
lease should remain stopped until a revised exact implementation assignment is
issued.
