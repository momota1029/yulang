# I29 recursive polymorphic Expression regression receipt

- Request: `20261016-loop-a-implementation-recursive-polymorphic-expression-040`
- Revision: 1
- Baseline HEAD: `ddaf10997fc5cc3e0cedc7e5a2c64d2c258c3fde`
- Requested/configured implementer: Luna/high
- Observed model/effort: UNKNOWN (not exposed by the runtime)
- Claim: bounded accepted-behavior regression evidence only; no proof or
  production-gate closure.
- Authority: approved G3/G4 module-expression owner and runtime handoff,
  established local-recursion contract, and efficiency principle §2.

## Frozen eleven-pin manifest

All eleven inputs matched before editing and at freeze:

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/tests/ordinary_expression_source.rs` | `8da42133b372be44c3a5ef7f186b1306f2860177417e72e9397945beff1ea7f1` |
| `tools/inference-playground/tests/runtime_module_expressions.rs` | `057030165810710cf0f883e320f2f08a05990bc4ccfae12ac8ae7c1e8ba2432c` |
| `crates/yu-solver/tests/candidate_local_self_recursion.rs` | `a6406f3eef2b25844272da9cbe121277001760d004f733029dcc3f600aa79c7a` |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` |
| `crates/yu-solver/src/candidate_scheme.rs` | `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a854331c9da334bf` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `tools/inference-playground/src/runtime/machine.rs` | `ce8a58b934591a0898487c5ea93f821a23054fdc68fdaf02f6d003754e665ce6` |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` |
| `notes/design/2026-10-16-module-expression-source-owner.md` | `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

## Implementation and verification

The native test `recursive_expression_later_uses_have_distinct_fresh_instances`
uses the exact fixture with one authentic Expression owner and only `main` as a
module binding. It follows the original loop initializer Lambda to its typed
body and If else branch for the recursive call, and follows the genuine `first`
initializer and Block final-expression indices for the two later calls. All
three original Name occurrences resolve to the same genuine local binding; all
three Apply occurrences have Calls under the same owner. The recursive Name has
no FreshUse, while each later Name has its own retained route with local Value
and Effect images; the two later local row sets have disjoint identities. The
candidate has no conflicts.

The runtime test `recursive_polymorphic_expression_results_are_discarded` uses
the existing bounded `assert_selected` helper and expects selected integer `7`.
It does not claim that the recursive branch executes.

The two assigned commands ran serially:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --test ordinary_expression_source recursive_expression_later_uses_have_distinct_fresh_instances -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 13 filtered out`.

2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_module_expressions recursive_polymorphic_expression_results_are_discarded -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 17 filtered out`.

No warning, timeout, owner/identity/route mismatch, dependency change, extra
test, or benchmark was observed. Benchmark budget was 0 processes / 0 samples.

## Reused evidence and limits

- Reused the established Definition-root local-recursion contract that a
  recursive initializer occurrence remains open while later uses can receive
  distinct FreshUse images.
- Reused I23's actual local Name-to-FreshUse and local Value/Effect row checks,
  and I26's Expression-root owner and typed-child traversal patterns.
- No language behavior, solver API, production implementation, or expected
  result was changed. The tests do not prove recursive-branch execution,
  generalization in general, source adequacy, or any open source/theorem/
  Context-MODEL/N1/F5/production gate.

## Complete literal baseline diff

```diff
diff --git a/crates/yu-solver/tests/ordinary_expression_source.rs b/crates/yu-solver/tests/ordinary_expression_source.rs
index cae51e383..fb9e8c47c 100644
--- a/crates/yu-solver/tests/ordinary_expression_source.rs
+++ b/crates/yu-solver/tests/ordinary_expression_source.rs
@@ -653,6 +653,156 @@ fn recursive_expression_uses_open_initializer_then_fresh_scheme() {
     }
 }
 
+#[test]
+fn recursive_expression_later_uses_have_distinct_fresh_instances() {
+    let text = r#"{ my loop x = if true: x else: loop x; my first = loop 1; loop "str" }; my main = 7"#;
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
+    assert_eq!(module_bindings.len(), 1, "no synthetic module binding: {text}");
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
+        panic!("the local recursive block remains one Expression root: {text}");
+    };
+    let root = hir
+        .expression_root(expression.occurrence())
+        .unwrap()
+        .expect("the original recursive expression root");
+    let owner = SourceRootId::Expression(root.clone());
+    let local = hir
+        .local_source_for(&owner)
+        .unwrap()
+        .expect("the authentic Expression owner retains LocalSource");
+    assert_eq!(root.occurrence(), expression.occurrence());
+
+    let loop_binding = local
+        .bindings()
+        .iter()
+        .find(|binding| binding.spelling.as_ref() == "loop")
+        .expect("the genuine local recursive loop binding");
+    let first_binding = local
+        .bindings()
+        .iter()
+        .find(|binding| binding.spelling.as_ref() == "first")
+        .expect("the genuine local first binding");
+    let source_root = local
+        .expressions()
+        .iter()
+        .find(|source_expression| &source_expression.occurrence == expression.occurrence())
+        .expect("LocalSource retains the original root occurrence");
+    let LocalSourceForm::Block { final_expression, .. } = &source_root.form else {
+        panic!("the original expression source is the block: {text}");
+    };
+    let LocalSourceForm::Lambda { parameter, body } =
+        &local.expressions()[loop_binding.initializer.ordinal() as usize].form
+    else {
+        panic!("the loop initializer retains its named parameter Lambda: {text}");
+    };
+    let [binding_parameter] = loop_binding.parameters.as_slice() else {
+        panic!("the loop binding has its one original parameter: {text}");
+    };
+    assert_eq!(parameter.id, binding_parameter.id);
+    assert_eq!(parameter.spelling, binding_parameter.spelling);
+    let LocalSourceForm::If { arms, else_branch } =
+        &local.expressions()[body.ordinal() as usize].form
+    else {
+        panic!("the named loop body is the original conditional: {text}");
+    };
+    assert_eq!(arms.len(), 1);
+    let recursive_call_index = else_branch
+        .as_ref()
+        .expect("the recursive application is in the original else branch");
+    let recursive_call = &local.expressions()[recursive_call_index.ordinal() as usize];
+    let first_call = &local.expressions()[first_binding.initializer.ordinal() as usize];
+    let final_call = &local.expressions()[final_expression.ordinal() as usize];
+    let LocalSourceForm::Apply { callee: recursive_callee_index, .. } = &recursive_call.form else {
+        panic!("the recursive else branch retains its Apply: {text}");
+    };
+    let LocalSourceForm::Apply { callee: first_callee_index, .. } = &first_call.form else {
+        panic!("the first later local use retains its Apply: {text}");
+    };
+    let LocalSourceForm::Apply { callee: final_callee_index, .. } = &final_call.form else {
+        panic!("the block-final later use retains its Apply: {text}");
+    };
+    let recursive_callee = &local.expressions()[recursive_callee_index.ordinal() as usize];
+    let first_callee = &local.expressions()[first_callee_index.ordinal() as usize];
+    let final_callee = &local.expressions()[final_callee_index.ordinal() as usize];
+    for callee in [recursive_callee, first_callee, final_callee] {
+        assert!(matches!(
+            &callee.form,
+            LocalSourceForm::Name {
+                spelling,
+                resolution: LocalSourceResolution::Local(resolved),
+            } if spelling.as_ref() == "loop" && resolved == &loop_binding.id
+        ), "all original loop Names resolve to the genuine local binding: {text}");
+    }
+    assert_ne!(recursive_callee.occurrence, first_callee.occurrence);
+    assert_ne!(first_callee.occurrence, final_callee.occurrence);
+    assert_ne!(recursive_callee.occurrence, final_callee.occurrence);
+
+    let applications = [recursive_call, first_call, final_call];
+    assert_eq!(candidate.source_call_count(), applications.len());
+    let calls: Vec<_> = (0..candidate.source_call_count())
+        .map(|index| candidate.source_call(index).unwrap())
+        .collect();
+    assert!(calls.iter().all(|call| call.owner() == &owner));
+    for application in applications {
+        assert!(calls.iter().any(|call| {
+            &call.source().occurrence == &application.occurrence
+        }), "each original Apply occurrence retains its Call: {text}");
+    }
+
+    assert!(
+        candidate.fresh_use(&recursive_callee.occurrence).is_none(),
+        "the recursive initializer Name remains open: {text}"
+    );
+    let mut later_local_rows = Vec::with_capacity(2);
+    for callee in [first_callee, final_callee] {
+        let fresh_use = candidate
+            .fresh_use(&callee.occurrence)
+            .expect("each later original local Name retains its FreshUse route");
+        assert_eq!(fresh_use.occurrence(), &callee.occurrence);
+        let local_rows: Vec<_> = fresh_use
+            .rows()
+            .filter(|row| row.source_row().is_local())
+            .collect();
+        assert!(!local_rows.is_empty(), "each later FreshUse has local rows: {text}");
+        for kind in [ComponentKind::Value, ComponentKind::Effect] {
+            assert!(local_rows.iter().any(|row| row.kind() == kind),
+                "each later FreshUse has a local {kind:?} row: {text}");
+        }
+        later_local_rows.push(local_rows);
+    }
+    let [first_rows, final_rows] = later_local_rows.as_slice() else {
+        panic!("both later local uses retain their own FreshUse routes");
+    };
+    for row in first_rows {
+        assert!(
+            final_rows.iter().all(|other| !row.same_identity(other)),
+            "later local uses have distinct local row identities: {text}"
+        );
+    }
+}
+
 #[test]
 fn forward_alias_expression_uses_keep_distinct_fresh_instances() {
     let hir = module(r"alias 1; alias (\x -> x); my alias = id; my id x = x; my main = 7");
diff --git a/tools/inference-playground/tests/runtime_module_expressions.rs b/tools/inference-playground/tests/runtime_module_expressions.rs
index 2c3b88a9c..58fae9323 100644
--- a/tools/inference-playground/tests/runtime_module_expressions.rs
+++ b/tools/inference-playground/tests/runtime_module_expressions.rs
@@ -162,6 +162,14 @@ fn recursive_expression_completion_precedes_selected_definition() {
     }
 }
 
+#[test]
+fn recursive_polymorphic_expression_results_are_discarded() {
+    assert_selected(
+        r#"{ my loop x = if true: x else: loop x; my first = loop 1; loop "str" }; my main = 7"#,
+        "7",
+    );
+}
+
 #[test]
 fn forward_alias_expression_calls_discard_results_before_selection() {
     assert_selected(
```

## Frozen output hashes and next owner

- `crates/yu-solver/tests/ordinary_expression_source.rs` SHA-256:
  `c223c913fcf8a9101fbc527979bbd104db68c1191ab53bf2f3c47dcd2fa53918`
- `tools/inference-playground/tests/runtime_module_expressions.rs` SHA-256:
  `8eaad5f05b2592ce068f6ed2ed2e7934eaad68e368f4f60b8e3a60e59cf9ff1f`
- This receipt SHA-256: recorded after freeze by the primary.

The lease ends with this frozen regression submission. Primary owns proposed
R43 review, record updates, and all Git operations.


## Revision 2 — manifest pin correction (append-only)

- Request: `20261016-loop-a-implementation-recursive-polymorphic-expression-040`
- Revision: 2
- Preserved revision 1 SHA-256: `11ce7c8b85e7232db961893afdaf1838b4c9272454e1bb474e485b58578283c5`
- Preserved revision 1 byte length: `13162`
- Verified `crates/yu-solver/src/shadow_apply.rs` SHA-256: `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`

This revision supersedes only the `shadow_apply.rs` pin printed in revision 1, which omitted `69` in the digest. The corrected pin above matches the current file and the original dispatcher-validated baseline. Every other manifest entry, test addition, command, result, and claim remains unchanged. No tests or other checks were rerun for this metadata correction.

The frozen test outputs remain `crates/yu-solver/tests/ordinary_expression_source.rs` SHA-256 `c223c913fcf8a9101fbc527979bbd104db68c1191ab53bf2f3c47dcd2fa53918` and `tools/inference-playground/tests/runtime_module_expressions.rs` SHA-256 `8eaad5f05b2592ce068f6ed2ed2e7934eaad68e368f4f60b8e3a60e59cf9ff1f`.
