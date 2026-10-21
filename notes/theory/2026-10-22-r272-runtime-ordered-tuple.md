# R272 — ordered Tuple runtime construction

Status: provisional runtime implementation checkpoint; primary-only and unreviewed. The parent Yulang2 sample and proof-backed compiler/evaluator goals remain open.

## Parent application

R270 and R271 preserve Tuple children through candidate traversal and the source Value-reference graph. R256 identifies the next source-owner obstruction: runtime compilation rejects `LocalSourceForm::Tuple`, and runtime values cannot represent products. R149 requires arbitrary finite ordered products and left-to-right evaluation, including correct behavior when evaluation suspends or captures a continuation.

This packet adds provisional runtime construction and preservation of already-evaluated tuple prefixes. It does not establish public type support or prove source/native correspondence.

## Implementation and evidence

- `LocalSourceForm::Tuple` compiles to an ordered runtime instruction; traversal used by runtime source inspection includes all children.
- Tuple evaluation advances one child at a time. Each received child, including its interface and view, is stored in an immutable node in the machine-owned prefix arena. Continuation frame copies retain only the prefix handle, so a resumed branch shares the prior nodes and appends a new one.
- `ordered_tuple_prefix_survives_resumes_without_replaying_prior_children` passes with candidate inference enabled. It resumes effects in two ordered tuple children and observes `(42, 10, 20)` in source order.
- `nested_tuple_runtime_values_keep_source_element_order` and `tuple_elements_retain_their_received_views` pass for nested and direct values.
- `execute_renders_nested_ordered_tuple_values` passes for nested output `(1, (2, 3), 4)\n` and singleton output `(1,)\n`.
- `cargo test -p yu-playground --test runtime_resume`: 21 passed. `cargo test -p yu-playground --lib tuple`: 2 passed. `git diff --check` and sprint static check pass.
- The build repeats existing HIR/solver warnings and reports the pre-existing `pinned_stdlib::source_for_module` test-only-use warning; the active diff adds no warning. `runtime_resume.rs` also has a pre-existing unnecessary `mut` warning outside the added tests.

No independent review is available under the user's solo-work instruction. This does not establish complete Tuple inference, public closed schemes, source/native proof, imports, host integration, exact R149 outputs, soundness, principality or production. Runtime and candidate observations remain provisional.
