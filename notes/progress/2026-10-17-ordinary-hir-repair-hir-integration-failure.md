# HIR integration run stopped on one assertion failure

Sprint rev6, contract SHA-256
`3d3f8fd3643bf3b1d27793f470f19b430779bc24f1698788d89295e770c258a4`.
After the focused HIR unit command passed 8/8, Luna ran the first integration
command exactly once:

```text
cargo test -p yu-hir --features shadow --test ordinary_application_admission
exit 101; elapsed 2.315s
```

It compiled successfully with the same three warning classes already recorded.
The integration binary ran 9 tests: **8 passed, 1 failed**.

Passing tests:

- `ambiguous_operand_has_one_owned_event_and_is_referenced_once_per_descendant_list`
- `grouped_unresolved_spines_forward_errors_without_changing_lists`
- `comma_bearing_call_tail_refuses_before_operand_resolution`
- `grouped_unresolved_nodes_keep_exact_distinct_parse_owned_keys`
- `fixed_source_is_admitted_through_ordinary_lowering`
- `duplicate_event_precedes_staged_operand_diagnostics_and_lists_use_final_dense_ids`
- `call_tail_group_and_nested_group_keep_distinct_occurrences`
- `unresolved_descendant_errors_are_materialized_once_per_apply_list`

Failure:

- `unsupported_and_recovery_bodies_keep_the_whole_body_refusal`

Exact failure: `crates/yu-hir/tests/ordinary_application_admission.rs:326` asserted
that `recovered.errors()` contains a `HirErrorKind::UnsupportedExpression`;
assertion was false.

Per rev6, execution stopped at the first assertion failure. Solver integration
was not started; there is no retry or modified expectation. Post-run review of
the exact receipt is required. No theorem condition closed: 0.
