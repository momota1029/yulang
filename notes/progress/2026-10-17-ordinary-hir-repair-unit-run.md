# Focused HIR unit run after rev6 repair

Sprint rev6, contract SHA-256
`3d3f8fd3643bf3b1d27793f470f19b430779bc24f1698788d89295e770c258a4`.
After CLEAN compiler delta review, Luna ran the one explicitly authorized
post-repair invocation exactly once:

```text
cargo test -p yu-hir --features shadow --lib module::tests::
exit 0; elapsed 4.30s
```

Result: 8 passed, 0 failed, 0 ignored, 122 filtered. The three required
falsifiers ran and passed:

- `module::tests::admission_root_collision_is_rejected_without_overwriting_or_publishing`
- `module::tests::evaluation_classification_is_private_and_frozen_on_bindings`
- `module::tests::many_simple_admissions_finalize_at_their_exact_item_indices`

The other five executed tests were parameter trait surfaces (2), distinct
zero-width occurrence IDs, DefId hash payload identity, and recovery partition
visitation/emission. No test failed. Compiler emitted three existing warning
classes: unread `AssociationProvenance::{Token,Synthetic}` payloads and unused
`replace_admission_root`; no warning was promoted to an error.

This command establishes execution evidence for the named HIR unit assertions
only. The two integration commands and fresh post-run regression review remain
pending. No parent theorem condition closed (0).
