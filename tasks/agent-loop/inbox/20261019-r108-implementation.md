# R108 implementation receipt

Applied exactly the two authorized reference corrections in `crates/yu-hir/src/tests/shadow_method_role_source.rs`: `declaration.node()` is compared with `&impl_node`, and `child.as_node()` is compared directly with `Some(&impl_node)`. No other source bytes were intentionally changed.

Pre-edit source SHA-256: `3519e4a5e3cf3fa2a855125f6ea739e6765fea0dd34b0c2c881088a129b259f4`. The source retains its final LF; no source literal, assertion meaning, expected behavior, formatting or production code was changed.

No test, build, compiler/runtime/CLI, formatter or Git command was run. Implementation is write-stopped; output awaits fresh post-output reviews.
