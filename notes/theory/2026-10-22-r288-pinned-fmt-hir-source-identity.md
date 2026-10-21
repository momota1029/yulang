# R288 outcome — source-only indexing for pinned fmt roles and implementations

The exact blob-checked Yulang2 `lib/std/core/fmt.yu` parses with no syntax diagnostics. Ordinary `lower_module_with_local_source` still returns `StructuralProjection`, first observed when the prefix reaches `my format_fill(spec: format_spec): str = case spec.fill`. Therefore module role/implementation indexing cannot depend on every unrelated value binding already having a candidate carrier.

Added a source-only `SourceRoleImplIndex` over the caller-supplied `ModuleIdentity` and exact `ParsedFile`. It retains source-keyed role and implementation declarations without asserting that the supplied identity authenticates import provenance. The focused pinned-fmt test now verifies the exact `Display` role members (`show`, default `say`, `note`), the two-parameter tuple `Display` implementation, ordered where/member entries, exact source slices, module identity and parent-qualified member identity.

Passed:

- `cargo test -p yu-playground --lib pinned_fmt_role_and_tuple_impl_keep_exact_module_and_parse_positions -- --nocapture`

Still OPEN: authentic import graph and visibility, type-head normalization, member/conformance checking, candidate selection, constraints, ordinary HIR body support, unchanged Types/Console execution and output, source/native correspondence, A/B proof gates and production. The experiment proves only this source-carrier boundary.

Solo-authored, unreviewed; no independent review ran.

Additional verification passed: `cargo test -p yu-playground --lib` (29 passed), `cargo check -p yu-hir`, `python3 tools/agent_sprint.py check`, and `git diff --check`.
