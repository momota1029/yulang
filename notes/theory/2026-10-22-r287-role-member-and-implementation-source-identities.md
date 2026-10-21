# R287 outcome — role members and implementation source identities

Role declaration bodies now expose direct member source occurrences in declaration order. Each member key is parent-qualified by its `SourceRoleId`, and its syntax kind, exact range and text are retained. Associated type declarations remain distinct from binding members by syntax kind.

Standalone root `ImplDeclaration`s now have `(ModuleId, ImplDeclaration SourceNodeKey)` identities. The sidecar retains the exact target/input and role TypeExpression owners and optional body. Body entries preserve ordered where clauses and member declarations; member keys are parent-qualified by the implementation identity. Two same-spelling impl heads still produce distinct source identities.

These are parse/source identities only. No imported role resolution, type-head normalization, member signature validation, implementation conformance, candidate selection, constraints, execution or theorem closure is added. Nested attached impl declarations and role/member semantic lowering remain open.

Passed:

- `cargo test -p yu-hir --features shadow role_identity_uses_module_and_exact_parse_occurrence -- --nocapture`
- `cargo test -p yu-hir --features shadow implementation_identity_retains_target_role_and_ordered_body_owners -- --nocapture`
- `cargo test -p yu-solver --features shadow-apply-candidate --no-run`
- `cargo check -p yu-hir` (ordinary non-shadow build)
- `python3 tools/agent_sprint.py check`
- `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'`
- `git diff --check`

Solo-authored, unreviewed. The unchanged R149 samples still have no runtime evidence. Role import resolution and identity-bound constraints remain the next dependency.
