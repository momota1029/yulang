# R286 outcome — source-qualified role declaration identity

The nonshipping HIR sidecar now exposes role declarations with identity `(ModuleId, SourceNodeKey(RoleDeclaration))`. It preserves visibility, the complete generic role head (including source spelling/range/key), declaration range, and the optional body node's source key/range/text. A test with two `Pick` declarations confirms equal spellings retain distinct parse identities and exact source correspondence.

This does not resolve imported names, define semantic role membership, parse member signatures, create implementation/member IDs, select an implementation, or change the ordinary `HirItem::Error` behavior for unsupported role declarations. It supplies the exact declaration owner on which those steps can build. Solo-authored and unreviewed.

Passed:

- `cargo test -p yu-hir --features shadow role_identity_uses_module_and_exact_parse_occurrence -- --nocapture`
- `cargo test -p yu-solver --features shadow-apply-candidate --no-run`
- `python3 tools/agent_sprint.py check`
- `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'` (57 tests)
- `git diff --check`
