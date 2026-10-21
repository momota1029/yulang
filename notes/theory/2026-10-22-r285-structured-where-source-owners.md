# R285 outcome — structured where-clause source owners

`LocalSourceWhereClause` now retains three distinct parse-owned identities: the whole clause, its constrained subject `TypeExpression`, and its role `TypeExpression`. Each has an exact source range and text. This keeps applications such as `Fold 'item` together as the role expression and supplies source anchors for a later identity resolver. No role/type DefId is assigned here.

The carrier validates the clause's exact child form (`where`, subject type expression, colon, role type expression), rejects recovery or unexpected children, retains source order, and accounts for the copied text and nodes in its retained-size estimate. Candidate preflight continues to fail closed while identity-bound constraint generation is absent.

Checks passed:

- `cargo test -p yu-hir --features shadow declaration_where_preamble_is_retained_without_becoming_an_expression -- --nocapture`
- `cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_preflight_does_not_drop_retained_declaration_prerequisites -- --nocapture`
- `cargo test -p yu-solver --features shadow-apply-candidate --no-run`
- `python3 tools/agent_sprint.py check`
- `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'`
- `git diff --check`

Solo-authored, unreviewed source evidence. The unchanged Yulang2 samples still do not execute. Exact role declaration identity/admission, constraint generation/propagation, runtime selection, source/native proof and production remain open. `[io]` in contravariant position retains its approved open-row meaning `[io,'e]`.
