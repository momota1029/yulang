# Contextual identity relation foundation (2026-10-10)

The private candidate now uses one typed relation authority for identity
contexts. Relation keys include typed canonical endpoints and a context handle;
incoming constraint occurrences remain separate origins. Derived and ordered
opposite-bound replay dependencies own semantic reachability, while transport
records fresh-use provenance without making a use's later conflict a semantic
consequence of its generic template.

The contextual graph now owns conflict replay. The duplicate typed-pair
adjacency and its undo/accounting path were removed. Bound origins and their
transfer through extrusion and qualifying intrusion remain explicit. Relation
creation, origins, bounds, dependencies, adjacency and rollback are covered,
including raw/canonical roots and independent fresh uses.

Review: the pre-write spec audit approved the identity-only foundation within
the contextual attachment gate. Post-write compiler-referee and
performance-auditor delta reviews found no remaining concrete issue. An
architect adjudicated removal of the duplicate adjacency as the selected
single-relation-authority design, not a new user decision.

Focused verification passed:

- `candidate_context::tests`: 8 passed.
- `candidate_effect::tests`: 25 passed.
- `candidate_intrusion::tests`: 5 passed.
- `candidate_annotated_function_formals`: 10 passed.
- `candidate_annotated_primitive_formals`: 21 passed.
- `simple_sub_local_source_retirement`: 7 passed.
- `rustfmt --edition 2024 --check` on the two new contextual relation files.
- `git diff --check` on tracked changed solver paths.

No timing measurements were run; no speedup is claimed. This foundation uses
identity contexts only. Concrete formal attachment operations, filters and
residual recipes, exact two-cycle acceleration and late-edge invalidation
remain open. Concrete and closed-empty formal effect rows remain explicitly
unsupported. Complete Call, full effect hygiene, soundness, principality,
ordinary/default publication and F5 retirement remain open.

Next: add the selected source-owned attachment/context operations to this
relation authority, then implement and verify the approved two-cycle lifecycle
without weakening the current formal-row refusal or expanding source admission.
