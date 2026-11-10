# Cycle84: source identity under fresh name allocation

Status: Draft proof-interface design, 2026-11-10. Authority: spec/06-roles.md
§6.3 gives related-type equations and conjunction/order independence. It does
not prescribe the invocation key or fresh-name allocator.

## Boundary found before extending declaration lowering

`Roles.Impl.constraints : List Roles.Goal` retains core where goals, but not the
receiver and associated-output source identities carried by
`CommonRoleAssociatedClauseExtraction.Clause`. `Roles.AssocImpl.assoc` is a list
of declaration bodies, not those where-clause equations. Therefore projecting
core constraints directly is not an adequate implementation of the requested
Parent/Left/Right source bridge. Do not silently invent missing source identities
or imply that declaration extraction is complete. Existing invocation/binder
questions remain open; no new language choice is made here.

## Bounded goal

Close the complete finite-source alpha-renaming interface: arbitrary injective
renaming of original receiver/output names and input names preserves and reflects
independent derivations, name-domain models, validation, and the actual outer
readiness result after reallocation and resaturation. This is a necessary
capture-avoidance contract for later source lowering, not that lowering itself.

Data: `renameEquation f`, `renameClause f`, `renameSource f`, `renameInput f`.
Role IDs, associated member IDs and scoped structural Goal binders are unchanged.

Independent judgments remain cycle83's `Derives`, `Models`, `ValidSource`, and
`Discharges`, never an equality asserted about a successful run.

Theorems, for all env/roles/src/input/name/head and injective f:
- Derives env roles (renameSource f src) (renameInput f input) (f name) head
  iff Derives env roles src input name head.
- Models on renamed source iff Models on original source.
- With explicit core wf and associated awf, runSource on renamed source/input
  equals runSource on original source/input.

Forward derivation transport needs no injectivity. Reflection does: a concrete
collision regression will show readiness can change when independent names are
merged. This is source-identity aliasing, not permission to choose which runtime
invocations share a source name. Neither parser adequacy, dynamic child closure,
full ordinary inference nor full B4 is claimed.
