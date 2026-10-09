# Question receipt — source-annotation-any-name-resolution q1

Question revision: `q1`
Answer draft: `source-annotation-any-name-resolution-q1-answer` / `d1`
Integration commit: `b0575d9b3` (`questions: approve builtin any type name`)

## Validation and outcome

The question, complete draft, and approved answer were checked together. Their
IDs/revisions and worktree/branch match; the approved answer embeds the exact
draft content and records the explicit approval quote `「うん」`. The bundle
matches its committed bytes at integration.

Accepted and consumed: lowercase `any` resolves as a built-in Type name without
a declaration or import; builtin resolution takes precedence and cannot be
shadowed by a same-named type declaration/import/alias. No uppercase `Any`
builtin alias is added. This is a name-resolution decision only.

This does not establish ordinary `Value(Any)` root formation, membership
guards/evidence, the hereditary Top law, Direct proof, annotation source
acceptance, compiler implementation, production routing, or F5 cutover.
Applied in `notes/design/2026-10-10-source-annotation-any-name-design.md` and
tracked in `notes/design/INDEX.md` and `tasks/current.md`.
