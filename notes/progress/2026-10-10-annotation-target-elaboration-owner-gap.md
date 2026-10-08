# Annotation target elaboration owner gap

Date: 2026-10-10
Status: non-authoritative source-to-code owner map; no semantic or implementation decision
Baseline: `9c87d4f1e` on `research/simple-sub-intrusion`
Scope: parsed source annotation types, ordinary typed target construction, and the existing closed-scheme boundary

## Result

The approved expression annotation decision identifies the boundary behavior,
but the current production path has no semantic elaborator from a parsed
`TypeExpression` to a completed annotation target or ordinary public root.
This is an earlier owner gap than the already recorded annotation-to-Direct
root/proof correspondence gap. It does not select an API or establish that
every annotation must pass through Direct.

Syntax production is present: expression `as Type` parsing is owned by
`crates/yu-syntax/src/expression/tails/type_annotation.rs`, while grouped
parameter annotations are parsed by `crates/yu-syntax/src/pattern/mod.rs`.
HIR association retains expression annotation structure in
`crates/yu-hir/src/lib.rs`, but `ResolvedExpr` has no annotation/check form.
`lower_simple_chain` in `crates/yu-hir/src/module.rs` admits only a childless
leaf and rejects the annotated expression before solver constraints. The
grouped annotated-formal route also fails ordinary header admission.

The shadow annotation occurrence and parameter-incidence records preserve
syntax identity and positions, but their typed correspondence remains
`PendingTypedPortAndProfile`. They do not supply the current endpoint, target,
scope/profile, or realization evidence. In `yu-types`, `ClosedValueScheme` is
an already-typed F5 representation. Its production finalizers consume semantic
drafts built from inferred F5 component rows; no source `TypeExpression` input
or annotation-target elaboration was found. Existing constructors therefore
do not close this source boundary by themselves.

## Owning boundary

Under SRC §3.2(6), the source annotation owner must elaborate the written type
as a completed typed contract in its original scope. The expression owner
supplies the exact current endpoint; a Direct input root is available only
when that exact ordinary public-root record already exists. The public-root
owner must construct the typed target as an ordinary root before Direct can
consume it. Direct checks supplied roots and finite evidence; it does not
construct the target. Existing scopes and prior evidence are retained, and
local boundary evidence is added. An executed conversion remains owned by the
source constructor/result handle rather than being encoded as proof-only
inclusion.

The PE §4/§6.2 unannotated-`id` route can derive its selected `Any` target
root and Top proof when that target is already assumed. It does not define a
general elaborator for a written Type expression, and its unannotated
extraction cannot stand in for a final annotation that selects a different
root.

## Next evidence and limits

The smallest useful application is one authentic annotated occurrence with:
the exact written Type and original scope; an already available source
endpoint/root; an independently completed ordinary target-root record; and
the preserved prior-plus-local evidence and outward target. Keep proof-only
and executed-conversion examples separate. If no current source occurrence
has an authentic endpoint/public root, trace that earlier owner first.

This is owner localization only. It authorizes no implementation, does not
close Hreg or any aggregate inference/principality gate, and does not promote
the annotation or Direct bridge to production. No tests, builds, or probes
were run. Pending question directories were not read or used.
