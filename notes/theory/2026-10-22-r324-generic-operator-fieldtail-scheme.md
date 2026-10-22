# R324 — generic operator FieldTail scheme boundary

## Parent outcome

The unchanged Yulang2 Types sample must proceed through ordinary inference and execution without sample, semantic, output, quantifier, or source-domain changes. R323 projected exact `Display.say`, tuple `Display.show`, and its exact `Display int` / `Display str` prerequisite overrides, then added a solver consumer that maps a selected member through one FreshUse.

## Observed obstruction

The R323 candidate worklist maps source FieldTail obligations from each `OperatorFreshUse` through that use's four row indices. It reaches the pinned `lib/std/core/ops.yu` infix `+` body `\\x -> \\y -> x.add y`. At this provider-template stage, `x` has no positive source shape, so the complete-evidence selection gate correctly returns deferred. The same source obligation is attached to an abstract provider graph and must survive until a concrete consumer contributes receiver bounds.

The key distinction is lifecycle: a graph FieldTail can be (a) source syntax inside a reusable provider template or (b) an active instance whose FreshUse rows belong to one concrete consumer. R323 handles (b) once an active instance is identified. It does not yet transport (a) through enclosing candidate schemes without making it active too early or dropping its source identity.

## Required construction

Trace the exact provider `ExpressionRootId`, nested FieldTail owner/occurrence, operator-use owner and occurrence, parent candidate graph capture, and eventual consumer. Preserve the original source obligation and role candidates while transporting its four interface rows through the same FreshUse used by the enclosing provider. Activate implementation selection only after consumer receiver and where evidence is complete. Separate uses must get separate maps and constraints.

This is a candidate construction and source correspondence problem. A passing test cannot establish the general FreshUse preservation theorem or source/native A/B bridge. `[io]` in a contravariant position remains `[io,'e]`, so `[state]` is allowed.

## Status

OPEN. Exact override projection and direct member FreshUse dispatch are implemented and checkpointed at `c49d1bf44`. The unchanged Types candidate remains deferred on generic operator `x.add`; no successful sample inference, independent review, theorem closure, R149 completion, or production admission is claimed. The user prohibits subagents, so this continuation is serial and unreviewed.

## R324 source-owner trace

The five retained `+` uses in this pinned Types candidate world are owned by member roots in `lib/std/core/fmt.yu`: the role/default and implementation members, at source-use ordinals 52, 56, 58, 61, and 63. They all use the exact imported `+` provider expression root at ordinal 44, whose `x.add` FieldTail is source occurrence 82. Therefore the FieldTail is nested in member templates, not an unrelated unused module expression. The first blocked template is role-owned `add`; its receiver has no positive shape or positive/negative frontier evidence, while the Add implementation inventory is complete. This is consistent with `Display.say`'s `a.show` and the concatenation `+` needing a staged discharge order.

A bounded prototype re-homed provider obligations into member templates and retried unavailable FieldTails after successful selections. In the pinned readback path this caused `Collection(MissingDefinitionEndpoint)` before a FieldTail readback could be produced. The prototype was removed; the focused R323 pinned readback test passes again. This identifies an integration falsifier, not a validated design. The next step is to isolate that collection failure and then carry source owner, template owner, occurrence, and receiver row as distinct coordinates. Repeated source occurrences must be matched by their concrete FreshUse receiver row, and an unavailable item may be retried only after another exact dispatch adds constraints. The unchanged Types sample remains OPEN.
