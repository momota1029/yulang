# Direct declaration-companion vertical-slices amendment

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-06

Scope: This amendment changes only the private direct-rewrite execution order
for declaration-companion addendum Gates 5--9. It replaces their horizontal
implementation staging with owner-local vertical slices. It does not change
the declaration-companion grammar, attachment matrix, CST, recovery ownership,
outer-only TypeExpression boundaries, AST contract, public grammar, legacy
parser, production dispatch, or the atomic final/public gate.

Drafted-by: primary agent

Reviewed-by: independent architecture and specification audit

## 1. Reason for the amendment

The approved companion addendum's Gate 5 requires typed episode handoffs for
Derives, Act, Type equality, and Enum/Error equals-inline payloads before any
owner adapter is wired. The direct rewrite currently has a Type owner and an
isolated shared variant core, but it has no direct Act, Enum, or Error owner;
Struct also has no direct Derives attachment. Implementing all horizontal
handoffs first would therefore require a detached carrier, test-only owner
adapter, stored continuation, or placeholder owner.

Those representations duplicate owner facts which are statically known at the
concrete call site and conflict with the direct rewrite's immediate Item
handoff topology. Waiting to create all declaration shells first would instead
invert the approved implementation order while leaving their handoff recovery
undefined.

## 2. Narrow amendment

On approval, replace only the construction order of the declaration-companion
addendum's Gates 5--9 with these private direct-rewrite vertical slices:

1. **Type slice.** Build Type Header/Derives and Equality-RHS outer-only
   `with` handoffs at their concrete owner positions. Preserve AttachedImpl
   priority, mandatory-slot no-cascade recovery, and nested TypeExpression
   suspension. The direct Type owner consumes an accepted companion immediately
   in its isolated route; it does not change production dispatch.
2. **Struct slice.** Build Struct Header and actual-complete braced/tuple
   trailing positions, including their existing Derives ordering and
   missing-close exclusions. A bare Struct remains unchanged.
3. **Enum/Error paired slice.** Build their shared Header/actual-brace
   positions and owner-parameterized equals-inline yield together. The shared
   variant core yields the exact outer `with`; the concrete Enum owner maps it
   to a companion and the concrete Error owner returns it to outer Statement.
   The variant core never decides that attachment policy itself.
4. **Act slice.** Build Act post-Head and post-Source outer-only `with`
   handoffs. Either accepted companion terminates the Act continuation; no
   post-body companion position exists.
5. **Atomic final/public slice.** Retain the original addendum's public matrix,
   full owner/position verification, and production-cutover requirements.

The completed common companion form and companion-Derives construction remain
private prerequisites. A vertical slice may provide isolated direct evidence
for its concrete owner but may not claim its original horizontal gate, an owner
family, or the final public scope complete until the corresponding original
acceptance conditions are met.

## 3. Required topology

Every slice uses the existing immediate handoff values only:

- `TypeExpression` observes `WITH` only in its outer logical episode and
  returns the unchanged pending `Item` with its existing origin and
  `LineEntry`; nested episodes retain `TypeOuterBoundary::NONE`.
- The concrete declaration owner, which already knows its owner and position,
  decides immediately whether that Item starts `DeclarationCompanion` or is
  returned to outer Statement.
- The companion starts only after exact contextual `with` selection.

This amendment authorizes none of the following: a general handoff carrier,
new `NormalizedExit` case, `Item`/`Recover`/Rowan-stored owner state, callback
registry, cached continuation, source/range reconstruction, rescan, replay,
test-only declaration substitute, global `WITH` activation, or future-owner
placeholder.

The existing Type/Derives immediate paths remain real owner-local paths. The
shared variant core may gain outer-only yield capability only in the Enum/Error
paired slice, where both concrete consumers exist. Act receives no standalone
witness before its direct owner exists.

## 4. Retained semantic and recovery authority

All of `2026-08-30-declaration-companion-with-addendum.md` §§3--12 remain
unchanged, including `DC-G`, `DC-J`, `DC-T`, `DC-R`, and the five-owner
attachment matrix. In particular:

- `with` remains contextual and exact; it never becomes a global keyword;
- nested parenthesized, call, forall, arrow, polymorphic-variant, record, and
  row TypeExpression episodes suspend `WITH`;
- missing/malformed predecessor slots retain their single local recovery before
  yielding the unchanged `with`;
- Enum and Error retain their intentionally different equals-inline ownership;
- no attachment crosses an incomplete/recovered close, equal/shallow boundary,
  or rejected owner position.

## 5. Per-slice evidence

Each vertical slice is M2 construction. Before writing, run the current
specification audit for the exact owner boundary. After writing, use a
compiler/recovery review and the applicable regression or specification review.
Run focused owner and handoff tests plus `cargo check -p yu-syntax`; defer broad
workspace verification to the coherent declaration/public phase. A performance
review or measurement is required only when the concrete diff introduces its
material-risk trigger, such as an ordinary/public edge, allocation, retained
collection, replay/rescan, added traversal, or a new loop on an ordinary path.

Every owner handoff witness records losslessness, exact pending Item leading
trivia/origin/`LineEntry`, CRLF/fence behavior, nested TypeExpression
suspension, predecessor recovery ownership, outer remainder, and the absence
of a public/legacy call edge. The paired Enum/Error slice additionally records
both mappings from the same variant yield.

## 6. Exact supersession

This amendment supersedes only the implementation ordering of
`2026-08-30-declaration-companion-with-addendum.md` §13 Gates 5--9 for the
private direct rewrite. It retains the original gate semantics, owner matrix,
verification obligations, and Gate 10 atomic public/final scope. It does not
supersede the recursive rewrite plan's no-legacy-crossing or direct immediate
handoff constraints.
