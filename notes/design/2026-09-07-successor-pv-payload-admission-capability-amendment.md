# Successor PV payload-admission capability amendment

Status: Draft; architecture re-entry required

Date: 2026-09-07

Drafted-by: primary after payload-adapter architecture re-entry

Scope: a proposed private capability prerequisite for conditional malformed
polymorphic-variant payload admission.  It authorizes no source, test
expectation, or public behavior change.

Depends-on:

- `2026-09-07-successor-pv-wrong-kind-primary-completion-amendment.md` §6;
- `2026-09-07-successor-structured-recovery-reservation-amendment.md` §§4–7;
- `2026-09-07-successor-structured-recovery-extent-validation-addendum.md`
  §2;
- `2026-09-03-yu-syntax-gate4-6-scc-amendment.md` §4.3; and
- direct legacy evidence `4ff97ddc` in
  `crates/yu-syntax/src/grammar/type_expr.rs`.

## 1. Pinned rows and unproven classes

The primary-completion construction proved that its primary boundary is causal,
but refuted its payload premise.  After `:{123}` completes as a wrong-kind PV
tag head, successor `type_polymorphic_variant_tag_payloads_after_head_normalized`
does not admit an unspaced `::` payload boundary.  It hands that Item back to
outer tag recovery.  Direct legacy makes payload admission conditional on a
later retry primary.  The following table is a design inventory, not a
generalized confirmed compatibility table: each row identifies the direct
evidence currently pinned and its remaining characterization boundary.

| proposed class | currently pinned direct fact / evidence limit |
| --- | --- |
| owner boundary, physical newline, native close, or EOF | valid-name `A` rows, plus CRLF after a malformed prefix; wrong-head and fence forms remain uncharacterized |
| adjacent admissible primary | existing primary bases named in the primary-completion evidence only |
| unspaced invalid retry | valid/wrong-head `::` and `->` rows, four colon-overlap rows, and valid-name `+`/`@@`/block-comment rows below |
| unspaced invalid run with no retry | valid/wrong-head dangling `::` only |
| ambient retry | visible no-stop `else` row only |
| spaced invalid run | valid-name `::{T}` row only |

`legacy_polymorphic_variant_conditional_payload_admission_is_execution_pinned`
records twelve exact rows: valid and wrong-kind `::`/`->` retries, valid and
wrong-kind dangling `::`, an ambient `else` retry rejection with no active
`Else` stop, spaced recovery, a recovered payload followed by ordinary payload,
newline, native close, and EOF.  It fixes AST slots/ranges, complete direct CST
preorder/token extents, ordered recovery records/evidence, close ownership,
payload shape, caller remainder, and ambient-context balance.  The nested-PV
external-tail row `:{:{A}(B)}` is separately pinned at `b6349f9c`.

`legacy_polymorphic_variant_payload_colon_overlap_is_execution_pinned` pins
the four additional sources `:{A::{B}}`, `:{123::{B}}`, `:{A:::{B}}`, and
`:{123:::{B}}`.  Legacy stops the scalar malformed run at the colon that starts
the nested `:{B}`: in `::{B}` it emits one-colon PayloadBoundary Error and
retries at the second colon; in `:::{B}` it emits a two-colon error and retries
at the third.  This directly contradicts a witness that begins only after a
successor-completed `::` PathSeparator Item.

`legacy_polymorphic_variant_payload_scalar_run_boundaries_are_execution_pinned`
adds the complementary scalar-run rows.  `->`, `+`, `@@`, and `::/*c*/` each
produce one PayloadBoundary Error followed by a nested-PV retry; the block
comment belongs atomically to the Error span.  `::\r\n:{B}` instead stops before
payload admission: the outer PV tag loop owns the `::` Error, the CRLF newline,
and the malformed nested starter separately.  These rows characterize only the
observed valid-name surfaces, not a generic fence or wrong-head rule.

For example, `:{123::T}` requires TagName Error `2..5`, then a sibling
`PolymorphicVariantPayload` with PayloadBoundary Error `5..7` and payload `T`
at `7..8`, then native PV close.  The trial primary-completion candidate got
the first range right but created a second `PolymorphicVariantTag` Error at
`5..7`.  No trial source or expectation was integrated.

The payload judge is shared by valid and wrong-kind tag heads.  A wrong-kind
only repair would duplicate the responsibility and leave the pinned valid-name
rows divergent.

## 2. Current capability mismatch

The current direct route owns one already-scanned invalid `Item`.  Its payload
decision must know whether a potentially later primary is admissible and free
of an ambient owner claim before that Item is emitted.  No existing successor
facility can provide that fact under current rules:

1. advancing through `current_item` creates owned Items; declining afterward
   loses intervening bytes unless it re-scans completed Items or retains a run;
2. output checkpointing wraps CST but cannot roll back output, and lexical
   transactions cannot access output; `Recover::Mark` is unit;
3. existing source-only probes inspect one prospective token/trivia fact, not
   an arbitrary malformed run and its retry eligibility; and
4. the payload interface receives stops, type-ML, delimiters, and fence, but
   no ambient-owner claim independent of stops.  The pinned `else` row proves
   such a claim is semantically material.

The initial suffix-only proposal has a concrete contradiction: successor scans
the first `::{B}` colon pair as one PathSeparator Item, while legacy must split
that surface before the second colon so it can retry nested `:{B}`.  A witness
starting after the completed Item sees `{B}` and cannot recover the lost retry
boundary without forbidden replay or retained source state.

Deleting the leading-trivia guard, handling `::`/`->` specially, unconditionally
consuming a malformed run, or making the rule wrong-kind-only violates at least
one §1 row.  Retrospective CST wrapping/splitting, emitted-output rollback,
Item cloning, retaining a run/source slice, and replay are likewise forbidden.

## 3. Re-entry boundary

This is not a reviewable construction.  The suffix-only witness is withdrawn.
A replacement must use two ordered prerequisites rather than attach an
ambient boolean to the scalar observer.

First, an ambient-context prerequisite must establish an immutable,
call-stack-only `AmbientClaimView`: the nearest visible statement baseline plus
the visible chain of active If-companion frames.  Root/indented statement
owners replace the baseline, inline owners forward the view, braced owners
start an empty view, and an If arm temporarily prepends its companion before
returning to its caller's view.  The query receives separately derived
position evidence (`has_physical_newline`, following indentation, and following
word) and returns only a boolean claim.  It must not use stop bits, retain
source, escape through an Item/exit/record/cache, or add mutable scope state to
`Recover`; ordinary return makes its frames rollback-safe.  The exact
virtual-statement/Yumark barrier map remains unproven, so this is a candidate
decomposition rather than an implementation authorization.

Only after that prerequisite is proven may a replacement decide whether a
bounded, source-only observation can occur *before* Item construction at the
scalar malformed-run boundary, and whether that observation is within the
SCC's candidate-token/prospective-trivia authority or requires a separately
approved extension.  Initial and retry positions must query the ambient view
independently; legacy can change the claim as the probe advances through trivia
and retry surfaces.

Any replacement observation must neither allocate nor retain an `Item`,
`Token`, `Trivia`, `LeadingTrivia`, `TriviaRun`, boxed slice, source-owned text,
offset, run, cache, recovery record, or output/checkpoint state.  It may not
advance a live cursor, construct/complete an Item, mutate recovery/output, or
assign CST/trivia/diagnostic ownership.  The ordinary scanner must remain the
sole owner of emitted bytes.  No payload-loop implementation is authorized by
this record.

### 3.1 Virtual-statement and Yumark classification remains a separate decision

Architecture tracing establishes a narrower fact than a visibility policy.
The Authoritative literal-cone addendum defines a `VirtualStatementBlock` as a
root-style `Statement*` owner, while direct legacy treats interpolation parsing
as opaque at its internal Type/PV decisions.  Neither fact proves that a
virtual statement inherits the enclosing ordinary statement's baseline or
If-companion chain.  In particular, the braced-owner controls justify clearing
an ordinary braced block; they do not classify a virtual statement block.

The currently recommended, but unapproved, candidate is to seed a virtual
statement block with a virtual-root baseline at its own start and no inherited
If companions, then restore the caller's immutable view at its return.  A
nested interpolation would establish its own seed.  If such a virtual block is
inside a Yumark fence, the fence would not apply a second reset: it would
retain the view selected by the virtual owner until that virtual boundary
returns.  This is a candidate interface rule only; it authorizes neither a
carrier implementation nor a payload decision.

The current `yumark_cell::yulang_code_cell_witness` reaches an isolated
statement entry at `(0, 0)`.  It can exercise a root seed in a test, but it
does not establish a production embedded-Yulang ingress or a virtual/Yumark
ambient policy.  No future production cell policy is implied here.

Before this class can be admitted to the ambient prerequisite, direct legacy
or an explicit user decision must settle all of the following:

1. an enclosing visible baseline/If companion around a normal and a heredoc
   interpolation, including restore of the outer view after interpolation;
2. a local If companion created inside the virtual block;
3. nested interpolation and a fence-terminated interpolation, proving which
   view each return restores; and
4. a future production Yulang-cell bridge independently from the test witness.

Until then, no code may classify virtual statements as ordinary braced owners,
inherit their outer companions, or treat the test-only cell witness as a
production policy proof.

## 4. Required capability proof and cost gate

Before a replacement Draft can become Reviewed, its construction route must
prove:

1. a finite pre-Item scalar-observation grammar that matches
   `consume_invalid_run`'s exact stop/retry boundary, including the split
   required by `::{B}` and `:::{B}`.  Direct legacy evidence must first cover
   every newly named multi-token, comment, CRLF/fence, and retry-classification
   row;
2. the complete, position-sensitive ambient-claim provenance map for every
   reachable PV payload caller, including the visible-no-stop `else` control,
   and why normal stops are neither overloaded nor silently reinterpreted;
3. no allocation or retention of Item/Token/trivia/source/run/offset/cache/
   recovery/output/checkpoint state crosses the probe boundary; decline
   preserves all cursors, while a committed frozen mismatch retains the
   existing discard-only reservation contract;
4. an aggregate work bound for `M` malformed bytes later consumed, `W` witness
   bytes, `A` admissions or declines, and `C` retry classifications.  It must
   prove `W <= c * M` for a fixed constant `c`, account for each `A` and `C`,
   and establish that valid input keeps its current work; and
5. fresh/frozen exact proof for all §1 rows, prefix/malformed tag/recursive
   reservation controls, Parenthesized/EffectRow extents, valid-name siblings,
   original three `::Next` controls, caller/outer boundary handoff, and
   rejection/mismatch invariants.

Before the ambient prerequisite can become Reviewed for a virtual-statement or
Yumark caller, it must additionally map that visibility transition against
legacy or record a user decision that explicitly supersedes an unavailable
legacy observation.  An ordinary-only carrier may instead preserve an explicit
unavailable context through those callers; it does not settle their policy and
does not make this prerequisite Reviewed for them.  Every approved carrier
still must prove the view cannot escape an active call frame and add seeded
visible/dedent/If, nested-If, and barrier controls at distinct initial/retry
positions.  Its initial implementation, if approved, changes no PV admission
or recovery output; scalar admission remains a later gate.

The direct parser is hot.  A new arbitrary raw traversal and unknown aggregate
frequency trigger independent performance review.  Timing budget is zero until
static analysis establishes a concrete implementation and a timing result could
change a decision; no benchmark is authorized by this Draft.

## 5. Status and scope

If later authorized, construction may be limited to the shared PV payload
adapter, its immediate lexical/context dependencies, and focused private
successor evidence.  It must preserve the primary-completion policy,
structured Error endpoint/byte validation, record ordering, valid primary
owners, raw close/caller handoff, and all delimiter scopes.  It may not alter
legacy parser behavior, public/root dispatch, AST/HIR, fixtures/goldens,
O6/public certification, or implement a broad lexer/cache/replay facility.

Independent compiler/recovery, specification, and performance review rejected
the initial Draft because its suffix boundary is too late, its compatibility
claims overgeneralize the present evidence, its ambient observation lacks
position provenance, and its allocation/work contract is incomplete.  No user
choice is requested from this rejected construction shape.  A replacement
capability design must first close the ambient prerequisite, then the scalar
frontier/probe proof in §§3–4, before independent review and a fresh user
decision; until then this Draft authorizes no implementation.
