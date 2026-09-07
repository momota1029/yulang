# Successor PV wrong-kind primary-completion amendment

Status: Authoritative; bounded construction approved

Date: 2026-09-07

Drafted-by: primary after direct legacy primary-boundary characterization and
an isolated base/candidate successor comparison

Reviewed-by: M3 independent compiler/recovery and specification review; one
batched Draft repair followed by clean compiler/recovery and specification
delta review

Approved-by: user

Approved-at: 2026-09-07

Scope: the private `PolymorphicVariantTagName` wrong-kind recovery path only.
It proposes that this path parse exactly one accepted Type primary before it
returns to the existing PV payload judge.  It is not implementation authority.

Depends-on:

- `2026-09-07-successor-structured-recovery-reservation-amendment.md` §6;
- `2026-09-07-successor-structured-recovery-extent-validation-addendum.md`
  §2;
- `2026-09-07-successor-delimited-boundary-priority-correction.md`; and
- direct legacy evidence `62324e98` and `0d58bf7c` in
  `crates/yu-syntax/src/grammar/type_expr.rs`.

## 1. Confirmed contradiction

Legacy accepts a non-Identifier Type primary in a polymorphic-variant tag
position, ends that malformed tag at the completed primary, then gives any
following payload, path, arrow, or application surface to the existing PV
payload/boundary logic.  The successor instead calls
`type_expr_from_nud_normalized` from
`type_polymorphic_variant_tag_after_wrong_kind_normalized`.  That function
continues through ordinary Type-expression tails, so a wrong tag head can
incorrectly absorb external `::`, `->`, and application tails inside the
already-open `PolymorphicVariantTagName` structured Error.

The contradiction predates the unintegrated shared delimited-boundary
candidate.  Its only candidate-dependent observable is the already-authorized
owner-local horizontal-gap extent inside an existing structured Error; it does
not decide whether a Call belongs to the malformed tag at all.

Direct legacy evidence fixes the required primary boundary:

| class | representative sources | legacy disposition |
| --- | --- | --- |
| atomic | `:{123::T}`, `:{123->T}`, `:{123 T}` | TagName Error is only `123`; `::`/`->` become PV payload-boundary recovery and the trailing Type is payload; horizontal spacing starts the ordinary PV payload |
| Parenthesized external tail | `:{(A)(B)}`, `:{(A)::T}`, `:{(A)->T}`, `:{(A) B}` | Error ends at the completed `(A)`; each following form is handled by existing PV payload/boundary logic |
| Parenthesized internal tail | `:{(A(B))}`, `:{(A::B)}`, `:{(A->B)}`, `:{(A B)}` | the nested group owns its own ordinary Type expression, so its complete source remains within the one TagName Error |
| other non-atomic primary | `:{'[A](B)}`, `:{{a: A(B)}(C)}` | Error ends at the completed EffectRow or record primary; external application is PV payload/boundary material |
| forall | `:{for 'a: A(B)}`, `:{for 'a: A->B}` | `for` owns its ordinary body; the whole complete forall primary remains inside one TagName Error |
| valid tag name | `:{A(T)}`, `:{A::T}`, `:{A->T}` | unchanged normal tag-name path; this amendment does not enter it |

Every cited row, including the committed `::Next` controls in `62324e98`, is
lossless and has a native PV `}`.  Legacy malformed topology is flat
`Error > Unknown`; successor structured topology remains separately governed
by the reservation amendments.  Required compatibility facts here are primary
end, outer structured Error extent/evidence, native PV close, payload/boundary
order, and continuation—not flat CST topology equality.

## 2. Proposed responsibility boundary

Add a private normalized helper beside `type_expr_from_nud_normalized` that
constructs the same outer `TypeExpression` wrapper and primary NUD dispatch,
but accepts an explicit primary-completion policy:

```text
type_primary_from_nud_normalized(..., completion)
```

Its private input policy is one of:

```text
ContinueExpression
ReturnPrimary
```

`ContinueExpression` preserves all present ordinary callers and must retain
the current `type_expr_from_nud_normalized` behavior byte-for-byte.  The only
initial `ReturnPrimary` caller is the nested closure in
`type_polymorphic_variant_tag_after_wrong_kind_normalized`; `NormalizedExit`
remains the result in both modes.

For `ReturnPrimary`, an atomic accepted wrong-kind primary emits its token and
returns success immediately.  Parenthesized, EffectRow, NamedRecord, and
nested PV owners each first complete their existing internal expression and
local delimiter work, then return their unchanged `NormalizedExit` after
closing their own node and before `continue_type_tail_normalized` considers an
*external* tail.  The policy is threaded only to those immediate primary
producer endings (`type_group_normalized`, `type_effect_row_normalized`,
`type_record_normalized`, and `type_polymorphic_variant_normalized`), not into
their delimiter/recovery loops or child type-expression calls.  Forall returns
only after its existing ordinary body completion; it must not propagate
`ReturnPrimary` into the forall body.

Leading BracketRow is excluded from this route.  Legacy primary admission
explicitly excludes it and its current successor path ultimately performs full
expression completion.  This gate keeps that behavior unchanged and requires a
frozen no-delta successor control; a BracketRow-admission change is a separate
decision.  Normal Identifier tag names do not use this helper or change
behavior.

The returned success or pending `Item` flows unchanged into the existing
`type_polymorphic_variant_tag_payloads_after_head_normalized`.  It performs
the established PV decisions for horizontal payloads, `::`/`->` boundary
recovery, local separator/close, EOF, and continuation.  The structured Error
endpoint remains derived from that returned post-primary frontier via
`structured_tag_name_end`; its range must still equal its emitted-byte
coverage.  No range clamp, PV-specific delimiter condition, replay, Item
clone, source reread, buffering, or post-hoc tail split is permitted.

## 3. Construction and proof obligations

Construction may change only the private primary-dispatch boundary; the
immediate owner-completion endings in `type_expr.rs`, `record.rs`, and
`variants.rs`; the PV wrong-kind call site; and focused successor tests.  It
may not duplicate primary-owner bodies, thread the policy into delimiter or
recovery loops, alter legacy grammar tests, public/root parser wiring,
AST/HIR, fixtures, goldens, or valid tag-name dispatch.

Before and after construction, focused fresh and frozen proof must cover:

1. every source class in §1 with actual PV close, including full Error
   records/evidence, direct CST ancestry, AST, remainder, pending Item, line
   entry, stops, and context.  The only currently execution-pinned `::Next`
   continuations are `:{123::T}`, `:{(A)(B)}`, and `:{(A(B))}`; no other
   continuation expectation may be assumed without first adding direct legacy
   evidence;
2. the numeric apparent-Call matrix in `0d58bf7c`, proving `:{123(F }` has
   TagName Error `123`, a separate Parenthesized payload, and the existing
   `PayloadBoundary` Missing rather than a Call inside TagName Error;
3. the approved P/E structured-Error extent controls, including prefix and
   nested controls, proving emitted Error coverage, native PV-close exclusion,
   record IDs/order/count, and no new recovery carrier; and
4. the reservation amendment's exact recursive `:{:{123}}` fresh/frozen
   control: outer/inner structured ranges, LIFO completion, frozen reuse and
   order, and the outer-close handoff.  Also characterize a nested-PV external
   tail such as `:{:{A}(B)}` directly in legacy before accepting a successor
   expectation for it; and
5. two distinct failure contracts: pre-reservation PV-probe rejection/decline
   preserves output, diagnostic cursor, input, recovery slots, and Item
   ownership; a committed frozen mismatch invalidates and discards the current
   output under the structured-reservation contract, with no rollback or
   reusable-result claim.

Any changed valid-tag parse, inner-primary tail, recovery ordering/role,
unconsumed PV close, non-lossless continuation, or scope outside this single
PV wrong-kind route returns the work to architecture.

## 4. Cost and review

The proposed route changes one private dispatch choice.  It introduces no
additional parse, scan, allocation, clone, cache, buffer, recursion, or
source retention; it uses the same Item and existing owner calls.  Timing
budget is zero samples/processes unless an independent review identifies a
material uncertainty.

This is M3: it changes a structured-recovery completion invariant whose
consequences include payload ownership and Error extent.  Independent
compiler/recovery and specification Draft review closed with one batched repair
and clean deltas.  After an approved construction, regression review covers
the direct PV sibling surface, then compiler/specification delta review closes
the changed dependency cone.  At most three review/repair rounds apply.

## 5. Decision record

Option 1 (recommended): approve the exact primary-completion construction in
§2–3.  It restores the direct legacy boundary while keeping ordinary type
expressions and all valid PV tag names unchanged.

Option 2: retain full-expression completion in the PV wrong-kind path.  This
leaves the observed Call/path/arrow/payload divergence, blocks integration of
the shared delimited candidate where it reaches that contradiction, and
requires an intentional successor-recovery divergence record before cutover.

The recorded recommendation delegation is inapplicable.  This proposal changes
the PV head-completion invariant, payload ownership, and possible recovery
record sequences, so it is a material recovery/scope expansion rather than a
same-carrier range/evidence correction.  The user selected option 1 on
2026-09-07.  The §2–3 bounded construction is now authorized; all stated proof
obligations and exclusions remain mandatory.
