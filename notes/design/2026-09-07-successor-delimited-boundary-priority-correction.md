# Successor shared delimited boundary-priority correction

Status: Reviewed; fresh user decision required

Date: 2026-09-07

Drafted-by: primary after execution-pinning the suspended fresh-slot and
post-item legacy boundary phases

Reviewed-by: M3 independent compiler/recovery and specification review; two
batched Draft repairs followed by clean compiler/specification delta review

Scope: define one phase-aware, private successor recovery-priority correction
for the immediate `TypeDelimitedOwner::{Call, ParenthesizedGroup, EffectRow}`
owners.  It addresses only ordinary horizontal leading before an already
recognized generic caller boundary or outer-owned close.  It preserves abstract
boundary handoff and matching-local-close behavior.  If approved, it authorizes
one private construction gate and no public dispatch, Yumark, legacy-parser,
or T4E recovery-cell implementation.

This Reviewed proposal records no user decision and authorizes no code or
expected-output change.

Supersedes if approved, and only for the horizontal ordinary-leading priority
described in §2:

1. `2026-09-07-successor-t3-typecall-recovery-amendment.md` §6's suspension
   of Call post-item horizontal generic-caller/outer-close
   certification/repair; and
2. `2026-09-07-successor-t4-inherited-type-ml-correction-amendment.md` §5's
   suspended Parenthesized/EffectRow boundary-priority scope, including only
   the withdrawn pre-trivia caller/outer priority sentence in that amendment's
   §2.

It retains T3 CallArgument and CallArgumentSeparator construction, T3b, T4P
provenance/separator construction, current owner-specific record publication,
normal local-close/EOF behavior, and every excluded T4E/T4B/T4A/T7c/O6/public
scope.

Governing sources:

- `2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md` §§2, 3.3, Gate 5,
  rollback, and review;
- `2026-09-02-yumark-gate3b-recovery-adoption-matrix.md` T3, T4, and RB-T;
- `2026-09-07-successor-t3-typecall-recovery-amendment.md` §6;
- `2026-09-07-successor-t4-inherited-type-ml-correction-amendment.md` §5;
- direct legacy evidence `c54c78c6`, `820dca87`, `b4c790db`, `a888a013`, and
  `3582cc35` in `crates/yu-syntax/src/grammar/type_expr.rs`.

## 1. Trigger and confirmed facts

The suspended T3a/T4P priority proof conflates two independent ownership
facts: returning a generic caller or outer-close payload unchanged, and
returning the same Item's leading trivia unchanged.  Legacy does the first but
not the second after the immediate delimited owner has accepted its
continuation.

For an ordinary horizontal gap after a completed item, legacy keeps a generic
caller or outer-owned close payload raw, emits the gap as an immediate
Call/Parenthesized/EffectRow child, and publishes the local close Missing at
the post-gap frontier.  An already-classified abstract boundary instead hands
off the whole gap and payload; its local close Missing uses the pre-gap
coordinate.  A matching local close accepts after the same owner-local gap.

Fresh slots are a separate phase.  The initial and post-comma/post-semicolon
legacy controls prove all of the following for Call, Parenthesized, and
EffectRow:

- generic caller `}` stays raw after the owner emits one horizontal gap; the
  owner publishes Item Missing then close Missing at the post-gap coordinate;
- a fresh lexical `else` candidate is parsed as a Type identifier, leaving its
  following `: 0` for the caller, subject to each owner's retained
  caller-stop/Type-NUD admission rule.  It is not reclassified as an abstract
  boundary merely because it occurs after a gap;
- a matching local close consumes the owner gap and finishes with no recovery;
  and
- nested outer closes have the same Item-Missing then close-Missing ownership,
  while their outer `]` or `)` remains actual and continues through its own
  BracketRow/arrow or Parenthesized owner.

The last point is execution-pinned for these complete, lossless controls:

| owner | initial | post-comma | post-semicolon |
| --- | --- | --- | --- |
| Parenthesized in BracketRow | `G T[( ]->U`, anchor `6` | `G T[(F, ]->U`, anchor `8` | `G T[(F; ]->U`, anchor `8` |
| Call in BracketRow | `G T[T( ]->U`, anchor `7` | `G T[T(F, ]->U`, anchor `9` | `G T[T(F; ]->U`, anchor `9` |
| EffectRow in Parenthesized | `G ('[ )`, anchor `6` | `G ('[F, )`, anchor `8` | `G ('[F; )`, anchor `8` |

Each row has exactly the immediate owner's Item Missing then close Missing,
both at the listed anchor; its one horizontal Whitespace is a direct immediate
owner child.  There is no separator, Error, or outer-close record.  The
zero-width attempted `TypeExpression` wrapper between the Whitespace and
Missing nodes is deliberately not a new topology contract.

## 2. Proposed phase-aware disposition

The proposed rule applies only after the direct delimited owner has committed
to its continuation.  It operates on the existing `Item` and its existing
leading-emission frontier.  It does not split, clone, recreate, rescan, retain
source text/ranges, or manufacture a replacement Item.

`Initial` means the slot after the opener; `AfterExplicitSeparator` means the
slot after an accepted comma or semicolon; `AfterItem` means the next Item after
one complete delimited TypeExpression.  The implementation may use a private
local enum or equivalent shared branch structure, but the phase must not live
in `Item`, `Recover`, output, a session-local field, or a public API.

| phase | already-classified abstract boundary | fresh lexical `else` under existing owner-specific admission | non-close caller boundary | explicit caller-owned mismatched close | outer-owned close | matching local close |
| --- | --- | --- | --- | --- | --- | --- |
| `AfterItem` | hand off whole Item, leading, and payload; existing close publication anchors at the pre-gap coordinate | not a distinct admitted row | emit eligible owner horizontal leading; preserve raw payload; existing close publication uses post-frontier | emit eligible owner horizontal leading; preserve raw payload; retain the owner's existing caller-close publication form | emit eligible owner horizontal leading; preserve raw payload; existing close publication uses post-frontier | emit eligible owner horizontal leading and actual close; no recovery |
| `Initial` | hand off unchanged with its existing Item/close publication | parse it as the first Type item; leave `: 0` for its caller | emit eligible owner horizontal leading; Item Missing then close Missing CST nodes at post-frontier; preserve raw payload | emit eligible owner horizontal leading; Item Missing then close Missing CST nodes at post-frontier; preserve raw payload | emit eligible owner horizontal leading; Item Missing then close Missing CST nodes at post-frontier; preserve raw payload | emit eligible owner horizontal leading and actual close; no recovery |
| `AfterExplicitSeparator` | hand off unchanged with its existing Item/close publication | parse it as the next Type item; leave `: 0` for its caller | emit eligible owner horizontal leading; Item Missing then close Missing CST nodes at post-frontier; preserve raw payload | emit eligible owner horizontal leading; Item Missing then close Missing CST nodes at post-frontier; preserve raw payload | emit eligible owner horizontal leading; Item Missing then close Missing CST nodes at post-frontier; preserve raw payload | emit eligible owner horizontal leading and actual close; no recovery |

Eligible leading in this Draft means nonempty ordinary horizontal Whitespace
only.  Newline, CRLF, line comment, block comment, fence prefix/carrier,
physical boundary, EOF, and Error-leading behavior remain governed by their
existing owner contracts and are not generalized by this correction.

An "already-classified abstract boundary" is a pending/abstract boundary from
the existing delimiter and caller context, not an identifier spelling tested
before fresh Type-primary admission.  The correction must therefore classify
the current phase and boundary kind before any leading/frontier/output
mutation.  It may advance only the immediate owner's existing leading frontier
on the generic/outer and matching-local rows.  The raw payload, Item identity,
item origin, line entry, stops, delimiter state, `TypeMlContext`, outer-boundary
context, fence, operators, and caller continuation remain unchanged on handoff.

Fresh caller-stop admission remains owner-specific and is not changed by this
correction.  In the current normalized fresh-slot check, Call recognizes an
active `STOP_ELSE` before admitting the lexical Type NUD and therefore hands
that `else` to its caller.  ParenthesizedGroup and EffectRow retain their
existing Type-NUD gate: the same lexical `else` continues as their Type item
even when the caller-stop bit is present.  The approved gate must retain those
paths unchanged.  It must add Call negative controls proving caller ownership
under active `STOP_ELSE`, plus Parenthesized/EffectRow positive controls proving
their retained Type-NUD admission; it must not infer a cross-owner override
from the ambient witness.

The post-item generic/outer row emits only its owner close Missing CST node.
The fresh generic/outer rows emit Item Missing then close Missing CST nodes.
No row emits a separator Missing, permits a boundary payload inside Error, or
adds an Error terminal.  Existing typed-record publication remains
owner-specific: Call retains its established Item/close records, Parenthesized
retains its existing close record for non-close caller and outer-close paths
without gaining an Item record, but preserves its untyped zero-record explicit
caller-close path; EffectRow remains untyped until the excluded T4E
construction.  Every existing record uses the frontier-aware missing anchor;
there is no diagnostic-only byte adjustment.

## 3. Bounded construction gate if approved

One approved construction pass changes only the private normalized Type
delimiter continuation at its owning sites:

- `crates/yu-syntax/src/rewrite/type_expr/delimited.rs`:
  `type_delimited_normalized` and `type_after_separator_normalized`, together
  with the smallest private classifier/helper necessary to share the exact
  phase disposition;
- its focused successor tests under `crates/yu-syntax/src/rewrite/tests/`;
  and
- task/progress/design-status records after review closure.

The construction must retain the completed T3 CallArgument and
CallArgumentSeparator behavior, T3b's seventh Error terminal, T4P's
`TypeMlContext` provenance/separator construction, current owner-specific
typed-record publication, normal local close and EOF behavior, and all current
rejection transactions.  BracketRow is an outer continuation witness only: no
BracketRow boundary or recovery behavior may change.  EffectRow receives only
this shared boundary-priority correction; its T4E Item/Separator/Close recovery
construction and all typed EffectRow records remain unopened.

No production dispatch, legacy grammar/parser, session API, Yumark bridge,
embedded recovery fact, fixture/golden update, O4/O6 certification, T4B/T4A,
T7c, NonTypeApply PV/declaration parity, or public cutover is in scope.

## 4. Required local proof and rollback

Before successor expectations change, retain the direct legacy controls in
§1 and execute focused successor evidence for each authorized changed cell:

1. fresh and frozen equality for all existing owner records, CST, frontier,
   remainder, origin, line entry, context, stops, delimiter, fence, operator
   identity, and diagnostics; Parenthesized Item and all EffectRow Missing
   stages prove no new record publication;
2. direct owner CST order: native Whitespace, then the applicable Item/close
   Missing sequence or native local close, without fixing the incidental empty
   wrapper;
3. raw generic caller/outer payload handoff and the actual outer continuation;
4. both the post-item one-close-Missing CST distinction and the fresh
   two-Missing CST distinction, with no separator/Error record or any newly
   introduced typed owner record; and
5. owner-specific caller-stop controls: Call `STOP_ELSE` negative handoff plus
   Parenthesized/EffectRow retained Type-NUD admission, and Parenthesized
   caller-close zero-record controls, proving those retained admission and
   publication forms; and
6. RB-T rejection, retry, frozen mismatch, and committed-completion controls
   proving no duplicated leading, boundary payload consumption, Error entry,
   or caller-state mutation.

The aggregate T3/T4 matrix remains Open; local direct evidence cannot replace
O6's real successor-Yumark AST/direct fact comparison and frame-pop proof.

Return to architecture without implementation if a non-horizontal leading
form changes, a fresh outer-close fact contradicts §2, an excluded owner changes,
an Item/payload must be split/cloned/replayed/rescanned, a child probe emits
leading before it commits, or the caller's raw payload becomes consumed.

## 5. Cost and review

On a relevant delimiter continuation, the candidate adds constant phase and
boundary classification plus at most the already-existing one leading-emission
pass.  It adds no traversal, allocation, clone, cache, buffer, source
retention, or recursion.  The timing budget is zero samples/processes unless a
review finds material uncertainty.

This is M3 because the correction changes shared recovery/CST/frontier
invariants.  Required design review is independent `compiler_referee` and
`spec_auditor`; after an approved implementation, add `regression_auditor` for
the shared sibling-owner test surface.  At most three review/repair rounds
apply.

## 6. User decision after review

After independent review, select one option:

1. **Legacy-compatible correction (recommended).** Approve §2 and the bounded
   construction gate.  The successor adopts the observed phase-sensitive
   immediate-owner gap ownership while retaining raw generic/outer payload
   handoff and abstract whole-gap handoff.
2. **Intentional successor divergence.** Keep whole-gap handoff at generic or
   outer boundaries.  This rejects §2, changes direct CST trivia placement and
   Missing coordinates from legacy, and requires a new explicit compatibility,
   reconciliation, O6, and public-surface decision before any construction.

Unconditional emit-before-boundary, unconditional whole-gap handoff, and a
downstream diagnostic-range patch are rejected: each contradicts at least one
execution-pinned phase or splits committed CST ownership from diagnostics.
