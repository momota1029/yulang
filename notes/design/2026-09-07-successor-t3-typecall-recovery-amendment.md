# Successor T3 TypeCall recovery amendment

Status: Authoritative; T3 core local construction complete; T3a post-item
horizontal caller/outer-boundary certification suspended by direct legacy
contradiction

Date: 2026-09-07

Drafted-by: primary from T3 architecture preflight after T2b local construction

Reviewed-by: M3 compiler/recovery, specification, and performance review; one
batched Draft repair followed by clean compiler/specification delta review

Approved-by: user

Approved-at: 2026-09-07

User-directed decision: the active replacement objective authorizes proceeding
with the recommended reviewed proposal unless a material issue requires a
different user decision.  Adopt both bounded, ordered T3 subgates exactly as
specified: T3a Call Missing/inherited type-ML construction, then T3b's
CallArgument-only seventh terminal and direct-child exception.  All scope
exclusions and O6 timing remain in force.

Scope: a bounded successor migration for `TypeDelimitedOwner::Call` only.  It
proposes two ordered local construction subgates: T3a typed Call Missing slots
and inherited type-ML separator recovery; T3b the CallArgument-specific Error
completion that current output authority cannot express.  It does not authorize
ParenthesizedTypeGroup, EffectRow, BracketRow, T4--T7/PV1, Yumark/session
transport, public dispatch, legacy production changes, or cutover.

Implementation status: T3a and T3b local Call construction completed on
2026-09-07.  T3a passed M3 compiler/recovery, specification, and regression
implementation review, one batched repair, and clean delta review.  T3b passed
the same panel after one repair and a test-only micro-delta.  Focused T3a/T3b,
TypeExpression/output/legacy-call tests, `cargo check -p yu-syntax`,
formatting, and diff checks passed; static cost is bounded and timing usage is
zero.  O6 real successor-Yumark fact equality, all non-Call owners, and public
cutover remain deferred.

Governing sources:

- `2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md` §§2, 3.3, Gates
  5, 8--9, rollback, and review;
- `2026-09-02-yumark-gate3b-recovery-adoption-matrix.md` T3 and RB-T;
- `2026-08-20-yu-syntax-chasa-architecture.md` Type ML scope, delimited
  layout, typed recovery, and TypeCall recovery;
- `2026-09-06-successor-typed-output-recovery-amendment.md` §§3--11;
- `2026-09-05-item-emission-ownership-frontier-amendment.md` Scope and §5;
- `2026-09-07-successor-t2b-pathsegment-recovery-amendment.md`, only as a
  boundary precedent for distinct sealed operations and O3/O6 timing, not as
  an authority extension.

This Reviewed design makes new durable recovery-output, CST-topology, and
evidence-timing decisions.  It requires explicit user approval before
implementation or expected-output changes.

Supersedes if approved, and only for every physical Item or eligible
retry-leading part actually emitted by the bounded T3b
`Type(CallArgument)` Error run:

- typed-output amendment §4's whole-Item/literal-only `ErrorRunOutput` surface
  and its architecture-return sentence, to authorize the seventh
  CallArgument-only partial-leading terminal described in §3.1;
- typed-output amendment §1's unchanged-CST sentence, rewrite-plan §2(1)'s
  exact green-tree rule and §5's full-CST acceptance bullet, to authorize only
  the direct-child tokenization delta in §3.2; and
- Item-emission-ownership-frontier amendment Scope and §5's one-whole-Item
  malformed nonboundary rule, to authorize the same T3b operation.

It does not supersede Item-frontier central emission or ownership, the fifth
T2a terminal, the sixth T2b terminal, any non-Call Error owner, or any parent
or sibling topology outside §3.2.

## 1. Established contract and capability contradiction

The authoritative T3 row has three finite responsibility families under the
Call delimiter owner:

| responsibility | grammar role | primary expectation |
| --- | --- | --- |
| pending call item | `Type(CallArgument)` | `TypeExpression` |
| missing call separator | `Type(CallArgumentSeparator)` | `DelimitedSequenceSeparator` |
| call close | `ClosingDelimiter { TypeCall, Parenthesis }` | punctuation `)` |

Each committed-rule expectation has primary index zero.  Nonempty CallArgument
and close Errors each publish exactly one whole-run `OtherCharacter` unexpected
fact and one record at the owner-local Error range.

The legacy parser establishes these direct facts:

- `T(` has ordered CallArgument Missing then TypeCall-close Missing, both
  `2..2`;
- `G T(F A)` has a CallArgumentSeparator Missing at `6..6`, retaining two
  call arguments;
- `T(A` has a close Missing at `3..3`;
- `T(A,` has CallArgument Missing then close Missing, both `4..4`;
- `T(@A)` has CallArgument Error `2..3` and retries `A` in that same argument;
- `T(@ A)` has CallArgument Error `2..4`, including the same-line retry
  leading space inside Error before retrying `A`;
- `T(A] )` has a TypeCall close Error `3..4`, leaves the following space
  outside Error, and accepts the actual `)` at `5..6`.

The current successor has only raw Call Missing construction, no typed
CallArgument or CallArgumentSeparator record publication, and inherited
`type_ml` is not threaded into Call item parsing.  Its shared delimited helper
currently gives ParenthesizedTypeGroup the only typed close branch.

More importantly, existing Error-run operations cannot realize legacy
CallArgument Error ownership.  The fifth terminal only widens a record and
leaves retry Item CST unchanged.  The sixth terminal is explicitly
PathSegment-only, accepts only a block-comment prefix, and leaves ordinary
space outside Error.  `T(@ A)` needs the opposite result: its valid retry
Item's same-line space belongs inside the CallArgument Error CST.  Reconstructing
or coalescing that Error from source, splitting an Item, retaining ranges, a
second builder, or replay is forbidden.  T3b therefore needs a separate,
strictly bounded terminal capability and owner-local direct-child exception.

The legacy TypeExpression path has no embedded Yumark recovery-fact
publication.  Actual embedded AST/direct equality cannot be fabricated from a
direct record during local construction.

## 2. T3a: typed Call Missing slots and inherited ML separator

T3a is the first, ordered construction subgate.  It is restricted to
`TypeDelimitedOwner::Call` and has no Error migration.

### 2.1 Call phases and typed Missing records

The Call owner distinguishes initial/open, post-item, and post-explicit-
separator phases.

- A matching `)` accepts an empty Call or a trailing separator boundary without
  an item Missing.
- EOF, an abstract pending boundary, or a caller-owned un-emitted boundary in
  an initial or post-separator item slot emits CallArgument Missing before the
  required close Missing.
- A completed item at EOF or an active close/boundary emits only the required
  close Missing when the close itself is absent.
- A missing separator between two accepted Call items emits exactly one
  CallArgumentSeparator Missing and retries from the same un-emitted Item.

Missing anchors are exact and shared only for this Call owner:

| condition | anchor |
| --- | --- |
| abstract pending boundary | `PendingBoundary::coordinate()` |
| caller/outer Item not emitted | that Item's remaining-start |
| leading emitted before EOF or a caller/outer Call boundary | post-frontier Item remaining-start |

T3a must execution-pin fresh and frozen direct records and CST for at least:

| source | required records |
| --- | --- |
| `T(,)` | CallArgument Missing `2..2` |
| `G T(F A)` | CallArgumentSeparator Missing `6..6` |
| `T(` | CallArgument Missing, then TypeCall-close Missing, both `2..2` |
| `T(A` | TypeCall-close Missing `3..3` |
| `T(A,` | CallArgument Missing, then TypeCall-close Missing, both `4..4` |

### 2.2 Inherited type-ML boundary

Inherited `type_ml` must be threaded only into Call item parsing.  When the
returned valid Type primary stops at inherited ML and a same-line valid item
remains, Call owns the one CallArgumentSeparator Missing before retrying that
Item.  This is the `G T(F A)` cell.

No ParenthesizedTypeGroup, EffectRow, BracketRow, nested general delimited
owner, TypeApply, or caller boundary may receive this transport or separator
behavior.  A matching close and any active outer/abstract boundary outrank
the Call item retry.

Inherited type-ML retains its all-nonempty-trivia stop behavior.  T3a must
also pin `G T(F\n  A)` with CallArgumentSeparator Missing `8..8` and
`G T(F\r\n  A)` with that Missing `9..9`: in both, the physical newline and
indent are Call-owned trivia, `F` and `A` are two complete arguments, and the
matching close remains `9..10` or `10..11`, respectively.  `G T(F\n  )` and
its CRLF form pin the priority control: the actual close wins with no separator
Missing.  No other delimited owner receives inherited type-ML transport.

## 3. T3b: CallArgument Error completion and close Errors

T3b follows T3a and is not authorized by itself before this Draft is approved.

### 3.1 Seventh sealed Error-run terminal

Add one seventh sealed Error-run terminal, available only to an open
`Type(CallArgument)` Error after the Call owner has already established that an
immediate retry Item is not an outer/caller/abstract boundary, a close, or an
explicit sequence separator.

It may, once only:

1. classify all eligibility before any Rowan, record, evidence, or Item-frontier
   mutation;
2. establish that the retry Item's payload begins a valid shared Type
   primary/NUD candidate for the same CallArgument slot, then borrow that one
   Item only when it has a nonempty contiguous same-line physical
   remaining-leading prefix;
3. emit that complete leading prefix into the open Error, advancing only that
   Item frontier;
4. finalize a terminal Error whose node and record extents are equal and whose
   one `OtherCharacter` fact covers that equal full run; and
5. return the same frontier-advanced Item to ordinary Call parsing so its
   payload retries in the same CallArgument slot.

Eligibility is false, with no mutation and an open Error run retained, for a
malformed lexical payload, newline or CRLF, caller/outer/abstract boundary,
close, explicit separator, carrier or quote prefix, empty leading, prior
frontier movement, payload inclusion, noncontiguous leading, a second use, or
any operation after sealing.  In particular `T(@ @@A)` remains one ordinary
maximal Error run rather than sealing before the malformed `@@` Item.  A
separator-leading Item such as the space before the comma in `T(@ , A)` is not
eligible; its leading remains Call-owned outside Error.
No source access, retained range/text state, Item split/clone, replay,
buffer, secondary builder, or nested Error recovery is authorized.

This seventh terminal is distinct from the fifth and sixth operations.  It
must not make either operation available to a new owner and must not become a
general delimited-owner facility.

### 3.2 CallArgument Error child topology

For every physical Item and eligible retry-leading part actually emitted by a
T3b `Type(CallArgument)` Error run, whether it finalizes ordinarily or through
the seventh terminal, direct Error children retain native item/leading token
boundaries rather than legacy's one coalesced `Unknown`.  A malformed payload
is an `Unknown` child; same-line leading retains its native trivia token kind.
The finite successor topology is:

| source | Error range | direct Error children | continuation |
| --- | --- | --- | --- |
| `T(@ A)` | `2..4` | `Unknown("@")` `2..3`, `Whitespace(" ")` `3..4` | `A` `4..5` retries in same CallArgument |
| `T(@@A)` | `2..4` | `Unknown("@")` `2..3`, `Unknown("@")` `3..4` | `A` `4..5` retries in same CallArgument |
| `T(@/*c*/ A)` | `2..9` | `Unknown("@")` `2..3`, `BlockComment("/*c*/")` `3..8`, `Whitespace(" ")` `8..9` | `A` `9..10` retries in same CallArgument |
| `T(@ @@A)` | `2..6` | `Unknown("@")` `2..3`, `Whitespace(" ")` `3..4`, `Unknown("@")` `4..5`, `Unknown("@")` `5..6` | `A` `6..7` retries in same CallArgument |

Each row has one equal-range CallArgument Error record, one equal-range
`OtherCharacter` fact, and primary `TypeExpression`.  The exception changes no
Error text/range, parent or sibling hierarchy, continuation, record, evidence,
expectation, diagnostic order, or lossless source result.  No other Error
owner or un-emitted Item part receives this exception.

This is required to emit the legacy `T(@ A)` Error extent `2..4` without
forbidden source reconstruction while returning `A` as the retry payload.

### 3.3 Call close Error handling

The Call owner also owns mismatched close recovery.  After high-priority
caller/boundary/actual-close classification, it emits each mismatched-close
payload as one `Unknown` Error item, keeping retry-leading trivia outside that
Error.  It continues until the actual matching close, safe boundary, or EOF.
Close Errors do not receive the CallArgument tokenization exception.

Required controls include:

| source | required continuation |
| --- | --- |
| `T(@A)` | Error `2..3`; `A` retries in the same argument |
| `T(@ A)` | Error `2..4`; space inside Error; `A` retries |
| `T(@\n  A)` and CRLF form | Error `2..3`; trivia outside Error; `A` retries |
| `T(@\n  )` | Error `2..3`; trivia outside Error; actual close is Call-owned |
| `T(@ , A)` | Error `2..3` containing `Unknown("@")` only; space `3..4` stays outside Error, comma `4..5` is Call-owned, and `A` `6..7` is the next complete argument |
| `T(])` | close Error `2..3`; actual `)` completes when present |
| `T(A]` | close Error `3..4`, then close Missing `4..4` |
| `T(A] )` and `T(A]/*c*/)` | mismatch Error only; trivia outside Error; actual close completes |

Before successor topology expectations are added, direct legacy baselines must
execution-pin the Error text/range, its exact one-`Unknown` child, record,
fact, AST continuation, losslessness, and remainder for `T(@ A)`, `T(@@A)`,
`T(@/*c*/ A)`, `T(@ , A)`, `T(@ @@A)`, and `T(A] )`.  T3b also pins active
caller close/newline and abstract/fence cases to prove the seventh terminal
never consumes an outer boundary.

## 4. Embedded evidence timing, scope, and rollback

T3a and T3b local O3/O4 evidence may prove only direct successor records,
CST/Item ownership, continuation, fresh/frozen reconciliation, and RB-T.  The
aggregate T3 matrix row remains Open.  O6, after real successor Yumark
adoption, must compare actual embedded AST facts with successor records in
source order and prove frame pop plus a clean following `\ref(C)`.

The minimum O6 witnesses are:

| embedded source | required primary fact |
| --- | --- |
| `\ref({type T = T(,)})` | CallArgument Missing `17..17` |
| `\ref({type T = G T(F A)})` | CallArgumentSeparator Missing `21..21` |
| `\ref({type T = T(})` | CallArgument Missing then TypeCall-close Missing, both `17..17` |
| `\ref({type T = T(A})` | TypeCall-close Missing `18..18` |
| `\ref({type T = T(@ A)})` | CallArgument Error `17..19`, actual record/fact equality in source order, native successor children `Unknown("@")` then `Whitespace(" ")`, and retry `A` in the same argument |
| `\ref({type T = T(A] )})` | TypeCall-close Error `18..19`, actual record/fact equality in source order, mismatch Error before the actual close |

Before successor expectations are added, legacy embedded direct baselines may
pin direct records, CST, losslessness, remainder, frame balance, and the named
CallArgument/close continuations, but make no nonexistent embedded AST-fact
equality claim.  Every O6 row also proves frame pop and a clean following
`\ref(C)` through the real successor route.

Return to architecture without implementation if direct legacy baselines
contradict these ranges or continuations; same-line retry leading cannot be
handled transactionally through one borrowed Item frontier; a caller boundary
would enter Error; preserving a cell needs source/range retention, copying,
replay, Item splitting/cloning, a secondary builder, or nested Error recovery;
or behavior leaks into a non-Call owner.

T2a/T2b, every other Type/PV owner, Pattern/Expression/declaration owners,
Yumark/session transport, public dispatch and cutover, legacy deletion, and
O4/O7 broad suites remain out of scope.

## 5. Cost, review, and approval

T3a adds only bounded Call-phase and inherited-ML branches on valid Call
parsing.  T3b runs only after a malformed CallArgument Error finds one immediate
retry Item.  Let `L` be that Item's total leading source bytes plus
leading-part count.  Classification uses a constant number of `O(L)` scans and
one prefix-emission pass; each accepted leading part emits at most once.  It
adds no source buffer, event stream, replay state, Item clone, or valid-path
rescan.  Static review must reject any quadratic path; the proposed timing
budget is zero unless it finds material uncertainty.

M3 compiler/recovery, specification, and performance review accepted this
design after one batched repair and clean compiler/specification delta review.
If the user approves, T3a is implemented and reviewed as the first coherent
gate; T3b then follows under the same approved scope.  This Reviewed design
records no user approval and authorizes no implementation.

## 6. Horizontal-gap boundary-priority implementation suspension

Direct legacy evidence at `c54c78c6` resolves the previously unselected
post-item anchor class in §2.1 and contradicts the completed successor T3a
boundary behavior.  After a completed Call argument, a generic caller or outer
close following ordinary horizontal trivia leaves its payload raw but the Call
owner emits that trivia and anchors its own close Missing after it.  Thus
`G T(F ]` leaves raw `]` and publishes TypeCall-close Missing `6..6` after the
Call owns space `5..6`; `G T[T(F ]->U` analogously publishes at `8..8` before
BracketRow consumes the `]`.  ASOB remains distinct and preserves the complete
space-plus-boundary gap before its close Missing.

This is a material architecture-return condition.  It suspends only T3a's
post-completed-item horizontal caller/outer-boundary CST, frontier, and
close-Missing range certification.  T3's CallArgument/CallArgumentSeparator
construction, inherited type-ML behavior, provenance-blind phase preservation,
matching local close, EOF behavior, and all T3b Error/terminal work remain
retained.  The shared P/E evidence in `820dca87` and `c54c78c6` shows that no
T3-only or P/E-only repair is coherent.  This document is not authority for a
boundary repair until a reviewed, user-approved successor distinguishes ASOB
whole-gap handoff from immediate-owner horizontal trivia consumption followed
by raw caller/outer payload handoff.  That successor must first execution-pin
the corresponding initial and post-explicit-separator horizontal-gap phases;
they remain uncharacterized here.
