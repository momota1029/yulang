# CaseLike Arrow/Body current-Item recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: Case/Catch arm Arrow and inline Body only. This replaces their raw
`Missing`/`Error` emission with atomic typed records and selects the one
root-cause representation for simultaneous Arrow/Body absence. Block, Arm,
Pattern, Handler, Scrutinee, Guard, Separator, Catch close, accepted grammar
and indented-body ownership remain outside this gate.

Authority: Case/Catch recovery contract, typed-output amendment §§3--4 and 6,
recovery-authority §§1--3, and SCC amendment E12f/g/j. The recovery authority
permits the selected successor representation below; it does not alter the
accepted-input Yulang2 evidence or the operator judge.

## Roles, root cause and records

| immediate condition | one typed publication | continuation |
| --- | --- | --- |
| Arrow absent; current Item is an admitted Body NUD | `CaseLike(Arrow)` Missing, punctuation Arrow | retain the Item and enter Body from it |
| Arrow absent; Body is absent at the same boundary | one `CaseLike(Arrow)` Missing with the two expectations below | return the exact boundary Item |
| exact Arrow admitted; Body absent | `CaseLike(Body)` Missing, Expression | return the exact boundary Item |
| Arrow absent; non-NUD non-boundary Body payload | Arrow Missing, then `CaseLike(Body)` Error | lexical retry |
| exact Arrow admitted; non-NUD non-boundary Body payload | `CaseLike(Body)` Error | lexical retry |

The simultaneous-absence record has zero-width `site` role
`CaseLike(Arrow)` and its ordered expectation union is:

1. `CaseLike(Arrow)`, punctuation Arrow, same zero-width range, primary index
   zero;
2. `CaseLike(Body)`, Expression, same zero-width range.

Both expectations have `COMMITTED_RECOVERY_RULE`; Missing has no unexpected
facts. It emits exactly one `Missing` CST node. The Body expectation is
diagnostic evidence, not another CST node. This explicitly supersedes the
Case/Catch recovery-contract phrase requiring internal slot markers *only for
this simultaneous root cause*: the one typed node/one typed record is the
needed marker. It also supersedes E12f's Arrow-as-Expression mapping and
E12j's second Arrow Error mapping, while retaining all their source literals.
The first now publishes Arrow punctuation; E12j publishes Arrow Missing then a
Body Error over the actual malformed run. E12g retains one Body Missing,
expected Expression.

Body Error has `CaseLike(Body)`, expected Expression, one `OtherCharacter`
token fact per native emitted lexical token, and its nonempty actual run range.
Nested expression recovery continues to choose its own immediate role.

## Boundary, leading and retry

Classify an inline Body absence before emission: abstract fence/EOF boundary,
active stop, explicit line stop, ordinary EOF, unread close, or a non-NUD
bracket opener. The close/opener cases are mandatory absence, not lexical
Error. A braced expression NUD remains admitted unless its active stop owns
the opener.

For every protected boundary other than ordinary EOF, leave the whole pending
Item and its leading untouched and anchor the Missing at the inspected abstract
coordinate or remaining-start. Ordinary EOF emits its existing remaining
leading in the Arm before anchoring Missing. Leading that was emitted by an
earlier arm owner is never recreated. These rules apply identically to the
combined Arrow/Body absence and actual-Arrow Body absence.

For a malformed Body payload, emit the initial current-Item leading directly
into the Arm, then consume one maximal nonempty lexical Error run with the
existing `expression_item` scan. Internal run leading belongs to Error;
retry/boundary leading does not. The scan stops before an admitted NUD or any
absence boundary named above. It does not invoke a grammar parser or builder.
After Error, return any boundary unchanged with no second Body Missing, or
append the admitted NUD through ordinary Body logic outside Error. Preserve
the Item/suffix/origin/line handoff, mode, stops and outer sequence policy.

No source replay, nested builder, retained run vector, new generic recovery
API, scanner, diagnostic sorting or accepted-layout change is permitted. Cost
remains one forward lexical pass, `O(bytes + structural work)`.

## Required evidence

Retain and audit E12f `case x: n yes`, E12g `case x: n ->`, and E12j
`case x: n @, _ -> b`; assert the exact successor records above. Add Case and
Catch Arrow/Body exact fresh, shifted, frozen and seeded records, including
shared absence after Pattern, Handler and Guard recovery. Cover ordinary EOF,
comma, semicolon, dedent, outer close, unread non-NUD opener and quoted fence,
before and after a raw Body run. Check UTF-8, CRLF, foreign-prefix coordinates,
accepted Arrow and following-arm continuation, and nested prefix/literal retry.

Before changing assertions, audit existing normalized controls: the missing
counts for `case x: n if` before a quoted fence and `case x: n` before `]`
fall by one because two raw markers become the one combined record. Preserve
their accepted text, exact remainder, pending boundary and line entry. Keep
actual-arrow EOF at one Body Missing. Separator and Catch-close expectations
remain untouched. The eight Catch handler/Arrow/Body normalized boundary rows
likewise each fall by one; an existing Handler or Catch-close marker remains
distinct and in source order.

M2: one implementation pass; compiler/recovery and regression reviewers in one
round; at most one repair bundle. Run focused CaseLike/output/normalized
controls, package check, scoped format and diff. Benchmark use is zero absent
material uncertainty. Synchronize task, ledger and daily progress before the
coherent commit.
