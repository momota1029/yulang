# Callback hygiene through an ordinary identity function

Date: 2026-10-15
Status: Authoritative for the explicit behavioral decision below; source construction and proof remain open
Approved-by: user, directly in the continuing playground hygiene conversation
Reviewed-by: spec_auditor, pre-write scope and post-write transcription reviews; no remaining findings
Scope: identity forwarding in the exact Yulang2 playground Callback Hygiene example and the direct clarification of ordinary forwarding for unhandled effects
Supersedes: the unresolved behavioral alternative in question 2026-10-15-callback-identity-release revision 1; no compose decision is superseded

## Direct decision

The user stated:

> 「id (h i) に包んでも、元の例と同じく callback の return は外側まで抜ける」という意図ですね．idは高等関数なんで意味がついては困ります

In the [exact original example](../../tools/inference-playground/oracle/callback-hygiene.yu),
add the ordinary definition `my id x = x` before `g` and replace only the loop's
`h i` with `id (h i)`. The callback's `sub::return 0` still bypasses `g`'s local
`sub` and reaches the outer `sub`. The pending `println` and final `2` in the
outer block are discarded. The program's displayed result remains only `0`.

This follows the ordinary behavior of the defined function. The identifier
`id` has no special inference or runtime rule. The decision cannot be
implemented by recognizing this function's name or this example's spelling.

## Direct clarification: ordinary forwarding of unhandled effects

The user subsequently clarified:

> idを挟んだ例は`id`が`h i`のエフェクトを素通りさせたからなんですよね．非ハンドラ関数はエフェクトを素通りさせる関数として振る舞います．

When execution through a function produces an effect that the function does
not handle, the function forwards that effect outward. Ordinary `my id x = x`
is one instance. In the selected Callback Hygiene example, inserting that
identity call does not change the callback return's required outer handling.
This follows from ordinary function semantics, independently of the
identifier's spelling. Handling is specific to the effect: a function that
handles one effect still forwards another effect it does not handle.

Forwarding does not consume the effect. The selected compose operation still
releases its attributed protection scope while preserving the effect
contribution, attribution and independent protections. Forwarding therefore
does not assert that every protection marker is unchanged. Annotation
permission alone does not perform handling.

This clarification changes no evaluation order or Value/Computation parameter
role. It does not require execution of an unused retained computation, choose
a runtime representation, or discharge the open source-correspondence and
hygiene obligations. The direct user statement supplies approval of this
behavior; no separate question-board answer bundle is claimed.

Clarification review: `spec_auditor` accepted the scope before transcription;
post-write transcription review found no findings. The earlier review attribution
below applies to the original identity decision.

## Relationship to the selected compose rule

The [compose scope-release decision](2026-10-15-compose-scoped-effect-release.md)
remains binding, including its selected output `['e?, 'f] 'b`. The attributed
`'e` protection must be released wherever it occurs in `f`'s output, including
`f = id`; effect membership, attribution and independent protections survive.
Release alone does not grant capture.

Both observable requirements must follow from ordinary source construction.
The current experimental collision between the h-call protection and an
argument-expression release does not decide which source witness or discharge
boundary is correct. Neither keeping an already released witness nor adding
an unexplained extra shield establishes the required correspondence.

## Authority and completion boundary

The behavioral alternative is resolved directly in the current conversation;
no separate answering-primary draft, approved-answer bundle or bundle
integration is claimed. The questioning primary records this resolution in
the local receipt. The unintegrated question directory stays outside ordinary
checkpoints under `rules/question-board.md`.

This decision approves no particular ownership representation, additional
witness, discharge algorithm, general contextual-equivalence theorem, or
production cutover. Source introduction, capture/FreshUse transport, matching
discharge and actual Catch eligibility remain proof and implementation work.
The original hygiene and soundness obligations remain OPEN.

The [existing native observation](../progress/2026-10-15-callback-identity-scope-observations.md)
establishes a protected/released difference before Catch. Native Catch still
forwards effects, so that observation does not demonstrate actual local capture
or a full runtime counterexample. The previously executed unchanged Oracle
example is separate from execution of this identity variant.

## Review scope

M2 behavioral-contract transcription, with one spec auditor. The pre-write
review accepted this scope and required distinguishing the resolved behavior
from the still-open source attribution. The post-write review found no
remaining findings in the addendum, task/index deltas or direct receipt.
Reference and whitespace checks apply;
this record alone requires no compiler build, test or performance measurement.
