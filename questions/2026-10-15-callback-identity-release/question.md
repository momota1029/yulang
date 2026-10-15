# Closed question: callback identity forwarding and scope release

Status: closed by direct conversational decision; archived at the user's explicit request, 2026-10-15
Resolution: [ordinary identity forwarding](../../notes/design/2026-10-15-callback-identity-forwarding.md)
Disposition and provenance: [receipt](receipt.md)

The revision-1 question below is retained as historical context. Its unresolved
alternatives and pending-publication statements describe the time it was asked;
they are not current task gates. This archive is not an answering-primary
approved-answer bundle and adds no language or implementation decision.

## Original revision-1 question

# Callback identity forwarding and scope release

Question ID: 2026-10-15-callback-identity-release
Question revision: 1
Predecessor/history: none; relates to the approved compose scope-release decision
Original worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Relevant source revisions: native scoped behavior e9790f96f154ef0ddf67cb45aa26a569148569d7; source-owner baseline b8a85e101f46192ee192266b1938656c42e2c7e5; current checkpoint 9393af08e7de7471d6e46a9c308db100236ed346
Task/thread locator: current API conversation; stable thread URL unavailable
Governing source: notes/design/2026-10-15-compose-scoped-effect-release.md; notes/design/2026-10-10-annotation-effect-hygiene-integration.md; typed-boundary protection-filter source-attribution premise

## Requested scoped decision

In the original Callback Hygiene example, replace only `h i` inside g's loop
with `id (h i)`, adding the ordinary definition `my id x = x`. Must the callback
return still pass g's local sub and be caught by the outer sub, or may the
argument-scope release make g's local sub eligible to handle it?

This concerns which source witness the argument release selects. It does not
reopen the already selected compose type or its requirement to release the
attributed e scope throughout f's output, including f = id.

## Background and current premises

The user's current request is: `yulang2 playgroundのhygieneの例がきちんと推論されて動くようにしたいんですよね`.
The exact unchanged old example has now inferred and executed successfully
through frozen Oracle a58eefc31's compact web std/control/evidence-VM route,
with the program output `Out 1: 0` and no intermediate println.

The selected compose operation releases its e protection while preserving
independent scopes. The existing protection-filter result allows witness release
while its receiver is live; activity alone does not prohibit release.

Current native constructors use the h-Apply computation scope both for its
omitted-formal protection and for the surrounding id argument release. A bounded
source-generated pair confirms protected state at Catch for `h 0` and released
state for `id (h 0)`. Catch still forwards effects, so this establishes neither
actual handling nor a soundness counterexample. The pair uses named callbacks
because the private carrier cannot admit the exact original lambda spelling.

An independent architect and constructive proof attempt could not establish
whether source formation licenses a distinct receiving-boundary witness here.
Adding a second shield without that premise could circumvent approved release;
guarding release merely by live receiver could also contradict it.

## Options and consequences

1. **The return still escapes g after identity forwarding.** Source formation
   must account for an independently surviving witness, or another reviewed
   attribution construction that preserves approved release. Merely retaining
   the very same released e protection is not an implementation of this choice.
2. **The local sub may handle the return after identity forwarding.** The h
   witness can be the argument's released witness; once no other protection
   applies, ordinary operation matching may select g's local sub. Plain `h i`
   and `id (h i)` may therefore differ in local handling.

Neither option is selected. The original example without id still has its
required outer-return behavior. Other scope/grant/survivor rules remain governed
by existing authority.

## Affected work

Blocked scope: adopting scope attribution or a protection-preserving/erasing
repair for this overlap, and any dependent selective Catch implementation.
Independent work: omitted-else support (committed), authentic source-owner
attachment observations, exact Oracle evidence, module/loop/source admission,
and proof obligations whose premises do not depend on this overlap.
Required answer: choose the intended handler visibility for the identity variant
and record the resulting source-witness attribution without weakening compose.

Pending publication: this directory remains unstaged and uncommitted under
rules/question-board.md. No answer or approval is presumed. Separate answering
primaries write only the selected answer files and perform no Git mutations.
