# Question: source-owned expression annotation bridge

Question ID: `source-annotation-typed-root-bridge`
Question revision: `q1`
Predecessor/history: none
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `1b57072ad`
Task/thread locator: unavailable; the active objective is supplied in the conversation context, with no exposed thread identifier
Governing source/section: approved `questions/2026-10-05-source-annotation-boundaries` q1/d1; approved `questions/2026-10-08-native-direct-consumer` q1/d1; `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3.2(6), 3.4; `notes/design/2026-10-08-native-direct-consumer-plan.md` §§2–3; `rules/design-authority.md`, “Approval and implementation gate”

## Requested scoped decision

Choose the next design gate for connecting one authentic source expression
`as Type` boundary to typed targets and, where applicable, the native ordinary
`Direct` checker. This does not reopen the already approved boundary behavior
or change the checker semantics.

The proposed source-owned bridge would retain the current completed operand
endpoint and prior evidence, elaborate the exact written Type into a completed
target in its original scope, establish the local proof-only inclusion or the
separate admitted executed conversion, and export the target with accumulated
evidence. An ordinary-root producer would construct complete roots when a
proof-only case uses Direct. Direct would consume those supplied roots and a
finite proof; it would not elaborate Type syntax or execute conversions.

## Background and current premises

The approved annotation decision selects binding, argument, and expression
annotation boundaries. Each checks the current endpoint directly against its
target, exports that target with local realization evidence, preserves earlier
evidence, and does not allow implicit intermediate concrete adaptation. It
does not specify a Rust representation or authorize compiler implementation.

The approved Direct decision selects a checker-only flat-arena direction for
finite proof terms over complete supplied ordinary roots. It does not approve
production routing, a public API, or F5 replacement. SRC §3.2(6) assigns the
annotation boundary its completed endpoint and retained realization evidence;
SRC §3.4 makes `view(h,q,V)` notation for an actual source checking rule.

Current production HIR retains annotation syntax but has no typed annotation
form and rejects the expression before solver constraints. Shadow occurrence
records remain `PendingTypedPortAndProfile`. Existing F5 negative `Top`
constructors do not provide a standalone ordinary `Any` target root with its
original source scope. PE §6.2's conditional `Any` proof assumes that exact
ordinary root already exists. See
`notes/progress/2026-10-10-annotation-target-elaboration-owner-gap.md`.

The architecture review found the source-owned package is compatible with
both selected proof-only checking and executed conversion. A universal rule
that sends every annotation through Direct would lose the executed-conversion
case; teaching Direct to elaborate written types would expand its checker-only
responsibility.

## Options and consequences

1. **Select source-owned formation with conditional Direct consumption.**
   Approve the described ownership boundary as the next design gate. The
   expression owner supplies the current endpoint; annotation checking
   elaborates the target in its original scope and retains local realization
   and outward evidence. The ordinary-root producer supplies the complete
   roots required by proof-only cases submitted to Direct; conversions retain
   their source constructor and result handle. The next work would
   produce a detailed reviewed design for one authentic expression case,
   including the Any target-root owner, before implementation. This provides
   one path that preserves both selected realization forms, while keeping
   production representation, routing, failure/resource policy and F5 cutover
   as separately reviewed gates.

2. **Demonstrate Direct only with supplied roots first.** Limit the next gate
   to one proof-only occurrence whose ordinary roots and finite proof are
   supplied independently. This exercises the approved checker boundary but
   leaves written-Type elaboration and source endpoint/root formation open; it
   cannot establish a complete source annotation bridge.

3. **Defer annotation work and continue other inference gates.** Keep the
   current annotation findings as research and make no design choice for this
   bridge. This leaves the production annotation and ordinary-target owners
   unresolved while other independent inference work proceeds.

Options 2 and 3 do not reject approved annotation behavior or authorize
permanent annotation exclusion. None of these choices by itself approves F5
replacement or cutover.

## Affected work

Blocked scope: selecting this annotation-to-typed-target design gate and
writing its detailed design. No compiler implementation is authorized by this
question.

Independent authorized work: continue the separate source registration,
public projection, Function/effect, principality, residual, and F5 replacement
gates without assuming an annotation API or Direct production caller.

Required answer: select option 1, 2, or 3, with any scope restriction.
Explicit approval must refer to this question revision.

Pending publication: keep this entire question directory unstaged and
uncommitted until the questioning primary discovers and validates an
explicitly approved local answer and commits the matching question/draft/
answer together. The answering primary never mutates Git. Posting does not
pause the goal; dependent work waits while independent work continues on
disjoint paths.
