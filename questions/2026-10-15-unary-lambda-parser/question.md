# Complete unary lambda header: parser construction approval

Question ID: 2026-10-15-unary-lambda-parser
Revision: 1
Status: closed by direct user decision; archived at the user's explicit request, 2026-10-15
Date: 2026-10-15
Worktree: /home/momota1029/rust/yulang
Branch: research/simple-sub-intrusion
Source baseline: 13a8e36eb595e97b5667230c7463fdb09aed67b8
Current proof checkpoint: 13e9448c6
Task: collaborative playground, inference and execution completion with proofs
Thread/message locator: unavailable in this API conversation
Questioning primary: current conversation /root
Answering primary: none assigned

## Decision artifact and premises

The complete proposed decision is
[the reviewed parser design](../../notes/design/2026-10-15-unary-lambda-parser.md),
sections 2–4, with the narrow architecture supersession in section 1.
SHA-256: `18d49bdff35490d142e799122a980617ffd0ac5c4789cec1781ad7d4b0313232`.
Two independent reviews found no remaining blocking/major finding. A minor
supersession locator was added without changing the selected behavior.

The exact retained Callback Hygiene source contains `g \i -> ...`.
Current production parsing cannot recognize the inline lambda; the source
spelling is already selected. The old callback endpoint-generation draft does
not authorize its parser construction. Current syntax authority and
`rules/parser-chasa.md` require the grammar/CST/recovery decision to be approved
before implementation. This question adopts no old F5 or expected-callback rule.

## Options and consequences

1. Approve the linked sections for the first unary identifier parser slice.
   A complete `\ Identifier ->` header wins before operator lookup, including
   unparenthesized ML arguments. Use existing inline trivia and maximal
   identifiers/exact arrow, dedicated lossless lambda CST and ordinary full
   expression body with caller boundary/recovery. Nonmatching backslash prefixes
   retain existing behavior. Implementation and focused checks may then begin.
2. Defer this parser construction. Native inference/proof work continues;
   the unchanged Callback Hygiene example retains the parser blocker.

Only the parser construction and its tests depend on this answer. Static
Computation-root observation, FreshUse correspondence and existing-authority
proof work can proceed independently. Additional binder forms, inline-lambda
HIR, imports/loop/std, complete hygiene and native execution remain later gates.

## Requested answer

Approve option 1 for the exact linked design revision, or select option 2.
If the precedence/body contract should differ, identify that change for a new
reviewed revision. Discussion or elapsed time is not approval. No separate
answer bundle or authority is claimed by creating this question.
