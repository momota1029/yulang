# R81 Stage 1 readiness

Date: 2026-10-19  
Sprint: `effect-hygiene-role-call-20261019-r81`, revision 1  
Contract SHA-256: `57989ca9d6f7b54d2bffa37fb5399f9d0bcaf16ea5193109d7bb7c7547914c16`  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
State: **Stage 1 artifacts frozen for independent review; adoption not yet ready**

## User priority and intended outcome

This sprint follows the user's current direction: balance breadth and depth,
prove useful method/role behavior alongside broad effect-hygiene evidence, and
reach the first runnable surface early. The six effect frontiers are a bounded
status map, not six claimed proofs. Storage/fiber inventory is outside scope.
The first proposed runnable program is `SecondInt::second 1 2`, with result
`2`, through ordinary Call/Apply. No source code or test command was authorized
or run in Stage 1.

## Frozen artifacts

- Draft decision: `notes/design/2026-10-19-r81-role-call-adoption.md`, SHA-256
  `793d71bf345a972d62dd24957cdcca42ed546f201e24b5be989e2004a168ec6d`.
- Conditional proof and status map:
  `notes/theory/2026-10-19-r81-role-call-request-prefix.md`, SHA-256
  `d3b3d52e19332506c6fab8eea7878a5ff1c81f90cf96dff548b30ab5f88c767f`.
- Proof handoff: `tasks/agent-loop/inbox/20261019-r81-proof.md`, SHA-256
  `db9aad31fcd982ab92087bf5b70ba472c9916fe07b2939e20bdca3e499b25cb0`.
- Prior R80 closeout:
  `notes/progress/2026-10-19-r80-rev2-closeout.md`, SHA-256
  `8b6593f1d2bc55a1c37065e2e9fd780cec46f3c92b3076329bde065f80f989f7`.
- Source manifest:
  `tasks/agent-loop/sprints/r80-producer-manifest-20261019.md`, SHA-256
  `a54331b710300baeb0b88a2032dccc0cf73a7cca838242643255e44108179803`.

The producer reports all 103 pins match. The design and proof artifacts are
frozen for fresh independent compiler/source and spec/design review. Their
findings decide Stage 1 readiness; authorship does not.

## What the Stage 1 evidence establishes

The proof gives a conditional ordinary-Apply prefix derivation. If the
unimplemented role path supplies exact selected-member identity, executable
root/environment, original binder annotations, ordinary curried graph and
complete admission, selection itself adds no entry or handler rule. From the
same initial state it transfers ordinary execution through completion, failure
or the first unanswered outward request. The pure example conditionally
completes with `2`.

The R80 unhandled Value example now stops at the first `observe(1)` request.
The Value formal has not returned, the next curried closure has not been
returned, and the second argument has not entered. The suspended suffix retains
the pending receiver entry and later application. No `observe(2)` or final `2`
is promised. Existing expected outputs remain untouched.

The Draft compatibility judgment compares exact arity, receiver and parameter
roles, bounded ground endpoints, and explicit annotations. Executable binder
roles remain those fixed by charter §21; a mismatch rejects that implementation
under the proposed pilot rule and never inherits a role from the signature.
The accepted-certificate lemma is finite and conditional on ordinary endpoint
evidence. It does not prove general conformance, source producer correctness,
or inference soundness/principality.

## Effect-hygiene frontier status

| Frontier | Current evidence | Still open |
|---|---|---|
| ordered matching handler | inspected ordinary consumer; R78 exact-fixture evidence remains conditional | complete source-generated selection membership |
| Value/Computation entry | §21 source rule and ordinary consumer traced; binder role retained by proposed compatibility certificate | role-member materialization must preserve authentic annotations |
| wrong or sibling permission | R78 fixture-conditional exact-positive-permission evidence | authentic source sibling construction and protected-sibling proof |
| shallow unmatched request | R78 fixture-conditional outward request evidence | native residual typing and complete source projection |
| continuation | one bounded pinned capture/binder/resumption path reported | full continuation-template owner and protected-sibling preservation |
| static → native/runtime | conditional source/candidate/runtime path reported | native operation/formal and joint K,D/residual owners |

These labels do not constitute a general hygiene theorem. No exhaustive storage
or fiber analysis was performed.

## Runnable path and hard gates

Current source facts stop before role-member execution: parser/HIR occurrences
do not yet supply an executable selected-member identity, and candidate/runtime
admission is not established for validated role/impl roots. The proof reports
P1–P4 as unproved producer hypotheses. The next implementation path, if
adopted, must establish declaration validation, exact member materialization,
ordinary Call formation, candidate admission and RuntimeProgram execution as
one source-qualified chain.

R80's previous unpinned dispatcher inspection boundary is resolved. Complete
literal-to-LocalSource projection remains OPEN; this does not allege a parser
defect. Native K,D/residual correspondence, protected-sibling preservation and
the original A/B obligations remain OPEN. Original parent/A-B stays OPEN 0→0;
R50 stays NOT_ADOPTED.

Stage 1 reserves 1200 seconds in total: design/bookkeeping 600, proof 300,
compiler review 150 and spec review 150. The proof allocation is fully charged;
review allocations are reserved for the two fresh reviews. No time carries
forward. At this snapshot, both review receipts are pending. Stage 2 has zero
issued/reserved time and no code authority. New semantics remain Draft pending
independent review and explicit user adoption. A major review finding blocks
readiness; no automatic correction retry is authorized.
