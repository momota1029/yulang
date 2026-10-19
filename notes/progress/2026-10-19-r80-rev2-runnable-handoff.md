# R80 rev2 runnable-surface readiness

Sprint: `effect-hygiene-role-call-20261019-r80`, revision 2  
Contract: `tasks/agent-loop/sprints/effect-hygiene-role-call-20261019-r80-rev2.md`  
Status: Stage 1 active; design candidate only; no semantic adoption or code authority  
Original evaluator/A-B: OPEN 0→0; R50: NOT_ADOPTED

## First runnable target

The proposed first result is `2` from:

```yu
role SecondInt { my second: int -> int -> int }
impl int: SecondInt { my second self selected = selected }
my answer = SecondInt::second 1 2
```

The role-qualified call is Draft. It offers a way to run one role-backed method while leaving general `receiver.member(args)` field precedence unresolved. No parser or compiler execution was performed to establish this program today.

## Approval-to-execution cutover

Stage 1 prepares and independently reviews the bounded proof and all semantic choices: role qualification, receiver-first ordinary Call, duplicate-key behavior, and diagnostic ownership. If the user explicitly adopts the exact reviewed draft, Luna records that authority and issues a separate Stage 2 contract. Only then may a worker edit code or run a command.

The Stage 2 destination is one vertical path: role/impl/member source identity → validation and executable member materialization → ordinary curried Call → `CandidateInference` admission → `RuntimeProgram` metadata and execution. The first focused verification targets a named runtime module-expression test and one `.yu` CLI fixture. Exact implementation paths, hashes, test fixture ownership and command receipts must be frozen in the Stage 2 contract before edits. Expected output `2` is a regression result, not a proof.

## Current source gates

R79 established that the prior role draft mismatched charter §21: an unannotated executable binder has Value entry, regardless of a Computation role signature. This draft now explicitly writes `(action:[_] int)` in the executable impl binder and makes no inheritance claim. R79 also required a complete missing-role program, which this draft now includes separately from missing member and missing implementation.

The current HIR path retains role and impl syntax occurrences but has no approved semantic resolution/admission path in this candidate. The existing candidate preflight and playground admit only their existing source-supported nodes. The Stage 2 design must materialize a validated member root and exact identity before exposing the candidate to solver/runtime consumers; generated Apply edges alone cannot supply either.

## Effect-hygiene breadth

The proof packet maps six fronts with separate status and owner: ordered local selection, Value/Computation entry, wrong/sibling permission, unmatched outward request, one bounded continuation/protected-sibling path, and one static-to-native/runtime operation path. R78's three runtime derivations stay conditional on authentic LocalSource input and establish no universal hygiene or native residual result. R79's parser-root gap remains OPEN. Any native or continuation owner outside the manifest stays uninspected until Luna pins it.

This advances effect coverage without using open-ended storage/fiber inventories as the standing goal. The role-call simulation remains the main constructive deliverable; six status entries are not six claimed proofs.

## Future-only commands

After adoption and under a new Stage 2 contract, propose:

```sh
cargo test -p yu-playground --test runtime_module_expressions role_qualified_member_call_returns_expected_integer
cargo run -p yu-playground -- --run answer tasks/agent-loop/fixtures/r80-role-call.yu
```

These commands are not authorized in Stage 1. Their test and fixture do not yet exist.
