# R80 revision 2 closeout

Sprint: `effect-hygiene-role-call-20261019-r80`, revision 2  
Contract: `tasks/agent-loop/sprints/effect-hygiene-role-call-20261019-r80-rev2.md`  
Baseline: `af3ccf2d63ba7f87e0359e183568db548ea53307`  
State: **REPLAN_REQUIRED; not adoption-ready**  
Original Simple-sub/evaluator and A/B: **OPEN 0→0**  
R50: **NOT_ADOPTED**

## Outcome

The revised goal now spans a runnable role-qualified method destination, a conditional ordinary-Call preservation argument, and six effect-hygiene frontiers. Stage 1 produced a complete Draft decision package and conditional proof/status map. The selector judged the six-frontier map feasible within 1200 seconds as bounded status/evidence, not six completed proofs.

Frozen artifacts:

- Contract: SHA-256 `e7ff179d48156bf3aa897c4e8f186916936a6b0bbcea7bc0314cad3a7e7f110e`.
- Manifest: SHA-256 `a54331b710300baeb0b88a2032dccc0cf73a7cca838242643255e44108179803`; all 103 entries matched.
- Decision draft: SHA-256 `3b57fcafd9021d631c6d709d8c84a99d2417a595146c1bcce8c35193a44c5ca0`.
- Runnable handoff: SHA-256 `4160ef792914f1aa8713dc3c3ab08d63e49530c17abc0da540df826a7b3cbdd6`.
- Conditional proof: SHA-256 `90f2d11a20002fc91d557273cb4f21bd528824bafef501e682f5f624f0d274f9`.
- Proof handoff: SHA-256 `462d16ff3e2f87e5904c1be0963adabb4619866107814682ccf04e64ed1688a3`.

The proof gives an occurrence-indexed conditional simulation from a selected member to ordinary Apply. It states the missing validated role/member/root/environment/annotation/provenance outputs rather than claiming current code emits them. The six-frontier map separates conditional handler selection, §21 entry, exact permission, shallow outward requests, one concrete continuation path and one static-to-native operation path. Continuation template definitions, full native `K,D`/residual consumers, protected-sibling preservation and complete U/O/S literal projection remain OPEN. The R79 `parse_root` read-boundary obstruction was removed by inspection; this does not prove those complete literal projections.

## Independent review findings

Fresh compiler/source and spec/design reviewers both found a **major** defect in the effectful Value example at decision lines 118–130. It contains no handler but promises two `observe` requests and result `2`. Under charter §21, the first Value entry forces `observe(1)`; ordinary unhandled-request propagation then exits before the second stage. The specified trace contradicts the pinned ordinary Apply/runtime behavior. Do not alter existing unhandled-request expectations to make the draft pass.

The spec/design reviewer found a second **major** omission: the package requires compatibility validation between a role signature and executable implementation formals but does not decide the bounded compatibility/rejection rule, particularly when a signature and binder express different entry roles. Rejecting signature-to-binder inheritance does not itself define compatibility.

The spec/design reviewer also found a **minor** readiness mismatch: it says the R79 parser-root gap remains OPEN. The precise state is that the prior unpinned-dispatcher read boundary is removed, while complete fixture-to-LocalSource correspondence remains OPEN.

Both reviewers verified their six assigned hashes and all 103 manifest entries. Their receipts were inline only; both stopped with no files, tests, probes, builds, CLI, Git or semantic adoption. The Stage 1 contract prohibits automatic correction retries. The frozen targets remain unchanged.

## Resources and authority

Stage 1 allocations are fully charged: proof 1200s, Luna design/bookkeeping 600s, compiler review 150s, spec review 150s; total 2100s. Proof observed 307 seconds with startup unknown, so the full allocation is charged; its capped parser/continuation exploration was 71 seconds. Stage 2's 3300 seconds remain unissued and unreserved. No Astra work.

No source, test, fixture, expected-output or runtime file changed. No tests, builds, probes or CLI commands ran. No semantic choice was adopted; no implementation lease follows. The role-qualified call, its diagnostic rules and declaration compatibility all remain user decisions. Preserve the R78/R79 OPEN states and all original parent quantifiers.

One incidental primary search printed an unmanifested HIR test path. It was not used as evidence and is not a dependency; no further read is authorized without a versioned pin.

## Next boundary

Return to `next_action_selector` with the exact example countertrace and declaration-compatibility decision gap. Preserve this failed adoption-readiness result; any further design attempt needs a separately versioned contract and must not be called a correction under R80 revision 2.
