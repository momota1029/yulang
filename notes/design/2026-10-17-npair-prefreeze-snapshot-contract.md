# Pre-freeze candidate snapshot: readiness decision

Status: **WAIT — no implementation-ready API contract**.
Sprint `npair-prefreeze-observation-boundary-20261017`, revision 1, SHA-256
`88a4a99d4b65cd7d582343455344e916300f168eb1d03d3b8aafed8066793b08`.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN.
This is the Luna readiness artifact under the exact assigned lease; it does not
expand source authority or grant compiler-code authority.

## Decision

The proof finds that `InferenceSession.bounds` and `effect_bounds` remain live
at the lexical seam after successful `execute()` and before consuming finish.
A shared borrow from that actual session could therefore avoid the earlier
post-solve storage-loss problem. This establishes visibility only.

The required completed/quiescent observation point is not established. The
pinned `execute_candidate_graph_plan` calls source-driver functions whose bodies
are outside this sprint's six-file source set. Local route commit, typed-drain,
replay, restoration and intrusion facts do not show that all their continuations
are complete at the top-level successful return. `execute() == Ok(())` and the
current finish assertions are not a substitute for that proof. The required
same-owner/non-escape API is also only conditional; no such private API exists.

Therefore this sprint does **not** specify an endorsed one-shot API, callback,
certificate or quiescence gate. Inventing a predicate here would turn the
missing source-return premise into an assumption. No code, test, probe or
source expansion is authorized by this readiness result.

## Exact next evidence and boundary

`NPAIR-PREFREEZE-DRIVER-RETURN-20261017` is the first missing premise: a
source-return invariant over every successful candidate path showing that no
route, typed frame, current/queued task, unconsumed replay child/return,
unfinished restoration or source/Local continuation, or intrusion pending/
dirty work remains at the proposed boundary, with processing restored to the
correct top-level state. The falsifier is any successful top-level return with
one of those obligations unfinished, or a proposed check that observes only
journal absence, queue emptiness or `Ok`.

The relevant `execute_candidate_source_root`, `execute_candidate_loose` and
`execute_candidate_expression` bodies need exact current source-owner paths and
pins. The proof intentionally did not expand its six-file lease; historical
pins do not establish current authority. The sprint contract says to return to
Luna if another pin is required, and to stop snapshot work if the safe point
cannot be established. So the result is WAIT, not another audit request under
this sprint. Any resumed work needs a new Luna decision fixing those exact
inputs and its scope.

Only if that premise is independently established can a future bounded API
contract address owner-minted checked physical-slot resolution, callback
non-escape, deterministic bounded traversal, incomplete antecedents and
resource accounting. The previous post-solve proposal remains a separate
reviewed-partial artifact; its storage transfer idea does not discharge this
pre-freeze completion premise.

## Parent and implementation status

The complete structural snapshot premise for the original negative-pair parent
stays OPEN. Original quantifiers, source domain and occurrences are unchanged.
`eta_op` / `realization_op`, adopted `At`, source admission, N-Transport,
N-Subtract-Elim, receive consumption, semantic promotion and production remain
unproved or WAITING as recorded in the parent state. This blocker applies to
snapshot-dependent implementation only; it does not close or refute the parent.

No source, semantics, tests, expected output or compiler code changed. No tests,
builds, probes, Cargo commands or source execution ran. Readiness used the
frozen proof and handoff plus the sprint contract; no additional source owner
was opened.

## Frozen evidence and resource receipt

- Proof: `notes/theory/2026-10-17-npair-prefreeze-observation-boundary.md`,
  SHA-256 `a80738cdb7ff40bc7f72b773490935a3657b8af442c2830e78d2a2208b5cda6b`.
- Proof handoff: `tasks/agent-loop/inbox/20261017-npair-prefreeze-observation-boundary.md`,
  SHA-256 `e64026fa9b51d4dfb20f34dd61db74be858f3f4c9c444a5e252c7e15db935837`.
- Contract: `tasks/agent-loop/sprints/npair-prefreeze-observation-boundary-20261017.md`,
  SHA-256 `88a4a99d4b65cd7d582343455344e916300f168eb1d03d3b8aafed8066793b08`.

Luna readiness charge: 240s of 240s, conservatively charged at the lane cap;
no carry-over. Total sprint charge at readiness freeze: 480s (60s coordination,
180s proof, 240s readiness). Three independent sequential reviews, 180s total,
remain. Parent remains OPEN. No code lease.
