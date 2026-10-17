# Frozen Luna source/native instantiation handoff — revision 3

Sprint: `catch-matcher-target-declaration-20261017`, contract rev1 SHA
`ccb332b41ae50c5361a977bbe6ba9791c5854123c3a20958e70a732ab5262170`.
Parent: original FORWARD-FIRST-CALL A/B and F1/FK1; target `μ_H` declaration
toward `CATCH-EXIT-INPUT-1/M_exit`. All parent gates remain OPEN.

Role/author: Luna primary `/root`, exact two-path source lane. Outcome: static
source/native correspondence for an unadopted Draft rule; no implementation,
accepted-source result or theorem closure.

Revision 2 corrects the MAJOR finding on revision 1 bytes. Compiler referee
found that exact `signal::ping()` lowers to a Unit payload pattern, which means
`Work::CatchArms` passes `payload=None` to `candidate_catch_operation`; it
therefore omits slots 60/61. Runtime Unit handling leaves the environment
unchanged. Revision 2 now says `P=Unit`, no payload binder, no candidate
payload links, and no runtime payload bind for the fixed specimen. It labels
the slots 60/61 binder path conditional on an actual variable payload pattern.
Slots 62/63 and 64/65 remain described only for the continuation-binder
candidate branch. The Function-result guard remains a pre-pop refusal, not
post-pop execution. Proposal bytes are unchanged. Revision 1 of this pair
remains in Git history at the reviewed snapshot.

Frozen target rule and prior review inputs:
- Proposal: `notes/design/2026-10-17-catch-matcher-target-declaration-proposal.md`
  SHA `6fb1fa9844b98fb8173d2faef2c609e35ea65248d78bf193c39ab7a85cee00d4`.
- Proof handoff: `tasks/agent-loop/inbox/20261017-catch-matcher-target-declaration-proposal.md`
  SHA `8d283cd6656f342cdc646cf1d42b710b12cbfb8456b89ba558e73f62843a6b93`.
- Initial compiler review: CLEAN for proposal plus revision 1 source instance
  except the above MAJOR; all 22 input pins matched; 120s charged; reviewer
  STOPPED. This old receipt covers old bytes only.

Corrected pair:
- `notes/theory/2026-10-17-catch-target-response-answer-instantiation.md`
  SHA-256 `6a86f684b0dfd879cc0a14addea293b2bde2766edd53829c2404a4290397de03`.
- This handoff is revision 3; revision2 SHA-256 was `379e0eeef5c002cbe0af51350e446a4de523ce27099c8afc6efd3fe101cf2aee`. Revision2 remains in Git history; revision3 binds the corrected instance hash.

Exact instance skeleton: P=Unit under a Unit pattern, with no payload binder;
B=Int→Int is the operation response; `ApplyOne(r)=Call(r,1)` yields A_S=Int.
The continuation candidate branch uses response ports from the operation
result and answer ports from the original scrutinee endpoint. `ResumeArgument`
consumes B and `ResumeReturn` produces A_S. The runtime Function-result guard
refuses before capture/pop; no execution was performed or claimed.

First missing join: the proposed outside metadata/raw source declaration and
full dependent raw certificate have no actual native/source producer. The
Unit pattern in this specimen supplies no variable payload-use join. Full
response admission, S/frame bodies, current owner/slot resolution, output
provider/future, source binder/Receive map and post-exit metadata correspondence
remain unproved. No `M_exit`, F1 or FK1 closure follows.

Checks: static reads, contract-pin verification and hashes only. No tests,
builds, runtime, probes, code/tests/fixture/expectation edits, network or new
source dependency. Correction was authorized up to 120s within the remaining
source allocation. The unused 90s source balance retires at this freeze.
Writer STOPPED after final hash; no descendants, scratch or pending writes.

The reviewer finding is repaired at the source-evidence layer. A fresh
independent compiler delta review is required; earlier reviews certify only
revision 1 bytes. Spec and architect reviews follow the delta review. Semantic
adoption and any code change require separate authority.


Revision 3 is a hash-only correction to the instance reference. No instance or proof bytes changed from revision2.
