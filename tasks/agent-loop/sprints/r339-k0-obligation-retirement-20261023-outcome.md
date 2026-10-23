# R339 outcome — K0 obligation retirement and Value-call prefix

**Status:** closed as a bounded research sprint. No parent theorem or production
gate is promoted. Contract rev2 SHA-256:
`953d0edfffc99645ab137819ae44d35a7df03b8e775b4e97317f825657dfaa00`.
User audit SHA-256:
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.

## Outcomes against the unchanged K0 obligations

- **D2 — narrow PASS:** for each actually emitted ordinary
  `candidate_replay_bound` child `q`, the two stored bounds `l ≤ o` and `o ≤ u`
  survive cache check, acknowledgement, reclamation and frame pop, so
  transitivity gives `H_after ⊨ q`. The one-child acknowledgement preserves
  `Sol(H)`. This does not prove whole-frame equality for initial, designated,
  processing or FunctionPort obligations, nor N or cache/temporal coverage.
  Proof: `notes/theory/2026-10-23-r339-k0-obligation-retirement.md`
  SHA-256 `8797013ab5ea77655629fce45031fb28e1c5557979c1f213b9268abd31080c87`;
  handoff SHA-256
  `cc597a0cbe1a6045e8bbb312f7fb5036858d5f66c8a4a99944c83b1a2c67e35b`.
- **D3 — OPEN / MAJOR proof-statement gap:** the reviewed note defines source
  typing and code/value/environment realization independently of successful
  execution, and traces the actual closure, whole argument Delay, formal/body,
  invocation and frames. Its input configuration is only
  `Evaluate(k_f, ηcaller)`; it carries no stack, call site, caller owner or
  continuation relation. The proof assumes the authentic preceding Apply push,
  so the claimed prefix does not yet start from the source Apply configuration.
  Reviewed note SHA-256
  `4301ed7e184915e75646809102a477f8d4b27f874478e364c03886ae1cfd2666`.

## Exact missing continuation premises

The next proof must keep the original M obligation and establish these links:

1. Relate an authentic source `Apply f a` and its lowered call/site labels to a
   configuration with stack `κ · Callee(k_a, ηcaller, site)` before callee
   evaluation. The frame must contain the whole argument code and actual caller
   environment.
2. Identify the current caller owner and show the same Callee frame and stack
   prefix survive the assumed callee-evaluation/return segment. Relate the
   returned actual `ValueHandle` to its `ExecutableValue::Closure`, saved
   capture environment and source Lambda realization; `SourceSite` alone is
   not closure identity.
3. At the matching Callee return, derive the actual
   `κ · ReceiverReturn(activation, previous) · ValueEntry(parameter, body,
   saved_environment)` continuation, fresh activation/owner and
   `Delay { code: k_a, environment: ηcaller }` for this same Apply.
4. For the conditional argument-return step, preserve that prefix, force the
   whole Delay in `ηcaller`, and bind the received value to the exact formal in
   the saved closure environment before evaluating the exact body.

Without these premises, the reviewed source/runtime trace is not a simulation
from an authentic Apply input. The reviewer found no source-qualified K0
counterexample or compiler defect; canonical-form/value-realization and
environment-transport suppliers also remain separate OPEN premises.

## Review, scope and next step

Fresh reviewer `/root/r339_bundle_review` stopped at 2026-10-23 05:44:03 UTC;
the full 750-second grant is charged. Dispositions: D2 PASS only for the stated
`q` family; D3 OPEN / MAJOR for the missing continuation premise. Selector
`/root/r333_selector` recommends closing R339 with D3 OPEN, preserving the
reviewed note hash, and using the next bounded outcome to prove the authentic
Apply handoff and continuation-prefix invariant before reapplying the existing
closure/environment/Delay argument. No repair or delta-review cycle is
authorized by R339.

R338 admission delta remains OPEN / incomplete: its separate 150-second review
checked amendment semantics without a new finding, but ended before byte-exact
rev1/rev2 comparison. It is not adjudicated by the R339 bundle review.

No compiler source was changed; implementation outcome is `NO_SAFE_CODE_SLICE`
because this review identified a proof premise gap, not a source defect. No
tests, Cargo/builds or probes were run. The only repository check is
`python3 tools/agent_sprint.py check`; it passes as static state/tooling
evidence, not as proof or independent review. Full N, W, Z, S0, principality,
original A/B, catalog and production remain OPEN. The user audit remains
untracked and is excluded from integration.

R339 resource grants: D2 producer 1,200s, primary D3 1,200s, R338 delta review
150s, fresh independent review 750s; integration charge and final hashes are
recorded in `tasks/agent-loop/current.json`. No carryover.
