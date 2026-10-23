# R344 outcome — K0 Call same-witness interface

**Status:** closed as a bounded research sprint after fresh independent
review. The accepted result is limited to the authentic selected-definition
K0 scope and the premises in the frozen proof. The full Yulang2/Simple-sub
source/native theorem and original A/B goal remain unchanged.

Frozen contract rev1 SHA-256:
`5fdf7dabdb96df7c22b07c5a5056b6c2bc65ad01e9f5ff2f40ca02c6572ec78b`.
Frozen source census SHA-256:
`90678f8570dd7619dcaf5a1ad6ad0b149031b449480d1d9cc3f9708ebf549195`.
User audit SHA-256:
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`.

## Dispositions

- **`R344-JOINT-PREFIX` — bounded PASS.** One authentic source Apply, one
  retained native Function demand and one assignment `ρ` correlate the four
  ordered ports `(argument value, argument effect, return effect, return
  value)` with one actual call witness. The proof retains the actual callee
  handle and saved capture, whole argument Delay and caller environment,
  invocation and owner chain, received argument record/view, and same result
  fields on an actual normal return. No call termination or future return is
  assumed.
- **Handle-indexed source origin — bounded PASS.** The ghost origin table is
  rooted in R336's independently constructed D1/`ρ` derivation at each exact
  HIR Lambda allocation. It is preserved by actual handle lookup, capture,
  forwarding and ValueEntry binding. Four-port inversion uses the stored
  intrinsic derivation for that handle, avoiding an unsupported claim that an
  arbitrary existential `TypedVal₀` proof contains `ρ`'s endpoint types.
- **`R344-REVERSE-VALUE-ENTRY` — restricted bounded PASS.** From the aligned
  independent derivation and the same reachable actual runtime realization,
  authentic K0 closure construction selects actual Value entry and the whole
  argument Delay under its caller environment. This is not a converse from an
  arbitrary negative Function term or complete native Function meaning.
- **Conditional result/effects/current future — bounded PASS.** R342 supplies
  same-result typing only after an actual body return; R343 preserves that
  result in the existing reachable K0 continuation and owner chain. Symbolic
  callee, argument and body effect credits remain distinct and compose with
  the enclosing credit. This does not interpret arbitrary native effects or
  future continuations. Budget pauses preserve the current witness; checked
  invocation identity exhaustion is a stopped resource refusal, not a
  successful entry.
- **Exact remaining supplier — OPEN.** At receiver entry, the proof still
  needs the original complete receiving and output-dependent result/future/
  effect interpretation for the same native record, `ρ`, provider/carrier and
  actual call witness, then transport through ValueEntry and ReceiverReturn.
  The owner is
  `PendingCallSupplier::ReceiverDispatchAndCompleteResultFutureInterfaces`.
  The broader `ArgumentReifyAndWholeCarrier` obligation also remains open.
  `NativeInterface` retention before admission is not a semantic consumer;
  `Receiving::matches_value` establishes same-handle identity only, and an
  opaque view retains unknown coverage. These identify missing proof
  suppliers, not a source-qualified compiler counterexample.
- **No compiler defect / no safe code slice.** The census and independent
  reviewer found no authentic K0 counterexample. Compiler source remained
  read-only; no code, test, build or expected-output changes were made.

## Independent review and frozen evidence

Fresh non-contributor `/root/r344_joint_review` (`compiler_referee`) returned
bounded PASS with no BLOCKING, major or minor finding. It independently
matched all **27 distinct supplied SHA-256 pins**: contract, census, proof,
handoff, audit, twelve prior evidence artifacts and ten source files. It
checked both call directions, the shared four-port witness, D1/`ρ` origin
provenance, actual handle/capture/Delay/owner/view/result identities, resource
cases and the exact missing complete-interface boundary. It found no
source-qualified counterexample.

The proof writer stopped at `2026-10-23 08:21:18 UTC`; the reviewer stopped at
`2026-10-23 08:24:30 UTC`. Exact active runtimes and effective model/effort
were unavailable, so the full 3,000-second proof grant and 1,500-second
review grant are charged conservatively. Requested settings were Sol/high
for the prover and role-default Sol/medium for the reviewer. Both lanes were
message-only/source-inspection work; no tests, Cargo, builds, execution
probes, Git, network, writes or descendants were used by either worker.

| R344 artifact | SHA-256 |
| --- | --- |
| Contract rev1 `tasks/agent-loop/sprints/r344-k0-call-interface-20261023.md` | `5fdf7dabdb96df7c22b07c5a5056b6c2bc65ad01e9f5ff2f40ca02c6572ec78b` |
| Source census rev1 `notes/theory/2026-10-23-r344-k0-call-interface-source-census.md` | `90678f8570dd7619dcaf5a1ad6ad0b149031b449480d1d9cc3f9708ebf549195` |
| Proof rev1 `notes/theory/2026-10-23-r344-k0-call-interface.md` | `9d03677ee92d9180aa801f448d437979c43160b2497126c5362045798608fc16` |
| Producer handoff rev1 `tasks/agent-loop/inbox/20261023-r344-k0-call-interface-prover.md` | `e972bb53864cd46f4724184bca0692c4633717cfdcb75be78368c5ed0b17f850` |

The proof and handoff are frozen after writer STOP. Luna's R344 integration
includes the reviewed proof, handoff, this outcome and compact current state;
the audit remains unstaged. Primary source allocation is charged at 2,400
seconds, proof at 3,000, review at 1,500, and integration at 300. The full
7,200-second envelope is charged at closeout; unused time is discarded, with
no carryover. Three legacy UNKNOWN worker identities remain quarantined.

## Application to S0 and remaining gates

Apply the accepted conditional result under exactly R341's existing S0
premises:

```text
ValidK0(s) ∧ NativeComplete₀(s,S) ∧ ρ ⊨ H(S) ∧ Reifiable₀(ρ).
```

R341 supplies independent source typing at the authentic endpoints; R343
supplies reachable typed K0 states after the same ordinary RuntimeProgram
has actually been constructed and entered through selected-definition
execution. R344 then correlates each actual returned-callee boundary with
its native demand and call witness. No new premise is added to S0; graph/model
existence, construction success and termination are not inferred.

Full C/M, the complete receiver/result/future/effect interpretation,
independent F1/FK1, Comp/operations/handlers and arbitrary foreign
continuations, N/cache/propagation, W/model construction, Z/solver termination,
source completeness, export transport, principality, the original A/B and
catalog, and production remain **OPEN**. No audit-wide or production claim
follows from this bounded supplier.

The static `python3 tools/agent_sprint.py check` is workflow evidence only; it
is not mathematical proof or independent review. No unit tests, Cargo, builds
or runtime probes were run.
