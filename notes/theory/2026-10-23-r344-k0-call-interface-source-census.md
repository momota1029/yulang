# R344 source census — K0 Call same-witness interface

Baseline: `research/simple-sub-intrusion` at
`5baf93fc64930b2b54fd13b40576985f8ec3db00`, equal to upstream when admitted.
All contract inputs and ten source hashes match the frozen R344 contract.
This is a source correspondence census, not a proof of the missing full M
interpretation. Compiler files are read-only; no tests or probes were run.

## Source Apply and one native Function demand

- `candidate_source.rs:1766–1877` handles an authentic `LocalSourceForm::Apply`.
  It retains the exact source expression/callee/argument identities, their
  value/effect endpoints, result/application-effect endpoints, owner, recipe,
  checking occurrence and cause in one `ApplySourceInput`. It then links that
  record to the exact candidate recipe before queuing its constructor. This
  establishes retained source correspondence, not a source typing theorem.
- `shadow_apply.rs:4090–4165` builds one negative Function demand from the
  source call's argument value, argument effect, result effect and result
  value. For a source Apply it records one `NativeInterface` containing that
  demand, positive callee, all four ports, invocation row and application
  effect before admitting the corresponding constraint. This supplies a
  shared syntactic/native record, not an interpretation of all four ports.
- `candidate_scheme.rs:4390–4424` reconstructs Function nodes from the same
  four ordered child terms `[argument, argument-effect, return-effect,
  return-value]` under the graph row map. `candidate_call.rs:500–562` observes
  an owned Apply and checks exact source occurrence, recipe, demand shape,
  kind/polarity and invocation-row identity. These checks do not establish
  semantic denotation or an actual runtime closure witness.
- `candidate_call.rs:177–193, 386–435` explicitly lists the unprovided
  `ArgumentReifyAndWholeCarrier` and
  `ReceiverDispatchAndCompleteResultFutureInterfaces` suppliers. The pending
  construction is not a semantic residual and `unresolved()` is not the
  premise for R344. This is the first visible open interface; it is not by
  itself a counterexample or proof impossibility.
- `candidate_effect.rs` is pinned because invocation/application effects
  require their own interpretation. Ordinary K0 does not thereby acquire
  scoped handlers, operation dispatch, or foreign continuations.

## Actual runtime realization already bounded

The pinned runtime owners match the R343 census and accepted result:
`program.rs` constructs the selected-definition `RuntimeProgram` from HIR;
`machine.rs:1162–1306` evaluates the actual callee and creates the invocation
from the returned value handle, closure/capture, whole argument `Delay`, and
caller environment; `dispatch.rs` resolves the executable by actual handle;
`receiving.rs` validates/observes the actual received record through a view.
R340 supplies the actual call continuation and owner prefix, R342 supplies
value/environment/capture correspondence only on finite actual-return
segments, and R343 supplies typed reachable K0 step preservation and semantic
unavailability exclusion under its explicit premises. None interprets the
native Function ports together or discharges the two pending call suppliers.

## Exact open boundary and falsifiers

The needed new relation must map the one source/native Function demand and one
solution witness to the same actual handle, saved environment, whole Delay,
caller environment, invocation/owner, received value/view, and result/future/
effect behavior. It must handle a finite call prefix without requiring normal
return, then preserve that same witness if return actually occurs. Four
independent port realizations do not establish this. The native query in this
census is not evidence that the current compiler violates the contract.

Falsifiers are: an authentic independently typed K0 Apply where the same
handle/capture/Delay/owner cannot realize the native ports; a normal return
whose source/native result or future/effect witness is mismatched; an actual
K0 Value entry that the proposed relation cannot cover; or a construction
that assumes termination, separate existential port witnesses, or
`candidate.unresolved().is_empty()`. Report a concrete executable
counterexample only when source and runtime reachability are established;
otherwise freeze the exact missing premise and owning transition.
