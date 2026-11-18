# Independent review: observed Plans and planned histories

Reviewer: alias/transport subagent; these two modules were written by the
coordinator, not the reviewer. The reviewer did write the imported PlanTransport
module, so this is not an independent review of that dependency.

Reviewed files:
- lean/Yulang/GeneralRebaseObservedPlan262.lean
- lean/Yulang/GeneralRebasePlannedTrace262.lean

At 2026-11-18 18:54–18:56 UTC. Source hashes are recorded in
planned-review-source-sha256.json and were unchanged at the end of the review.

## Result

No correctness defect found in the stated scopes. Both modules independently
rebuilt into a separate cache with --trust=0 -DwarningAsError=true, exit0.
The 11 principal declarations audited have only propext, Classical.choice and
Quot.sound. Detailed outputs: planned-independent-build.txt and
planned-independent-audit.txt. This was a fresh rebuild of these two modules,
not their entire dependency closure or the whole repository.

## ObservedPlan262

- observe constructs each proposal from `facts (plans state root) owner` and the
  exact executable request list of `inspect state` and that selected root.
  It does not covertly build every proposal with the reference Plan.
- Compatible requires structural Same only for roots actually in roots state;
  it is quantified over every finite state, not merely the run's reachable states.
  It contains structural table/variable data, not desired ClassEffects equivalence.
- observe_eq follows exact list equality of fact tables for each selected root.
  This preserves proposal order and multiplicity, including duplicate roots.
- write_eq/step_iff therefore relate the actual-Plan observer to the fixed-Plan
  finite basis without replacing the finite state or its stored fact meaning.
- completion inherits finite coverage and novelty-gated termination. It is not
  Ready, model existence, packet validity, or evidence synthesis.
- step_actual chooses a selected root once and proves the meaning equation for
  all assignments. Root uniqueness is not claimed: different selected roots can
  emit identical proposals. Its existential witness is sufficient for the theorem.

## PlannedTrace262

- Trace.next records exactly inspect before, root and plans before root, plus the
  actual proposal write equation, novelty and the rest of the trace.
- from_runs preserves the step count. to_runs reconstructs a run of history.length.
  These two theorems need no semantic compatibility or coverage assumptions.
- models_exact does not use the potentially nonunique existential root from
  step_actual. It uses the exact root stored in each Trace constructor, transports
  that root's write, then its actual Plan semantics. Thus the final history means
  the actual chosen observations of that witness trace.
- certificate chooses one after/history outside the universal assignment. The
  same compressed history certifies every assignment simultaneously.
- The history is a proof witness; the runtime finite state does not need to retain
  the entire growing event list. The theorem does not assert a unique trace.
- The unchanged base predicate and conjunction of event effects can describe an
  empty model set. .ok is successful finite scheduling, not satisfiability.

## Source certificate quantifiers and limitations

- Source formation is supplied before the existential pool. The same pool is then
  quantified before every base, reference Plan, owner, inspect, roots and plans.
  This is a genuinely source-derived common pool, not a newly chosen pool for
  each encountered observer state.
- Each inspected snapshot must be reachable from the same initial source under
  the existing mixed source boundary. Its coverage is derived by the source-pool
  theorem, not separately assumed from the desired conclusion.
- Reachability is pointwise. Consecutive inspected snapshots are NOT required to
  be connected by a source Step or to occur in a single monotone source execution.
  No old/new Step simulation or old Step termination follows.
- Selected roots need not carry Generated proofs, and supplied Plans need not
  carry Frame, Ready or packet certificates. “Observed Plan” here means the Plan
  the caller's observer actually supplies and whose facts are really proposed;
  it does not mean a source compiler has constructed a valid candidate Plan.
- Same restricts Plan changes; arbitrary changing declarations/captures and
  nonpoint→point transitions are not automatically covered.
- inspect/roots/plans remain input functions. Parameterized definitions are
  executable, but a noncomputable supplied function can prevent running that
  concrete instantiation. The certificate does not construct the source observer.

These caveats are consistent with the modules' comments and should remain in
user-facing scope summaries. No code changes were made during this review.
