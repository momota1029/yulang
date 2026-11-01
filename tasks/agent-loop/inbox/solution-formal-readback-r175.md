# R175 — same-solution readback outcome

Status: **BLOCKED_SOLUTION_REGISTRATION**. Parent
`YulangClosure.SourceProblem.InferenceSoundness` remains **OPEN**. No safe
Rust or Lean code slice is established by this preflight.

## Original obligation and semantic authority

Keep the parent claim unchanged (`Contracts.lean:127–130`):

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

There is one source derivation `e` and one shared `sameScoped` witness for the
same solution `a`. The existing source typing, descriptor/interface,
permission, effect-inflow, and residual laws are present in the frozen semantic
authorities. The audit found no missing or competing source-semantic choice.
In particular, keep declared permission, actual constraint-derived inflow,
and post-subtraction residual distinct; the approved annotation correction
remains in force.

The blocker is the bridge from the *same actual successful inference
solution* to those existing original meanings. No concrete registration was
found for the solution carrier and success relation, nor a readback that
constructs the total pre-invocation `FormalAssignment` while preserving the
source declaration, route, complete prior telescope, and shared witness.
Therefore this is not `BLOCKED_SEMANTIC_AUTHORITY`.

## Frozen evidence

Contract revision 7 SHA-256: `db9e77b97ec86ef32e8de0ababc3b5daa25ef09d4b961cbe8153c4a5cb0f22ca`.
The prior frozen dependency set is unchanged from contract revision 6; all 33
hashes matched before the proof lane's last reads. Source lane's exact owner
hashes and revision-2 contract hash are recorded in activation receipt
`tasks/agent-loop/history/solution-formal-readback-r175-activation.md`.
No additional path was read or admitted. No files were written by either lane.

### Rust representation trace

The source lane located the ordinary public path `SolvedModule::solve` at
`crates/yu-solver/src/lib.rs:20387`; ordinary collection selects candidate
flags false (`938–953`). The feature-gated, default-off candidate route is a
different carrier: `CandidateInference::solve` returns `Result<Self,
CandidateError>`, where the wrapper retains the private `CandidateSolvedResult`;
`run_candidate` is the function returning that private result. A feature-gated
`CandidateValueObservation` route
instead uses legacy fresh capture. Do not conflate these APIs. An `Ok` result
is not itself the parent `solves` relation because returned results can retain
conflicts; candidate export separately rejects nonempty errors.

For the candidate formal observer, `CandidateInference::computation_source_plan`
passes the result's HIR, store and formal state to
`candidate_call::observe_computation_source_plan`. The observer authenticates
owner/Lambda/formal identity, scopes, a live Value `native_root`, annotation
owner and row structure. Its Value branch checks no effect and returns
`None`; the Computation branch exposes `native_root` and `entry_effect`
handles. A distinct authenticated Call observer can expose a Value root for a
formal-use Call. These are structural handles, not an original `Descriptor`,
complete `Interface`, inherited-scope valuation, `FormalAssignment`, or
`JointWitness`. The Computation observer does not establish that
`entry_effect` denotes the complete original interface.

This route audit is bounded to the frozen owners and handoffs. External caller
coverage and whole-repository API adoption are unverified. The structural Value
`None` result is not a reachable compiler counterexample.

### Original semantic declarations

The proof lane source-inspected, but did not freshly Lean-print or build, these
existing definitions:

- `OriginalParameterWorld.lean:53–59`: `FormalAssignment` maps each
  parameter, route, and full prior `ScopeValues` to the original contract;
  Value contracts use `s.Descriptor`, Computation contracts use
  `s.Interface`.
- `OriginalFormalAdmission.lean:154–160`:
  `produced_description_admitted` consumes an already supplied
  `FormalAssignment`; it does not derive one from the solver solution.
- `OriginalFormalAdmission.lean:467–500`:
  `actual_build_from_whole_telescope` consumes the complete local
  `Satisfies ... (Build ...)` premise and supplied assignment; it does not
  register the parent solution.
- `Contracts.lean:128–130`: the original parent quantifiers and shared witness
  remain unchanged.

The bounded eight-file Lean audit found no concrete Yulang
`SourceProblem`/sort assignment connecting the actual Rust solution to these
abstract original meanings. Existing construction notes explicitly leave the
full instance/registration open. This is not an exhaustive repository-wide
absence claim.

## Gate decision and next evidence

No source-semantic choice is needed. The next useful packet must first identify
and freeze the ordinary inference route's actual successful-solution relation
and concrete carrier interpretation. It must then construct, from that same
solution, a Value `Descriptor` via prepared `native_root`, and a complete
Computation `Interface` via `native_root + entry_effect`, under the same
source declaration/route and complete prior telescope. It must cover every
formal in the `FormalAssignment` domain and construct the relation needed for
the parent's single `sameScoped` witness. Do not stipulate `solves :=
Satisfies`, carrier identity, a readback function, or use later invocation to
select the contract.

R173's local generation result remains only a conditional premise until this
registration is supplied. Applying a partial formal observation or a local
effect/member correspondence cannot close the parent theorem. No theorem,
Rust implementation change, or production promotion follows from R175.

## Lane and review receipt

- Source lane: `/root/solution_formal_readback_r175_source`, stopped; structural
  endpoint observations only, no files written.
- Proof lane: `/root/solution_formal_readback_r175_proof`, stopped; source-level
  declaration/authority audit only, no theorem delivered and no files written.
- Independent review: pending against the frozen handoff, contract revision 7,
  and activation/current-state synchronization.
- Verification: required static sprint checker only; no tests, Lean, Cargo,
  builds, runtime inspection, scratch/cache/environment creation, or source
  edits were performed.
