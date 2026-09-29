# Rust replacement boundary map

Date: 2026-09-29
Branch: `research/simple-sub-intrusion`
Classification: read-only implementation map; no replacement semantics or code
authority

## Public solve path

The current production path is:

```text
ConstraintBatch::collect
  -> SccPlan::build (sealed during collection)
  -> SolvedModule::solve
  -> InferenceSession::try_new / run
  -> execute_scc_plan_inner
  -> finish
```

Relevant locations in `crates/yu-solver/src/lib.rs`:

- collection and SCC-plan sealing: `ConstraintBatch::collect` (around line
  813; `SccPlan::build` near line 1223);
- public inference entry: `SolvedModule::solve` (15663),
  `InferenceSession::try_new` (9176), and `run` (9729);
- SCC execution and the current component publication path:
  `execute_scc_plan_inner` (12882);
- per-member scheme production: `component_generalization_draft` (15160) and
  `finalize_generalization_draft` (15185);
- external use consumption: `route_incoming_inner` (14875);
- result construction and current root projection:
  `InferenceSession::finish` (15417) and `SolvedModule::root_value_for`
  (15706).

## Replacement boundary

The existing dependency-first SCC scheduler and open internal-use routing run
before member generalization. After that, the current path builds one closed
scheme per member, installs all member schemes, routes incoming uses by
instantiating those schemes, and retains a closed type arena for result
projection.

Therefore the replacement cannot be a local swap of
`component_generalization_draft`. The coupled boundary includes:

1. production of the frozen generalized component and member-root views;
2. publication of all views before processing incoming uses;
3. incoming-use handling with independent substitutions over the shared graph;
4. the solved result's retained representation and root projection.

This path is a plausible shell for an alternative engine behind the same
collection and solve entrypoints, but whether the F4 scheduler and live bound
store can be retained depends on the successor semantics. No production code
or data representation is selected here.

## Ownership finding

`yu-solver` currently owns `InferenceSession`, SCC execution, F5 draft
generalization, scheme installation, and instantiation routing.
`yu-types` owns `ClosedValueScheme`, `ClosedTypeArena`, and transactional
finalization. The F5 architecture crosses that crate boundary. A replacement
that abolishes F5 must also state whether the closed scheme arena remains only
as a presentation/export layer or disappears from the solver result contract.
No production caller of `SolvedModule::solve` was found outside `yu-solver` in
the inspected source search; broader public documentation and downstream
workspace usage were not audited.

## Next semantic gate

Define the component/member-root denotation, boundary-parent selection,
root-local view, independent incoming-use overlay, and result projection as one
operation. Then state the simulation/principality property and prove it for a
declared finite graph class before choosing which existing Rust owners survive.
The executable Python characterization is not implementation evidence and
does not close any of these obligations.
