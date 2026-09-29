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

## Current Rust-path baseline probes

On 2026-09-30, two focused tests in `yu-solver` were run against the current
Yulang3 inference path:

- `tests::f5d_parameter_alpha_rename_shadows_module_name_and_does_not_leak`
- `tests::f5d_productive_function_recursion_and_unproductive_names`

Both pass with `RUSTC_WRAPPER= cargo test -p yu-solver <test-name>`. The first
observes identity-Function aliasing and current quantified-binder reuse through
the retained closed-scheme view; the second observes the current productive
recursive scheme shape and unproductive-name results. These tests characterize
the existing F5-backed implementation only. They do not prove Oracle
equivalence, validate intrusion semantics, or make Q/R and closed schemes part
of the replacement contract. They give Rust-side baseline evidence at the
current solver path while the replacement remains unimplemented.

The configured `sccache` wrapper failed to start in this environment with
`Operation not permitted`; setting `RUSTC_WRAPPER=` let Cargo invoke `rustc`
directly. No compiler source or test was changed for these probes.

## Oracle source witness is outside current Yulang3 HIR

A focused Rust test attempted the exact frozen-Oracle two-use source
`pub id x = x; pub number = id 1; pub function_value = id (\\x -> x)`.
The test compiled but failed at HIR diagnostics: the backslash lambda is not
accepted, and `id 1` becomes `UnsupportedExpression`. The temporary test was
removed rather than weakening the source or expected result.

The source limitation is visible in `yu-hir`: `ResolvedExpr` has no call or
application node, and `lower_simple_chain` accepts only a leaf Integer or
Identifier after it rejects `HirExpr::Apply`. The current Yulang3 path therefore
cannot replay this source-level Oracle witness, even though the frozen Oracle
accepts it. This is a language/HIR boundary gap, separate from intrusion
correctness. For Gate C, a test-only semantic batch can characterize the graph
and independent incoming-use mechanism; it cannot prove source-level parity.
Before Gate E, the successor contract must explicitly include expression
application in the source envelope or record that source-level behavior as a
compatibility delta. A broad Oracle-capability claim requires adding the source
path before calling the work complete.
