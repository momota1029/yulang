# Complete Call solver and publication seam map (2026-10-10)

## Scope

This bounded read-only map follows the reviewed practical complete-Call
proposal after a complete correlated Call residual has been constructed. It
does not assume a decision for the pending ordinary-value/formal rule or use
the unintegrated local q3 answer. Baseline: `c32ff7c0980e8844803cc7638cfdc34b06900a51`.

## Direct source observations

- **Constraint inputs:** `crates/yu-solver/src/lib.rs` defines
  `ConstraintOccurrence` as a lower/upper `Term` pair plus occurrence/cause
  (`:436`). `crates/yu-solver/src/term.rs` has four-field polarized Function
  constructors (`:170`). There is no direct constructor here for the complete
  dependent Call telescope, carrier/provider/world, independent admission or
  evidence telescope.
- **Effective solver:** `InferenceSession::constrain_live` drains a memoized
  Value/Effect worklist (`yu-solver/src/lib.rs:11310`). Function comparison at
  `:11412` decomposes into argument, argument-effect, result-effect and result
  comparisons; `apply_effect_task` at `:11104` propagates scalar effect bounds.
  These are scalar propagation services. The inspected entrypoints do not
  return a certified complete-Call residual or preserve its joint evidence
  alternatives.
- **Generalization owner:** `execute_scc_plan_inner` processes SCCs and freezes
  component drafts (`yu-solver/src/lib.rs:13135`). The production flat route
  calls `F5cGeneralizer::build_and_stage_flat_raw_candidate`
  (`yu-solver/src/lib.rs:13686`; implementation in
  `yu-solver/src/f5c_generalization.rs:10538`). Its `non_generic_closure`
  (`f5c_generalization.rs:9204`) handles existing variable dependencies.
  This provides an enclosing-root owner, but the inspected walk has no
  correspondence for complete Call dependencies, fixed anchors, jointly
  scoped clauses/evidence or whole-frame template eligibility.
- **Export representation:** `GeneralizationDraft` contains quantifier count,
  recursive value bounds and a positive predicate
  (`f5c_generalization.rs:505`). `ClosedValueScheme` freezes those fields in
  `yu-types/src/lib.rs:630`; `finalize_indexed_scheme`
  (`f5c_generalization.rs:2258`) validates the production flat scalar grammar.
  The inspected effect views (`yu-types/src/lib.rs:614–619`) are Bottom/Empty;
  `pure_function_effect` (`f5c_generalization.rs:6440`) accepts those leaves or
  an exactly bounded live row. The closed representation does not directly
  retain a complete Call package or a symbolic complete Call effect allowance.
- **Fresh use:** `route_incoming_inner` reads finalized schemes
  (`yu-solver/src/lib.rs:15162`); `instantiate_and_route_closed_inner`
  (`:14795`) allocates fresh scalar rows, restores scalar bounds and routes
  predicates. `closed_parts` (`:14467`) reconstructs scalar terms. This
  preserves scalar binder sharing, but no inspected decoder checks a correlated
  Call telescope, complete interface, fixed dependencies or evidence action.
  `decode_closed_scheme` (`:14374`) is test-only, not a production decoder.
- **Public observation:** ordinary `SolvedModule::projection_for` and
  `root_value_for` (`yu-solver/src/lib.rs:16085`, `:16101`) return coarse
  projections; structured root predicates yield `Unknown`. Rich closed-scheme
  observation is behind `shadow-f5` (`:16024`).
- **Native precedent:** the native projection design §§3–4 selects finite
  extraction and fresh ordinary roots for id/pick, not an F5 Call
  implementation. The research direct checker
  (`tools/research_projection_public_direct.py:431`) checks a conditional
  same-inlet Function fragment whose `PublicRoot` (`:154`) has echo/fixed/any
  result dependencies and Pure/Value defaults. It is not a complete Call
  decoder or solver.

## Smallest correspondence still needed

After a complete correlated residual exists, the production chain needs:

1. a certified complete-rule result retaining all joint solutions and
   evidence alternatives;
2. a dependency-aware enclosing-root generalization correspondence;
3. finite ordinary extraction of the correlated package;
4. a fresh-use decoder/checker for the whole Call frame and its fixed
   dependencies; and
5. atomic publication of the ordinary package only after these checks.

Current scalar machinery may provide leaf services and transaction patterns,
but reuse requires a typed translation and preservation argument. Existing
native id/pick laws do not supply it for Call. These are source observations
and a bounded architectural inference, not a proof that no other route exists.

## Limits and checks

Read-only bounded inspection only. No edits to compiler code, tests/builds,
runtime probes, measurements or Git operations. No complete test inventory,
performance analysis, or production conformance certification was attempted.
