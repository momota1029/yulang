# Intrusion redesign: initial Oracle behavior ledger

Date: 2026-09-29
Oracle revision: frozen `main` at `a58eefc3`
Status: partial source/test audit; tests not executed

This ledger records directly observed Yulang2 behavior for the new SCC
intrusion design. It does not use F5 closed schemes as the target. Test
assertions below were read from the frozen source; no suite was run in this
research step. “Observed” means stated by source/test construction, not an
independently reproduced execution.

## Observed behavior

| Topic | Frozen-source observation | Evidence |
|---|---|---|
| Bound insertion / extrusion | Lower and upper bound insertion call `extrude_pos` / `extrude_neg` at the target/source level. `extrude_type_var` lowers the existing variable in place and traverses its installed lower and upper bounds with a visited set. Function argument positions traverse negatively and results positively. This implementation does not allocate a fresh parent representative. | `crates/infer/src/constraints/machine/bounds.rs`: insertion around 645/830; traversal around 4523–4727. |
| Definition SCC generalization | `quantify_component` creates a generalized result for each `(DefId, root)` member, collects all results, inserts all schemes, then processes finalization/recording. Incoming uses are not admitted inside the member-draft loop shown here. | `crates/infer/src/analysis/session/instantiate.rs:14–89`. |
| Identity Function boundary | The unit helper encodes an identity lower bound as `Fun(arg = -inner, result = +inner)` with pure Bottom effects. Under `FetchValue`, the fixture asserts the inner variable is quantified. Under `FetchComputation`, the same shape asserts no quantifier because the root remains at the binding boundary. | `crates/infer/src/analysis/tests/case_03.rs:338–371,1770–1787`. |
| Fresh use level | A manually built scheme with one quantifier is instantiated into a use value at root level; the test asserts the fresh variable is distinct from the scheme binder and is allocated at the use's root level. | `crates/infer/src/analysis/tests/case_02.rs::instantiate_use_freshens_quantifiers_at_secondary_level` (`:78–128`). |
| Recursive bound restoration | A manually built scheme with a recursive lower `int` bound is instantiated; the test finds a fresh variable on the use path and asserts that `int` is restored as its lower bound. | `crates/infer/src/analysis/tests/case_02.rs::instantiate_use_restores_recursive_bounds_for_fresh_quantifier` (`:219–281`). |
| Naked variable generalization | A child-level naked variable is generalized/finalized to an empty compact root and `Bottom` predicate, with no quantifiers. | `crates/infer/src/generalize/tests.rs::finalized_generalized_naked_root_variable_becomes_never` (near `:800`). |
| Recursive bound observation | A recursive interval containing `self ∪ int` is finalized with one recursive scheme bound whose lower side still contains `int`. | `crates/infer/src/generalize/tests.rs::finalized_generalized_root_moves_recursive_bounds_into_scheme` (`:834–861`). |
| Independent uses and shared outer identity | One manually constructed imported scheme is instantiated twice. The test asserts distinct fresh Q and R variables for each use while both uses map the same outer boundary variable to one session-level imported identity. | `crates/infer/src/analysis/tests/case_02.rs::oracle_a1_stage_3_exit_preserves_q_r_and_b_lifetimes_across_imported_uses` (`:494–598`). |

## Open rows

This is not yet a complete observable contract. Still to inspect and record:

- source-level valid identity/constant and two-use programs through the frozen
  Oracle's public analysis path;
- mutually recursive definitions with incoming and internal uses;
- a shared diamond and a descendant outside the definition SCC;
- a nested polarity inversion with a rigid enclosing non-generic variable;
- guarded and unguarded recursive cycles from full analysis, not only a
  manually constructed finalizer fixture;
- exact use independence under interleaved constraints and later generalization
  continuations;
- whether a behavior is fixed by tests/observable output or only inferred from
  the machine's implementation order.

## Research consequence

The sketch's “ordinary extrusion allocates fresh low-level representatives”
claim does not describe the audited Yulang2 `main` implementation. Treat
intrusion as a new candidate semantics and compare observable results, rather
than presenting parent allocation as a direct refactoring of the inspected
Yulang2 extrusion procedure. The new design remains free to choose a shared
SCC graph if its soundness/principality argument and Oracle behavior hold.
