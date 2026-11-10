# Mixed associated and ordinary evidence closure

Status: Draft implementation boundary, 2026-11-10, cycle 100.

## Goal

Close one finite fragment of B4 bridges 2/3: associated declaration outputs and
explicit reciprocal ordinary-variable edges must enable each other repeatedly,
not merely run once in a fixed order. Reuse existing declaration computation,
source identity transfer, scalar equality encoding, and finite Horn engine.
No new language rule or candidate-uniqueness commitment is introduced.

## Data and independent judgment

Inputs are existing `AssocEnv`, `RoleDecls`, core well-formedness, a finite
`CommonRoleFiniteAssociatedClosure.Source n`, and grammar-valid `State n`.
Facts are `(Fin n, Base)`, hence a complete universe of `4*n` facts. Independent
`Derives env roles p s fact` has four constructors: explicit initial scalar
pair, equal source identity, reciprocal variable edge, and associated output
using `DeclarativeComputed`. Associated well-formedness appears in correctness,
not executable input. Arbitrary finite source cycles and duplicates are allowed.

## Executable and target

Compile existing associated rules and ordinary evidence rules into one Horn
system; saturate once, emit resulting paired scalar constraints, and pass the
computed batches to the existing checked replay. For all environments, sources,
states and facts, under core/associated well-formedness:

- cache membership iff independent mixed derivation;
- emitted scalar evidence iff mixed derivation;
- re-running from the actual emitted state gives identical fact membership;
- emitted models are exactly original models satisfying all mixed-derived facts;
- checked replay succeeds exactly when those ordinary models exist and the
  diagnostic registry passes its existing check; snapshots <= 1+4*n.

The model characterization does not assert that associated equations preserve
all original models. Fixedpoint and stopping apply to this finite rule system,
not newly allocated slots, new reciprocal edges, dynamic where generation, or
all ordinary semantic consequences. Source identity/receiver templates remain
explicit caller inputs. Existing boundary questions remain open. B4 has five
unfinished bridges. spec 6.3 provides sibling conjunction and associated-equality
flow; it does not settle the outstanding invocation identity boundary.
