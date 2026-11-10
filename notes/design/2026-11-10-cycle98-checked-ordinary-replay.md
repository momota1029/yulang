# Checked cumulative ordinary states and cached frontier replay

Status: Draft implementation boundary, 2026-11-10, cycle98.

## Objective

Close the gap between cycle97's caller-supplied Chain and an executable ordinary
solver boundary. For arbitrary grammar-valid additive constraint batches, compute
all cumulative states, invoke the existing finite ordinary solver at every state,
and prove acceptance exactly when their final accumulated state has a Common model.
On acceptance, derive Chain internally and reuse the exact cached diagnostic replay
and per-occurrence fresh graph adapter with source-computed rebuild/visit bounds.

## Data and independent judgment

Inputs: existing `State n` (atoms plus three grammar certificates), a finite list
of such batches, registry, original Goal, slots, Sources and per-occurrence old demands.
Append retains all atoms, order and duplicates. The independent semantic condition
is `State.Models` of the cumulative final state, not Boolean solver success.
No interpretation of batches as source syntax, candidate commitment or generated
ordinary work is imposed. In particular, do not append a sole candidate's head
merely because it is unique. This is the additive ordinary boundary of spec6.3.

## Executable interface and quantified claims

`trace initial batches` computes post-update states. `validate initial batches`
checks the initial state and every computed post-update state using the actual
`CommonRoleOpenPropagation.consistent` solver. No model or Chain is an execution input.
For every initial state and every finite batch list:

- validation succeeds iff final cumulative constraints have some Common assignment;
- successful validation derives Chain on the actual cumulative atom lists;
- successful public replay implies exact snapshots and a rebuild bound of
  1 + the original Goal's variable-occurrence potential, with full preorder
  occurrences bounded by that number times the computed source work-domain length;
- the existing graph adapter still refreshes every occurrence, including plateaus.

Invalid declarations and inconsistent ordinary constraints remain different
premises in the exact success characterization. These auxiliary results do not
prove parser adequacy, source/invocation identity, finite generation of the batch
list, saturation termination, final role classification or dictionary equivalence.
Finite list length is still caller input. All five major B4 bridges remain open.

Yulang2: reread work/dots-audit x-oracle X13-X16. Those local observations do not
prove a generic additive solver trace; no new external runtime experiment is claimed.


## Final interface and scope detail

`validate_models` states the conjunction independently over one shared assignment;
`final_atoms` retains the exact concatenation. `run_none_iff` separates unsatisfied
ordinary constraints from invalid declarations. `runGraphs` is now a public gated
graph-returning adapter, not just an existence statement about another interface.
Its result can contain unsatisfiable graphs because old demands and role plans
are not part of the initial ordinary check.

Every batch shares fixed Fin n. The original Goal, slots and Sources are fixed;
no fresh allocation is performed. The inherited materializer recognizes explicit
paired-int evidence only. Visits count rebuilt-tree preorder occurrences, not
ordinary-solver work, graph refresh, all traversals or wall-clock runtime. Validation
checks every cumulative state on success and may short-circuit on failure.
