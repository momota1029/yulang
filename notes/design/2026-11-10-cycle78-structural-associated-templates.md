# Cycle78: structural associated goal templates

Status: Draft. 2026-11-10. B4 bridge 1 implementation fragment.

## Objective and boundary (written before Lean)

Replace the arbitrary `Inference.Base → Roles.Goal` input of the finite named
associated program with checked first-order goal syntax. The only placeholder
is `Roles.Term.var 0`; constructor identities, argument order, arity, role and
associated name come from syntax. Existing int/str materialization is used.
Unsupported bool/unit inputs remain blocked inside this fragment, not rejected
as language programs. Scope-resolved names and the finite occurrence list are
still source-boundary inputs. No decision on dynamic invocation identity,
unbound where variables, nonlinear heads, or general interval knownness is made.

## Data and independent judgment

`Template` contains a goal skeleton and a proof `argsBound args ≤ 1`.
A finite `Program` is a list of receiver/output/name/template records.
An independent structural `Fill payload original result` judgment substitutes
only placeholder 0, preserving all application constructors and argument lists.
`Materializes template head goal` uses existing scalar encoding and `Fill`, not
an arbitrary template function, resolver return value, or saturation result.
The executable template uses structural substitution. Unsupported input maps to
an explicitly unbound sentinel, making the existing closed-goal guard false.

## Intended theorem chain (universally quantified)

1. For all payloads, scoped terms and results, Fill iff structural substitution
   produces the result. Materializes similarly iff the generated goal, with
   its closedness guard. Role and argument count are preserved.
2. For all registries, finite structural programs, old ordinary states, source
   names and scalar heads, compiled named derivability iff independent source
   derivability using Materializes and independent associated declarations.
3. For all well-formed core/associated registries, programs and old states,
   concrete returned evidence and every ordinary model are exact for that
   independent source judgment. Model existence agrees with the actual solver.

No successful resolution, complete frontier, chosen assignment, or external
fuel is an execution premise. Registry well-formedness and syntax scoping
remain explicit. This is not source parser adequacy or full B4. Five major
bridges remain open. Boundary tests must cover nested constructors, multiple
arguments, int/str, unsupported bases, absent seeds and source-name sharing.
