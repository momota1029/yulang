# Cycle88: annotated pure scalar expression inputs

Status: Draft. 2026-11-10. Scope: bridge 1, not full B4.

Goal: extend checked annotated source inputs beyond literals to finite closed
expressions built from existing literals, de Bruijn variables and let. Read spec
3.1, 3.5 evaluation order, and 4.2 annotation checking. No source syntax or
semantics is changed. Unsupported expressions stay outside this fragment.

The executable evaluator computes an optional scalar tag from a scalar context.
An independent inductive evaluation judgment uses literal, lookup and let rules.
For every such judgment, every existing presence-aware typing has the evaluated
scalar as a lower bound. Conversely the canonical scalar context types it at that
scalar with an empty row. The let proof must handle both existing value and
computed rules, including captured polymorphic bindings, rather than assuming
an evaluator is an inference oracle.

For closed expressions with explicit scalar annotations, check evaluation equals
the annotation. Derive named facts and reuse canonical allocation/readiness.
The intended exact statement quantifies arbitrary finite source and binding lists:
run = true iff checked inputs, valid source, an independent source model and all
source roles discharge. The independent side reads original expressions through
the inductive judgment; it does not receive ordinary atoms, slot maps or success.

Caller inputs retained: scope-resolved names, grouped source clauses, explicit
annotations, role/impl registries and their wf/awf. No general parser lowering,
recursive or effectful input inference, invocation identity, dynamic child closure,
final diagnostic or dictionary equivalence is claimed. Five B4 bridges remain.
