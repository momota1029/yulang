# Cycle94: retained frontier to ordinary graph family

Status: Draft implementation boundary, 2026-11-10.

## Objective and source

Connect the actual fixed-interval diagnostic frontier to the existing ordinary
constraint graph, preserving all original type/row assignments and prior atoms.
Spec 6.3 requires conjunction within one declaration and delayed child diagnostics;
competing declarations remain alternatives. No graph model existence or successful
child is a compilation input. This closes a graph integration subgoal, not state
materialization, saturation, final classification, or an executable decision.

## Data and independent meaning

For arbitrary n, existing atoms over Fin n, old source-named demands, and an actual
frontier tree, compile one CommonPresenceConstraintGraph.Compiled n for each
complete plan. The original diagnostic tree is returned unchanged, even when the
graph list is empty. Each graph compiles existing ++ generate (old ++ plan).
Graph semantics is the existing independent Models relation over definitions,
subtype edges and original rows. Its readback preserves computations literally.
The source judgment is GuardedIntervalPlans.Derives with one shared source
valuation for all descendants. It does not mention the generated graph family.

## Main quantified target

For every registry, slots : Nat -> Fin n, Sources, old, existing, root and original
assignment, the public run returns a graph with a model whose readback equals that
assignment iff Checked registry and the assignment satisfies existing and there
exists one shared source valuation satisfying old and Derives at root.

A second target quantifies every graph in a returned family and every model of it:
readback satisfies the same independent source meaning. Original rows are not
replaced, and original input indices stay injective. An arbitrary later appended
ordinary atom list can only remove assignments; replay into the previous graph
family preserves the identical original assignment, not internal node numbers.
The graph family may contain inconsistent graphs. Empty graphs and absence of
models are distinct. No caller-provided grammar certificate is introduced.

## Remaining B4 bridges

All five major bridges remain: source boundary adequacy, generally materialized
finite work, saturated closure/termination, stable four-way classification, and
dictionary order equivalence. This adapter does not infer new endpoint syntax from
state, settle invocation identity, or claim the ordinary solver covers every Form.
