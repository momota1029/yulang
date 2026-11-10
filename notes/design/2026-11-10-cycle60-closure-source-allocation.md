# Closure-wide source occurrence allocation

Status: Draft, 2026-11-10. Scope: B4 source identity and generated work; the existing unary/int materialization adapter only.

## Bounded objective

Compute one finite occurrence table for the entire structural source-template closure. Every actual capture-bearing child at any reachable parent must have all its source dependencies represented in that same table, with the exact old canonical roots and complete inspection snapshots. The table is computed from the registry and root, never from the currently selected child or ordinary state.

## Data and independent judgment

`entries registry root` traverses the existing finite `closure registry root` in order and pairs each source request with each of its ordered dependency slots. It preserves duplicates. `names table registry root` maps these entries to the old source names. The independent membership claim uses `CommonRoleSourceTemplateClosure.Reach registry root child` and membership in `dependencies child`, rather than the allocation function's own output.

Allocation reuses `CommonRoleAllocatedGraph.allocate table names graph`. An indexed occurrence has an old owner given by its entry's second component. No source-name equality, graph adequacy, chosen fuel, or caller-supplied finite universe is required.

## Main theorem shape

For every table, checked registry, root and parent source request, ordinary state, declaration, lower/upper type, capture depth and actual generated child: if the parent has a finite actual production trace from the root, production succeeds with the declaration and bounds, its head has the stated capture depth, and the child occurs in its produced children, there exists a child source template with the extended actual trace whose present evaluation is that child. The trace stores an independent ordinary state at every actual generation edge; membership in the computed closure follows by induction and is not supplied by the caller. Its evaluation belongs to the finite materialized domain at every future state. For every dependency slot of that template, there exists an occurrence index in the one global names table with exactly that child/slot entry, the old source name, the retained old canonical root, and the retained complete inspection snapshot for every old graph, role and visible-head list.

`entries_exact` additionally proves soundness and completeness of the global occurrence enumeration against structural reachability. `identity_exact` compares any two occurrences across arbitrary children by original source identity, not by unknown observations.

## Boundary and evidence

This closes the shared finite allocation domain in the existing adapter. Structural alternatives overapproximate actual selection; occurrence allocation does not allocate constructed wrappers as fresh source variables. General interval materialization, recursive syntax graph allocation, updates of old nodes, saturation and B4 remain outside the claim. All five general B4 bridges remain open.

Before implementation, the current `work/dots-audit` oracle was read: X13–X16 and C3-PARENT show source-level sharing/where behavior, not numeric allocation correctness. The graph allocation theorem has no direct Yulang2 runtime observation. Spec 6.3 remains the authority; no new semantic choice is made.
