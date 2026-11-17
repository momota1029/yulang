# Cycle235: current point packet for actual mixed regression218

The actual source-derived point state is `MixedGround218Point235.point`, reached
by original source initialization, the first parent installation, then improving
reobservation. No legacy post-install state is lifted as a new initial state.
The current root plan is `GroundCopy218SaturatedParent.planFor` specialized to
that actual state's allocation, reservation, and ordinary journal.

## Scope and proof strategy

The point descriptor exposes arguments (4,4) and (5,5). The declaration's two
binders are distinct, so versioned capture contains exactly those singleton
bounds. The child is nonterminal: its occurrence and actual centers are retained,
with revised point bounds, not erased to a terminal approximation.

`PointPacket235` establishes one full packet model using the independently
verified actual point model. `PointFrame235` proves freshness, preparedness and
actual current Frame. Freshness does not assert disjointness from all allocated
names: any supported nonsmall source comes from a recorded allocation, so a
collision forces the same owned key by source identity injectivity.

`PointAllModels235` proves full packet semantics from current raw state Models,
not from a hypothetical committed current packet. Projections and head schema
are derived from the point nominal descriptor; remaining cross/self/child-output
constraints are reflexive. `PointUniform235` generalizes that proof to arbitrary
allocation, reservation, and ordinary atom lists: its sole semantic premise is
raw Models of that context. It supports a later actual equality-closure endpoint
without assuming the endpoint has the same ordinary list as this point state.

`PointChildren235` proves exact ordered versioned children equal the singleton
new child occurrence of the existing218 specification, and every child has no
output requests. All five modules are additive; old definitions are untouched.

These modules alone do not claim Stable, selected, or EvidenceAt. Other modules
assemble actual subsequent operations and guards. Generic EvidenceNode remains
conditional on the documented ChoiceCompatible and common-model obligations.

## Validation

Every new module was compiled directly with Lean `--trust=0` and
`-DwarningAsError=true`. Axiom audits show only propext, Classical.choice,
and Quot.sound. No sorry, new axioms, or native_decide.
