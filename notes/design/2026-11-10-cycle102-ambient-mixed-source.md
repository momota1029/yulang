# Cycle 102: ordinary-only variables in structural mixed allocation

Status: implemented and focused-kernel verified, 2026-11-10.

The partial goal is an exact mixed closure whose computed slot table includes
ordinary-only source variables as well as associated occurrence endpoints.
This closes the allocation restriction in cycle 101, not dynamic generation.

## Data and source boundary

For every finite structural Program p and every finite list extra of already
scope-resolved source names, compute table p ++ extra. Existing occurrence
positions embed into its prefix; extra slots need no fake associated request.
The original State over this computed table remains input, with its existing
grammar proofs. Repeated names impose type equality, including extra names.
Effects are not identified. The extra list comes from future ordinary lowering,
not from a new language restriction or a decision about invocation identity.

## Independent judgment and executable entry

Derives env roles p extra s name base has exactly three rules: original scalar
seed at any slot, reciprocal original ordinary edges, and structural associated
steps from members of p. No allocated output slot or executable resolver occurs
in the associated rule. The executable entry compiles endpoints, adds physical
same-name edges, and runs the existing finite mixed closure.

For all env, roles, well-formedness wf/awf, finite p/extra, original s and every
assignment v, prove output models iff original models and a single source type
valuation factoring v satisfies every independent Derives fact. Prove its actual
ordinary solver iff existence corollary, scalar evidence exactness, and capacity
4 * (2 * p.length + extra.length). No model, consistency, fuel, successful resolve,
or precomputed graph map is an input. Raw validation remains separate.

## B4 and authority

This advances source allocation in bridge 1 and the finite fixed-universe part
of bridge 2. It does not close any whole B4 bridge. Parser lowering, fresh dynamic
children, general forms, scheduler fairness, final classification and dictionary
observational equivalence remain outside. Spec 6.3 is authority for associated
equalities and conjunction; existing source equality is reused. The audit's
x-oracle C3-PARENT evidence is relevant background, not a test of this new entry.
No new Yulang2 execution or new language decision is claimed.
