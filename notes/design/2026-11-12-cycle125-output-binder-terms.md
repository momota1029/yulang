# Cycle125: explicit output-only RHS terms

Status: Draft implementation bridge, not a new language decision.

I-18 item5: shrink the arbitrary output side of dictionary `TermInstances`.
General B4Bridges V3 remains12/12 unfilled. Astra-owned declarations/state stay
unchanged. Spec06 §6.3 makes generated associated binders ordinary output-only
variables. We can therefore interpret an actual explicit RHS `.var b`, where
`b` is in the declaration's outputNames, as the ordinary source variable
`capture.outputs b`. No input interval endpoint, nominal encoding, or positional
default interpretation is selected.

Data: existing checked declaration, capture, actual RHS provenance, and source
state. Executable lookup first uses AssociatedProvenance.lookup, then accepts
only a normalized explicit output-only variable. Unsupported/default/input
bodies return none, meaning deferred, never language rejection.

Independent judgment: an actual Supplies explicit equation whose normalized RHS
is an output binder denotes exactly `.var (capture.outputs b)`. Prove lookup iff
this judgment for associated-name-unique declarations, and functionality.
Checked.Produced supplies an actual where child equation producing that same
source variable. This producer fact does not solve the child or certify a fresh
capture/allocation.

For any Located package with each lifted output equal to the computed RHS,
actual equation recording implies, in every final source model, that each root
output equals the computed source binder. The output interpretation is no longer
an unrestricted predicate, but head instantiation and frame derivation remain
explicit. Repeated output names retain every original target and occurrence.
Exact model/satisfiability claims retain their old-state and all-equation
premises; no empty-model soundness is sold as feasibility.

Next: implement input/default and structured RHS only after their ordinary
representation is available; actual source frame generation remains separate.
