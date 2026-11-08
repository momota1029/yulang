# Cycle 2: computed associated bodies into ordinary state (Draft)

Spec 6.3 supplies an associated equation only after its receiver is determined
and an implementation is resolved. This bridge reuses `Roles.assocOf`, rather
than manufacturing an ordinary constraint at the call site or inferring a
receiver from singleton visibility. A restricted scalar decoder interprets the
existing first-order codes 0/1 as int/str; all other terms are unsupported.

Data: an associated request contains a first-order goal, associated-name, and
output slot. Execution computes assocOf, decodes the scalar RHS, then appends
the existing equality atoms. The computed provenance predicate states the computed
associated RHS and semantic equivalence of the output slot; no manual ordinary
atom list is part of a source request. For all environments, their WellFormed
proofs, requests, states and assignments, successful production has exactly
old-state models AND output equivalence. A wrapper then recollects sibling
candidates from that produced state using the existing ordinary solver.

Concrete entry uses the existing checked declaration
`impl Index (box 'a) int: type value = 'a` at `box str`, and binds value to the
same source variable consumed by Left's int/str candidates. It proves str
survives and int does not. This is not the complete Parent/Left/Right source
parser/lowering or saturation driver: the associated receiver is explicitly
known and first-order. No final resolve_exact is claimed.

`Computed` refers to the actual `assocOf`; it is not an independent source
judgment. `computed_of_derivation` connects the independent `Roles.AssocDerives`
under explicit AssocWellFormed, resolved, knownness and scalar-decoding premises.
`source_store_agrees` connects the real `RoleConstraints.addAssociated` adapter
to the ordinary-slot producer. The source slot is checked, not silently renamed.
