# Finite complete-interface presentation gate

Date: 2026-10-02
Branch: `research/simple-sub-intrusion`
Status: precise unresolved construction gap; no implementation authority

## Closed source simulation package

The exact complete-interface embedding in
`notes/design/2026-10-02-source-interface-adequacy-theorem.md` has been
reviewed as a candidate-machine theorem package. It covers the initial
relation, primitive source-rule images, latent future use, and admissible
resumption; the finite-resumption bind lifting premise was separately
reviewed. This closes source-to-exact-interface simulation for the candidate
ordinary machine. It does not show that current Yulang typing derives its
candidate binder ownership, nor that this exact interface has a finite
inference presentation.

The selected callback rule is carried into the reference: a concrete callback
capture contract visible throughout its complete `CallView` determines
receiver-local visibility for direct and `Force`-exposed requests alike.
`Force` reveals latent behavior but creates no authority. Caller origin,
dynamic event identity, and symbolic `K,D` remain attached to each event.

## Milestone-3 result

The existing finite candidates do not close the joint typed interface under
ordered handler image and interface projection:

- finite request-support closure can forget correlations between family
  predicates, root views, residual effects, and continuation views;
- the closed point-row formula result retains disjunctive matches, but does
  not cover assignment-dependent handler visibility or the shared symbolic
  fibers of those other views;
- the Galois-connection least-closure argument is conditional on an effective
  complete lattice and monotone transformer, neither of which is constructed
  for the typed interface language.

Thus no terminating finite formula language is currently shown to preserve
these joint fibers through handler images and yield the least representable
well-typed interface. This is the precise obstruction to closing Milestone 3,
not an impossibility theorem or proven expressibility limit. The next proof
target is one terminating compositional presentation with effective source
images and principal projection; support leastness alone cannot discharge
inference principality.

## Boundary-rule delta

The coarse may-block candidate treated `UnknownOrigin` as an independent
reason not to subtract a request. That candidate bookkeeping is superseded by
the selected source semantics. Origin uncertainty alone cannot veto a
concrete callback contract when the complete `CallView`, exact operation
coverage, and active receiver-local handler are established. Any blocker must
come from unresolved behavior or event-relevant boundary incidence in the
actual configuration. `UnknownOrigin` remains useful as provenance and may
indicate such a blocker when those facts are unresolved; it is not a separate
permission rule. The correction is recorded at the source in
`notes/progress/2026-10-01-intrusion-coarse-effect-abstraction-candidate.md`.

No new fixture rules, compiler changes, tests, or performance measurements
were added. Milestone 4 remains dependent on a defined Milestone-3
presentation. Method/roles/implementation resolution stays a later mandatory
gate.
