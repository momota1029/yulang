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

The existing candidates do not yet construct a finite joint typed interface
under ordered handler image and interface projection. A stronger conditional
algorithmic target is now isolated in the coupled-interface draft as the
finite guarded-saturation theorem:

- Fix a finite complete-state quotient `Q` and a finite basis `P` of
  predicates over the shared assignment `ν`.
- Represent every formula by its truth table over the `2^|P|` predicate
  valuations. The abstract state is a vector of such formulas, one per `q∈Q`.
- If each primitive transition has an exact guard `G_qr` in this basis and
  keeps `ν` fixed, transfer is `F(φ)_r = Init_r ∨ ⋁q(φ_q ∧ G_qr)`.
- For each predicate valuation this is reachability on a finite graph over
  `Q`; iteration from bottom reaches the least fixed point in at most `|Q|`
  rounds. The result is the least reachable relation in this declared finite
  presentation and retains disjunctive assignments without choosing a match.

This is a reviewed conditional theorem, not a constructed Yulang presentation.
It materially sharpens the missing construction: show that recursive calls,
live state, activation identities, raw resumptions, latent future use,
existential local binders, ordered handler selection, and all dependent
`K,D` views admit a finite *joint* `Q`; show every generated type/family
predicate remains in a fixed finite `P`; and prove projected interfaces are
exact for the selected derivation preorder. Incompatible-arm admissibility
must follow actual ordered selection, not be hidden in a runtime guard or
invented by spurious quotient routes. The callback contract rule remains
uniform for direct and Force-exposed requests.

The compiler-referee audit supplied a concrete reason the quotient condition
is stronger than may-reach soundness. If reachable `c₁` and unreachable `c₂`
share `q`, and only `c₂` reaches an incompatible selected arm, the existential
abstract edge reports that arm as reachable and can reject an admissible
source program. Dropping it because another route is compatible can hide a
real incompatible selection. Therefore selected-event admissibility must be
preserved by the quotient itself or by a separate exact witness; the ordinary
support over-approximation cannot impose typing obligations on its invented
routes. This does not forbid conservative row support.

The older candidates still do not close the joint typed interface:

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
target is to construct `Q`, `P`, their exact source-image guards, and the
principal projection bridge for the conditional saturation theorem;
support leastness alone cannot discharge inference principality.

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
