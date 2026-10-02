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

## User-directed classification of finiteness

The user selected three distinct outcomes for the finite-presentation inquiry:

| Class | Meaning | Current evidence |
|---|---|---|
| Finite but unbounded | Each finite source has a finite principal presentation; size/work grows across inputs with no fixed source-independent ceiling | Pure finite endpoint-graph saturation is finite for each finite input graph, establishing a resource component only. Principality is not proved even for the full pure fragment. |
| Infinite unfolding, finite graph | Recursive behavior expands indefinitely but its meaning admits a finite cyclic/SCC/regular representation with a preservation proof | Recursive bounds use finite back-edge data structures, but their regular unfolding and preservation are not established. Regular active stacks are another candidate component, not a complete handler/interface quotient. |
| Genuinely non-finite for the chosen abstraction | A concrete witness proves no finite sound/principal representation exists for that chosen abstraction | No such witness is established or ruled out. A missing quotient construction is not evidence for this class. |

A regular-stack-only quotient has a concrete limitation. Two candidate
configurations can have the same active/captured stack words and source sites,
but differ in whether a captured reference `x` aliases a caller reference `y`.
Both cells initially contain `0`. The saved raw continuation captures `x`; its
suffix writes `1` through `x` and then emits the same operation `E`. Both
handlers are otherwise visible and cover `E`. The inner handler's guard accepts
exactly when `y == 1`; the outer handler accepts unconditionally. After resume,
the inner handler is selected when `x` aliases `y`, while the outer handler is
selected when the cells are distinct. A stack automaton that omits the live
capture graph merges states with different actual selected handlers. This
selects or rejects the wrong assignment if the merged route set is used as a
typing obligation. The witness is over the candidate source machine, not an
executed Yulang program or Oracle acceptance observation. It refutes the
stack-only quotient, not richer finite relational graphs.

The earlier nonregular-tree assignment witness refutes replacing an arbitrary
`P(N)` observation fiber by regular languages without further justification.
It does not classify Yulang source assignments as genuinely non-finite:
whether that powerset is the source's expressible type domain remains
unproved, and finite cyclic type graphs may be the correct class-2 model once
their semantic preservation is established.

## Finite/regular quotient construction inquiry

The regular-stack-only quotient is rejected: active and captured stack words
do not retain the alias relation between a saved continuation's reference
and a caller handler guard's reference. The same witness also rejects any
independent marginal-store abstraction that forgets this incidence and has no
separate exact selection witness. It does not reject a relational graph that
retains the incidence, nor a marginal store paired with an independently
proved exact selection relation.

The next representation candidate is a joint rooted relational graph whose
candidate roots/edges connect finite source sites, ordered active frames,
suspended invocation/re-entry wrappers, captured environments, live cells,
closure/thunk environments, continuation roots, and receiver/handler
incidence. It must retain runtime identity equality and aliasing under
consistent renaming, while keeping request origin and dynamic event identity
distinct from handler authority. The same graph must transport source-owned
symbolic binders and joint `K,D` incidence. These are candidate coordinates
to investigate, not a selected sufficient representation.

Finite source labels and alpha-renaming do not bound graph size or prove a
regular graph grammar. The full construction still needs effective closure of
the symbolic predicate language, treatment of existentially local identities,
and universal latent-value/resumption future use. A source-image theorem must
preserve actual ordered-selection admissibility and the complete shared-`ν`
fibers through calls, `Force`, store updates, effectful guards, dispatch,
forwarding, raw resumption, and suspended invocation re-entry. Forward
simulation or may-support coverage alone cannot prevent invented incompatible
routes from rejecting an otherwise admissible assignment. A separate
projection theorem must then establish the least representable interface for
the chosen derivation preorder.

Classification remains open for the joint effect interface: class 1 is not
established; class 2 is plausible for control components but unproved for the
joint capture/store/resumption/type-family graph; class 3 has no established
witness and is neither concluded nor excluded. The fixed-`Q/P` saturation
theorem only proves termination after the quotient, predicate closure, source
image, and projection premises are supplied. A resource ceiling cannot stand
in for those proofs.

## Conditional lower bound for exact event quotients

There is a conditional obstruction to demanding an *exact, effective*
finite/regular event quotient. Let `L` be a source fragment with an effective
encoding `(M,w) ↦ p(M,w)` of deterministic Turing machines and finite inputs
as closed, well-typed programs under an effectively supplied finite
monomorphic signature. Require the encoding to have one designated operation
`E` such that some actual execution selects `E` exactly when `M` halts on
`w`. Suppose a total computable presentation builder `Q` works on every such
program and a total computable predicate `HasE` decides from `Q(p)` whether an
actual selected `E` event is represented exactly. Then
`HasE(Q(p(M,w)))` decides the halting problem, a contradiction. Therefore no
such pair `(Q, HasE)` exists.

The encoding premise is plausible for frozen Yulang source: recursive
function SCCs are allowed; immutable lists have finite constructors and
head/tail patterns; enums and ordered cases express a finite machine state and
transition table; and one concrete shallow handler can select the designated
operation. Represent the tape by the current symbol and two lists for its left
and right stacks. Each machine transition is one case branch and a recursive
call at the same monomorphic function type; only the halt branch requests
`E`. A concrete handler around the run selects that operation. Frozen-source
locators at commit `a58eefc3`: `web/docs/reference/types.md` § recursive
components; `web/docs/reference/std/list.md` construction and head/tail
access; `web/docs/reference/patterns.md` list and enum patterns;
`web/docs/reference/functions.md` type/effect annotations; and
`web/docs/reference/effects.md` operation calls and shallow handlers.

This remains conditional, not a theorem already derived from the candidate
ordinary-machine rules: those rules do not define recursive binding,
list-pattern, enum, or general typing judgments. It also assumes the effective
supported envelope contains the full machine-encoding family. A deterministic
resource boundary that excludes some encodings limits the theorem's scope.

The lower bound concerns exact event reachability. The adequacy target permits
a sound conservative presentation (`Sem ⊆ ⟦P⟧`), so a presentation may retain
`E` even for a non-halting machine. That does not decide halting and may still
be principal relative to a chosen coarse abstraction. The result also does
not rule out finite graph syntax whose exact event query is undecidable; it
rules out the effective exact-query package stated above. It is therefore not
a class-3 result for the successor abstraction and does not justify shrinking
the supported envelope. It rules out requiring exact trace support as a
decidable inference presentation over an envelope encoding arbitrary
Turing-machine runs, consistent with using exact traces only as a soundness
reference.

The user explicitly permits class-1 resource limits. A later representation
may cap an explicit structural dimension such as presentation nodes, symbolic
states, or saturation work. Exceeding the cap must produce a deterministic
inference-complexity failure, never an ill-typed result, truncation, or partial
publication. The metric, check point, and threshold are deferred until the
presentation is constructed; no cap is selected here.

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
