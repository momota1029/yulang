# Cycle216: current selected head tests from actual input provenance

Goal: derive arbitrary recursive selected-head schema tests from actual corrected
reachable input ancestry, not from a historical plan of the same declaration.
No finite-input premise may be added to the final reachable theorem.

First obstruction: `CountedMeaning` records closed+covered normalized patterns
and their semantic values, but not constructor interpretation/arity coverage.
Unknown applications evaluate to bottom. Thus blindly converting every counted
label into a closed canonical `Expr` is not justified. The actual provenance
starts at closed canonical ground roots and uses covered unnamed argument
production; either preserve that stronger provenance or use a generalized
pattern-bracketing proof which handles unrepresentable labels honestly.

Before code: inspect existing recursive finite matching and centered child
production proofs; determine whether a stronger closed canonical center invariant
can be transported through corrected208 installs without changing their premises.
Counterexample probes concern helpers only, not EvidenceNode.

## Completed generalized argument

The canonical-Expr route was rejected, not assumed. Existing
`GeneralNominalCenteredHeadMatLabelDomain.no_old_closed_term` already records
a covered arbitrary-tail record outside the old ClosedTerm domain. The new
proof handles that domain directly.

1. `CountedRoot216` classifies any normalized pattern into bottom, scalar,
   nominal, canonical structural primitive, or a syntactic arbitrary-tail
   record. Unknown applications and malformed primitive arities remain bottom.
   Scalar and invariant nominal lower bounds exclude all incompatible roots.
2. `RecordBracket216` uses a finite lower record bound to exclude unlimited
   terminal fields and nontrivial absent optional observations. Both finite
   endpoint bounds recover the exact field signature. The resulting record
   spine is equivalent to a sorted finite record without assuming its original
   tail was empty or canonically representable.
3. `CountedBracket216.structural` therefore derives arbitrary canonical
   structural head tests from a closed normalized pattern between two
   same-shape endpoints, including record/exact-empty separation.
4. `CountedObservation216` derives a closed-normal observational label directly
   from CountedMeaning (normalizing again soundly), and propagates such labels
   through actual structural and nominal projections using HeadParts inversion.
5. `CountedInspection216.inspect_tests/many_tests` prove all recursive schema
   head tests from current SourceModels, labelled bounded roots, and Finished.
   No historical declaration or finite-Expr assumption appears.
6. `CountedCandidate216.tests` obtains the labels from actual corrected208
   sites_bounded/head_readback, with the existing initial source/point/ground/
   coverage boundary, and derives all current candidate head tests. No new
   finite-center hypothesis is imposed. `tests_of_finished` removes Frame and
   Prepared, requiring only current context, registered input, located bounds
   and explicit Finished instead.

## Exact scope and remaining sharing obstruction

These are semantic head-test theorems, not a proof of unrestricted EvidenceNode,
ChoiceCompatible, current Prepared, or a common journal/head/effect witness.
Repeated-variable-only schemas have no tests, so this result alone cannot force
two distinct actual capture origins with the same name to be equivalent.
ProjectionModels also requires such sharing; cross-capture fits can be derived
from sharing and the independently obtained anchors.

Current Prepared supplies an existential raw source/head witness, whereas
counted ancestry is proved for journal Models. A Prepared witness cannot simply
be substituted into sites_bounded without first proving journal membership.
Conversely, failure of capture sharing in one particular journal model does not
refute the existential common-witness goal. A fixed-journal sharing criterion is
stronger than existence of some compatible journal witness.

No interval endpoint collapse is claimed: the new bracket establishes the
constructor shape and projected labels, not equality of arbitrary interval
extrema. Actual reachability might supply further constraints, but none were
silently imported from the initial point-root condition.

## Verification

All six new modules pass Lean 4.35.0 strict compilation with -j1 and
warningAsError=true. A trust=0 scan over every constant defined in these modules
passes: COUNTED216-PASS, 63 constants in 6 modules. Transitive axioms are restricted
to propext, Classical.choice, Quot.sound. No sorry, new axiom, native_decide,
or import of obsolete operational Steps is introduced. Older pure semantic
lemmas are reused without model casts. Publication and full integrated build
belong to the parent.
