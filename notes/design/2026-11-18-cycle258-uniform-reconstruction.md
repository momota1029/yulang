# cycle258 uniform reconstruction — Draft

Start2026-11-18T14:25:58Z, deadline15:20:58Z. I50 unchanged.

## Target and ordering

Cycle257 gives a fixed finite journal observation for the terminal I45 family,
but its reconstruction uses a growing historical block. Test whether one
assignment, independent of the stage n, can reconstruct every positive journal
from its fixed observation. This is auxiliary model representation, not a
new Step, general source closure, or Acc.

The family names lower(i+1), upper(i) are generated injectively and separately.
Prove their index is below their numeric name. Then membership in each infinite
family can be recognized by a bounded search through indices up to that name.
Define fill(assignment,name): preserve rows everywhere; for lower names choose
assignment(2).ty, for upper names assignment(4).ty, otherwise preserve assignment.
The names0..4 and fixed actual binder are outside both families.

Target quantified claims:
- for all assignments, names and stages, fill is stage-independent, fixes public
  names and all rows, fills the two actual endpoint families, and is idempotent;
- for all n and assignments, the actual lower/upper history block holds under
  fill, by idempotence of join/meet and literal endpoint classification;
- for all assignments modeling the fixed positive finite journal View, that
  SAME fill assignment models every actual positive journal state;
- public existential models are equivalent, with no per-stage growing-history
  argument in the reconstruction function.

The bounded search is executable in Lean but can be extremely expensive:
allocated numbers grow rapidly. A finite formula/function is not a constant
cost algorithm, finite numeric name bound, or bound on old state storage.
No private name is added to the public aggregate basis.

If this fails, record the exact obstruction, not a language-level rejection.
A broader all-source closure proof still needs the explicit consumer inventory
from cycle257; no arbitrary packet/schema preservation is assumed.

## Prior runtime/spec check

Read work/dots-audit role-boundary record at55574b605 and spec6.5's separate
interval/actual-center meaning. This purely internal assignment reconstruction
has no recorded Yulang2 oracle. No new language-visible outcome is introduced.

## First verified slice

The bounded recognizer, uniform fill, all-stage block proof, finite-view
preservation and simultaneous-journal model projection passed strict Lean.
`UniformJournal258.all_stages` quantifies one assignment transform outside
forall n, including stage0, under the positive finite View premise.
`positive_models` shows that a public boundary has a model at any positive
stage iff it has ONE model for all stages. This strengthens the prior
per-stage reconstruction without invoking compactness or changing old Step.

Implementation safeguard: names≤4 immediately return false before enumerating
indices. Without this guard, proof reduction of a concrete small name expanded
irrelevant huge allocator numerals and hit Lean's numeral-size limit. The
logical characterization is unchanged; the guard is proved from above_seed.
The algorithm still lacks an acceptable general cost bound.

## Next slice: initial public model extension

The previous stronger boundary fixes the internal actual binder. An initial
journal does not constrain that binder, so not every initial assignment can be
extended while keeping it. For the actual source public boundary (names0..4
and all rows), test the explicit repair: set actual.ty := assignment(2).ty,
then apply uniform fill. Prove that this one repaired assignment models the
entire trace iff the original assignment models the initial raw snapshot.
Do not claim preservation of the original private binder or arbitrary program
semantics; this is the fixed terminal family and an existential extension of
its source public observations. Keep the prior stricter Agree results intact.

## Second verified slice

DirectView258 compiles the raw state through a stage-independent alias mapping.
It has n+5 slots and4+16n ordinary entries, so it is NOT itself a finite storage
solution. Its Models is exactly the old raw Models under fill and hence the
fixed five-slot observation's Models.

InitialFill258 and SourceExtension258 prove the source-boundary extension:
set the private actual binder to the source slot2 type, then fill. This single
assignment models every stage iff the input models the initial raw snapshot.
The boundary fixes all initial0..4 complete values and all rows, but releases
the internal binder. PrivateBoundary258 proves on the earlier seed that keeping
that binder makes positive extension impossible; repairing it changes the
assignment while preserving the source boundary. These two boundaries are not
interchangeable, and no original assignment is claimed to model all stages.
