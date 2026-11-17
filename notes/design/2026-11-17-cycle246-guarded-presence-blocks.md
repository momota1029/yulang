# Cycle246 plan: constructive cyclic definition blocks in actual Presence terms

I47 remains active. Cycle245 proved public solution preservation for External
blocks, but also showed that an actual satisfiable guarded recursive block
fails External and every strict source rank. Those checks cannot become source
acceptance rules. This cycle develops a concrete finite guarded fragment whose
block equations are generated in actual Presence TyTerm/Atom syntax and whose
regular Common solution is constructed for every outside assignment.

## Data and executable translations

Use a finite node index and a finite parameter index. A guarded layer contains
base/bottom/top, unions/intersections, exact/width-empty records, record tails
and whole-record-default sources inline. Every recursive or parameter reference
is under a genuine payload constructor (pair, record/required, variant, arrow,
or default fallback). Row terms remain actual RowTerm Name expressions and are
evaluated against the unchanged row assignment. This is a representation
fragment, not a restriction imposed on the source language. Arbitrary unguarded
aliases or source-type expressions are not asserted encoded by it.

Translate a layer to actual TyTerm using the supplied finite node/parameter
name maps. Separately lower it to CommonNominalSyntax.Layer with evaluated
rows. Prove an exact interpretation bridge by induction over every constructor.
The maps for recursive targets must be injective; parameter names must be
outside that target image. Parameter names may repeat. These are allocation
conditions on a finite block, not assumed semantic solvability.

## Intended theorems (with explicit quantifiers)

For every finite guarded body, injective target map, disjoint parameter map and
arbitrary original Comp assignment, construct a new assignment that:
1. agrees literally at every name outside the target image;
2. has the same row component at every name, including targets;
3. satisfies every actual two-inequality definition in the compiled block.

Use existing all_parameter_sound for the finite regular Common closure, not an
assumption of the desired block satisfiability. Then recover every original
block model up to mutual subtyping at targets using all_models_recovered.
The type/root representation need not be antisymmetric.

Connect the finite block to literal public-model extension for consumers that
do not read its private targets, and document the remaining general-rebase gap:
the existing finite TyTerm substitution cannot directly embed arbitrary closed
regular graph values. No solver termination, arbitrary source-body compiler,
all-metadata coverage or EvidenceNode claim follows from this fragment.

Before ending, continue independent finite-allocation or consumer-transport work
rather than declaring completion after the first lemma. Research until20:15 UTC;
verify, publish and report before20:25. No large OriginView/journal rebuild.
