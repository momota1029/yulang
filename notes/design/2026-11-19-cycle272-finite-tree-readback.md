# Cycle 272: certified finite branching readback
Continue I-52. Cycle271 requires a supplied full-model witness with unary
nominal type trees. A finite canonical tree of arbitrary nominal type
arity, scalar, pair, variant, exact-empty and finite record is a more
useful witness. No language or raw execution rule changes.

1. Define explicit finite terms plus canonical record condition, carrier
denotation, and height. Carrier equivalence fixes the canonical head
and child denotations; prove height invariant. Proof must use carrier
equivalence, not literal equality.
2. Use the old all-model Edge and a single actually valid model. Under a
known finite tree, a raw or semantic projection cannot escape its
children. Literal noncanonical record tests require first-visible labels:
reject shadowed positions from live equality, otherwise map to actual
canonical child. This proves old semantic edges strictly decrease height
near these witnesses, not old kernel stopping.
3. Compute a query by walking a supplied finite witness tree, trusting
only independently certified model readback. Distinguish missing source
support, truly absent observations, and nonfunctional but possibly
observable shadowed positions. Test branching successes and negatives,
then seek a pre-existing real full model, ideally with a branching
retained output and an independently readable emitted equation.

The tree walker distinguishes four statuses. Unsupported source identity
is unknown; an invalid label set/index or constructor is genuinely
unobservable in the supplied model; a shadowed record position can
observe every carrier type; otherwise the source is represented by
a known canonical subtree. An arbitrary-observations parent differs
from mere failure of all-model equality: whenever a further nominal
(or a valid structural) projection is requested, an arbitrary payload
can be realized by selecting a corresponding parent value. The checker
carries this explicit proof rather than collapsing it to absent.

## Verify emitted-equation readback, without inventing variable shapes

Compile the checked emitted expressions in the finite grammar using a
partial table of variable witnesses indexed by observation mode. The
existing carrier meaning dictates the mode (nominal children are
always actual). Accept exact or width-empty leaves, scalar, pair,
variant, nominal of any finite type arity, and records whose closed
width tail and label order are certified. Abstain on joins and other
unsupported forms. A matching equation is used only with its original
schema evidence and the caller-supplied full model, not as an override
of the original journal. Exercise it on real emitted 252 and verify
that optional output (join) in 238 stays unsupported.

The interpreter is total on every syntactic continuation of a supplied
finite source witness; unknown is exactly missing initial source
support. The real installed 218 model supplies a two-argument nominal
root with two variant children read back as Int and Bool, respectively.
Its unrelated interval endpoint remains unsupported. Root K2 can be
computed and checked directly on the original installed journal; this
does not judge the separate shared-input child guard.

## Fixed-point enclosure for a fixed retained plan list

Witness propagation never replaces a previously established shape and
adds only targets from the actual emitted equation lists. Use the
number of target occurrences still unknown as a natural rank; duplicates
are allowed. If an entire pass changes the shape table, at least one
previously unknown target is filled, so the rank strictly decreases.
A pass can be iterated a bounded, source-dependent number of times
(no guessed search fuel necessary), and the computed output is a
fixed point of this compiler on that fixed set of plans. This is
verification of witness propagation, not stopping of the old Step,
not completeness of the admitted grammar, and not dynamic install
observer completeness.

One pass on the actual retained plan list of installed 252 derives output
3 from a seed witness for input 2 only, using the emitted expression and
the existing full model proof. The three nominal selections on the
derived output compute Int. A separate synthetic schema covers nominal
branching, pair, finite ordered record, variant and exact-empty. The
existing optional output in 238 still abstains on the join.

Canonical carrier equivalence determines the entire finite witness tree,
not just its height. Therefore a newly enabled earlier equation cannot
change the chosen tree in the same model. Adding more certified seeds
preserves each compiler result; the bounded closure is least among
certified fixed points extending the seed, and independent of permutation
of a fixed retained plan list in the same model.

## A countermodel comparator for finite readbacks

Compare canonical finite trees by a reified head/child code. A single
actual model can refute old all-model Equal when projected observations
are absent, nonfunctional, or have distinct readback trees. Matching
codes prove model-local Same but do not establish an all-model positive.
Exercise this on the two actual 218 variant branches that have the same
coarse tag but different scalar leaf types. It is a certificate about the
specified origins, not a substitute for the separate child sharing guard.

The same evaluator has an all-model positive variant only with uniform
source certification. Fixed emitted equations preserve the uniform
certificate one plan/pass at a time. In real installed 252 the source
input tree is forced across all models by its retained packet, and the
derived output tree after two selections computes the same witness as
input 2. The comparison becomes a genuine all-model Equal proof there.
An isolated fixture model by itself can only disprove that judgment.
