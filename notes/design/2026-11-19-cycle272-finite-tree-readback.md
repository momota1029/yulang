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
