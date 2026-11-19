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
