# Actual recursive fixture: why the resumption contract cannot be applied

The existing recursive fixture has one recorded nonterminal producer and an
unrecorded terminal child. Its semantic dictionary is complete in a concrete
model, but its packet is unsettled. The exact operational obstruction is not a
missing proof of the new trusted guard: any installable packet at that generated
child is already Committed under the ordinary feedback relation, so novelty
fails before the new guard is considered. Concrete guarded stability also rules
out every child At transition, not just an installation.

This specializes existing concrete commitment/stability results rather than
introducing a new semantic rule. It explains why ConsumerResume.leaf_then_consumer
is not an executable recipe for this fixture. No existence of an installable
child packet, generic progress result, or change to settlement is asserted.
