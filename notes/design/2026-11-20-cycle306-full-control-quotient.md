# C306 full-path control (building on C286, not replacing its raw rules)

C286 already proves the actual pre/install/post partition, offers a checked
install from every pre representative, and keeps scalar atom/cache support
through it. Reuse those facts rather than restating a second phase invariant.
Combine an executable packet-presence bit with the two executable Known bits.
Each raw edge projects either to install (same scalar mask) or to labelled
scalar gain (same phase); batch gain may change both scalar bits. Lift every
edge from every reached representative by the checked promotion or C286
install offer. Forgetting labels needs more than counting obligations:
two pending scalars can batch, while one pending install and one pending
scalar cannot be batched. Separately keep the fixed signed witness rows along
all refresh prefixes of the pre phase.
