# C306 extension: actual scalar control before installation

Separate unchanged prior models from post-install model constraints.
Starting at the source initial state, track all refresh-only prefixes.
Only the two scalar identities can become fresh (a Top witness excludes
unconstrained names >=3 and the retained opaque nominal at 2 is known).
Show every possible next raw step from these prefixes is either a
certified tracked scalar gain or a real install. Do not treat install
eligibility as a Boolean until a plan is reconstructed and certified.
Carry the positive/negative signed witness table along the whole
prefix through actual certificates, not only the canonical scalar cache.

C286 already proved the robust pre/installation split and availability.
The final C306 implementation reuses it, rather than publishing a
second pre-anchor; the new contribution is an executable quotient
with every batch lift and fixed finite signed witness transport.
