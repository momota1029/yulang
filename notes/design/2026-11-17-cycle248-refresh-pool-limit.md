# Full source pool is not an owner-relative protected refresh pool

Actual Allocation.propagate reserves every registry/root key. State.sources
includes the resulting reserved list, including the owner's stable lo/hi keys
even when its previous occurrence count was one. For a declared input name
with new occurrence count different from one, Definitions241.Fresh against
that entire propagated State.sources list is therefore false.

This is a general limitation of using that sufficient protected-pool condition
for refresh. It is not failure of Allocation.Fresh, which deliberately permits
already-owned reservations, and not a language rejection or unreachable-source
claim. A successor refresh producer needs an owner-relative representation and
boundary argument rather than reusing the first-install protected-pool proof.

Verification: GeneralNominalOrderedRefreshPoolLimit248 passed focused Lean
--trust=0 -DwarningAsError=true in cycle247-clean. The general membership
lemma covers both purpose 0 and 1. The negative Fresh theorem uses purpose 0
and requires no old occurrence-count assumption and no model assumption.
No existing Lean file was modified.
