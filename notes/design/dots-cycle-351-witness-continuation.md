# C351 release-backed witness continuation

## Current checked interfaces

* A successful scoped replay now independently computes both the author
  compiler and the consuming record forest. The same fixed declarative
  state and same model validate both dictionaries and all fixed writes.
* The producer row is from the compiler's literal ordered trace, with
  occurrence path, role, independently fixed active version, write
  ordinal, and logical target. The full request at the ordinal, including
  associated name, can be recovered. A release is matched on the entire
  key and becomes only a completed output origin, never a source origin.
* The positive tagged preparation distinguishes literal anchored merges
  from a recursive named proof. The latter keeps actual read authority at
  every arm, prepares using the existing named patch route, and independently
  replays the same ordinary compiler and current equations. This yields
  genuine exact local node/leaf Evidence; it is not yet a positive election
  or forest using the recursive named route for arbitrary competing candidates.

## Design cut for next cycle

1. Unify the decoder front doors without equating their readings. For
   tagged literal inputs reuse `WitnessTagLocal351.input_direct` and the
   existing C340 whole input. For named tagged input use
   `WitnessTagSources351.named`, `WitnessTagNode351.local_node`, and add
   a real supported named alternative to independent positive election.
   Verify viable alternatives and priority, rather than treating the
   direct-path `none` as rejection, as pending, or as proof of uniqueness.
2. For nested record binder patterns or where operands, connect the exact
   named recipe to its real allocated slot/sidecar and ordered child
   demands. C351 validates the whole payload at one leaf and both mixed
   upper/lower routes, not arbitrary nested pattern coverage. Existing
   `TaggedNamedRoute340.under_siblings` separates placed sibling fields
   from protected actual center and source provenance.
3. Generalize finite input layouts and independently stamped producers
   to more than a single checked producer forest with the same fixed
   model. Stamps and releases currently belong to the immutable caller
   inputs; bind them to actual normalized source and a versioned
   recorder when extending the implementation. No evidence is recovered
   from C316 or inferred from matching either a target or model value.
4. Keep I-59 ordinary root K2 distinct from absence of input authority.
   The exact normalized shape from an ordinary row does not make that
   row available. General diagnostics and completeness still need their
   own proof; no argument here concerns raw solver termination.
