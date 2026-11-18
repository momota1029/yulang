# Source representatives: precise scope

`RegisteredAt` is witnessed by an actual source-reachable snapshot and membership in its versioned plan journal, with exact encoded owner equality. `representatives` uses classical choice to pick one registered plan for each owner that occurs anywhere in the source future. For codes that never occur it reuses one actual registered plan as fallback. Thus construction needs a single existential nonempty registered-plan witness; the empty-source-future case is not handled by this function.

This is a noncomputable mathematical family, not an executable search, future plan enumeration, selector, or compiler. Its existence proof does not prove source compilation success. Only occurring owners have the RegisteredAt guarantee; no claim is made that the fallback has a nonoccurring owner code.

`representative_layout` uses actual checked registry and source path metadata only. `representative_compatible` additionally uses `SourceHeads`, which requires head-schema satisfaction of every registered plan at every reachable snapshot under the supplied assignment. This is strong and explicit. It contains no body, child, ClassEffects or desired-equivalence premise; it is NOT automatically derived from source initialization, nor from Models at one unrelated snapshot. The head-only center induction supplies the transport theorem without circular output assumptions.

The actual example is CompoundStep238's verified one-installation source prefix. Its versioned journal contains the actual installed Plan, so the representative family is genuinely inhabited. This example demonstrates classical family construction, not an executable computation of its chosen Plan or universal SourceHeads.

Strict focused builds and axiom probes pass. Only standard propext/Classical.choice/Quot.sound appear. No frozen files or original compiler modules are modified.
