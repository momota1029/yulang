# Cycle244 read-only owner dependency review

Scope: I47 option A, existing semantics unchanged. The independently checked SyntaxGrowth244 refutes a syntax-finiteness shortcut only. No actual source-reachable mutual-owner cycle or failure of the proposed complete successor has been proved.

## Where aggregate dependencies actually come from

`GeneralNominalRebaseDefinitions241.entries` obtains each aggregate RHS from `lower/upper (occurrences bindings name)`. `GeneralNominalRecursiveInspection.bindings` maps the finite report captures to `state.base.source` at the two bound slots. Its origin witness is retained separately; it does not classify those endpoint identities as public or owned by an ancestor. `AllocationSupport.report_endpoints` proves membership in all raw sources, not absence of private targets.

`RecursiveInspection.inspect` traverses structural head child-slot lists for node queries and descriptor argument intervals for nominal queries. A variable query copies the supplied bounds. Thus promotion of an allocated identity into an actual source slot is enough to make that identity a later aggregate dependency, if the certified descriptor/inspection path reaches it.

### Operation-by-operation

* Stable install: Allocation.capture uses the bound pair directly for one occurrence, or stable purpose0/1 private cells for multiple occurrences. Allocation.allocation gives compound child inputs purpose3/4 cells and output equations purpose5 cells. A child variable can therefore inherit the parent's aggregate endpoint. A child's later report may read that parent-private cell. This is a real syntactic route, not evidence of a cycle.
* Refresh: MixedObservations233.Refresh.support says new sources were already in the old source list; that old list includes reserved identities. Refines.base embeds the old slots and fixes their source identities, but new slots may expose reserved cells. The support certificate has no owner-depth direction. Cache/constraints supply semantic soundness, not an explicit source-provenance order.
* Reobserve: Revision fixes the base/source map while replacing nominal descriptors. Its catalogue and domain conditions do not impose an ownership order on argument intervals. I45.Preserves fixes already-point descriptors exactly, but does not constrain the target identity chosen when changing a nonpoint descriptor. The real semantic raw/cache and Improves guards remain necessary.
* Merge/equate: outputAtoms add variable equalities among output targets; they do not immediately change report bounds. They can supply later observation evidence that exposes or relates endpoints. Neither the equality syntax nor Alias itself encodes an owner dependency rank.

## Why Paterson is not yet the missing rank

ChildProduction241.production and birth_bound constrain the semantic labels of **actual child inputs** under Frame/Holds/Coverage, and child_ancestry follows the emitted invocation edge. They do not constrain the lower/upper envelope endpoint identities or their allocation owners. A child-to-parent endpoint dependency can follow ancestry, but no inspected theorem forces every dependency to have that form.

The old, already verified240 family illustrates a different route: LooseFamilyPacket240.bindings_exact gives repeated(lower n,4) at the same root/decl owner. LooseFamilyBase240.source_anchor exposes lower n as a source slot. LooseFamilyInstallation240.lower_in_merges records the next lower cell as union(lower n,lower n). LooseFamilyReobserve240.step supplies actual I45-preserving reobservation; the root remains nonpoint while another newly exposed slot supplies strict point progress. This is owner-local refinement, not child birth, so Paterson descent is irrelevant to that edge.

These facts concern the old versioned allocator. Replacing all its names with one stable cell is NOT an embedding of its transitions: source injectivity, Fresh/External, and observation premises must be rechecked. In particular the next RHS would appear to read the reused cell, so the stable projection's External requirement is a genuine obstruction to a naive port, not a proven stable-kernel counterexample.

## Important qualification of the standalone syntax example

EscapedStore242.replaceAll rewrites all other owners' blocks, not just a separate consumer. In the diagnostic A:=join(B,B), B:=join(A,A), eliminating A rewrites B into a self-reading block. The next External premise may therefore fail. The standalone infinite substitution sequence does NOT establish an infinite sequence satisfying the whole actual store-replacement guards. What it establishes is that finite names and initial owner-local externality are insufficient to infer bounded retained syntax or preservation of those guards.

## Three concrete proof obligations

1. **Actual dependency provenance and guard preservation.** Define an edge from an owner to the owner of each private source read by its real entries and retained consumers. Derive the permitted edges from actual reports, promotion and generated-site history. Do not replace this producer by an assumed acyclic graph. Check the same-owner promotion case before claiming ancestry is a rank.
2. **Other-owner definition-form preservation.** Prove a syntactic lemma for actual atomSubst: with disjoint target lists, inlining owner A into `definitionBlock B` equals a definitionBlock whose RHSs are the substituted B RHSs. Prove coherence and External of that transformed list from explicit cross-read conditions. A sufficient check is that every A RHS substituted into B avoids all B targets; whether that check follows from actual reachable provenance is still obligation1. The new theorem must not merely assume the transformed block is External.
3. **A monotone observable fact compiler.** Known/point progress can use actual source IDs and I45/Refines retention. Equal facts about hidden private coordinates cannot simply reuse MixedAdministrative236.monotone after rebase: the old/new230 witness intentionally changes their values. Use fixed public observables under PublicModel242.raw_step_models, then prove that those observables and complete retained readback suffice for discover/service/classification. Scheduler242's `compile facts owner` is a literal block, so history-dependent rewritten consumers need a proved representation factorization; finite owners and source names do not supply it.

Safe next unit after cache recovery: obligation2's actual entry-rewrite/form lemma, followed by the smallest same-owner240 promotion check for obligation1. Do not begin a new canonicalization policy or assert a full finite fact universe before those producers are known.
