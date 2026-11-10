# Draft: persistent keyed local-capture registry

Status: Draft. Date: 2026-11-10. Scope: B4 source boundary in the existing structural interval grammar.

## Goal and constraint

Close actual finite registry allocation and reuse for explicitly identified invocations. A source key is `(invocation, binder)`. Invocation identity is provided by the caller; deriving that identity from source syntax, candidate identity, and parent obligation paths is a separate bridge. No decision is made that equal goals, equal endpoint observations, or equal binder spelling from different invocations should share.

An offset-only map for an invocation is insufficient: its image for all natural-number binders overlaps the image of a later allocation. The registry therefore stores finite pairs and uses first occurrence positions, plus a fixed boundary above all initial ordinary demand names. Extending a registry retains every old first position. Each actual accepted capture registers its finite captured binder pairs before producing constraints. Repeating a fully registered capture returns the same registry, even when the captured interval endpoints change.

## Data and independent judgments

Registry data are a finite pair table and a reserved natural-number boundary. Registration appends a batch only when at least one key is absent. Duplicate historical table entries are harmless because first-position routing is canonical. The execution state retains both the registry and all previous ordinary demands. Initial registry has an empty table and a boundary computed from the initial demand list.

The actual candidate inspector is unchanged and keeps outside / negative / positive outcomes distinct. Only a positive candidate registers its returned binders; original head and where-template constraints use the computed map. A revisit shares exactly the same semantic variable for the same explicit invocation and binder. Two present pairs have equal allocated names iff the pairs are equal. Ambient endpoints and semantic local names remain different namespaces.

## Quantified target

For every table, boundary, key batch and present source pair, registration preserves its allocated name. Every requested pair becomes present, first positions distinguish all distinct present pairs, and registering the same batch again leaves the table unchanged. For every initial demand member and every allocated pair, the allocated name differs from the initial demand name.

For every assignment, slots, state, invocation key, declaration, goal and result, the actual positive runner return with a model is equivalent to an independent accepted capture, the explicit registered output structure, and one valuation satisfying prior demands together with the original head and all original where templates through the computed registered map. The common valuation is existential in the conclusion, not a model-existence or consistency premise. Intentional reuse cannot be replaced with independent per-visit existential valuations.

Prove that accepted captures with the same declaration have the same finite binder list, independently of their goal endpoints. Then all revisits of that declaration under the same explicit invocation key reuse the complete source map even after intervening allocations. Missing/negative candidates do not add registry entries. No successful where dictionary is assumed.

## Evidence and open boundary

Read spec 6.3 sharing, related-type equality and stable sibling regeneration; audit x-oracle X13–X16 and C3-PARENT / C3-PARENT-NEG. Those examples constrain source identity but do not verify the registry algorithm. No new Yulang2 execution. General graph adequacy, associated feedback, finite goal closure, saturation and final classifications remain open. B4 still has five main bridges. This is an explicit-key local utility, not a choice of language-visible invocation identity.

## Finite shared-model closure

The implementation also closes the arbitrary finite sequence, not only the single-return wrapper. `VisitsFit slots assignment locals visits` uses only original accepted captures, original head/where judgments, and a valuation indexed by `(invocation, binder)`. It mentions no allocated natural-number names, registry, ordinary constraints or runner. The same valuation is shared across all visits with a repeated key.

For all slots, assignments, initial demand lists and finite visit lists, `follow_models_exact` proves actual final success with a request model iff the initial demands have a model and one keyed valuation satisfies every original visit. The proof constructs a flat valuation from the old witness and keyed witness using the final finite registry; it does not assume compatibility of reused variables. A disagreement among repeated-key intervals is rejected by the generated cross-visit constraints. The driver processes caller-specified visits, so it proves neither finite generation of all goals nor fairness or saturation.
