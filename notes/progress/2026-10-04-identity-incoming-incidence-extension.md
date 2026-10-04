# Identity-scheme incoming extension for production value incidence

Date: 2026-10-04
Status: source-generation theorem extending a restricted structural
projection; no implementation or semantic authority
Scope: current F5 value projection for error-free binding HIR with
integer, identity, or alias-cycle cross-SCC targets
Depends on: [current HIR value-skeleton incidence theorem](2026-10-04-production-f5-value-skeleton-hir-incidence.md), Theorem S in [the source-generated theorem package](../design/2026-10-04-source-generated-callback-structural-theorems.md), and the current `yu-hir` / `yu-solver` generation rules

## Result

The incoming-`Int` theorem has a useful non-extrema extension. Consider its same finite HIR grammar and the same value projection, but allow each cross-SCC resolved use to target one of:

1. a name-binding alias chain ending at an integer binding; or
2. a name-binding alias chain ending at an own-parameter identity lambda, `f p = p`; or
3. a name-binding alias chain ending at an alias-only cycle.

The walk follows only resolved one-name bindings. It must end at an integer or identity lambda without repetition, or enter an alias-only SCC. No other cross-SCC target shape is admitted. This is checked by a finite walk over resolved HIR and the SCC plan, independently of structural satisfiability or any regular witness.

After actual F5 routing and rational-equality normalization, the resulting free/free value-incidence components still satisfy Theorem S. Integer routes contribute closed `Int` anchors. Identity routes contribute exactly one open positive `Function(q,q)` anchor per retained use component. Alias-cycle routes contribute no value inequality, so their use-side component has no incoming value anchor. The fresh identity `q` is unanchored and occurs only as a Function child. Thus, if the projected package is satisfiable, it has a simultaneous regular witness.

This is a sufficient source condition, not a rejection policy or a claim of necessity. It strictly admits a structured polymorphic cross-SCC scheme excluded by the previous incoming-`Int` restriction. It still does not cover arbitrary structured schemes, full Function effects, or the coupled four-port package.

## Source-generation lemmas

**Identity terminal.** For the current unannotated source `f p = p`, HIR resolves the body to the same `HirParameterId`. `emit_lambda` and `admit_lambda_fact` generate the positive value descriptor `Function(p,p)`; the F5 generalizer closes it as one quantified variable shared by argument and result, with no recursive bounds. The existing source assertion at `crates/yu-solver/src/lib.rs` (test `f5d_source_identity_boxed_and_flat_candidates_agree`, near line 20591) checks this exact output. For this value projection, its effect children are omitted; in F5 the source test also confirms the pure effect children.

**Acyclic alias preservation.** Induct on the finite alias-chain length from a cross-SCC use target to that identity terminal. The terminal case is the identity scheme above. Each preceding alias definition has exactly the generated occurrence-to-root fact `v_o <: r_d`; its resolved use is routed from the finalized target scheme. Instantiation allocates one fresh row `q'` for the single target quantifier and, because the scheme has no recursive bounds, routes exactly `Function(q',q') <: v_o`. The alias component therefore has one positive Function lower descriptor and no independent upper/closed value fact. Generalization preserves this single shared child row as one quantifier, again with no recursive bound. This proves that every target root along the admitted acyclic chain has the same scheme up to quantifier renaming. The induction uses the actual finite generation and generalization clauses; it does not test or assume regular satisfiability.

The route shape follows `route_incoming_inner`, `instantiate_and_route_closed_inner`, and `closed_parts` in `crates/yu-solver/src/lib.rs`: a quantified positive Function is reconstructed once, and recursive lower/upper restorations are absent. The broader positive-union Cartesian expansion and recursive-bound restoration paths are not reachable from this generated scheme.

**Alias-cycle terminal.** An alias-only SCC has no integer or lambda producer. The current F5 generalizer materializes its empty positive root expansion as `PositiveValueView::Bottom`; a finite acyclic alias prefix ending at that SCC has the same no-lower-bound result. When this target is used cross-SCC, `route_incoming_inner` takes its Bottom-trivial branch and emits no value inequality. The source occurrence-to-root clause remains, but no Bottom/`Never` value-type interpretation is introduced into this structural theorem. This is only a characterization of the existing route's no-op value projection.

## Incidence extension

Retain the source alias graph and post-routing cut distinction from the incoming-`Int` theorem. A name-binding root has at most one outgoing resolved-name edge. Every edge on an acyclic alias chain is between distinct SCCs: an alias-only strongly connected component has no terminal exit, and the identity lambda has no module-name body dependency. Each such cross-SCC edge is cut by routing; the source-side alias root is not connected to its target root. A cut whose target lies in an alias-only cycle also contributes no value edge, by the Bottom-trivial dispatch described above.

A source-side alias fragment has at most one outgoing cut because it has outdegree at most one. In the admitted grammar its edge is itself the use being routed, so no component can accumulate two fresh identity descriptors through separate cuts. A lambda-body use is also its definition's sole resolved use; when it crosses an SCC boundary, it contributes no free/free edge to that target root. The lambda root's Function descriptor reaches the body only by a constructor-child edge, so it does not become a competing anchor in the body's free/free component.

The original cases remain unchanged: an integer terminal and any cut fragment ending in an incoming integer are grounded by closed `Int`; a retained lambda root has its single source-generated Function descriptor; own-parameter and integer body components are respectively unanchored or grounded; internal name uses retain their root-to-occurrence edge; alias-only cycles have no descriptor anchor. A cut to such a cycle leaves an unanchored use-side component. The identity case is a cut fragment with one incoming `Function(q,q)` descriptor, which meets Theorem S's one-open-anchor condition. The `q` component has no incident free/free inequality and is handled by the no-anchor case. Rational equality introduces no extra identifications because the generated package has no equations. Theorem S now applies to every component.

## Separate HIR/source-generation theorem

The source condition is decidable from the finite resolved HIR and its SCC plan: classify each cross-SCC target by following resolved-name binding edges; accept integer or own-parameter identity terminals after an acyclic alias walk, or detect an alias-only cycle. The source-generation lemmas above show that the collector, SCC router, scheme finalizer, and incoming instantiator emit exactly the admitted anchors or no value edge. The incidence argument then verifies the finite generated package without solving it.

This source theorem extends the previous value-projection theorem to incoming identity schemes and alias-cycle no-op routes. It does not prove that every current Yulang module satisfies the condition. In particular, constant/name-result lambdas, productive recursive lambdas, direct arbitrary annotations, effects, and other structured schemes remain outside this source fragment. No counterexample to regular completion is established.

Independent compiler-referee review identified the alias-scheme preservation
and one-cut obligations; both are proved above. A separate spec audit
confirmed the source clauses and component classification. No compiler code
or tests changed or ran.
