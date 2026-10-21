# R245 — Receipt-loss admission consequence

Status: active source/proof audit. Parent, R71/R72, review and production remain OPEN.

R244 found that receipt loss can omit the exact R187 slot-4 edge from a local Capture. That alone does not show that the original theorem's mapped inequality fails. This audit follows the missing edge through every authentic Local map and the same-use Apply, including admitted constraints, contexts, views, replay parents and unchanged shared endpoints. It must establish a complete receipt-independent implication path or a complete finite non-implication certificate. No fault injection, tests, builds, samples or code changes are authorized.

## Initial route map

For one local forwarding edge, the parent requires `e_A <= mu(t_u) <= mu(n_u) <= mu(r_u) <= e_C <= e_out`. R187's relay source includes the inner Apply joins `n_u <= t_b^v` and `r_b <= c_u`, application effect `c_u <= q_u`, and Lambda result `q_u <= r_u`; the outer Apply separately joins its own actual argument, mapped callee ports and demand result effect. The candidate Capture omission concerns the q-to-r Lambda edge under receipt loss. Remaining question: whether exact Apply constraints, a shared port, later admissions or replay supply the missing mapped relation without relying on that retained Capture edge.

The R187 note's displayed finite interpretation is expressly incomplete: it says it satisfies the enumerated candidate graph, not every emitted fiber. Do not reuse it as a countermodel until every actual constraint/view/context and the map identity is accounted for. R217's receipt-retaining Capture assertion is implementation evidence only; it supplies no receipt-independent implication.

## Current status

No complete implication or non-implication certificate yet. Parent closure is not inferred from R244. Next, enumerate the source facts and their exact solver consumers for bridge's body Apply, relay's Lambda slot 4, relay's Local capture/restoration, and the outer actual Apply; then test whether the missing row relation is derivable in that complete finite slice. Keep R71/R72 and source/native approval separate. No code, tests, builds or samples changed or ran.

## R245 route audit

The parent §6 premise is per compared use: one authentic `mu_i` must actually admit the source body's mapped edges through that provider's mapped return effect. For the R187 relay use, the required step is the mapped path from `n_u` through the body Apply and its called bridge to `r_u`, before the outer Apply can yield `e_A <= mu_i(t_u) <= mu_i(n_u) <= mu_i(r_u) <= e_C <= e_out`.

The source Apply relations do exist in the original live inference session: its callee/argument comparison supplies `n_u <= t_b^v` and `r_b <= c_u`; its Application effect supplies `c_u <= q_u`; Lambda slot 4 supplies `q_u <= r_u`. `r_b` and `n_x` are older shared anchors in the R187 construction. At the relay scheme's positive Function Capture, the structural shape reaches `t_u` and `r_u`; it reaches `n_u`, `t_b^v` and shared `n_x` by the listed captured edges. The physical owners in R187 place `r_b <= c_u` on local `c_u`, `c_u <= q_u` on local `c_u`'s upper lane, and equal-age `q_u <= r_u` on `q_u`'s upper lane. The first two owners are not reached from the Function shape. The third owner is found by R217's restricted reverse-owner index only when its completed Lambda receipt is retained. If that receipt is absent, R244 shows this edge is also omitted.

A further frontier limitation remains even with a retained receipt: R217's index is built only for owners whose upper endpoint is already in `shape_effect_rows`, and its discovered owners do not recursively widen that frontier. Thus discovering q from the shape row r does not make q a shape row; the index does not then discover c from c <= q. `Capture::bound` and `expand_row(q)` recover only q's owned adjacency, which for equal-age q <= r is q's upper row r; they do not enumerate incoming owners of q. The older shared r_b is unchanged, but the edge r_b <= c is owned by the unvisited local c, so the shared endpoint alone does not bridge to q or r.

The actual Local route has one captured `Graph`; `prepare_candidate_fresh_use` creates a consistent map for its captured rows, and `step_candidate_local_use` restores each and only each `Graph::bounds` entry through that map before linking the fresh root to the local value. It does not copy the live session's unvisited c/q/r adjacency into the use. The later outer Apply compares the actual argument effect to the mapped Function AE, the mapped Function RE to its demand RE, and that demand RE to the Apply output. Those joins provide the ends of the chain but no mapped `n_u <= r_u` middle edge. No equality between a missing row and its copy, and no existence of a `LocalFreshRoute` by itself, supplies it.

This gives a conditional non-implication certificate for the inspected captured-use graph. Assign the reached mapped prefix `mu(t_u)=mu(n_u)=mu(t_b^v)=n_x={signal}`, retain shared `r_b={signal}`, and assign the use's mapped `r_u`, actual demand RE and this Apply output to empty. Assign original un-mapped `c_u,q_u,r_u` consistently to `{signal}` so their live original source edges hold. The captured prefix bounds and outer Apply joins hold, while `mu(n_u) <= mu(r_u)` fails. This is the R187 candidate shape already proposed in its note, now checked against the exact use-map/restoration owner: omitted graph bounds have no restoration step. It is not a complete source-qualified solver model; no executed source artifact, complete emitted-fiber ledger or runtime allocation fault was produced here. Do not claim a language-level counterexample or refutation of §1.

## Outcome

R244 is stronger than a generic graph-completeness concern for the inspected constructor route: the missing Capture bounds are exactly the middle admissions needed by the conditional §6 instance implication. No receipt-independent route from the captured relay Function ports to its mapped RE was found. The candidate use graph therefore does not discharge the parent's mapped-admission premise. The remaining gap is complete source/native qualification of the R187 generated slice and all alternative admitted contexts, not an algebraic step in §6. The parent's language theorem remains OPEN; R71/R72, dynamic source/runtime bridge, review and production remain OPEN. R245 is conditional and unreviewed.

No compiler files, tests, builds, samples or fault injection changed or ran. No repair authority or code lease was requested or assumed.
