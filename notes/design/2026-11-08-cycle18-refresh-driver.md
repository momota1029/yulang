# Cycle18: state-changing producer-cache refresh

I-7 bridge 2. Build an executable cache of actual producer child rows on the computed source domain. On each supplied ordinary-state update, reuse a row iff its dependency dirty list is empty; otherwise recompute that parent's actual children. Recompute reachability from the refreshed rows, not by unioning old visited nodes (old edges may disappear).

Independent judgment: existing `CommonRoleSourceWorklist.Reach registry root state q` uses actual production, not cache content. For every registry, root, arbitrary finite state trace and node, the refreshed driver's final visited set must be equivalent to this judgment at the final state. No monotonicity/consistency premise is needed for refresh exactness. Those premises remain necessary for cycle17's finite invalidation bound.

Data: cache is a function from computed finite Node to child list; initial rows actualNext; refresh uses dirty; replay folds over a finite list of supplied states. Claims: valid cache preserved by refresh; each cached rule set equals actual rule set; replay final cache valid; final worklist iff independent Reach, root included and actual children closed. Existing finite Horn termination applies per refresh. This is NOT autonomous ordinary-fact saturation: the state trace is supplied, not generated, and its length is not bounded here. General interval / dictionary classification remain open; no semantic decisions added.

Yulang2: x-oracle X13–X16 consulted. Its external examples do not expose cache invalidation and do not certify this operational property. Spec6.3's delayed child finalization motivates refreshing rather than preserving stale edges. This is an internal int-only unary-template fragment.
