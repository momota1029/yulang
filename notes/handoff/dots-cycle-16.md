# Yulang cycle16: actual source worklist at a fixed state

Started 2026-11-08T21:54:16Z; report prepared 22:01:20Z (about 7 minutes; final time in heartbeat). Fresh integration `0605a0b66`; ACTIVE I-7, limit24. Previous cycle15 completed with report, verified via API. No overlapping writer. Reused yulang-cycle6 and cache; local branch dots-cycle16-local. Disk start/end 19G free /63G. No cache deletion. Local commits 085b750cb and 5cdc519c5.

## Result and exact boundary

Computed duplicate-free worklist over cycle15's finite source closure, now with **actual first-hit producer edges at arbitrary fixed ordinary state**, rather than every structural declaration alternative. It retains source identity and includes every concrete child of visited capture-bearing production. `saturate_exact` equates output membership to independent actual-source reachability. Capacity is computed from declarations/root, not supplied fuel or closed-domain evidence. Each inserted node is fresh; leastness excludes unrelated structural alternatives from the result.

This is a useful fixed-state kernel of bridge3, NOT state-changing saturation. No ordinary evidence is added by this scheduler. It does not justify suppressing revisits when state changes. Int-only/unary/capture-bearing restriction is an implementation-fragment restriction, NOT a specification decision. Checked Paterson bounds are specification-derived. Actual producer is first-hit data, not unique candidate selection. Arbitrary state is quantified but held fixed across each run. General B4/T1c/X13–X16 remain NOT PROVED. No new semantics or question decision made.

## Quantified theorem inventory

Namespace `Yulang.CommonRoleSourceWorklist`. Throughout, n is any source-slot count, registry any checked Registry, root any SourceRequest n, s any State n. Node is the subtype of membership in the computed source closure. All results are auxiliary to B4, not full typing/principality claims.

- `actual_next_generated`: 任意parent/childについて child∈actualNext registry s parent なら Generated registry child parent。実生成の包含、健全性補助。
- `nodes_complete`: 任意Node qについて q∈nodes registry root。有限宇宙補助。
- `edge_rule_present`: 任意Node parent/childについて child.val∈actualNext registry s parent.val なら edgeRule parent child∈rules registry root s。完全性補助。
- `derives_sound`: 任意Node qについて FiniteHorn.Derives (rules registry root s) q なら独立Reach registry root s q。健全性補助。
- `derives_complete`: 任意Node qについて Reach registry root s q なら同じHorn Derives。完全性補助。
- `saturate_exact`: 任意Node qについて q∈saturate registry root s iff Reach registry root s q。固定状態の到達性について健全性・完全性。
- `saturate_nodup`: 任意registry/root/sで結果リストは重複なし。停止補助。
- `saturate_capacity`: 任意registry/root/sで結果の長さ≤計算されたsource closureの長さ。停止補助。外部fuelなし。
- `saturate_actual_closed`: 任意Node parentが結果に属し、任意source childがactualNextの子なら、結果中にval=childのNodeが存在。閉包補助。
- `concrete_child_visited`: 任意Node parentが結果に属し、任意d/lp/hp/depth/childについてproduction registry.declarations (parent.val.eval s)=some(d,lp,hp)、captureDepth d.head=some depth、child∈children (parent.val.eval s) d lp hpなら、結果中にq.val.eval s=childのNode qが存在。具体的実childの包含補助。
- `root_visited`: 任意registry/root/sでrootNodeは結果に属する。完全性補助。
- `saturate_least`: 任意Node上の述語holdsについて、rootNodeで成り立ち、任意parent/childでholds parentかつactualNext辺ならholds childを満たすとき、任意結果中Node qでholds q。最小閉包の補助。これを一般言語意味論の仮定として完成を装ってはいない。

## Verification

`cd lean && lake build --wfail Yulang.CommonRoleSourceWorklist`, exit0:
```text
✔ [284/284] Built Yulang.CommonRoleSourceWorklist (1.2s)
Build completed successfully (284 jobs).

real	0m1.348s
user	0m1.093s
sys	0m0.421s
```
`cd lean && lake env lean --trust=0 /tmp/cycle16-axioms.lean`, exit0:
```text
'Yulang.CommonRoleSourceWorklist.actual_next_generated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceWorklist.nodes_complete' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceWorklist.edge_rule_present' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceWorklist.derives_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceWorklist.derives_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceWorklist.saturate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceWorklist.saturate_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceWorklist.saturate_capacity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceWorklist.saturate_actual_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceWorklist.concrete_child_visited' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceWorklist.root_visited' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceWorklist.saturate_least' depends on axioms: [propext, Classical.choice, Quot.sound]
```
`git diff --check`, exit0. No sorry/new axioms/native_decide. Existing Lean edits are append-only imports, Audit registrations, README. New module builds; full Audit/Yulang target not run. Full `lake build` and `bash tools/verify-lean.sh . origin/integration/m1-final` NOT RUN under standing orders; supervisor must run full verification, no full PASS claim.

## Publication and limits

5 implementation/design/registration files published individually to work/dots-main and byte-equal API readback. Integration merge `fc7d3a6b3` is on remote. `git merge-base --is-ancestor origin/integration/m1-final origin/work/dots-main` exit0; `git diff --exit-code HEAD origin/work/dots-main -- lean` exit0. This report is artifact6; heartbeat separate. No other branch written. Existing supervisor spec/idea changes imported unchanged during merge, no author edits to spec/plan/lakefile.

Initial build failed on subtype DecidableEq visibility and shadowed binder, then passed; leastness extension failed because induction retained the membership premise, fixed by clearing that premise. One local checkpoint was made before discovering that second failure; subsequent validated commit fixes it. No timeout/reset. Initial merge ref update was rejected by auto-review for possible loss of published artifacts. It had not moved the ref. Safer merge built FROM CURRENT work/dots-main, importing only the two supervisor-updated blobs, preserving all artifacts; nonforce expected-head update succeeded. No approval bypass. Usage accounting unknown.

Yulang2: read integrated x-oracle X13–X16 and existing ordinary-knownness/finite source work. Those examples do not certify this fixed-state scheduler; no new Yulang2 run or runtime equivalence claim.

## Remaining B4 bridges

Still five major groups: source_boundary_adequate; generated_work_closed for general intervals/source graphs; saturate_terminates_and_closes for state-changing evidence; saturated_frontier_exact; resolve_dictionary_order_sound. This cycle supplies a fixed-state subcomponent of group3, not its completion. Exact micro-lemma count unknown.

Next named work: `state_change_invalidates_parent_cache` plus a finite universe of newly added ordinary facts; `dynamic_saturation_semantic_closure` (update state, revisit siblings/parents, prove stable closure); `general_interval_template_materialization`. A fixed-state least closure must not be reported as the state-changing saturation theorem.
