# Yulang cycle15: computed source-template closure

## State and scope

Started 2026-11-08T21:25:08Z; report prepared 2026-11-08T21:30:30Z. Completion time is recorded in heartbeat, within25 minutes. Current integration fetched: `9471107b6`. Standing orders/inbox reread: ACTIVE, I-7, cap24. Previous cycle14 completed and its report was read. No recovery or overlapping writer. Reused yulang-cycle6 and its cache; local branch dots-cycle15-local. Local commits e2848b0f4, edeb4c42e, 078ff53ef. Disk start/end19G free of63G; no deletion or new worktree.

## Result / boundaries

The int-only unary source adapter now computes a finite source-template closure, not a supplied work domain. Structural extraction retains slot identity. All declaration/where alternatives are enumerated and strictly decreasing sourceWeight children retained; every actual Generated edge passes this filter by the existing checked-Paterson theorem. Recursion terminates without supplied fuel/Acc/domain. Every actual capture-bearing child of any member at any ordinary state has a source witness in the same closure. Every future materialization of that witness belongs to a computed finite Request domain.

This advances I-7 item1 for a narrow fragment. `closure_exact` is exact only for paths through the structural enumeration, NOT actual candidate-selection reachability. The enumeration may include role/head-incompatible alternatives; source variant enumeration also overapproximates shared-slot consistency. No claim that all enumerated requests are reachable. Int-only/unary/capture-bearing limitations are implementation-fragment restrictions, not language design decisions. Checked Registry Paterson constraints are specification-derived. `production` is first-hit data, not unique selection. Arbitrary-state edges do not imply candidate stability. No same-parent saturation termination, general interval/source-graph adequacy, parser bridge, final classification or dictionary theorem. B4/T1c/X13–X16 remain NOT PROVED. No semantic choice or new question note.

## Theorems and quantifiers

All names below are in `Yulang.CommonRoleSourceTemplateClosure`; all quantify over arbitrary source-slot size n and checked registry. All are auxiliary to B4 soundness/completeness, not principality. No fixed concrete example is the result.

1. `next_decreases`: 任意のchild,parentについてchild∈next registry parentならsourceWeight child < sourceWeight parent。列挙側の停止尺度。
2. `generated_present`: 任意のchild,parentについて既存Generated registry child parentならchild∈next registry parent。Generatedは実productionとcapture位置、両端点のsource抽出、where requirementを保持する。実生成から有限列挙への健全性側の補助。
3. `closure_complete`: 任意のq,targetについてReach registry q targetならtarget∈closure registry q。Reachは構造列挙の辺の有限反射推移経路。言語の選択判断ではない。列挙完全性。
4. `closure_sound`: 同じ任意のq,targetについてtarget∈closure registry qならReach registry q target。列挙健全性。
5. `closure_exact`: 同じ任意のq,targetについて上の二方向のiff。独立な言語的Classifyとのiffではない。
6. `reach_trans`: 任意のq,middle,targetについてReach q middleかつReach middle targetならReach q target。補助。
7. `generated_closed`: 任意のroot,parent,childについてparent∈closure rootかつGenerated child parentならchild∈closure root。任意状態の連続した子生成の閉包。補助。
8. `actual_child_closed`: 任意のroot,parent,s,d,lp,hp,depth,childについて、parent∈closure root、production registry.declarations (parent.eval s)=some(d,lp,hp)、captureDepth d.head=some depth、child∈children (parent.eval s) d lp hpなら、childSource∈closure rootかつchildSource.eval s=childとなるsourceが存在する。実生成の包含で、閉包充足を仮定していない。補助。
9. `all_states_present`: 任意のroot,source,sについてsource∈closure rootならsource.eval s∈materializedDomain registry root。materializedDomainはclosureの全variantsを列挙する有限リスト。補助。
10. `actual_child_all_states`: 定理8と同じ全量化・全前提の下で、同じsource witnessが存在し、任意のfuture:State nに対してchildSource.eval future∈materializedDomain registry root。futureでも候補が選ばれるとは述べない。補助。

## Verification

`cd lean && lake build --wfail Yulang.CommonRoleSourceTemplateClosure`, exit0:
```text
✔ [283/283] Built Yulang.CommonRoleSourceTemplateClosure (1.2s)
Build completed successfully (283 jobs).

real	0m1.343s
user	0m1.016s
sys	0m0.379s
```
`cd lean && lake env lean --trust=0 /tmp/cycle15-axioms.lean`, exit0. Script imports the new module and prints all10 theorem axioms:
```text
'Yulang.CommonRoleSourceTemplateClosure.next_decreases' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceTemplateClosure.generated_present' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceTemplateClosure.closure_complete' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceTemplateClosure.closure_sound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceTemplateClosure.closure_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceTemplateClosure.reach_trans' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceTemplateClosure.generated_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceTemplateClosure.actual_child_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceTemplateClosure.all_states_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceTemplateClosure.actual_child_all_states' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
`git diff --check origin/integration/m1-final`, exit0. No sorry/new axioms/native_decide. Existing Lean files only append-only registration changes. No spec/plan/lakefile edits.

Full `lake build`, full Audit and `bash tools/verify-lean.sh . origin/integration/m1-final` were NOT RUN under latest standing orders. No full PASS claim or fabricated output. Supervisor must run full verification.

## Publication / interruptions / comparison

Six implementation/design/registration files were individually published through GitHub app to work/dots-main, each fetched back and byte-equal. Published Lean tree compared with local verified Lean tree: no differences. Integration ancestor check exit0. This report is seventh artifact; heartbeat separate. No other branch written.

Initial focused build failed due inductive constructor binder order and a multiline tactic indentation error; both fixed, then focused build and axioms passed. No timeout, reset, approval wait or environment interruption. A plain git fetch updated FETCH_HEAD but not the remote-tracking ref; corrected using explicit refs/heads/work/dots-main:refs/remotes/origin/work/dots-main before tree comparison. Usage quota accounting unknown.

Yulang2 comparison: read integrated notes/audit/x-oracle.md X13–X16; these do not establish arbitrary interval/source-template closure. Read spec06 role structural decrease, stable sibling deferral and K2 clauses; no new runtime run. No claim of runtime-conformance proof.

## Remaining bridges / next tasks

Five major B4 bridge groups remain: source_boundary_adequate; generated_work_closed (general source/interval adapter); saturate_terminates_and_closes; saturated_frontier_exact; resolve_dictionary_order_sound. This cycle closes computed-domain child containment only for the specified adapter, not general group2. Exact micro-lemma count unknown.

Next named work: (1) general_interval_template_materialization to remove int-only adapter restriction; (2) finite_new_fact_saturation excluding no-information same-parent revisits, using a computed domain; (3) saturated_diagnostic_frontier_exact retaining child result trees. Do not count child accessibility as saturation.
