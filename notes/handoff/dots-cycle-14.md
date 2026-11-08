# Yulang cycle14: source-preserving child templates

## State / scope

- Started 2026-11-08T20:55:28Z; report prepared 2026-11-08T21:03:00Z. Under25 minutes; publication completion time is in heartbeat.
- Latest integration fetched with explicit remote tracking refs: `2c42e6c45` (cycle13 integrated). Standing orders and inbox reread, ACTIVE/I-7, cap24. Previous heartbeat cycle13 completed with report; no recovery, no overlapping Lean worker.
- Reused `/workspace/scratch/1d0b4aaa3394/yulang-cycle6`; no copied cache or new worktree. Integration merged locally before edits. Six implementation/registration files published and exact readback confirmed. This report is seventh; heartbeat separate.
- New module `lean/Yulang/CommonRoleChildTemplates.lean`; new design `notes/design/2026-11-08-cycle14-child-templates.md`; append-only Yulang.lean, Audit.lean, README.md, notes/design/INDEX.md. No existing theorem modified. Small local commits ad7a79ebe, a1affaa04, 106117f31, 4c284c425.

## Result and boundaries

Actual unary capture is lifted back into Endpoint source templates without conflating equal Ty values or erasing source slots. Child requirements substitute those templates rather than the current materialized values. Extraction and substitution commute with materialization at every state. The int-only adapter has state-independent Paterson weight. For a checked registry, actual capture-bearing child-generation edges strictly decrease that weight even when a different state is used at every edge, hence are accessible without an externally supplied Acc/fuel/closure premise.

**This does not prove saturation termination.** A same-parent revisit is not a Generated edge. `production` means first-hit candidate data, not unique selection. The adapter is still int-only, fixed and unary; this does not establish general interval adequacy, global source graph allocation, or arbitrary generated-template finite-domain enumeration. Noncapture literal heads are outside the new lifting theorem. Open endpoints lower≠upper are allowed, but this is not general open interval inference.

I-7 item1 partially advanced and child-creation subcase of item2 advanced. General B4, T1c and X13–X16 remain NOT PROVED. No language semantic choice made and no question note added.

## Theorems (all auxiliary to B4 soundness/completeness, not principality)

All names are in `Yulang.CommonRoleChildTemplates`. The implicit source-slot size n is universally quantified, not fixed to an example.

1. `extract_eval`: 全n、自然数k、Endpoint nのe、State nのsで、構造抽出extract k eをsで評価したOptionは、eval s eの深さkの部分木と等しい。前提なし。補助。
2. `extract_exists`: 全n,k,e,s,payloadについて、atDepth k (eval s e)=some payloadなら、source Endpointが存在し、extract k e=some sourceかつeval s source=payload。補助。
3. `plug_eval`: 全n、Template t、Endpoint e、State sで、source代入plug t eの評価は、評価したeをtへinstantiateした結果と等しい。前提なし。補助。
4. `child_eval`: 全n、requirement r、Endpoint lo/hi、State sで、childTemplateの評価はrのroleと、lo/hiの各評価をrのtemplateへinstantiateした両端点からなるRequestに等しい。前提なし。補助。
5. `production_lifts`: 全n、visible宣言列、source、s、d、lp/hp、depthについて、実production visible (source.eval s)=some(d,lp,hp)かつcaptureDepth d.head=some depthなら、sourceのlower/upperから抽出されたlo/hiが存在し、sでlp/hpへ評価され、任意のfuture状態でも元の両端点の同じ深さに位置し、全requirementsのchildTemplateをsで評価した列が実childrenと一致する。補助。
6. `every_child_lifts`: 上と同じ量化とproduction/capture前提に加え、任意のchildが実childrenの要素なら、lo/hiとd.requirementsのrが存在し、sourceの両端点から抽出され、childTemplate r lo hiをsで評価するとchildとなり、任意のfutureでも両端点capture位置が保存される。補助。
7. `replay_children`: 全n,source,d,lo,hi,depthについてextractがlo/hiを返しhead capture位置がdepthであり、任意のfuture,visible,lp,hpで同じdがproductionに再度現れるなら、保存済みlo/hiから全requirementsをfutureで再評価した列が実childrenと一致。**後続productionが実際に同じdを返すという条件付き**。候補安定性の証明ではない。補助。
8. `eval_form`: 全n,e,sで、eval s eのFormがshape eのFormと一致。前提なし。int-only adapterの性質。補助。
9. `eval_weight`: 全n,source,sで、評価したRequestの実OpenDescent weightが静的sourceWeightと一致。前提なし。補助。
10. `generated_decreases`: 全n、checked Registry、child,parentについてGenerated registry child parentならsourceWeight child < sourceWeight parent。Generatedの各辺は任意のStateでの実production、head capture位置、source extract、実where requirementを保持。registryのcheckedは既存Paterson検査。補助。
11. `generated_accessible`: 全n、checked Registry、任意のparent SourceRequest nでAcc (Generated registry) parent。外部Acc/fuel/closure前提なし。各辺の状態は独立に選べる。**同親再訪は対象外**。補助。
12. `every_child_generated`: 全n,registry,source,s,d,lp,hp,depth,childについてproductionが(d,lp,hp)を返しcapture位置がdepthでchildが実childrenに入れば、sでchildに評価されるchildSourceが存在し、Generated registry childSource sourceかつAcc (Generated registry) childSource。補助。

拒否範囲の区別: checked RegistryのPaterson制約は確定仕様。int-only、unary、capture-bearingという制限は実装断片の制限で、一般仕様を狭めた決定ではない。docstringにも制限を記載。

## Verification

`cd lean && lake build Yulang.CommonRoleChildTemplates --wfail`, exit0:
```text
✔ [282/282] Built Yulang.CommonRoleChildTemplates (1.1s)
Build completed successfully (282 jobs).

real	0m1.254s
user	0m1.093s
sys	0m0.402s
```

`cd lean && lake env lean --trust=0 /tmp/cycle14-audit.lean`, exit0; all12 declarations registered in Audit:
```text
'Yulang.CommonRoleChildTemplates.extract_eval' depends on axioms: [propext]
'Yulang.CommonRoleChildTemplates.extract_exists' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleChildTemplates.plug_eval' depends on axioms: [propext]
'Yulang.CommonRoleChildTemplates.child_eval' depends on axioms: [propext]
'Yulang.CommonRoleChildTemplates.production_lifts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleChildTemplates.every_child_lifts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleChildTemplates.replay_children' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleChildTemplates.eval_form' depends on axioms: [propext]
'Yulang.CommonRoleChildTemplates.eval_weight' depends on axioms: [propext]
'Yulang.CommonRoleChildTemplates.generated_decreases' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleChildTemplates.generated_accessible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleChildTemplates.every_child_generated' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only propext/Classical.choice/Quot.sound. No sorry/new axiom/native_decide. `git diff --check` passed. Full `lake build`, full Audit and `bash tools/verify-lean.sh . origin/integration/m1-final` **not run**, per latest standing orders/I-5. Thus there is no verify-lean output or exit code and no full PASS claim. Supervisor verification remains pending.

## Publication / limits / next

- GitHub app publication one file at a time, all6 readbacks exactly equal. Full published lean/ tree compared with locally verified tree; ancestry of integration checked. Report and completed heartbeat published separately. Only work/dots-main written.
- Initial compile failed at Option-map simplification; explicit Option case split fixed it. Later descent proof simplification needed childTemplate/plug_eval unfolding; fixed. `/usr/bin/time` was absent (exit127), so Bash time was used. No timeout, environment reset, or approval wait. One initial heartbeat contained a malformed deadline phrase; completed heartbeat replaces it. No fabricated progress or hidden interrupted execution.
- Disk start/end19G/19G free, 63G volume70% used. No caches deleted this cycle. Unpublished historical local records preserved. Usage quota accounting unknown.
- Yulang2: read work/dots-audit x-oracle (X13–X16 and Paterson X2 context); no fresh runtime test. No claim that template materialization/provenance is runtime-conformance validated. Current spec, not old Y2 behavior, remains authoritative.
- B4 still has5 major bridge groups: source_boundary_adequate; generated_work_closed; saturate_terminates_and_closes; saturated_frontier_exact; resolve_dictionary_order_sound. This cycle advances group2 and structural child-creation part of group3, but closes neither group in general. Exact remaining micro-lemma count unknown.
- Next named tasks: (1) computed finite source-template closure using Generated descent, plus all-state rematerialization membership; (2) general interval/source-identity adapter beyond int-only; (3) finite-new-facts saturation with same-parent revisit exclusion. Retain distinction between child-generation descent and driver saturation.
