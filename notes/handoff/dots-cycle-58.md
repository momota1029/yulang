# Cycle58: source allocation preserves complete graph inspection

## Result and scope

有限の source table に occurrence を追加したとき、既存ノードの構造辺・nominal 引数辺を再構成し、既存 root の経路、直接循環、有限深さの観察、bisimulation を保存する部分目標を閉じた。追加領域を unresolved で初期化する `allocate` については、実際の K2 `regularAt`、head inspection、順序と重複を保った完全な snapshot まで保存する。

対象は任意の有限 `table` と `extra`、任意の旧 `graph`、旧 root/target、観察深さ、pattern、role、visible-head list。非循環性、source 名の一意性、外部から渡す graph 正当性を前提にしない。一般の `grow` は新領域の任意の node を許すが、K2 と inspector の保存には新領域が unresolved である `allocate` を使う。旧ノードの内容を後から更新する操作は対象外。

新 alias は同じ source 名の旧 canonical root を使い、新しい source 名は計算された新 canonical root で unknown になる。この区別を保ち、raw alias storage 自体の同一性を要求しない。

## Main theorem groups and their role

以下はすべて M1 の健全性・完全性・主型性そのものではなく、B4 の source-identity/generated-work 境界に効く補助結果。iff はこの有限 graph 断片内の双方向性を示す。言語全体の分類、拒否範囲、停止性を完成したとは主張しない。

- `grow_retained`, `successors_retained`: 任意の table/extra/graph、新領域の node 関数、旧 slot に対して、旧 node と successor 列は retain に沿って再構成される。
- `path_forward`, `path_origin`, `path_exact`: 同じ一般条件で、旧 slot からの経路は旧領域にとどまり、旧経路と正確に対応する。`path_origin` は拡大後の任意 target への経路から、その target が retain された旧 slot であることも回復する。
- `structural_cycle_exact`, `recursiveAt_retained`, `observe_retained`, `canonical_observe_retained`, `canonical_cycle_retained`: 任意の旧 root と有限深さについて、直接構造循環・実行可能な循環検査・有限観察を保存する。canonical 版は source identity の再計算も含む。
- `bisimilar_retained`: 任意の旧二点について bisimulation の iff を得る。新領域の内容は任意でよい。`regularAt_allocated` は unresolved の新領域について、任意の旧 root の K2 判定を保存する。
- `inspect_allocated`, `inspectChildren_allocated`, `inspectAll_allocated`, `inspectAllChildren_allocated`, `canonical_inspect_allocated`, `inspectAllVisible_allocated`, `snapshot_allocated`, `canonical_snapshot_allocated`: unresolved allocation と、任意の pattern/対応する子列/role/visible-head list/旧 root について、既存 inspector の結果が retainObservation または retainSnapshot に一致する。capture、mismatch 後の兄弟、head の順序・重複を含む。
- `allocate_new_unresolved`: 任意の追加 slot の raw storage は unresolved。`new_alias_inspection` は新旧 source 名の等式を前提に旧 canonical 観察を再利用する。`fresh_snapshot_unknown` は旧 table にその source 名の representative が存在しないことを前提に、新 canonical root の snapshot が unknown になる。
- `unrolling_allocation_regression`: shared unknown を含む既存の有限 unrolling 例に alias と新 source 名を追加しても cycle encounter が残る。固定例だけの成果ではなく、一般の inspector 保存定理の回帰例。

## Validation

復旧時にローカル実装 commit `b8c6ae6a38102181ef32e8c06ee571e66b9bf2da` の変更を確認し、以下を再実行した。実装に変更は加えていない。

1. Focused build, exit 0:
   `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake build --wfail Yulang.CommonRoleAllocatedGraph`

```text
Build completed successfully (300 jobs).
```

2. Focused axiom audit, exit 0:
   `cd lean && ELAN_HOME=../../elan timeout 120 ../../elan/bin/lake env lean --trust=0 /tmp/cycle58-audit.lean`

この入力は当該モジュールを import し、今回追加した主要24宣言の公理を列挙する。24宣言すべての依存公理は propext / Classical.choice / Quot.sound の範囲内。

```text
'Yulang.CommonRoleAllocatedGraph.grow_retained' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.successors_retained' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.path_forward' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.path_origin' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.path_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.structural_cycle_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.recursiveAt_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.observe_retained' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.canonical_observe_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.canonical_cycle_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.bisimilar_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.regularAt_allocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.inspect_allocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.inspectChildren_allocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.inspectAll_allocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.inspectAllChildren_allocated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleAllocatedGraph.canonical_inspect_allocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.inspectAllVisible_allocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.snapshot_allocated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.canonical_snapshot_allocated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleAllocatedGraph.unrolling_allocation_regression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleAllocatedGraph.allocate_new_unresolved' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.new_alias_inspection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleAllocatedGraph.fresh_snapshot_unknown' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Diff gate, exit 0:
   `bash tools/verify-lean.sh . origin/integration/m1-final --no-build`

base は API でも確認した `f17c31a83199110544e8ae0a92032bd65ce9523f`。

```text
verify-lean: . @ b8c6ae6a3 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check` も exit 0。報告作成前の working tree は clean。

全体の `lake build --wfail`、全 `Audit.lean`、広域 AxiomGate は実行していない。常設指示に従い監督役の検証に残す。focused build と24宣言の監査を全体検証 PASS と読み替えない。公開 commit の GitHub CI の終了結果はこの報告時点では未確認。

## Publication and preserved remote tree

開始心拍の remote commit は `822c4cc50a80eb0f1ec22af12070b4905212fd4d`、その API 確認済み tree は `6f44e47969e137a07f201506952ee81b5f2fcbcb`。既存成果6ファイルの親 blob と最新 remote blob が一致することを確認した。未確定の ref 更新は見つからなかった。

成果6ファイルを個別 blob として公開し、返された SHA がローカル blob と一致することを確認した。最新 remote tree を base として成果だけを追加した commit は `f4b9374461a42ea122914ac402a76a6b67068e51`、tree は `06b35a72b45a0a908624e84077a5a1bb3642ae54`。非 force・expected-head 付き更新で `work/dots-main` に公開済み。

公開後に再帰 tree を取得し、成果6ファイルの blob が一致し、変更対象以外の既存 blob がすべて保持されていることを確認した。古い tracking tree を base にしなかった。integration/m1-final や他ブランチには書き込んでいない。

公開した成果:
- lean/Yulang/CommonRoleAllocatedGraph.lean
- lean/Yulang.lean
- lean/Audit.lean
- lean/README.md
- notes/design/2026-11-09-cycle58-allocated-graph.md
- notes/design/INDEX.md

この報告と完了心拍の2ファイルを追加し、サイクル全体では8パス。

## Interruption and timing

開始は 2026-11-09T23:27:19Z。25分枠の期限は 23:52:19Z。ローカル実装 commit は 23:36:43Z にできていたが、remote は 23:30:45Z の running 心拍のまま、成果・終了報告は未公開だった。23:55 UTC の確認時、ローカル最終心拍は 23:36:42Z、関連ビルドや公開の実行中プロセスは見つからなかった。停止原因は特定できていない。

開始から25分以内に公開・報告を終えられなかった。10分/20分の定期心拍も remote に反映されておらず、運用要件を満たさなかった。この遅延を作業時間として成果の大きさに換算しない。復旧では新しい証明作業を増やさず、残っていた実装の再検証と安全な公開に限定した。

報告準備時刻: 2026-11-10T00:01:13Z。開始から 33.9 分（25分枠を 8.9 分超過）。公開完了時刻は最終 commit の時刻で確認できる。

## Yulang2 comparison and remaining bridges

実装の設計ノートが参照する証拠は work/dots-audit の x-oracle X13-X17 と C3-PARENT。source/associated constraint の共有を支えるが、内部の numeric graph allocation の実機証明ではない。今回の復旧では新しい Yulang2 実行はしておらず、新しい言語意味論も決定していない。

一般 B4 の未完了の橋は引き続き5本: `source_boundary_adequate`, `generated_work_closed`, `saturate_terminates_and_closes`, `saturated_frontier_exact`, `resolve_dictionary_order_sound`。今回閉じたのは allocation/inspection の部分目標で、橋全体は閉じていない。T1c の一般 resolve_exact や X13-X16 の外側入口の完成も主張しない。

次の候補:
1. 宣言が生成する child source 名と `newRoot`、retained capture を接続する。
2. allocation 後の旧 node 更新・生成制約が graph inspection と source model に与える変化を独立に扱う。旧 node 更新で regularity が変わる既存反例を尊重する。
3. 生成仕事の閉包を `generated_work_closed` と飽和の停止/意味的閉包へ接続する。

新しい意味論判断や質問ノートは追加していない。既存の作業場・キャッシュを再利用し、追加 worktree や cache copy は作らなかった。元サイクル開始時の容量は未記録。復旧確認時の空きは48GB。使用量の残枠は不明。

## Exact audited theorem signatures

名前の要約で前提を省略しないため、今回監査した24宣言の型をそのまま記録する。名前空間は `Yulang.CommonRoleAllocatedGraph`。

```lean
theorem grow_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (i : Slot table) :
    grow table extra graph fresh (retain table extra i) =
      mapNode (retain table extra) (graph i)
```

```lean
theorem successors_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (i : Slot table) :
    successors (grow table extra graph fresh) (retain table extra i) =
      (successors graph i).map (retain table extra)
```

```lean
theorem path_forward (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length)
    {a b : Slot table} (path : FiniteWorklist.Path (successors graph) a b) :
    FiniteWorklist.Path (successors (grow table extra graph fresh))
      (retain table extra a) (retain table extra b)
```

```lean
theorem path_origin (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length)
    (a : Slot table) (target : Slot (table ++ extra))
    (path : FiniteWorklist.Path (successors (grow table extra graph fresh))
      (retain table extra a) target) :
    ∃ b : Slot table, target = retain table extra b ∧
      FiniteWorklist.Path (successors graph) a b
```

```lean
theorem path_exact (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (a b : Slot table) :
    FiniteWorklist.Path (successors (grow table extra graph fresh))
      (retain table extra a) (retain table extra b) ↔
        FiniteWorklist.Path (successors graph) a b
```

```lean
theorem structural_cycle_exact (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (root : Slot table) :
    StructuralCycleAt (grow table extra graph fresh) (retain table extra root) ↔
      StructuralCycleAt graph root
```

```lean
theorem recursiveAt_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (root : Slot table) :
    recursiveAt (grow table extra graph fresh) (retain table extra root) =
      recursiveAt graph root
```

```lean
theorem observe_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length)
    (depth : Nat) (root : Slot table) :
    observe (grow table extra graph fresh) depth (retain table extra root) =
      observe graph depth root
```

```lean
theorem canonical_observe_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length)
    (depth : Nat) (root : Slot table) :
    observe (grow table extra graph fresh) depth
      (canonical (table ++ extra) (retain table extra root)) =
        observe graph depth (canonical table root)
```

```lean
theorem canonical_cycle_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (root : Slot table) :
    recursiveAt (grow table extra graph fresh)
      (canonical (table ++ extra) (retain table extra root)) =
        recursiveAt graph (canonical table root)
```

```lean
theorem bisimilar_retained (table extra : Table) (graph : Graph table.length)
    (fresh : Slot (table ++ extra) → Node (table ++ extra).length) (a b : Slot table) :
    Bisimilar (grow table extra graph fresh) (retain table extra a) (retain table extra b) ↔
      Bisimilar graph a b
```

```lean
theorem regularAt_allocated (table extra : Table) (graph : Graph table.length)
    (root : Slot table) :
    regularAt (allocate table extra graph) (retain table extra root) =
      regularAt graph root
```

```lean
theorem inspect_allocated (table extra : Table) (graph : Graph table.length)
      (pattern : Pattern) (root : Slot table) :
      inspect (allocate table extra graph) pattern (retain table extra root) =
        retainObservation table extra (inspect graph pattern root)
```

```lean
theorem inspectChildren_allocated (table extra : Table) (graph : Graph table.length)
      (patterns : List Pattern) (roots : List (Slot table)) :
      inspectChildren (allocate table extra graph) patterns (roots.map (retain table extra)) =
        retainObservation table extra (inspectChildren graph patterns roots)
```

```lean
theorem inspectAll_allocated (table extra : Table) (graph : Graph table.length)
      (pattern : Pattern) (root : Slot table) :
      inspectAll (allocate table extra graph) pattern (retain table extra root) =
        (inspectAll graph pattern root).map (retainObservation table extra)
```

```lean
theorem inspectAllChildren_allocated (table extra : Table) (graph : Graph table.length)
      (patterns : List Pattern) (roots : List (Slot table)) :
      inspectAllChildren (allocate table extra graph) patterns (roots.map (retain table extra)) =
        (inspectAllChildren graph patterns roots).map (retainObservation table extra)
```

```lean
theorem canonical_inspect_allocated (table extra : Table) (graph : Graph table.length)
    (pattern : Pattern) (root : Slot table) :
    inspect (allocate table extra graph) pattern
      (canonical (table ++ extra) (retain table extra root)) =
        retainObservation table extra (inspect graph pattern (canonical table root))
```

```lean
theorem inspectAllVisible_allocated (table extra : Table) (graph : Graph table.length)
    (role : Nat) (root : Slot table) (visible : List VisibleHead) :
    inspectAllVisible (allocate table extra graph) role (retain table extra root) visible =
      (inspectAllVisible graph role root visible).map
        (fun p => (p.1,p.2.map (retainObservation table extra)))
```

```lean
theorem snapshot_allocated (table extra : Table) (graph : Graph table.length)
    (role : Nat) (root : Slot table) (visible : List VisibleHead) :
    inspectSnapshot (allocate table extra graph) role (retain table extra root) visible =
      retainSnapshot table extra (inspectSnapshot graph role root visible)
```

```lean
theorem canonical_snapshot_allocated (table extra : Table) (graph : Graph table.length)
    (role : Nat) (root : Slot table) (visible : List VisibleHead) :
    inspectSnapshot (allocate table extra graph) role
      (canonical (table ++ extra) (retain table extra root)) visible =
        retainSnapshot table extra (inspectSnapshot graph role (canonical table root) visible)
```

```lean
theorem unrolling_allocation_regression :
    inspect (allocate [7,7,9] [9,7,11] unrolledWithSharedUnknown)
      (.structural 0 [.variable 3,.variable 4]) (retain [7,7,9] [9,7,11] 0) =
        .cycle (retain [7,7,9] [9,7,11] 0)
```

```lean
theorem allocate_new_unresolved (table extra : Table) (graph : Graph table.length)
    (i : Slot extra) :
    allocate table extra graph (CommonRoleCanonicalSourceGrowth.allocated table extra i) =
      .unresolved
```

```lean
theorem new_alias_inspection (table extra : Table) (graph : Graph table.length)
    (pattern : Pattern) (old : Slot table) (new : Slot extra)
    (same : CommonRoleSourceIdentity.source extra new = CommonRoleSourceIdentity.source table old) :
    inspect (allocate table extra graph) pattern
      (CommonRoleCanonicalSourceGrowth.newRoot table extra new) =
        retainObservation table extra (inspect graph pattern (canonical table old))
```

```lean
theorem fresh_snapshot_unknown (table extra : Table) (graph : Graph table.length)
    (role : Nat) (new : Slot extra) (visible : List VisibleHead)
    (fresh : CommonRoleSourceDescent.representative table
      (CommonRoleSourceIdentity.source extra new) = none) :
    inspectSnapshot (allocate table extra graph) role
      (CommonRoleCanonicalSourceGrowth.newRoot table extra new) visible = .unknown
```

