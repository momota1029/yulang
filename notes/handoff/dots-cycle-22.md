# Yulang Lean cycle 22

開始 2026-11-09T00:57:44Z。基点 integration/m1-final `3181de1ac`。
最新 standing orders と inbox I-11 までを取得し ACTIVE/上限24を確認。
前回21はcompleted、報告あり。今回の環境に生きた Lean ビルドなし。
前回の作業場を再使用し integration をmerge、work/dots-main の心拍もmerge。
25分上限・focused-only・一括公開を優先したが、公開API待機で25分を超過。下記の復旧記録を参照。

## 部分目標と結果

開始時の目標は実adapterの EmissionMonotone の証明または反証。
**associated-only decoder 全般については閉じていない**。
ただし「通常制約が増えれば actual Reach は保たれる」という証明方針は
実producerの検証済み反例で否定した。first-hitは最終選択ではない。
先行 literal と後続 capture がある checked registry で、slot が int になると
先行literalがhitになり、capture由来のchildがReachから消える。
frontierは当初pending、その後ambiguousで、いずれもselectedでない。
これは言語の反例でなく speculative producer を選択として使う実装上の境界。

反例だけでは終えず、任意の registry/source/annotation/観測stateについて、
最終Reachが実際に支える関連型方程式だけを再生成するviewを定義し、そのモデルの
健全性・完全性を証明した。さらにunsupportedTokensが空という実行可能チェックから、
既存persistent collectorと再検証viewのモデル同値が従うことを証明した。
再検証がReachを変えないこと、反復が停止すること、チェックが常に通ることは主張しない。
既存コード・定理の意味は変更していない。

## 定理（量化子・前提・側）

`CommonRoleFeedbackSupport` は全n、checked registry、source root、
computed closure上のannotation（固定receiverの関連型Request列）を量化する。
関連型の定理は更に全env, roles, wf:WellFormed env.coresを量化する。

- `Adapter.emitted_owner`（補助）: 全node q、全table index iについて、
  iがqからemitされる iff table entryのsourceがq。
- `Adapter.monotone_iff`（補助）: 全decodeに対し、実emitのEmissionMonotone iff
  全a⊆bと全非空annotationを持つqについてReach(decode a,q)ならReach(decode b,q)。
  追加仮定の十分条件ではなく、既存仮定の必要十分条件。
- `supported_exact`（健全性/完全性の補助）: 全観測state、全request rについて、
  再計算リストのr所属 iff あるReach node qのannotationにrが属す。
- `revalidate_exact`（健全性/完全性の補助）: 全seed・観測state・assignmentで、
  再検証stateのモデル iff seedのモデルで、かつ全Reach nodeの全annotationと
  全Computed結果headに対し、その出力slotがheadとEquivalent。
- `certified_final_models`（健全性/完全性の補助）: 全seedとassignmentについて、
  各collected indexに最終Reachなemitterがあるという明示的前提の下で、
  既存finalStateのモデル iff finalStateを観測してseedから再検証したstateのモデル。
- `checked_final_models`（健全性/完全性の補助）: 同じ量化子の下で、
  実行可能なunsupportedTokensチェックが空なら上記モデル同値。

`CommonRoleFirstHitSupportBoundary` は具体的なchecked registryと1slotの回帰例。
- `atoms_included`: before.atoms⊆after.atoms（補助）。
- `child_disappears`: beforeのactualNextにchild所属、afterには非所属（反例）。
- `frontier_not_selected`: beforeはpending、afterはambiguous（反例の根拠）。
- `not_universal_child_monotone`: 全checked registry、全1slot source親/子、全state
  a,bについてatom inclusionがactualNext inclusionを含意する、という一般命題の否定。
- `reachable_disappears`: 実Reachについても同じchildが消失（反例）。

主型性の新しい定理なし。実装断片の制限を仕様の拒否規則と混同しない。
B4の主定理は依然**5橋とも残る**。今回閉じたのはbridge2内の
「最終source支持の監査と方程式viewのexactness」。一般resolve_exact、X13〜16の
外側入口PROVED、動的receiver、source lowering、独立診断treeは未達。
次: (1) frontier-awareな候補guardつき方程式の導出、
(2) associated-only legal histories上での支持喪失の検証、
(3) 再検証/再tractionを含めた停止尺度と独立診断treeの接続。
質問ノートを1本保存したが、既存specの遅延規則を変更する設計判断はしていない。

## 検証・中断

- git fetch integration/m1-final, work/dots-main, work/dots-audit 成功。
- git merge origin/integration/m1-final / origin/work/dots-main 成功。
- ELAN_HOMEを既存dots-probe-elanへ指定、Lean 4.35.0/cache再使用。
- 初回ELAN_HOME未指定はread-only /home/agent/.elanで失敗、指定して修正。
- 開発中にwfail linter、FrontierのDecidable不在、by_contra tactic不在が発生し修正。
- 最終 `timeout 120 ... lake build --wfail Yulang.CommonRoleFirstHitSupportBoundary`
  と `lake env lean --trust=0 /tmp/cycle22-audit.lean` は両方exit0。
- 全体lake build、全Audit、verify-lean.shは最新指示で未実行。全体PASSではない。
  verify-lean.sh出力/終了コードは存在しない。
- 新規11定理はpropext/Classical.choice/Quot.soundのみ。sorry、新axiom、native_decideなし。
- git diff --check成功。

最終 focused + axiom log 全文:
```text
✔ [293/294] Built Yulang.CommonRoleFeedbackSupport (1.1s)
✔ [294/294] Built Yulang.CommonRoleFirstHitSupportBoundary (1.3s)
Build completed successfully (294 jobs).
'Yulang.CommonRoleFeedbackSupport.Adapter.emitted_owner' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleFeedbackSupport.Adapter.monotone_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFeedbackSupport.supported_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFeedbackSupport.revalidate_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFeedbackSupport.certified_final_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFeedbackSupport.checked_final_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFirstHitSupportBoundary.atoms_included' depends on axioms: [propext]
'Yulang.CommonRoleFirstHitSupportBoundary.child_disappears' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleFirstHitSupportBoundary.frontier_not_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleFirstHitSupportBoundary.not_universal_child_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleFirstHitSupportBoundary.reachable_disappears' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Yulang2との照合

最新work/dots-auditのx-oracle X13〜X16を読んだ。旧実機のcheck/dump成功は
今回の内部first-hit/Reach遷移を観察していない。この反例のYulang実機再現は未実行。
対応する規則はspec6.3の兄弟安定までの遅延であり、first-match意味論は導入しない。

## 公開・資源

自作9paths: Lean新規2、追記3、design1、question1、report1、heartbeat1。
これに最新integrationのinbox更新をそのまま取り込む（編集なし）。
work/dots-mainのみへ非force・expected-head付き一括tree/commit/ref公開する。
公開後、remote treeとローカルtreeを照合する。最終commitと照合結果は親への報告に記載。
ローカル証明commit: 1ea7c5f82 / da8e21a7d / 5ec96a26b。
空き容量は開始・終了とも19GB。キャッシュコピー、破壊的cleanupなし。
使用量枠への計上は不明。環境再作成なし。約9分時点で報告を準備。

## 公開中断と復旧

一括 create_tree API が1183.8秒応答せず、親が中断した。create_commit/update_ref は未実行。remote 心拍は00:58:10 runningのまま、報告は404だった。25分の制限と10分ごとの心拍を守れなかった。成果はローカル ab2038c12 に残り、失われたファイルはない。

復旧は2026-11-09T01:27頃開始。focused 294 jobs と11定理のtrust=0監査を再実行し成功。内容blobを個別作成してからSHAのみの小さなtreeを作る方式で、work/dots-main のみを非force・expected-head付きで一括更新する。公開完了とtree一致の確認結果は親への最終報告に記す。復旧時刻: 2026-11-09T01:27:57Z。
