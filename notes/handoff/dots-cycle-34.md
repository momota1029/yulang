# Cycle34: directed conflict pruning

## 時刻・基点
通知 2026-11-09T10:27:19Z、実着手10:28:03Z。期限10:52:19Z。
integration/m1-final@4871ea4c1、前回work/dots-main@759466946。
最新standing orders/inboxを取得、ACTIVE・上限なし・cycle33 completedと報告あり。
作業場はyulang一つ、空き開始57GB。並行writerなし。

## 部分目標と結果
有向scalar上下界の矛盾証明を実行検出し、自己出力探索からその出力だけを除いて全モデル族を保つ。
この部分目標は閉じた。一般充足可能性判定や言語のrejected分類ではない。

## 定理一覧（量化と前提）
CommonRoleDirectedConflicts の6定理は任意のslot数n、State nのsについて。
- check_exact（健全性/完全性）: 実checkがtrue iff あるslot iと異なるscalar lo,hiについて、lo≤iとi≤hiが独立Derivedで導出される。
- conflict_no_model（健全性）: 上記Conflictの前提下、任意の割当aはsの全atomのモデルではない。
- checked_no_model（健全性）: check=trueの前提下、任意の割当aはsのモデルではない。
- model_check_false（健全性）: 任意割当aがsのモデルならcheck=false。
- normalize_conflict（補助）: 正規化後Conflict iff 元のConflict。
- normalize_check（補助）: 正規化前後でcheckのBool値が等しい。

CommonRoleConflictFilteredInference の最初の3定理は任意nと有限State nリストstatesについて。
- prune_exact（健全性/完全性）: 任意状態sについて、pruneへの所属 iff 元リストに属しかつConflictでない。
- prune_models（健全性/完全性）: 任意割当aについて、prune後の状態のモデルになる iff 元リストの状態のモデルになる。
- pruned_no_models（健全性）: pruneが空なら、元リストのどの状態にもどの割当にもモデルがない。

残る3定理は任意n, Registry, SourceRequest n, AssocEnv env, RoleDecls roles,
WellFormed env.cores, route/宣言ごとの入力Requestリストannotations, seed State nについて。
- infer_models_preserved（健全性/完全性）: 任意割当aについて、pruned infer出力のモデル存在 iff 元のdirected infer出力のモデル存在。
- infer_models_exact（健全性/完全性）: 任意割当aについて、pruned infer出力のモデル存在 iff aがseedモデルで、ある新Stable表が存在し、その全選択route/宣言の全注釈要求と全Computed headについて出力slotがheadとEquivalent。
- empty_excludes_stable_model（健全性）: pruned inferが空、任意表が新Stable、という前提の下、任意割当aはその表の出力モデルにならない。
主型性定理はない。出力モデルの不存在から言語rejectedへの橋は未証明。

## 検証
ELAN_HOME=/workspace/scratch/1d0b4aaa3394/elan、そのbinをPATHへ設定。
`lake build --wfail Yulang.CommonRoleConflictFilteredInference`: exit0、315 jobs。
`lake env lean --trust=0 /tmp/cycle34-audit.lean`: exit0、12定理、公理は標準3種のみ。
初回wrapperのprune_exact証明はrewrite不一致で失敗。その後case分解へ修正し、最終再検証成功。
全体build・全Audit・verify-lean.shは常設指示に従い未実行。全体PASSではない。
読取りレビューで問題なし。レビュー担当はwrapperの独立ビルドをしていない。

### 最終検証出力全文
~~~text
Build completed successfully (315 jobs).
BUILD_EXIT=0
'Yulang.CommonRoleDirectedConflicts.check_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedConflicts.conflict_no_model' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDirectedConflicts.checked_no_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedConflicts.model_check_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedConflicts.normalize_conflict' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDirectedConflicts.normalize_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleConflictFilteredInference.prune_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleConflictFilteredInference.prune_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleConflictFilteredInference.pruned_no_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleConflictFilteredInference.infer_models_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleConflictFilteredInference.infer_models_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleConflictFilteredInference.empty_excludes_stable_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
AUDIT_EXIT=0
~~~

## 未達・次
一般B4の主定理には依然5橋が未完。今回橋3/4内部の矛盾証明とモデル保存枝刈りを接続しただけ。
check=falseは充足可能性を意味しない。存在・一意性・主型性、source生成、state依存receiver、role feedback停止、言語分類、X13〜X16外側PROVEDは未達。
次候補: (1) source/receiver生成との接続、(2) 構造型も含む独立矛盾証明、(3) 診断分類への接続。
意味論判断をしていないため質問ノートなし。

## Yulang2との照合
既存取得済みnotes/audit/y2-claims-role-boundaries-cycle-2.md ROLE-MORE-001〜008を再読。
latest audit取得・新実機照合は未実行。今回の判定はordinary部分型推移律と異なるscalarの非部分型性のみで、role候補選択の意味論を決定していない。
spec/04-types.md scalar/never節も確認。上界だけが異なる場合を矛盾とはしていない。

## 公開・制限
work/dots-mainのみ、GitHubアプリの個別blobとSHA treeによる一括・非force expected-head公開。
新規Lean2、root/Audit/README追記、設計ノート/索引、報告/心拍の9ファイル。
中断・承認待ちなし。使用量枠は不明。短時間で終了する理由は明示部分目標の証明・検証が閉じ、別の橋は次回に分けるため。

## 公開照合・終了
2026-11-09T10:35:39Z: work/dots-main@c90336665 をfetchし、ローカル全treeとのdiff空・cleanを確認。9ファイル公開。空き終了57GB。実着手から約7分半、通知から約8分半。コード変更なしで終了記録とcompleted心拍を追加公開する。開始心拍updatedを10:30:00と手入力したが実際は約10:29で最大約1分先だった。以後はdateの実時刻だけを使用し、この終了記録で訂正。
