# dots cycle 18: 状態更新後の実producer cacheと最小閉包

開始2026-11-08T22:57:58Z。検証終了23:02:28Z、公開準備23:04 UTC。integration基点 `6008183c12d0cc6590aa6e7297bf3ef91a482182`、前回公開 `582bd23629d12fda046520d64a033ce76894d0fd`。前回cycle17 completedと報告を確認し、同一作業場を再利用。開始時点ではクラッシュ復旧ではなかったが、後述の公開停止から救済した。最新inboxはACTIVE、上限24。25分上限を優先。

## 実装と範囲

`CommonRoleRefreshDriver` を追加。前後ordinary stateの依存slotを調べ、cleanな親のcache行は再利用し、dirtyな親の実producer子を再生成する。到達集合は更新した辺から再計算し、古い訪問集合を単に和集合で残さない。最終状態の独立な `CommonRoleSourceWorklist.Reach` と実行結果の所属のiffを証明した。

制限はdocstringにも明記: int-only materializationとunary capture-bearing source-templateの既存断片。ordinary状態列は外から与えられる有限リスト。ordinary制約を自律生成して飽和に到達するdriverでも、一般B4でもない。first-hit producerを用い、候補の一意選択を主張しない。

## 定理（namespace Yulang.CommonRoleRefreshDriver）

共通の量化: 任意の有限slot数 n、registry、source rootを取る。Nodeは宣言とrootから計算された有限領域の要素。以下すべての状態・cache・node・traceは任意。

- `initialCache_valid`（補助）: 任意の状態sの初期cacheは、全node qで実actualNext registry s q.valと等しい。
- `refresh_valid`（補助）: 任意のbefore/after/cacheで、全nodeについてbeforeでcacheが実producerと等しいなら、更新したcacheは全nodeについてafterの実producerと等しい。状態の単調性・整合性の仮定は不要。
- `clean_row_reused`（補助）: 任意のbefore/after/cache/nodeで、そのnodeのdirtyが空なら更新後行は元のcache行に等しい。
- `dirty_row_recomputed`（補助）: 同じ量化でdirtyが空でなければ更新後行はafterのactualNextに等しい。
- `cached_rules_exact`（補助）: 任意のs/cacheについて全nodeでcacheが正しいなら、cacheから作ったHorn規則列はsの実規則列に等しい。
- `cached_saturate_exact`（健全性・完全性）: 任意のs/cache/qで同じcache正当性を仮定すると、qがcache閉包に属することとsで独立Reachが成り立つことは同値。
- `replay_valid`（補助）: 任意のs/cache/有限traceで初期cache正当性を仮定すると、trace全更新を処理したcacheは処理後状態で正しい。
- `replay_state`（補助）: 任意のs/cache/有限traceについて処理後状態は独立に計算したfinalState s traceと等しい。
- `run_exact`（健全性・完全性）: 任意の初期状態、有限trace、qについて、qがrun結果に属することとfinalStateでReachが成り立つことは同値。cache正当性や状態の単調性・整合性を外から仮定しない。ただし有限状態列そのものは入力。
- `run_root`（補助）: 任意の初期状態と有限traceについてrootNodeがrun結果に属する。
- `run_actual_closed`（健全性の補助）: 任意の初期状態/有限trace/parent/childについてparentがrun結果に属し、childが最終状態の実actualNextに属するなら、同じchild値を持つNodeがrun結果に存在する。
- `run_nodup`（補助）: 任意の初期状態と有限traceのrun結果に重複はない。
- `run_capacity`（停止の補助）: 任意の初期状態と有限traceのrun結果の長さは計算されたsource closureの長さ以下。
- `run_least`（完全性の補助）: 任意の初期状態/有限trace/Node上の述語holdsで、rootでholds、かつ最終状態の全actualNext辺でholdsを保存すると仮定する。任意のrun所属nodeでholdsが成り立つ。
- `run_observational_independent`（補助）: 任意の2初期状態と2有限traceで、最終状態の全slotのknown bitが等しいと仮定する。任意のqの両runへの所属は同値。リスト順序の一致ではない。

主型性の新規定理はない。断片制限は実装側の制限であり、仕様による拒否範囲とは扱わない。

## 検証とコマンド

`git fetch origin '+refs/heads/integration/m1-final:refs/remotes/origin/integration/m1-final' '+refs/heads/work/dots-main:refs/remotes/origin/work/dots-main' '+refs/heads/work/dots-audit:refs/remotes/origin/work/dots-audit'` 成功。fetchのみでは追跡refが更新されない設定だったので明示refspecで最新を再取得した。`git merge --no-edit origin/integration/m1-final` 成功（inbox追記のみのmerge）。

`cd lean && lake build --wfail Yulang.CommonRoleRefreshDriver` 最終終了コード0。出力全文:
```
✔ [286/286] Built Yulang.CommonRoleRefreshDriver (1.1s)
Build completed successfully (286 jobs).

real 0m1.251s
user 0m0.986s
sys 0m0.378s
```
`lake env lean /tmp/cycle18-audit.lean` 終了コード0、上記15定理すべての公理は `[propext, Classical.choice, Quot.sound]` のみ。Audit.leanに15定理登録。sorry、新しいaxiom、native_decideなし。

途中の失敗: initializeが予約語、Validの展開不足、nodes長さの変換、帰納法で残った仮定の4箇所を修正。最初の局所commitは構文エラーを含んだが、後続commitで修正した。公開木は最終検証済み版のみ。`/usr/bin/time` が無くexit127、bashのtimeに切り替え測定。環境の再作成は確認されていない。公開工程が停止し、心拍が23:00 UTC以降更新されなかったため、元作業を中断して救済した。

`git diff --check` 成功。全体lake buildおよびverify-lean.shは最新standing ordersどおり未実行。全体PASSは主張しない。

## B4の残り・次の一手

5橋の一般形はいずれも残り、残数は5。今回bridge2の更新処理と意味的閉包の部品を接続したが、自律的なordinary-fact生成と停止が未接続。次の候補は(1) 実宣言から発生する有限ordinary-fact更新をこのrefreshの入力に結ぶ、(2) cycle17の有限無効化上界と更新driverの停止を結ぶ、(3) 独立な最終診断tree/辞書の正準順。一般区間への拡張、X13–X16外側PROVED、全B4 resolve_exactは未達。

## Yulang2との照合

最新work/dots-auditのx-oracle X13–X16を読んだ。外部例は内部cache更新を観察できず、その性質の実機照合は未実施。Yulang2のcheck成功をこの定理の根拠にしていない。spec6.3の兄弟更新安定まで子最終化を遅らせる方針と整合する内部処理であり、新たな意味論選択なし。質問ノート追加なし。

## 公開・資源

ローカルcommit: d11769856, a6315d75c, 0820e4def, 2f190c119。独自成果5ファイル（新Lean、新設計、Yulang/Audit/README追記）＋報告＋心拍＋復旧記録=8パスをcontents APIで順次公開。最新integrationから継承したspec等5ファイルはこの救済では上書きしていない。公開ブランチをintegrationへmergeしたとは主張しない。

## 公開停止と救済

最後の公開心拍は23:00:00 UTC、remoteは57f53033dで報告未公開。元作業を親が中断し、23:25:03 UTCに救済でローカルcommitを確認。停止原因は未特定。25分以内の公開・報告に失敗した。救済終了準備23:27:27 UTC、開始から29分29秒。救済開始から約2分24秒で成果5パスの公開が成功した。

救済で lake が初期PATHになくexit127。ELAN_HOME=/workspace/scratch/1d0b4aaa3394/dots-probe-elan とそのbinをPATHへ設定して再実行:

```
lake build --wfail Yulang.CommonRoleRefreshDriver
Build completed successfully (286 jobs).
BUILD_EXIT:0
lake env lean /tmp/cycle18-audit.lean
AXIOMS_EXIT:0
```

15宣言の公理はpropext/Classical.choice/Quot.soundのみ。全体ビルド・verify-leanは再度未実行。公開後の照合結果と最終公開commitは会話報告に記録する。既存の未公開commitを含むcloneは削除せず、cache複製なし。使用量枠への計上は不明。
