# Yulang Lean cycle 10 — source occurrence割当の保守性

- 基点 integration/m1-final: `7b66157ec`。最新standing orders/inboxを読了、ACTIVE、上限12内。cycle9報告とcompleted心拍を確認して再開。
- 開始: 2026-11-08 16:55:33 UTC。検証・成果公開の終了: 17:02:04 UTC。報告・完了心拍を含め17:04 UTCまでに終了予定（実終了はcompleted心拍参照）。25分上限内。
- 再利用workspace: `/workspace/scratch/1d0b4aaa3394/yulang-cycle6`。新clone/キャッシュコピーなし。開始・終了とも空き19G、使用42G/63G、70%。未公開のローカル履歴がある古いworkspaceを推測で削除していない。

## 結果

`CommonRoleSourceGrowth`を追加。任意の有限source occurrence表へのappendについて、旧Comp値（型とeffect）を文字通り保存し、source coherenceを保つ拡張を構成した。実普通stateのatomをretainでrenameして新表のidentity atomを加えた状態について、実ordinary solverのacceptanceが元の状態と同値であることまで証明した。固定例でなく任意表・任意旧普通状態の定理。

**一般B4、XのPROVED、source provenanceの自動生成は未達。** source ID表は入力であり、実childから導けるとはしていない。新ordinary constraint追加が無害とも主張しない。

## 追加定理（名前のprefix: Yulang.CommonRoleSourceGrowth）

以下でtable/extraは任意のNatの有限リスト、slotは各表の有限添字、valuesはslotからComp Common.modelへの任意の写像、fallbackは任意のComp、Coherentは同じsource IDの型成分がCommon.Equivalentであること。

1. `restrict_grow`（補助・保存）: 任意table, extra, values, fallbackについて、growした値を旧slotへrestrictするとvaluesに等しい。前提なし。effectも含む関数の等式。
2. `restrict_coherent`（soundness側の補助）: 任意table, extra, 拡張表valuesについて、valuesが拡張表上Coherentなら、そのrestrictは旧表上Coherent。
3. `grow_factors`（completeness側の補助）: 任意table, extra, values, fallbackについて、旧valuesがCoherentなら、全拡張slotのgrow後型成分は、そのsource IDに対する旧valuesのdescend（未使用IDはfallback型）とEquivalent。
4. `grow_coherent`（completeness側の補助）: 同じ任意引数と旧Coherentを前提に、grow後は拡張表上Coherent。
5. `extension_exact`（soundness/completeness両方向の補助）: 任意table, extra, values, fallbackについて、旧valuesがCoherentであることと、restrictがvaluesに等しく拡張表でCoherentな拡張valuesが存在することが同値。
6. `constrained_atoms_exact`（両方向の補助）: 任意table, extra, 旧Comp valuation上の任意述語old, fallbackについて、「oldを満たし旧実identity atoms全てを満たすvaluesの存在」と「restrictがoldを満たし拡張表の実identity atoms全てを満たす拡張valuesの存在」が同値。oldに追加の制限はない。
7. `growState_models_exact`（両方向・実state接続）: 任意table, extra, grammar条件を持つ旧State state, 拡張valuesについて、growStateの全atomを満たすことと、「restrictが旧stateの全atomを満たし、拡張valuesがCoherent」が同値。
8. `solver_growth_exact`（両方向・実solver接続）: 任意table, extra, grammar条件を持つ旧State state, fallbackについて、consistent(growState table extra state)=trueと、consistent(旧tableのidentity atomsでextendしたstate)=trueが同値。source ID重複禁止などの仮定なし。solverの完成性を自作せず既存consistent_exactを用いた。

全8定理をAuditへ登録。principality本体は今回追加していない。設計ノートにB4までの最短連鎖と残る5橋を記載。

## 実行と検証

- `git fetch origin integration/m1-final work/dots-main` と `git merge --no-edit origin/integration/m1-final` 成功。single-branch refspecではwork/dots-mainのtrackingが更新されなかったため、最後に `git fetch origin work/dots-main:refs/remotes/origin/work/dots-main` を明示して成功。
- work/dots-auditのx-oracleをGitHub read-onlyで確認。Y2に構造区間構文の制限があるため、今回一般定理をY2実測で確認したとはしない。
- 初回focused buildはdeprecated dif_neg警告とgrow_coherentの省略引数の過剰適用で失敗。dite_eq_rightへ変更し引数を明示して修正。
- 最終 `cd lean && lake build --wfail Yulang.CommonRoleSourceGrowth` 終了コード0。出力全文:

```text
✔ [277/277] Built Yulang.CommonRoleSourceGrowth (1.1s)
Build completed successfully (277 jobs).

real    0m1.260s
user    0m0.938s
sys     0m0.401s
```

- `cd lean && lake env lean /tmp/cycle10-audit.lean` 終了コード0。8定理の#print axioms。restrict_grow/restrict_coherent/growState_models_exactは[propext, Quot.sound]、残りは[propext, Classical.choice, Quot.sound]のみ。
- sorry、新規axiom、native_decideなし。既存Leanファイルは許可された3ファイルへの追記のみ。spec/planは編集・公開していない。
- 最新standing ordersに従い全体build/全Audit/verify-lean.shは実行していない。**verify-lean.shの出力・終了コード・PASS判定は存在しない。** 全体検証は監督役に残る。
- ローカルcommit: `b5a5b2991`（モデル拡張）、`7be88c511`（実state/solver接続）、`588d1ad5f`（登録・設計）、`44888a18b`（README節間空行）。

## 公開と制限

GitHubアプリ経由でwork/dots-mainのみへ5成果ファイル公開、各ファイル再取得内容一致。さらにremote branchをfetchして下記5ファイルのHEADとの差分が空であることを確認:

- lean/Yulang/CommonRoleSourceGrowth.lean
- lean/Yulang.lean
- lean/Audit.lean
- lean/README.md
- notes/design/2026-11-08-cycle10-source-growth.md

成果公開最後のcommit: `5502a68f7a651f6f16c9b90b3e104dced288c1eb`。
README初回updateはauto-reviewが「巨大文書への置換」として拒否。既存277839文字が完全prefixで追加754文字だけ、明示的追記許可、ローカルdiffを確認してから同じAPIで再試行し成功。迂回手段は使っていない。ローカルも同じ内容に整えSHA一致。
この報告と心拍を含む公開対象は7ファイル。開始心拍 `52ceceb6f`。10分未満で完了するため途中心拍なし、終了心拍を続けて公開する。
過去cycle5報告/旧cycle8 plan等の既存ローカル差分は今回の成果ではなく再公開していない。work/dots-mainとローカル木全体の一致は主張しない。5成果ファイルだけを照合済み。

## 残る仕事

1. 実producer child/captureと独立source originを接続する。
2. narrowing/materialization後も閉じる有限仕事領域。
3. 普通制約更新・候補再生成の単調飽和と停止。
4. 安定四方向分類と子結果を保持する診断tree。
5. 正規順dictionaryおよびB4のsoundness/completeness/principality接続。

今回、意味論の設計判断を新たに決めていないため質問ノートなし。途中クラッシュ・環境再作成なし。使用量の計上枠は不明。
