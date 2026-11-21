# C314: 履歴のある据付のヘッドと実値の健全性を一般に証明

開始 2026-11-21 05:30 UTC / 14:30 JST。C313 完了 81ed8a6aba89ada711c8c091013feeba76b94491、
integration af2ac2ebd8aff9088fc65fc3eb85e799f71600e6 の standing orders と inbox を再読。
終了前に integration fc059f2157cf0dc4bcf35697ccc956951b174571 を再確認し、両文書の内容は未変更。
I-55 (4) 型推論・一般辞書健全性を優先。(2) 成功停止時の部分正当性の一般化や、
停止性・探索順序・クラス最小化には手を広げていない。

## 一般に証明したこと

- **数値 owner が初めて据え付けられる枝。** 他 owner の install / refresh / reobserve / merge が
  あっても、その owner の private 座標は旧 packet、class body、実登録済み child を含む
  full mixed Models の履歴 support にない。checked registry、実到達、現在の実選択、妥当モデルの
  存在から、一つの割当てで現 head、class 出力、where の上下端・子の実中心・計算出力を満たす
  実 Residual と Installable を構成。source ルートの形や要求の追加制限なし。
  GeneralVersionedHistoricalSupport314.all / absent、
  GeneralVersionedNewOwnerInstall314.joint / installable / node_and_edges。
- **過去に同じ数値 owner の据付がある枝。** 実 install は同じ owner では宣言鍵を保つ。
  さらに現在の実選択と同じ owner の過去宣言は、新しい読みや実併合の後でも一致する。
  現在側の鍵一致を前提にしない。raw の保護集約を、正確な入力名・極性・順序付き観測版・
  多重度を照合し、実履歴に書かれた式として回収。
  GeneralVersionedReservedVersion314.raw_history、GeneralVersionedSameOwnerChoice314.prepared / key_eq。
- **全選択済み frame の共通モデル。** 実到達した任意の現在の選択済み frame で、モデルが存在すれば
  全 journal を保つ一つの割当てで HeadEquations を構成。constructor tests は実生成辺と型付き
  ソースラベルから作る。保護 purpose-8 binder には同一 owner・宣言・名前の過去の実 binder
  がある。選ばれた集約を保護する全 journal / report / live class の実足跡には正確な台帳がある。
  GeneralVersionedReachableTests314.tests、GeneralVersionedPrivateJournal314.owned、
  GeneralVersionedHistoricalHead314.head、GeneralVersionedAggregateClassNow314.ledger。
- **再訪の実値書込み。** 実 child-center と計算 where 出力は、読む区間をそのまま replay しなくても、
  同じ owner の実履歴から同一モデル上に運べる。正規化した source 項の実値だけを使い、上下端と
  混同しない。自由な書込みの衝突整合も一般に成立。
  GeneralVersionedRevisitActual314.child / output、GeneralVersionedRemainingWrites314.internal。
- **残る実 where 下限・上限。** 保護された複合 where endpoint の同じ行は、過去の同じ owner が
  実際に生成した式一覧に存在する。完全な読みリストの一致ではなく、その式が実際に読む
  (mode, name) の値の同値だけで、過去行を現モデルへ移せる。nominal 部分は上下端の式の中でも
  actual を読む。読みが空ならこの入力は自動。
  GeneralVersionedEndpointLedger314.previous_of_endpoint、
  GeneralVersionedEndpointModes314.value_agrees、GeneralVersionedEndpointReduction314.closed_reads。

## I-55 の残り（未証明インターフェース群）

- **(4) 2 本。**
  - **(4a)** 異なる数値 owner が実併合で alias になった任意の non-replay 枝で、旧選択の鍵と
    現選択の鍵が一致すること。不一致なら、旧候補を今再読した非単一の集約 target が semantic raw
    pool に現れ、その入力名・観測順序が一致する予約を現 owner の実 install が別の鍵として
    作っているが、その target の台帳式はない。これは必要条件であり、実到達する反例ではない。
    GeneralVersionedRemainingWrites314.choice、GeneralVersionedForeignCollision314.wrong_key / same_version。
  - **(4b)** 再訪で保護された複合 where の下限・上限の行について、式が実際に読むオペランドの
    同値を持つ少なくとも一つの同一 owner の実履歴を与える Readback の一般化。
    現 head・集約・private binder・実 child-center・計算 where 出力・自由な行はこの未証明入力に
    含まれない。一般の interval refresh だけで上下端が同値を保つ、とは示していない。
  - この二つから実 B4SkeletonV8.EvidenceNode を組み立てる
    GeneralVersionedRecursiveCut314.evidenceNode を証明。二つの入力なしの一般辞書健全性は未証明。
- **(2) 2 本、変更なし。** **(2a)** 実履歴付き Local 行を生成する一般 source observer/compiler。
  **(2b)** Sat が成功返却した場合だけ、実 mixed Step 経路・返却地点の停止証拠・返却木と
  宣言的 Local/Classify の一致を与える橋。

本数は未証明の入力群であり、必要な補題数の予測ではない。次は (4a) で併合と予約の衝突を
排除するか、既に真の集約式を示す。(4b) は点化等の再読で実 readback を検証し、
必要なら上下端の現モデル条件を直接扱う。停止性とは切り離す。
[技術ノート](../design/2026-11-21-cycle314-historical-write-readback.md)。言語設計の質問ノートなし。

## 検証・公開の範囲

32 個の追加 Lean モジュールの scoped build、各ソース trust=0、独立監査、差分検査の結果は
[検証ログ](../verification/cycle314/verification.md)。Rust・CI・全体 Lake build は未実行。
言語仕様・コンパイラ本体・実行時の受理条件に変更なし。通常の公開先は work/dots-main のみ。
前の正確なリモート head を指定した非強制更新と固定コミットでの読戻しを行う。

この周期の差分は heartbeat を除き 68 ファイル。消費枠残量は不明。
最終公開の時刻、所要時間、参照先は同じコミットの完了 heartbeat に記録。
