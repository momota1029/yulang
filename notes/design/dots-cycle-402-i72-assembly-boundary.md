# C402 / I-72: Lean の依存図と、まだ定義できていない原始規則

[`I72.assemble_named`](https://github.com/momota1029/yulang/blob/4ac5acce992e6562d945c771b55ec5bf8e31b04a/lean/Yulang/GeneralDeclarativeI65I72Obligations402.lean) は、S01・S02–S09・S11・S13 の五つの葉から I-65 の意味的辞書健全性へ結線する。S10 は `provide_node_at_same_selected_source` で S02–S08 から、S12 は `general_tree_meaning_from_local` で S09 から得る。ここでの型は暫定のソース原始規則 `SourcePrimitives` と訪問等の `SourceSpecification` に対する **相対版**。固定公刊文の前提にこの二つを足したとはしない。

- [固定目標と有限導出](https://github.com/momota1029/yulang/blob/4ac5acce992e6562d945c771b55ec5bf8e31b04a/lean/Yulang/GeneralDeclarativeI65I72FixedGoal402.lean): C365 の論理状態に I-70/71 の B6 注釈を保持。出力は木のまま。原の raw graph の root K2 なら、任意の原始体系候補・未完了読みであっても拒否が先。支持辺は同じ状態で実際に完了した元の Request・dictionary・出力 ordinal／元の型つき payload を指し、辞書へ入る where 子とは別。物理版や release、model の判定を足さない。
- [構造側の証明](https://github.com/momota1029/yulang/blob/4ac5acce992e6562d945c771b55ec5bf8e31b04a/lean/Yulang/GeneralDeclarativeI65I72Assembly402.lean): 実 source trace の `LocalSource` 投影、各実 node から同じモデルでの右辺の読み、元の ordered where の lowering と meaning の fold、同じイベント／元 ordinal の typed replay（S13a, S13ba, S13bba の相対版）を Lean で確かめた。固定先へ等式を解釈することは RHS の読みだけではない。S13bbbb は意味的な等式として残す。
- `assemble_remaining` でこの版の結線に仮定として残る named proposition は **9 種類**（S02–S08、S13bbba、S13bbbb）。これは原始 source 規則を実装済みという数ではない。現行 C380 の数を更新しない。integration 未取込のこの相対版で構造が検証済みなことと、S 行の真の閉鎖は別。
- scope: S07 は I-67・I-71 を受け、物理作者／版／release を使わず、元の decl と captured slot に索引づけた literal typed tree を読む。実 source の論理出力の根拠・モデル上の固定先等式は選択から単に推測しない。今回の `CapturesActualHead` は actual center の連結を記述するが、全 source 形の端点・訪問・捕捉の規則が完成したことは主張しない。

## 次に必要なこと（S 行の追加ではない）

1. `SourcePrimitives.elected` 等を、外部パラメータでない独立の元 source 規則として実装する。実 `State` の同じ完全な可視候補順、独立に支持された lower、実訪問位置の raw K2、各 branch の保留・不一致・選択を揃える。可能な port を actual visit にせず、未知の観測を拒否・保留・選択のどれかに作り替えない。実 where と読み producer は別の有限証拠のまま。
2. C401 の B6 受渡しを元の実 `State` で供給する。これは B4 内の再型付けではない。同じ選択出現の actual head・frame・端点と、B6 が渡した元 RHS を本当に集める。C402 前半の C357 join 到達範囲は候補の実 frame の真の一例だが、全言語の原始規則でも B6 全体でもない。
3. ここまでを実 State で閉じた上で、固定先の状態保持を S13bbbb として示す。I-65 step 2 の `check` は途中で False に置き換えず、step 3 もまだ作らない。

実装不足は新しい意味の選択ではない。仕様を変更せず、未決事項を作り出さない。固定文と統合チェックリストのファイルは変えない。
