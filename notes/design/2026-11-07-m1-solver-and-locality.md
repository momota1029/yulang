# M1 solver の内部契約と局所更新

Status: Draft — 実装済みの限定された kernel と、統合前の境界を区別する。
Date: 2026-11-07
Scope: `integration/m1-solver` の要求モデル、tail/cache 表現、selection と増分計算の内部設計。言語仕様の追加決定ではない。

## 1. 決定済み仕様との境界

決定46・47と demand-model Q5 の回答に従い、要求は union を含まず、型変数と role 制約を持つ。
有限 rigid 観測の列だけに型変数を割り当てる旧候補は `int | str = any` を導くので採用しない。
旧候補の証明と、この過剰な同一視を示す反例は削除しない。
record の tail へは先頭 label の要求だけを取り除いて渡す（`spec/04-types.md` 4.3）。
variant の tag row に書く `|` は正位置の型 union とは異なる。

内部モデルの選択肢はこのメモで比較する。Yulang のコードで観測可能な未決定差だけを
`notes/questions/` に置く。cache の shape、mask の列挙、観測の rank の選択はユーザーへの問いにしない。

## 2. SCC の selection を一度で確定する条件

`MethodResolutionLocality` は既存の `MethodResolution.resolve` をそのまま呼ぶ。
未知 receiver では当該 method 名の可視 role/declaration 候補集合だけを読む。
既知 receiver ではその field の存在を優先し、不在時だけ typed fallback を読む。
他の field の payload、別の名前の role、処理しない SCC の snapshot を変更しても結果は変わらない。

SCC が確定した snapshot と、SCC が所有する selection site ID 列を渡し、各 site の解決結果を
回答表に書く。候補なし・一意・曖昧の三値を保持するので、エラーを黙って捨てる比較ではない。
同じ SCC 集合を含む任意の処理列で結果が等しい。順序入替えに加えて重複処理も冪等である。

採用理由は決定29の「SCC 確定時に選択し、後続具体化で選び直さない」と一致するため。
代案の全 selection 再走査 loop は、この snapshot 確定後の解決には必要ない。
ただし receiver の最終知識を得る constraint solver、SCC の抽出、scope の整合性は別の前提であり、
この定理から上流の求解そのものが一回で終わるとは結論しない。

## 3. module cache と実際の増分手続き

### 表現

`ModuleIncremental.Dependencies` は node `i` の依存を `List (Fin i)` に保存する。
node は module、または import cycle を既に縮約した SCC。すべての依存が先行することを型で表す。
順序と重複を消去しないため、compile が順序を観測しても定理は成立する。

`compile : Source → List Interface → Interface` の `Source` はソース本文だけでなく完全な cache key を含む。
`Interface` は成功した公開型に限らず、エラー、残余 qualifier、辞書依存、nominal identity なども含められる。
純粋な関数が読む入力を明示することで、成功を前提にせず全結果の一致を証明する。
本体以外の ambient state を読む compiler を、この型の関数と同一視してはならない。

`dirty` は変更フラグを依存先から利用側へ伝播する有限の topological pass である。
独立判断 `Affected` は「直接変更された」または「影響を受けた node に依存する」という有限経路で定義する。
`dirty_exact` が両者を一致させる。
`rebuild` は dirty node でのみ実 compile 分岐を通り、clean node は cache を返す。
その呼出し列は dirty な node の昇順列と等しく、長さは node 数以下である。

### cache に必要な前提

`rebuild_changed_graph_exact` は新旧依存 graph が異なる場合も扱う。
変更なしとマークした node は、自身の source/key と直接依存列を変えてはならない。
dirty の伝播は新 graph 上で行う。全体 build と増分 build の artifact 表は文字通り等しい。
したがって任意の決定的な表示関数を適用しても等しくなる。

採用したのは、意味的同値の判定器を仮定しない、完全な artifact/key の等号による cache 境界である。
代案の「同値な型なら同じ key」という意味的 cache は、完全な標準形を構成してから追加する。
`ProducerNormalForm.normalize_equivalent` は同値を保存する一方向の整理であり、
`Equivalent A B ↔ normalize A = normalize B` をまだ与えない。
標準形の完全性を仮定した wrapper を、その構成を済ませた定理として数えない。

この kernel は source の名前解決・依存抽出・SCC 発見・topological ID の新旧対応をまだ証明しない。
また `rebuild_calls_le` は compile の呼出し数だけであり、型 solver の時間計算量ではない。
参照実装は `dirty` の prefix を再評価しうる。Rust 実装では一度得た dirty 表を再利用するが、
そのデータ構造実装の時間上界はこの定理には含めない。

### EOF の独立性との関係

`EOFNoDefaulting.accepted_export_independent` は、同じ model・decode・割当て・interface の下で、
二つの impl 環境で **両方の finish が成功した場合**、公開された `ClosedInterface` が等しいという定理。
後から impl が増えて曖昧になる可能性を消していない。型の表示 cache と、EOF の成功判定や
辞書 artifact の cache は読む依存が異なる。
既存の Rust oracle plan §6.1 にある visible impl・辞書 body・設定・version まで key に保持し、
公開型が変わらないことだけを理由に診断の再検査を飛ばさない。

## 4. 残る統合義務

- 任意の constructor 制約から、意味を失わない分岐と受理枝の閉 cache を構成すること。
  旧 cache の子辺まで全 mask に閉じる表現には既存の反例がある。別の obligation 表現が必要。
- Q5 を満たす要求モデルでの任意の arrow 引数の分解と、exactEmpty/required/whole recordDefault image の統合。
- 具体モデルで `presence_solve_complete` と `presence_generate_exact` を結合し、残余 existential 制約を持たない scheme family を得ること。
- 新独立 `Typing` から旧 scheme の新 instance を得る完全性と、統一 `Core.infer` の主型性・拒否完全性・unsupported 排除。
- role・nominal・effect・regular graph を含む全 interface の完全な標準形と、実 module compiler への cache kernel の接続。

これらは定理の成功や自由 parameter の制約を前提にして閉じたことにはしない。
