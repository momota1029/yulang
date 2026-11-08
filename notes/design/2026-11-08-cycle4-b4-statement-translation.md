# Cycle 4: B4 主張の Lean 翻訳と未接続の境界

承認済み `2026-11-08-b4-main-statement-draft.md` を出発点とする。
この翻訳は **未証明の target schema** である。一般 source carrier / propagation が未定義なので、
既存 settled carrier を全 B4 の代わりにしない。`SourceBoundary` のフィールドは未接続箇所を
名前にしたもので、その存在・実装・正しさを定理の外部仮定に隠して完成と称しない。

## 型

`Vocabulary` は有限 registry、source graph 状態、区間需要、モデル、宣言識別子の型。
`SourceBoundary` は実行関数を参照しない checked/Models/Step/Stable/Survivor/K2/knownness/
Evidence/Reorders/DictionaryEquivalent を持つ。`Classify` はこの boundary から帰納的に定義する。
`Executor.run` は `(R,Σ,d)` から状態と四方向結果を返し、fuel/Acc/成功証明を引数に取らない。
`Main.B4Statement boundary executor : Prop` は全 registry, checked, state, demand を量化し、
停止・閉包・モデル減少、独立 Classify との iff、並替え不変、全モデルの辞書健全性、
偽拒否なしを要求する。**この型を閉じた一般 B4 の命題へ instantiate する具体 boundary はない。**

## 意味を勝手に埋めない箇所

`Classify` は草稿に記載された root-pending、K2/候補消滅拒否、複数候補曖昧、
唯一候補＋全where子selectedの規則だけを持つ。唯一候補の子がpending等の場合を
無断で親pendingへ写さない。これにより全体totalityはまだ得られない。
辞書の子列はwhere順を保持するため、順序独立は独立な `DictionaryEquivalent` を使う。
その具体的意味（列の並替え・子需要の対応など）は質問ノートに分離する。

## 最短の未証明連鎖（5 本の主要橋、細分補題数は未確定）

1. `source_boundary_adequate`: 実 source/registry/state/knownness/K2/propagation に boundary を実装し、
   独立 survivor・証拠・辞書同値の意味を確定する。carrier と質問への回答が必要。
2. `generated_work_closed`: 実宣言から作った有限仕事領域・source identity・新childの登録を証明。
3. `saturate_terminates_and_closes`: Paterson/K2と有限新事実により再訪排除・停止・安定閉包を証明。
4. `saturated_frontier_exact`: 完成状態の四方向 Classify と実局所分類の iff、偽拒否なし。
5. `resolve_dictionary_order_sound`: 全where子辞書の全モデル健全性と並替え観察同値。

この5本を示しただけで現在の schema に使う具体 boundary の定義が自動で生まれるわけではない。
第1橋には定義の構成自体を含む。特に未決規則を仮定で埋めて残り4本を証明しても全B4完成ではない。

## 既存成果の位置

| 既存宣言 | B4のどこに効くか | 限界 |
|---|---|---|
| SettledResolver.resolve_exact | (2)健全性/完全性 | 等端点、共有状態の一般narrowingなし |
| OpenProducerAccess.accessible | (1)補助 | 固定構造的producerのwhere child、同親再訪ではない |
| OpenRecursivePass.run_exact | (2)補助 | 一回pass、最終分類ではない |
| OpenFiniteClosure.closure | (1)補助 | 固定producer閉包、状態依存childに未接続 |
| StatefulPathComplete.checked_exact | (2)健全性/完全性 | 入力された有限path、一般仕事生成ではない |
| PathOrder.observable_order_independent | (3)補助 | 有限pathと固定associated seedの断片 |
| NamedPath.outer_exact | (2)(4)健全性/完全性 | source名からslotを計算する有限path、全sourceではない |

全体の主型性はこのB4 schema単独の項ではなく、B6のTyping/推論scheme familyとの結合で必要。
