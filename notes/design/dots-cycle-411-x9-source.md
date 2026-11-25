# C411 / I-74 C03: X9 の親と実 where 子

仕様 §6.3 の `impl Show (list 'a) where Show 'a` / `show [loop 1]`。親の根は構造的な巡回ではなく、invariant list の literal binder は payload を開かない。実宣言の where 0 番から `p.root.occurrence ++ [0]` の子を生成したとき初めて、元 payload を根とする無濾過の同じ raw K2 を用いる。親の report を裸の `rejected` tree に置き換えず、`selected parent [.rejected]` を rejected に集約し、書込みは空。

- 局所規則は true を前提にせず、見えている唯一の実宣言・実 mode・元 point の捕捉と exact where だけを読む。既存規則 `R2` との和を `R3` にし、`∀ s q d, Classifies R3 s q (.selected d) → ∀ m, Fits s m → DictionaryEvidence s m q d`。
- 実行証人は C410 の parent escape と元 origin ordinal、および既存の raw cycle 証人。需要やその位置、親の宣言、結果を証人から作らない。チェックは元 state から作る子の demand に既存 raw `Cycle350.check` を実行する。我々の許す狭い例以外は unsupported（言語の拒否とは言わない）。
- exact 型を保つ: `∀ p r w, check p r w = true → ClassifiedAs p.state p.root r ∧ ∀ m, Fits p.state m → ReportEvidence p.state m p.root r`。木、元 where ordinal と role、同じ実 point、正確な順の空 write と同じ model を保持。従来分岐には手を入れない。
- この確認点では local rule、dictionary sound、R2 の exact report 移送まで strict Lean 4.35.0 + 独立 Audit（標準 axioms のみ）。実子 raw branch と X9 テストは未完了。
