# Common signed row 解釈の基礎

日付: 2026-11-07。状態: **row 解釈の契約は証明済み。B3 の生成・全 instance solver・公開 Core 統合は未完。**

対象は [前回の結果 §7.5](../handoff/2026-11-07-core-common-coverage-results.md#75-b3-effect-の有限宣言signed-row全称-handler) の
`common_effect_row_interpretation_exact` である。任意の有限 scope 数に対する実 signed row の包含を保存・反映し、
protect / release / residual と可換となる解釈を構成した。型の carrier、既存 `Core.infer`、
`Core.PresenceOnly` 以下の公開 theorem は変更していない。

## 1. 二つの row carrier と実際の写像

`Directed.Occurrence n Nat` は key と `Fin n → Int` の符号付き座標を持つ。
`Directed.Row n Nat` はその有限 list である。一方、`Common.Occurrence` は key と `List Int`、
`Common.Row` はその全 occurrence に対する述語であり、有限集合に限定されない。

`CommonSignedRows.encodeOccurrence` は実座標を `List.ofFn` で書き出す。
末尾のゼロも削らず、座標数 `n` と順序を保持する。
`embedRow` は、元 list に存在する occurrence の像であるという述語を作る。
入力 list の順序と重複は row の意味に影響せず、座標の位置と長さは保持する。

`encodeOccurrence_injective` は任意の `n` と任意二 occurrence について符号化の単射性を示す。
`embedRow_le_iff` は任意 `n` と任意 `r s : Directed.Row n Nat` について、

```text
SignedStructural.RowLe r s ↔ Common.rowLe (embedRow r) (embedRow s)
```

を示す。有限性や正規化済み入力を追加前提にしない。
`embedRow_empty` / `embedRow_join` は任意の同じ scope 数の rows について empty / union と可換である。
像の各 occurrence の長さは必ず `n` であるが、任意の Common row がこの像に入るとは主張しない。

## 2. 任意 Common row に作用する可逆な transport

`shiftOccurrence scope permission delta` は、既存座標のうち index が `scope` であり、
key が許可されていない位置だけに整数 `delta` を加える。
key と list 長は保持する。指定 index が存在しない occurrence はそのままにする。
この定義は、同じ長さの occurrence の集合上で、`delta` と `-delta` が互いの逆になる。

`transport` はその逆写像による row の引き戻しとして定義し、
`transport_member_iff` で順写像の像による定義と同じことを示す。
`commonProtect` は `delta = 1`、`commonRelease` は `delta = -1` である。

以下には有限 row、固定長、非負座標、solver 成功の前提がない。

```text
任意 scope : Nat、permission : Nat → Bool、delta : Int、row : Common.Row,
  transport scope permission (-delta) (transport scope permission delta row) = row

任意 scope : Nat、permission : Nat → Bool、row : Common.Row,
  commonRelease scope permission (commonProtect scope permission row) = row
  commonProtect scope permission (commonRelease scope permission row) = row
```

実 finite signed 側との可換性は、任意 `n`、`scope : Fin n`、permission、delta、signed row に対して示す。
この場合は全 occurrence が該当する座標を持つため、上の「存在しない index」の規約は関与しない。

**内部の選択と代案。** 任意長の occurrence に不足座標を zero-padding する案は、
既存 Common occurrence の文字どおりの同一性を変え、単純な逆変換で元の長さを回収できない。
今回は長さを保つ全域作用を使い、実 scope vector との関係を別 theorem にした。
この選択は、将来の source scope 割当て・fresh 化・潜在 closure の衛生性を証明済みにするものではない。
任意の Common parameter を有限 `Directed.Row n Nat` として decode する仮定も加えない。

## 3. residual と閉じた row 解釈の契約

`Capturable handled occurrence` は、key が handled list に含まれ、かつ全座標がゼロであること。
`commonResidual handled row` はその occurrence だけを取り除く。
負の座標をゼロに丸めたり、正の座標だけを残したりしない。

`encode_capturable_iff` と `embedRow_residual` は、任意 `n`、handled list、signed occurrence / row に対し、
既存 `Directed.Capturable` / `Directed.residual` とこの定義が一致することを示す。

### `CommonSignedRows.common_effect_row_interpretation_exact`

任意 `n : Nat`、`r s : Directed.Row n Nat`、`scope : Fin n`、`permission : Nat → Bool`、
`handled : List Nat` について、追加前提なしに次の四つが同時に成り立つ。

```text
(SignedStructural.RowLe r s ↔ Common.rowLe (embedRow r) (embedRow s))
∧ embedRow (r.map (Directed.protect scope permission))
    = commonProtect scope.val permission (embedRow r)
∧ embedRow (r.map (Directed.release scope permission))
    = commonRelease scope.val permission (embedRow r)
∧ embedRow (Directed.residual handled r) = commonResidual handled (embedRow r)
```

scope が存在しない `n = 0` に対しても、個別の包含・empty・join・residual の theorem は適用できる。
protect / release の scope 引数を存在しないところから作る主張ではない。

`nonzero_retained` は任意 handled list、任意 Common row、そこに属する occurrence、
その座標 list に属する任意の非ゼロ整数について、residual 後もその occurrence が属することを示す。
前提は元の membership、座標の membership、非ゼロ性の三つだけで、負の整数も含む。

## 4. 任意の有限 row 式への拡張

`commonAlgebra n : RowInference.RowAlgebra Nat (Fin n)` は、上の全 Common.Row carrier と作用を使う。
operation head は `n` 個のゼロ座標を持つ raw occurrence の埋込みである。

`rowExpr_interpretation_exact` は任意の型 `α`、`n`、
`assignment : α → Directed.Row n Nat`、`expression : RowExpr Nat (Fin n) α` について、

```text
embedRow (expression.eval (signedAlgebra n Nat) assignment)
  = expression.eval (commonAlgebra n) (fun name => embedRow (assignment name))
```

を示す。全 finite row 式の var / empty / head / union / protect / release / residual を扱う。
同じ全量化で任意二式を取る `rowExpr_le_exact` は、評価後の signed 包含と Common 包含を iff で結ぶ。
assignments を任意 Common row に広げたときも commonAlgebra の演算自体は定義済みだが、
finite signed 側への全射性や solver の完全性をこの theorem から結論しない。

後続の [有限 operation 宣言と request 生成](2026-11-07-common-effect-request-generation.md) は、この Common 行代数を用い、local 型を存在量化する request 一段の実有限生成を独立 Typing へ接続した。全称 handler と全 instance solver はその追加後も未完である。

## 5. 残る B3 契約と作業順

この row 解釈は nominal / pattern の本体と独立なので、B5・B2 と並行して先に閉じた。
未完だった原 statement の量化子を縮めず、そのうち独立した一つを完了できるためである。

`generate_common_effect_finite_exact` は依然として、任意の有限検証済み operation 宣言、
関連する symbolic / semantic 環境、任意の式・出力・割当てについて、
独立 Common effect Typing iff 実有限 Formula の充足を要求する。
有限な row 解釈だけでは、operation-local 多相と全 handler を持つ有限生成を供給しない。
handler の量化順は `∃ outer input/result, ∀ local assignment, ∃ arm result` のまま保つ必要がある。

`solve_common_effect_all_instances_exact` は、任意の実生成問題と任意の独立 rows / 全 node values に対し、
Models iff 実返却 scheme の無制約 parameters が同じ rows / 要求同値な全 values を回収すること、
および任意返却 scheme・任意 parameters の Models を要求する。
transform の循環による符号付き座標の増大は、source slot の有限性だけでは有限列挙へ落とせない。
全称 handler の検査や行の残余条件を自由 parameter の前提として残さない solver が必要である。

effect 注釈の見える部分は spec 5.5 の一規則に従い、binding/SCC の一般化前に検査する方針を維持する。
今回の row 基礎は E7（`x | catch:` の左辺 effect）の結論を必要としない。
新しい `notes/questions/` はない。
