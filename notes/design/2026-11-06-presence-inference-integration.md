# Presence 型と required-field 主型推論の統合

状態: **Draft（実装・証明の工程案）**
日付: 2026-11-06
範囲: 決定44の presence 型を、既存の自由 parameter を持つ推論器へ接続する。
正本: `spec/04-types.md` 4.3、決定38〜40・44。新しい言語仕様の決定は含まない。

## 1. 出発点と、同一視しないもの

| 層 | 入力・結果 | 現在の正確性 |
| --- | --- | --- |
| `SourcePrincipalInference` | 閉じた `Inference.Expr` → regular な型・行の自由 parameter scheme の有限列 | 行順序の反対称性と `supported e = true` の下で、全 instance と元の `Inference.Typing` が同値 |
| `PresenceDataInference` | data 式 → 有限の exact `Shape` | 任意の意味的述語 `T` への型付けと、推論した exact 型の `T` への包含が同値 |
| `PresenceDataSafety` | 独立な presence 型付けと、その環境を満たす値の列 | 実際の `SourceDataRuntime.eval` が成功し、返り値が型を満たす |
| `PresenceDataCompatibility` | exact 環境の descriptor と同じ source 式 | `synth` と `eval` の成功結果が一致する。型付け・推論成功を前提にしない |
| `PresenceLegacyBridge` | 有限 legacy 型と、隠す field 名の有限列 | 既存の data 意味を required/presence 述語へ構成的に翻訳し、包含と data 型付けを移す |

`Shape.denote` は `exact shape.value` である。現在の値の literal は base tag なので、
これは「任意の整数値を持つ source 全体の主型」ではなく、既存 data 値の exact descriptor である。
`SourcePrincipalInference` の自由 parameter と regular block はこの descriptor に潰さない。
両者の主型が等しいとは、現時点でも統合後の目標としても無条件には主張しない。

`SourcePrincipalInference.infer` の `requiredFieldsOnly` gate は維持する。
実際のsupport判定はこのgateと生成clauseのsupportの連言である。`RecordFree` はその十分条件であり、
`RecordFree`でない式を一律に拒否する必要条件ではない。
`recordDefault` を含む入力の `.unsupported` は、型エラーを意味する `.rejected` と区別する。

## 2. この段階で閉じた橋

新しい `PresenceLegacyBridge.translate T hidden` は、次のように既存の型構築子を翻訳する。

- base・pair・variant・union・intersection は対応する presence 述語へ写す。
- legacy の width 型 `{}` は `records` へ写す。`exactEmpty` へは写さない。
- `record l A R` は、見える `l` の `required l A` と、`l` を隠した `R` の要求の共通部分へ写す。
- 隠れた同名 field は要求を足さない。mask は union/intersection を含む tail の内部にも渡す。
- arrow は data 値を持たないため `never` へ写す。これは closure の意味ではない。

`translate_exact` は任意の有限 legacy 型 `T`、任意の `hidden : List Nat`、任意の runtime 値 `v` について、
翻訳後の所属と `DataTypeSemantics.Holds T (· ∈ hidden) v` が同値であることを示す。
`shadow_subtype_preserved` は、任意の Shadow 部分型導出と mask について、翻訳した述語間の包含を導く。
逆向きの部分型完全性は主張しない。

`closed_typing_translates` は任意の行代数、閉じた supported data 式、raw Shadow 型判断について、
同じ式の presence 型判断を、翻訳した返り値型で構成する。評価成功は仮定ではない。
`legacy_data_plan_translates` は、`RigidRecordValueInference.infer e = .inferred p` なら、
一つの新しい推論結果 `s` が存在し、**すべての** `p.Parameters (Ty Row)` について
`s.denote ≤ translate (p.evaluate parameter) []` を示す。
この `p` は finite-data 推論器の plan であり、`SourcePrincipalInference` の regular scheme と混同しない。

## 3. Presence を失わない制約表現

内部表現では少なくとも `required l A`、`optional l A`、`lacks l` を区別する。
`lacks` の内部使用は、新しい surface 構文を追加する提案ではない。
既存の述語定義だけから、次の二つを `PresenceLegacyBridge` で証明した。

```text
∀ l A v, optional l A v ↔ lacks l v ∨ required l A v
∀ l v, optional l never v ↔ lacks l v
```

実装案は、presence の選択肢と payload の制約を有限の選言として保持する形である。
これは solver の表現案であり、自由 parameter を有限個の値へ制限する案ではない。
`l` がある枝とない枝で異なる他 field の制約があるとき、その相関を捨てない。
required/optional の印だけを各 field へ別々に射影すると、相関を失う可能性がある。

必要な証明は、表現の所属判定が独立な述語に正確であること、union/intersection と mask が意味を保つこと、
同じ field が後ろで隠れたときに payload の制約が残らないことである。
既存 required-field fragment に対しては、翻訳の保存と反映を別々に示す。

## 4. 制約生成と評価順

`recordDefault l source fallback` の source を `optional l A`、fallback を `B` で制約する。
結果の `l` は `A | B` で上から押さえられるが、これは record 全体の主型ではない。
他 field の要求・存在情報も保持した `recordDefault` の意味的 image が先に必要になる。
`PresenceDataSafety.optional_operator_principal` は、その image の全 target への包含と型判断を同値にする。
これを `required l (A | B)` だけへ置き換えると、既存の主張を弱めることになる。

source と fallback の両方の型付け・effect を生成する。source に `l` があるときでも、
record 構築の fallback 式は評価される（決定42・43）。
record **pattern** の default は field がないときだけ評価される（`spec/03b` 3b.3）。
二つの規則を同じ「default」constructor の単純な読み替えで統合しない。

生成器についての目標は、任意の対応する環境、型・行の割当て、結果型・行に対し、
拡張した生成制約の充足と独立な presence 型判断が同値になることである。
旧 fragment では元の `principal_exact` を保ち、既存の value-let の全選択肢と captured slot を残す。

## 5. Regular solver への接続

`JointConstraintInference.model` は `RegularInferenceModel` を使う。
有限 data 型の `translate_exact` だけでは、この model の regular block・関数・行の意味は与えられない。
その段差を次の順で埋める。

1. presence を保持する有限 layer と mask の操作を定義し、有限観測の意味との保存・反映を証明する。
2. block の展開・graph embedding に対して、その意味が不変であることを示す。
3. presence 制約を含む有限 alternative の飽和と解の抽出を証明する。各 free parameter は任意に選べるままにする。
4. alternative の列をまとめる `collect` の exactness を再利用または保守的に拡張する。
5. 旧入力を埋め込んだ場合の全 instance の保存・反映を示し、その後で新しい入口を公開する。

最終の solver 定理では、任意の行代数に加え、既存定理と同じ行順序の反対称性を明示する。
任意の入力 `e`、`supportedPresence e = true`、任意の結果 `c` に対して、
`(inferPresence e).Instance c ↔ PresenceTyping [] e c` を示す。
`.rejected` と「型判断を持たない」の同値も、同じ support 範囲で証明する。
regular/function/effect の interpreter を与える前に、arrow の空の data 意味で安全性を済ませない。

## 6. 必須の反例と比較対象

| 入力情報・式 | 保持する事実 |
| --- | --- |
| legacy `{}` と値 `{x: "text"}` | `{}` は満たすが、`lacks x` でも `optional x int` でもない |
| exact `{}` と default `x: int` | `x` は absent と確定し、結果は fallback の型で要求できる |
| `x?: A` と default `x: B` | present/absent の両枝を残し、結果の `x` は `A | B` に入る |
| `{x:A, x:B, ..R}` | 任意の非rigidな `R` に対して、隠れた `B` は型要求からも消える |
| 使われない record default の effect | 値で採用されなくても、構築時の effect と訪問順は残る |
| optional 構文を旧入口へ渡す | `.unsupported`。`.rejected` に変えない |

`records_not_le_lacks`、`records_not_le_exactEmpty`、`records_not_le_optional_int` が最初の境界を既に証明している。
`PresenceLegacyBridge.legacy_emptyRecord_not_absence` も、翻訳した旧型に対して同じ境界を明示する。
これらの反例を消すために、旧 `{}` の意味や既存定理の量化子を変更しない。

## 7. 完了条件

当面の完了単位は、有限 required demand の翻訳、presence layer の exactness、
regular block の移送、拡張制約生成、拡張 solver の全 instance、実行への接続で分ける。
今回閉じたのは最初の翻訳と closed supported data 型判断の移送である。
`SourcePrincipalInference` 全体への統合、関数を含む runtime interpretation、
Rust の構文・型推論器との対応は引き続き証明義務として残す。
