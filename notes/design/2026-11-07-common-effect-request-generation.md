# Common の有限 operation 宣言と request 生成

日付: 2026-11-07。状態: **Draft — request 一段の有限生成と独立判断の同値は kernel 検査済み。再帰的 effect 生成・solver・公開入口は未完。**

対象コード: `lean/Yulang/CommonEffectRequestGeneration.lean`。
全体の目標は [effect / role / nominal 統合の残る契約](2026-11-07-common-effect-role-nominal-contracts.md) §3.3 と、
[前回の引継ぎ](../handoff/2026-11-07-core-common-coverage-results.md) §7.5 の
`generate_common_effect_finite_exact` である。以下の request 定理は別名の独立した進捗であり、
その全 statement を置き換えない。

## 1. 今回閉じた境界

有限な型構文で記述した operation の payload と response を、実際の Common carrier で解釈する。
operation-local な型変数は呼出しごとに任意の `Common.Ty` へ具体化する。
payload の型検査には既存の `PresenceGeneration.generate` を実際に呼び、
独立の `PresenceGeneration.Typing Common.model` との対応を使う。
このため exact empty、required field、strict default と、捕捉した polymorphic binding を含む。

生成結果は inductive な有限 `Constraint` である。葉は有限な既存 presence formula と有限行式の包含だけであり、
Typing、任意の `Comp → Prop`、意味的な signature 関数、solver 成功を格納しない。
入力の宣言を型付け判断の別名として包んだ実装ではない。

ただし payload の文法は `Inference.Expr` である。任意の λ/application/let/branch/record/default などを含められるが、
request/handler を payload 内に再帰的に書く Core effect 文法ではない。
新しい `Core.Expr` の受理範囲を増やしたわけではなく、`Core.infer` と既存の公開定理を変更していない。

## 2. 有限宣言と table identity

`Declaration α` は次の有限データを持つ。

| 欄 | 内容 |
| --- | --- |
| `locals : Nat` | operation-local な型 slot 数 |
| `key : Nat` | この operation が送出する解決済み occurrence key |
| `extra : List Nat` | 追加で送出する有限 key 列 |
| `input : TyTerm (α ⊕ Fin locals)` | payload の有限 presence 型構文 |
| `output : TyTerm (α ⊕ Fin locals)` | response の有限 presence 型構文 |

`α` は捕捉された ambient slot の型であり、その各値は型と行の組である。
`Sum.inl` は ambient slot、`Sum.inr` は local 型 slot を表す。
`α` 自体が有限であるとは仮定しないが、各 declaration 本体は有限構文なので参照箇所は有限である。
`localEnv` は ambient 割当てをそのまま保持し、local slot の行成分を常に空行にする。
local に新しい行 parameter を選ばせない。

これは resolved declaration の中間表現であり、Yulang の全宣言構文を parser から変換した結果だという定理ではない。
family 引数と operation identity から `Nat` key を作る名前解決、可視性、alias、role 義務はここでは生成しない。
型本体には presence generator の全有限 `TyTerm` 構成子が使えるが、それぞれを source の宣言位置で直接記述できると主張するものでもない。

`Declarations α` は declaration の有限 list である。
`generateDeclared` の `operation : Nat` は **その table 内の位置**であり、
送出される `declaration.key` とは別の識別子である。
実際に `declarations[operation]?` を計算し、範囲外なら `.core .bot` を返す。

重複する `key`、同じ内容の declaration、重複する `extra` は禁止していない。
table position による lookup は一つの declaration を決めるので、ここに曖昧性の選択はない。
同じ key を持つ複数 declaration の input/output が整合するという検証もしていない。
後で key から handler signature を引くには、その整合性を別に扱う必要がある。
実 registry の名前解決や重複検証をこの lookup の定理で代用しない。

## 3. 検証する内容

`rowWellKinded` は行位置に operation-local な型 slot が現れないことを検査する。
ambient 行 slot、空行、行の union は許す。
`typeWellKinded` は有限型構文を再帰し、arrow の incoming/outgoing 行にもこの検査を行う。
`Declaration.wellKinded` は input/output 両方、`Declarations.wellKinded` は table 全体を検査する。

`checkAndGenerate` はこの table 全体の Bool 検査を実行してから lookup と生成へ進む。
したがって今回使わない entry がこの検査に失敗していても拒否する。
成功の意味はこの値/行 kind の区別だけであり、以下は含まない。

- key の一意性、宣言名、scope/可視性、family 引数の well-formedness。
- operation-local な role 義務とその dictionary。
- handler の permission と hygiene、operation payload pattern の coverage。
- 注釈で見える effect の取得と検査。
- 任意の制約の satisfiability、solver 成功、runtime safety。

未検査の raw declaration についても、型構文の評価自体には意味がある。
そのため `generate_request_exact` と `generate_declared_request_exact` は kind 検査成功すら前提にしない。
raw input を受ける checked entry の theorem は、kind 検査成功を結論の右辺に明示する。
これを全宣言の `D.Valid` が実装済みであるとは呼ばない。

## 4. 型と行の意味

scope 数 `scopes : Nat` は宣言側の有限座標 interface である。
生の operation head は `CommonSignedRows.commonAlgebra scopes` により、
その長さの全ゼロ重みを持つ occurrence に解釈する。
`scopes = 0` の場合も含む。

一方、ambient 行・payload 行・出力行はすべて **任意の `Common.Row`** である。
有限 list として表せること、occurrence の全重み列が同じ長さであること、有限個の key しか含まないことは仮定しない。
有限 scope interface の head を使うことと、自由な行 parameter の carrier を有限行に制限することは別である。

新しい `RowExpr scopes α` は var/empty/head/union/protect/release/residual の有限構文を持つ。
protect/release の mask は任意関数ではなく、`Permission.all` または `Permission.only keys` という有限構文である。
`all` は table に出ない key も許す。自由な行 parameter に後から入る key を列挙済みのものに制限しない。
解釈には実 `CommonSignedRows.commonProtect` / `commonRelease` / `commonResidual` を使う。
今回の request 生成が実際に出す行式は var/head/union と出力の元の行式だけであり、
protect/release/residual の source 生成を完了したという意味ではない。

spec 5.1 に従い、request の行は

```text
payloadRow ∪ ownHead ∪ extraHeads
```

を出力行以下に要求する。`extra` を own key の置換にしない。
request ごとの local 型は自由に選べるが、ambient 型/行、元環境、出力型/行はその外で固定する。

## 5. 証明した theorem の全量化と前提

以下、`Comp := PresenceGeneration.Comp Common.model`、
`out.eval ρ := out.eval Common.model ρ` と略記する。
`EnvRel` は元の presence generator のものをそのまま使い、
任意 lookup index と任意 computation に対する symbolic scheme と independent binding の instance の一致を表す。

### `generate_request_exact`

任意の `scopes : Nat`、任意の ambient index 型 `α : Type`、
任意の `sΓ : SchemeEnv α`、`Γ : List (Binding Common.model)`、`ρ : α → Comp`、
`EnvRel Common.model ρ sΓ Γ`、任意の有限 `d : Declaration α`、
任意の `payload : Inference.Expr`、任意の `out : CompTerm α` について、

```text
(generateRequest sΓ d payload out).Holds ρ
  ↔ RequestTyping scopes ρ d Γ payload (out.eval ρ)
```

が成立する。右辺の独立 request rule は、ある任意 Common 型割当て
`ι : Fin d.locals → Common.Ty` と、ある任意 `payloadRow : Common.Row` が存在して、
次の三つが同時に成立するという判断である。

1. 元の同じ環境 `Γ` で payload が `(d.input.eval (localEnv ρ ι), payloadRow)` に型付く。
2. `d.output.eval (localEnv ρ ι)` が `out.eval ρ` の値成分以下である。
3. `payloadRow ∪ ownHead d.key ∪ extraHeads d.extra` が `out.eval ρ` の行成分以下である。

生成器は `.existsTypes d.locals` の内側に `.existsSlot` を置き、payload の実生成 formula と二つの比較を出す。
solver 成功、support、fuel、closed cache、既知の Typing、有限な行表現を前提にしない。
kind 検査成功もこの theorem の前提ではない。

### `generate_declared_request_exact`

任意の `scopes, α, sΓ, Γ, ρ` と上と同じ `EnvRel`、
任意の有限 table `D : Declarations α`、任意 `operation : Nat`、
任意 `payload : Inference.Expr`、任意 `out : CompTerm α` について、

```text
(generateDeclared sΓ D operation payload out).Holds ρ
  ↔ DeclaredRequestTyping scopes ρ D Γ operation payload (out.eval ρ)
```

が成立する。右辺は実 table lookup で得られる declaration と、その独立 `RequestTyping` を要求する。
lookup 成功を前提にしない。見つからない場合は両辺とも偽になる。
table の key の一意性や kind 検査成功を仮定しない。

### `checked_request_exact`

任意の `scopes, α, sΓ, Γ, ρ, D, operation, payload, out` と、
上と同じ `EnvRel Common.model ρ sΓ Γ` について、

```text
(checkAndGenerate sΓ D operation payload out).Holds ρ
  ↔ D.wellKinded = true
    ∧ DeclaredRequestTyping scopes ρ D Γ operation payload (out.eval ρ)
```

が成立する。raw table の kind 検査と lookup を実際に計算する。
この theorem も検査成功を呼出し側の前提には置かない。

3 theorem とも `--trust=0` に通り、`#print axioms` は `propext`, `Quot.sound` のみである。
新しい公理、`sorry`、`native_decide` は使っていない。

## 6. 元の B3 全契約との差と次の不足補題

### 再帰的な source generation

`generate_common_effect_finite_exact` が求めるのは、effect を含む同じ source 文法の任意の式・環境・出力・割当てに対する iff である。
今回の payload は任意 presence 式だが、その中に request、boundary、handler を入れられない。
value-let が捕捉する scheme も既存 presence formula である。
effect formula を捕捉・rename・instantiate しながら同じ新 source 文法を再帰する generator と、
その独立 Common judgment の対応が不足している。

### handler の全称

`Constraint.forallTypes` の有限構文と意味は定義したが、handler の formula は生成していない。
必要な statement は、元の同じ環境と最終結果を固定して、

```text
∃ actionInput, ∃ returnResult,
  action と return arm の型付け
  ∧ ∀ operation-local type assignment,
      ∃ operationArmResult,
        arm の型付け ∧ 値比較 ∧ 残余行比較
```

を有限構文で生成し、独立 handler rule と同値にするものである。
local 型ごとに outer environment/action input/final output を取り替えず、
shallow resumption の出力には減算前の元 action computation を使う。
複数 arm と payload coverage に基づく減算も未接続である。

### permission と spec 5.5

`Permission` は有限な mask の表現であり、source の注釈から handler permission を計算した結果だという証明はない。
request の3 theorem は permission を使わない。
spec 5.5 の「明示的に見える effect を検査する」という一つの規則、
および spec 5.5b の binding/SCC 推論完了時・一般化直前の検査を実装したものではない。
任意の permission 関数を theorem の前提に置いてこの欠落を埋めることもしない。

残る補題は、有限な注釈・origin 情報と同じ宣言を使って visible effect と permission を計算し、
その値が独立した静的規則に一致すること。
source の順序や後の具体化によって注釈を再検査する別規則に置き換えない。
E7 の `x | catch:` の到達問題は、この request 一段では新しく決定していない。

### solved families と公開入口

有限 formula の Holds と Typing の iff は、formula の全 Models を無条件の自由 parameter family にする theorem ではない。
signed row transforms、全称 local、宣言由来の制約を実 solver に渡し、
元の任意 Common rows と全 node values を同じ行・要求同値な値として回収する
`solve_common_effect_all_instances_exact` は未閉である。
返却された任意 scheme の任意 parameter の健全性と、rejected iff 型付け不存在も effect について未接続。
今回の theorem から「新しい Core effect source を受理した」「B3 が完了した」とは報告しない。

今回、新しい `notes/questions/` の問いは追加していない。
finite syntax、table position、kind checker の内部モデルを明示し、未実装の仕様を追加決定していない。
