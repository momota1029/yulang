# Common pattern 環境橋の小段階（B2・2026-11-07）

## 1. 到達点と元の目標

B2 は **部分**。`CommonPatternEnvironment.lean` と `CommonPatternDefaults.lean` は、
任意の元環境を保持する環境拡張と、default pattern の入力型を作る前提の有限生成を示す。
続く `CommonPatternLookup.lean` と `CommonPatternTyping.lean` は、Common の観測から実データの
shape / field lookup を反映し、独立した構造 pattern 判断から実 scoped matcher の結果束縛の型付けを示す。
後者は default 実行に外部の全環境成功契約を仮定する補助定理であり、一般の型付いた default が必ず成功・
停止するという目標ではない。全 pattern の source generator と実照合結果を結ぶ iff、実行結果と行の
対応、ordered coverage、および公開 solver 契約への接続はまだ閉じていない。
`Core.Expr` / `Core.infer` の構成子はこの変更で増えない。旧定理は変更しない。

元の handoff §7.4 の目標はそのまま残る。

> 必要な `common_pattern_environment_exact` は、任意の対象 pattern（default 式を含む）、任意の元環境、
> 任意の subject 型・実照合値・照合結果束縛について、元の binder 順序/共有/presence を保った
> Common 環境の有限制約と独立 pattern judgment の iff。
> default は Q4 の累積環境で型付ける。名前 binder を一般化しない。

> 必要な `generate_common_case_exact` は、任意の finite arms と任意 subject/guard/body、任意の結果について、
> source の first-match 順序・guard・default 評価・失敗行を含む独立 Common case Typing iff 実有限制約。
> その全 Models を任意 parameter の solved list に変換し、§2 の公開三契約へ接続する。

環境橋は nominal/list/handler の実装に依存しないため、B5 の全体が閉じる前に進めた。
独立しているこの部分を完了済みの全 B2 と呼ばない。

## 2. 証明済みの全称命題

以下の `Comp`、`Typing`、`EnvRel`、`generate` は `Core.PresenceGeneration` のもの。
`EnvRel` は、全 lexical index と全 value/row computation について、symbolic scheme lookup と
独立した semantic binding lookup の instance が一致する関係である。

### `CommonPatternEnvironment.monomorphic_prefix_environment_exact`

任意の型 `α`、割当て `ρ : α → Comp Common.model`、
名前付き型参照列 `bindings : List (Nat × TyTerm α)`、symbolic 環境 `symbolic`、
semantic 環境 `semantic` に対し、`EnvRel Common.model ρ symbolic semantic` を仮定すると、

```lean
EnvRel Common.model ρ (symbolicPrefix bindings ++ symbolic)
  (semanticPrefix (evalTypes ρ bindings) ++ semantic)
```

が成立する。元の名前の順序、同じ参照の共有、外側の captured polymorphic scheme を変えない。
追加した各 binder は `mono (pure type)` であり、値か否かによる一般化を行わない。
型参照自身の推論や、実 matcher の返した bindings がこれらの型を持つことは仮定から構成していない。

### `CommonPatternEnvironment.cumulative_default_generation_exact`

上と同じ任意の `α, ρ, bindings, symbolic, semantic` と同じ `EnvRel` 前提について、
さらに任意の `fallback : Inference.Expr`、`result : CompTerm α` に対し、

```lean
(generate (symbolicPrefix bindings ++ symbolic) fallback result).Holds Common.model ρ ↔
  Typing Common.model (semanticPrefix (evalTypes ρ bindings) ++ semantic)
    fallback (result.eval Common.model ρ)
```

が成立する。Q4 に従い、default より前に作った bindings を元環境の前に置く。
空の prefix だけでなく任意長を扱う。free parameter の閉性・成功・残余条件を仮定しない。
`fallback` の範囲は現在の `Inference.Expr` 全体であり、将来の effect/role/case 構成子の追加を意味しない。

### `CommonPatternDefaults.optional_constraints_exact`

任意の型 `α`、任意の `ρ : α → Comp Common.model`、`label : Nat`、
`source payload : TyTerm α` に対し、

```lean
(optionalConstraints label source payload).Holds Common.model ρ ↔
  CommonDefaultRequired.OptionalPayload label
    (source.eval Common.model ρ) (payload.eval Common.model ρ)
```

が成立する。生成式は、`⊤ ≤ payload ∧ source ≤ {..}` または
`source ≤ exactEmpty ∪ required(label,payload)` という二つの有限な枝だけを持つ。
`OptionalPayload` や Typing を新しい formula atom として埋め込まない。

### `CommonPatternDefaults.default_input_generation_exact`

任意の型 `α`、`ρ : α → Comp Common.model`、symbolic 環境 `symbolic`、
semantic 環境 `semantic` について `EnvRel Common.model ρ symbolic semantic` を仮定する。
任意の `label : Nat`、`source : TyTerm α`、`fallback : Inference.Expr`、
`result : CompTerm α` に対し、

```lean
(generateDefaultInput symbolic label source fallback result).Holds Common.model ρ ↔
  DefaultInputTyping semantic label (source.eval Common.model ρ) fallback
    (result.eval Common.model ρ)
```

が成立する。独立 judgment `DefaultInputTyping Γ label source fallback result` は、
ある Common 型 `payload` とある computation `fallbackResult` が存在し、次の三つが成り立つことを
一つの inductive constructor で要求する。

1. `OptionalPayload label source payload`。
2. `Typing Common.model Γ fallback fallbackResult`。
3. `(payload ∪ fallbackResult.value, fallbackResult.row) ≤ result`。

生成側は payload と fallback computation の二つの existential slot を作り、既存 generator と
通常の型・行不等式だけを使う。payload slot の row は未使用で、逆方向では empty row を選ぶ。
この選択は free parameter を制限しない。`symbolicPrefix bindings ++ symbolic` を環境に与え、
最初の環境橋を使えば Q4 の累積環境で同じ命題を適用できる。

これは default の入力型を作る **前提** の exactness である。required と default の併記が
source 上合法かという presence 検査、実 matcher の条件付き評価、残りの pattern の推論、
case 全体の失敗行はまだ主張しない。fallback の行はその計算が起こりうる場合の静的な上界であり、
実行時に present field の fallback も評価するという意味ではない。

## 3. 内部モデル上の選択と代案

- **順序は `prefix ++ outer` のまま保持する。** 現在の scoped matcher と Typing が、左の pattern が
  作った binding 列をその順で右の pattern / default の環境へ追加するためである。prefix を reverse
  する案は lexical index の意味を変え、別途 renaming 定理が必要になる。今回は採用しない。
- **名前付き列から positional 環境へ写す。** 名前は `evalTypes` に残し、SchemeEnv に写す時にのみ
  消える。`evalTypes_names` と append の補題で名前と連結順を保存する。source の重複 binder 検査や
  or-pattern の整列はこの橋に押し込まない。
- **optional を一つの union 上界に置換しない。** 任意の payload が top の場合、constructor depth 0
  の観測を保存するには width record の枝が必要になる。既存の
  `CommonOptionalBound.width_not_below_guarded_top` が単一枝案の反例である。
- **strict record default と pattern default を区別する。** 前者の `recordDefault` はレコード全体の型を
  作る操作で、後者は lookup した payload または absent 時の fallback を子 pattern に渡す。
  今回は `OptionalPayload` と fallback の union を用い、whole-record default へ lower しない。
- **実行時の集合型を Common 型そのものとはしない。** `CaseValues.Ty` は runtime value の述語、Common
  は有限 demand 観測の順序である。両者を定義上同一にすると exactness が自明化し、masking と
  presence の意味が失われる。既存の `Core.PresenceMaskObstructions.no_extensional_mask` が
  runtime 集合の等しさだけで mask を定義する案の障害を示す。

この範囲で新しいユーザー判断は必要ない。既存の言語の意味を選び直していない。

## 4. 閉じていない補題（handoff §7.4 の粒度）

### `common_pattern_environment_exact` — 未完

必要なのは、任意の対象 pattern（default 式を含む）、任意の元環境、任意の subject 型・実照合値・
照合結果束縛に対し、元の binder 順序/共有/presence を保った Common 環境の有限制約と独立 pattern
judgment の iff である。前提に solver success、closed cache、fuel、追加の支持条件を置かない。

現在閉じた橋の入力は **既に与えられた任意の型参照列** であり、pattern の構文と matcher の結果から
その型参照列を構成し、全 Common model を回収する補題がまだない。具体的には次が残る。

1. **構造 pattern の独立 Common 判断と実照合の橋の残り。** 本メモ §6–§7 の追記で、Common 型の独立
   `CommonPatternTyping.Typing` と実 scoped matcher の soundness は、明示した構造規則と外部
   `DefaultSound` 契約の範囲で閉じた。任意の元環境・subject Common 型・実 subject 値を扱い、実 matcher
   の結果の binder 順序と値の型付けを保存する。ただし、この judgment の導出を実 finite generator から
   作る iff はない。全言語の実行との橋では、default の return/error と実 trace を値型・宣言行に結ぶ
   部分正当性の契約へ matcher theorem を拡張する必要がある。現在の `DefaultSound` を全 default に
   要求するのではない。既存の `ScopedCasePatterns.Typing` を定義上 Common 型へ同一視した証明ではない。
2. **その判断の有限生成の逆方向。** 任意の pattern 導出に現れる全 payload / record / branch 型 witness
   を一つの共有 slot 割当てとして実 generator の clause へ回収し、同名 binder の共有と or-branch の
   出力環境を保持すること。固定 annotation の checker の iff だけではこの逆方向を代用できない。
3. **presence metadata の橋。** 任意の source field/default annotation の合法性と、元の record の presence
   要求を保存する有限制約との対応。今回の OptionalPayload の exactness だけでは required/default
   併記の source 検査を含まない。
4. **残る構成子との接続。** nominal/list pattern は B5 の nominal identity と invariant parameter、
   effectful default は B3 の見える行の解釈との接続を要する。構造部分の環境拡張自体はこれらを待たない。

次は、§7 の独立構造 judgment に対する実 finite generation の iff と、default の実行が返した値・許された
error・trace を型と行へ結ぶ部分正当性の橋を閉じる。後者は成功・停止を一律に要求せず、matcher の
return/miss/error を扱う定理への拡張を伴う。逆方向では 2 の共有 allocator / witness 回収が必要になる。
最初の環境橋と default 入力の生成定理を再利用できるが、これらをつなぐだけで allocator の完全性が
得られたとは扱わない。

### `generate_common_case_exact` — 未着手

必要なのは、任意の finite arms、任意の subject/guard/body、任意の結果について、first-match 順序、
guard、条件付き default 評価、失敗行を含む独立 Common case Typing iff 実有限制約である。
さらに全 Models を任意 parameter の solved list に変換し、公開 principality / all-parameter soundness /
rejected iff を接続する。単一 name arm の既存 lowering や今回の default-input rule はこれを代用しない。

## 5. 検証と統合

四つのモジュールを Lean 4.35.0 の `--trust=0 -DwarningAsError=true` で検証した。
既存 import の olean は同じ baseline の検証済み build を読取り利用し、新しい出力は独立した作業領域に
出した。全体 `lake build --wfail` と `Audit.lean` は integration 側で実行する。
追加する import は `Yulang.CommonPatternEnvironment`、`Yulang.CommonPatternDefaults`、
`Yulang.CommonPatternLookup`、`Yulang.CommonPatternTyping`。
Audit 登録対象は本メモ §2、§6、§7 の主要 theorem。新しい公理、`sorry`、`native_decide` はない。


## 6. Common の観測を実データへ反映する追加補題

以下はすべて `CommonPatternLookup` namespace にあり、既存の独立した
`Core.CommonData.ValueTyping Common.model` を用いる。この judgment は literal / pair / 有限 record /
single-tag variant の実データを構成規則で型付け、格納された全 field を検査する。
`Value` は `CaseValues.Value Empty` である。nominal/list/float に新たな型付け規則は足していない。
以下の補題には別途 `covered`、solver の成功、キャッシュ、fuel の前提はない。

### `typing_change_result`

任意の実値 `value : Value`、`source target : Comp Common.model` について、
`ValueTyping Common.model value source` と `Common.Subtype source.1 target.1` を仮定すると、
`ValueTyping Common.model value target` が成り立つ。source と target の行は任意で、その間の包含を
仮定しない。具体的なデータの生成は pure なので、既存導出の行の過大近似を引き継ぐ必要がない。
この補題を一般の計算式に適用して effect を消すことはできない。

### `required_lookup`

任意の `fields : CaseValues.Bindings Empty`、`source : Comp Common.model`、`label : Nat`、
`payload : Common.Ty` について、

```lean
ValueTyping Common.model (.record fields) source
Common.Subtype source.1 (Common.required label payload)
```

を仮定すると、ある実値 `value` が存在して、

```lean
CaseValues.lookup label fields = some value ∧
ValueTyping Common.model value (Comp.pure Common.model payload)
```

が成り立つ。record の重複 label を禁止せず、matcher と同じ最初の一致を返す。
任意の regular / lattice / masked 型を含む source と payload に対して成り立つ。

### `optional_lookup`

任意の `fields`、`source`、`label`、`payload`、実値 `value` について、

```lean
ValueTyping Common.model (.record fields) source
OptionalPayload label source.1 payload
CaseValues.lookup label fields = some value
```

を仮定すると、`ValueTyping Common.model value (Comp.pure Common.model payload)` が成り立つ。
lookup の存在はこの補題の前提であり、optional 観測から field の存在を導いたわけではない。
別 label の head をたどる時は、record の既存規則の tail-width 前提から optional-trivial 観測を回収する。

### `records_of_width`

任意の実値 `value` と `source : Comp Common.model` について、
`ValueTyping Common.model value source` と `Common.Subtype source.1 Common.emptyRecord` を仮定すると、
ある `fields` が存在し `value = .record fields`。subject が record であることを事前に仮定しない。

### `pair_components`

任意の実値 `value`、`source : Comp Common.model`、`first last : Common.Ty` について、
`ValueTyping Common.model value source` と `Common.Subtype source.1 (Common.pair first last)` を仮定すると、
ある実値 `left right` が存在して、

```lean
value = .pair left right ∧
ValueTyping Common.model left (Comp.pure Common.model first) ∧
ValueTyping Common.model right (Comp.pure Common.model last)
```

が成り立つ。

### `literal_of_base`

任意の実値 `value`、`source : Comp Common.model`、`scalar : Inference.Base` について、
`ValueTyping Common.model value source` と `Common.Subtype source.1 (.base scalar)` を仮定すると、
ある実 literal `literal` が存在し、`value = .literal literal` かつ
`Core.CommonData.literalBase literal = scalar`。整数・文字列などの格納内容自体を型へ消去していない。

### `variant_payload`

任意の実値 `value`、`source : Comp Common.model`、`tag : Nat`、`payload : Common.Ty` について、
`ValueTyping Common.model value source` と `Common.Subtype source.1 (Common.variant tag payload)` を仮定すると、
ある実値 `item` が存在し、`value = .variant tag item` かつ
`ValueTyping Common.model item (Comp.pure Common.model payload)`。
これは一つの tag の規則であり、複数 tag の variant 行を型の union で表す仮定は置いていない。

## 7. 独立した構造 pattern 判断から実 matcher への橋

### judgment と実行契約

`CommonPatternTyping.Typing DefaultTyped types pattern input bindings` は Common 型を直接使う
inductive judgment である。`Formula.Holds`、solver 成功、matcher 成功を constructor の前提に入れない。
扱う構文は wildcard / bind / literal / intRange / pair / recordEnd / field / defaultField /
single-tag variant / or / as で、任意の Common subtype による narrow 規則もある。
nominal/list/float、複数 tag の variant 行、source の presence annotation の検査はこの判断に含めない。
元の B2 の全 pattern statement をこの部分 judgment に置き換えない。

`valueAt type value` は独立した `ValueTyping Common.model value (pure type)`。
`bindingTypes` は名前付き Common 型の列を、その順序を保ってこれらの値の述語に写す。
Common の型順序を runtime 集合包含で再定義したものではない。shape / lookup は §6 の観測反映で証明する。

`DefaultTyped : NamedTypes → D → Common.Ty → Prop` は外部の独立した型契約であり、
`DefaultSound DefaultTyped defaultEval` は次を **全称に仮定する実行との契約** である。
任意の `types : NamedTypes`、`code : D`、`type : Common.Ty`、`DefaultTyped types code type` と、
任意の実 `environment : CaseValues.Bindings Empty`、
`CaseValues.BindingsHold (bindingTypes types) environment` に対し、ある実 `value` が存在して、

```lean
(defaultEval environment code).result = .ok value ∧ valueAt type value
```

が成り立つ。成功した default の結果だけを条件付きで検査する契約ではなく、型付いた各 default が
すべての許された実環境で成功することを要求する。宣言された error/effect を起こす計算や非停止を許す
言語全体では、source Typing だけからこの契約を一般に導くことはできない。元の B2 も、全 default の
成功・停止を目標にしていない。現在の `defaultEval` の値域 `Logged` は有限の結果を返す関数の
インターフェースであり、このインターフェース自体に非停止の表現はない。

全言語との橋には **部分正当性**、すなわち終了を要求せず、実行が結果を返した場合の値・失敗・観測が
型と宣言行に適合するという契約が必要になる。default が値を返せばその Common 値型と trace を、
error を返せば許された error と trace を行に結び、matcher 側では return/miss/error と、その前に起きた
default/guard の観測を扱う定理へ拡張する。source の実行関係や観測可能な有限実行を使ってこの橋を置き、
非停止から成功結果の存在を要求しない。行と trace/failure の具体的な対応は B3 との接続で残る。

現 `typing_matches` は強い `DefaultSound` を明示的に仮定する補助定理として保持する。
成功・停止・結果の値型が別途保証される適用ではそのまま使える。pure であることだけから停止が従うと
仮定したり、この補助契約を全 default の source typing に追加したりはしない。

### `CommonPatternTyping.Typing.binding_names`

任意の型 `D`、独立な `DefaultTyped`、`types`、`pattern : Pattern Empty D`、`input : Common.Ty`、
`bindings : NamedTypes` と `Typing DefaultTyped types pattern input bindings` の導出について、

```lean
pattern.names = bindings.map Prod.fst
```

が成り立つ。as binder は子より先で、or の両枝は同じ出力 binding 列を要求する。
異なる順序の source or-branch を同じ positional 環境へ整列する elaboration の完全性は未証明。

### `CommonPatternTyping.typing_matches`

任意の型 `D, E, R`、`floatCheck : Empty → Empty → Bool`、
`defaultEval : CaseValues.Bindings Empty → D → Logged E R Value`、独立な `DefaultTyped` について、
`DefaultSound DefaultTyped defaultEval` を仮定する。
任意の `types`、`pattern : Pattern Empty D`、`input : Common.Ty`、`bindings` に対し、
`Typing DefaultTyped types pattern input bindings` の導出を仮定する。
さらに任意の実 `environment` に対して
`CaseValues.BindingsHold (bindingTypes types) environment`、任意の実 `value` に対して
`valueAt input value` を仮定すると、

```lean
CasePatterns.Holds (bindingTypes bindings)
  (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result
```

が成り立つ。`Holds` の意味は、結果が miss なら真、成功なら実 binding 列が宣言列と同じ順序・名前で
各 `valueAt` を満たすこと、error なら偽、である。matcher の成功は前提に置かない。
任意の Common 型が現れてよく、regular 型の制限や solver の成功は仮定しない。

証明は変更していない実 `ScopedCasePatterns.run` を使う。field/default の rest は元の record を受け取り、
後続 component の環境は先行 bindings を元環境の前に置く。present field では fallback を評価せず、
absent field ではその時点の累積環境で fallback を評価する。失敗した or の左枝の bindings は右枝へ漏れない。
`typing_matches` の結論は結果の型付けであり、event trace と effect row の対応を新たに主張しない。

### この段階から先に残る正確な境界

- 実 finite generator と、この独立 pattern judgment の導出を結ぶ iff がない。
- 全言語への実行の橋は、default の return/error と trace を値型・宣言行に結ぶ部分正当性の契約、および
  matcher の return/miss/error を扱う定理への拡張が不足している。`generate_models_iff_typing` から得る
  source Typing だけを使って、現 `DefaultSound` の全環境成功・停止を導くことは一般の義務ではない。
  成功・停止・値型が別に保証された適用では、現 lemma をその限定された用途で再利用できる。
- 逆方向では、任意の pattern 導出と任意の実照合値・結果束縛に対し、source 順序・presence・共有を保つ
  一つの allocator / clause / 全 witness 割当てを回収する必要がある。今回の soundness はその iff ではない。
- source の presence metadata、or-branch の binder 整列、複数 tag の variant 行は未接続。
- effect rows と failure、default / guard の観測、first-match arms 全体の coverage は未接続。
  `DefaultSound` を現在の inference が満たすと暗黙に仮定して公開定理へ接続してはいけない。
- nominal/list は B5、float は B1、effectful default は B3 の残りとも接続する必要がある。

以上の追加は元の §7.4 を閉じていない。B2 は引き続き **部分**であり、公開 principal /
all-parameter soundness / rejected iff の形式・前提・対象構文は変更していない。新しい仕様の問いはない。


### 追記分の直接検証

`CommonPatternLookup.lean` と `CommonPatternTyping.lean` を、上の同じ kernel 設定で再検証し、
どちらも diagnostics なし・終了コード 0。追加した九つの主要 theorem の `#print axioms` は
`propext`、`Quot.sound`、一部で `Classical.choice` のみだった。これは局所的な依存確認であり、
integration 側の `lake build --wfail` と `lake env lean --trust=0 Audit.lean` を代用しない。
