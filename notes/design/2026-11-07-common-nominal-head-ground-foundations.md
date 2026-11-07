# Common nominal head と ground cast の基礎

日付: 2026-11-07。状態: **部分実装・kernel 検査済み。B5 全体は未完。**

対象は [前回の結果 §7.7](../handoff/2026-11-07-core-common-coverage-results.md#77-b5-nominal-invariance--ground-cast--construction-sites) と
[B5 の不足契約](2026-11-07-common-effect-role-nominal-contracts.md#6-b5-invariant-nominal-と純粋な-castconstruction) の基礎である。
既存の `Common`、`Core.infer`、`Core.PresenceOnly`、`Casts.Compatibility` の定義・主張は変更していない。
意味上の根拠は spec 6.5 の nominal 引数の不変性と、同じ意味の型を同一視する spec 4 の規則である。

## 1. 閉じた部分と、その境界

追加したのは、専用 nominal head の要求意味、実 finite presence atoms への比較のコンパイル、
旧 Common 型と nominal を同居させる**外側の根**の順序、明記した ground 文法の実 cast compatibility である。

nominal を structural variant へ符号化していない。declaration ID、引数の順序、値型・行の種別を保持する。
値型引数は任意の `Common.Ty` で、regular graph、mask/default、負位置を含む。
行引数は任意の `Common.Row` で、有限集合に限定しない。

ただし、`CommonSyntax.Layer` 自体に nominal 構成子を追加したわけではない。
新しい nominal の根を arrow/record の子に置くこと、nominal の相互再帰 graph、
nominal を内部に持つ新型を nominal 引数に置くこと、source の typing/solver の保存拡張は未完である。
このため、前回 §7.7 の **`common_nominal_invariant_exact` 全契約を完了とはしない**。
新定理は `nominal_head_invariant_exact` / `nominal_root_invariant_exact` と別名にした。

## 2. 任意 Common 引数の不変性

`CommonNominalHeads.Argument` は `.value Common.Ty` と `.row Common.Row` を区別する。
同じ種別の引数間の `Le` は、それぞれ既存の `Common.Subtype` と `Common.rowLe` である。
異種別の比較は偽。`Argument.Equivalent` は両方向の `Le` として独立に定義する。

`Head` は `name : Nat` と `arguments : List Argument` を持つ。
要求は head の ID/arity、および各位置の lower/upper bound であり、
`Subtype` はその要求受理の反転包含である。引数同値を `Subtype` の定義に書き込んだものではない。

主要定理は次の通りである。

```text
nominal_head_invariant_exact:
  任意 first last : Head,
  Subtype first last ↔
    first.name = last.name ∧
    first.arguments.length = last.arguments.length ∧
    ArgumentsEquivalent first.arguments last.arguments
```

`ArgumentsEquivalent` は、順序を保った全対応引数の `Argument.Equivalent` である。
追加前提はない。全観測深さ、負位置の rank、要求環境を量化する旧 `Common.Subtype` をそのまま使う。
成功、正規化済み入力、有限 depth、fuel を前提にしていない。
`Argument.equivalent_row` は任意二行の両方向包含を**文字どおりの行等号**へ戻す。
`nominal_head_subtype_symmetric` は任意二 head の一方向 subtype から逆方向を導く。

## 3. 共有 slot を保つ有限比較

`CommonNominalConstraints.ArgumentTerm` の値型引数は既存の `TyTerm α`、行引数は `RowTerm α` である。
`HeadTerm α` は declaration ID とその有限引数列を持つ。
同じ `α` の出現は同じ assignment を読むため、引数間の共有を分離しない。

`compile` は ID/arity/kind を検査し、対応する各値型・行引数について
既存の `PresenceNormalForm.Atom.tyLe` / `.rowLe` を**両方向**に出力する。
kind/arity/ID が違えば `none`。それらが一致しても、返した atoms が充足可能とは限らない。
type checker や任意の意味述語を atom にしたものではない。

```text
compile_nominal_comparison_exact:
  任意 α : Type,
  任意 first last : HeadTerm α,
  任意 assignment : α → Comp Common.model,
  (∃ atoms,
    compile first last = some atoms ∧
    PresenceNormalForm.All Common.model assignment atoms)
  ↔ CommonNominalHeads.Subtype
      (first.eval assignment) (last.eval assignment)
```

追加前提はない。この定理は**比較の生成**を閉じる。
元の `CommonBoundRefSolver.generated_models_exact` は実 source 生成文法についての定理なので、
任意のこの atom 列へ自動的に適用できると扱わない。
nominal source からの生成と、その生成文法に対する全モデル回収は別途必要である。

## 4. 旧 Common 順序の保存・反映

`CommonNominalRoots.Ty` は `.common Common.Ty` と `.nominal Head` を持つ。
`Demand.upper bound` は既存 Common 型の上界要求、`Demand.nominal` は前節の nominal 要求である。
旧型から nominal への交差は bottom 以下の場合、逆の交差は top が受けられる場合に限る。
これは nominal の structural layout を公開する規則ではなく、outer-root order の内部選択である。

次はすべて追加前提なしである。

| 定理 | 全量化した主張 |
| --- | --- |
| `common_subtype_exact` | 任意旧 `a b : Common.Ty` について、`Subtype (.common a) (.common b) ↔ Common.Subtype a b` |
| `common_equivalent_exact` | 任意旧 `a b` について、新旧の要求同値も iff |
| `nominal_root_invariant_exact` | 任意 `a b : Head` について、根の subtype iff ID 等号・arity 等号・全対応引数の同値 |
| `common_nominal_exact` | 任意旧 `a` と nominal `b` について、`.common a ≤ .nominal b ↔ a ≤ bottom` |
| `nominal_common_exact` | 任意 nominal `a` と旧 `b` について、`.nominal a ≤ .common b ↔ top ≤ b` |
| `bottom_le` / `le_top` | 任意の根に対する旧 bottom/top の法則 |

新 carrier の全構成子を持つ `PresenceGeneration.Model` はまだ構成していない。
従って、この順序の保存から old source typing / old solver の保存を証明済みとはしない。
旧 code を変更していないという事実と、新しい mixed model への保存定理は別である。

## 5. ground cast の文法と正規化像

`CommonGroundScalarCasts.Scalar = ProducerCanonicalOpen.Expr 0` は、
既存4基底型、bottom、top、union、intersection だけからなる有限型である。
型変数・行変数を持たない。

`check_exact` は任意二 scalar に対し、実 canonical-code checker が true iff 既存 Common subtype とする。
`scalar_normalized_quote_exact` は任意二 scalar の Common 要求同値 iff
既存 scalar 正規化後に `Casts.Ty` へ戻した型の文字どおりの等号を示す。

`CommonGroundNominalCasts.Ground` の全文法は次である。

```text
Ground ::= scalar Scalar | nominal Nat (List Scalar)
```

`lower` は nominal の**全型引数**を正規化してから `Casts.Ty.nominal` に渡す。
外側の scalar にはそれ自身の正確な判定器があるため、元の scalar 構文を保持する。
`meaning` は正規化前の元 Ground を `CommonNominalRoots.Ty` に解釈する。

```text
normalized_ground_compatibility_exact:
  任意 source target : Ground,
  fitsCommonGround.Rel (lower source) (lower target)
    ↔ CommonNominalRoots.Subtype (meaning source) (meaning target)

normalized_ground_check_exact:
  任意 source target : Ground,
  fitsCommonGround.check (lower source) (lower target) = true
    ↔ CommonNominalRoots.Subtype (meaning source) (meaning target)
```

いずれも追加前提なし。`fitsCommonGround` は実装した有限 checker を持つ
実際の `Casts.Compatibility` であり、外部 compatibility oracle を引数に取らない。
raw nominal 引数の不変性を要求する既存 field `nominalInvariant` も変更していない。

この grammar では `N (int | str)` と `N (str | int)` が同じ型として通り、
`N int` から `N (int | str)` への片向きの widening は拒否される。両方を kernel の計算で確認した。

**対象外**: nested nominal 引数、row 引数、nominal を内側に持つ pair/record/arrow、
mask/default、regular nominal graph、自由型変数、実宣言一覧からの名前解決。
`Casts.Compatibility` は全 `Casts.Ty` を入力にする既存 interface なので、
上の grammar 外の二つの nonscalar endpoint は raw equality で全域化した。
その全域化を Common 全型の ordinary compatibility として公開入口に接続してはならない。

## 6. 残る補題

前回 §7.7 の元 statement は変更しない。次が不足している。

1. **`common_nominal_invariant_exact` の全 carrier への接続。**
   任意 declaration ID/arity/新 carrier の型・行引数について同じ invariant iff を示し、
   任意旧 Common 型の順序と旧 source typing / solver を保存する。
   nominal を任意 constructor の子・regular block 内に保持する finite/regular layer、
   独立要求意味、constructor inspector、全 parameter readback が必要。
2. **`nominal_graph_compile_exact`。**
   任意検証済み有限宣言、元環境、元 nominal/list/construction 式、結果について、
   独立 mixed Typing iff 実 finite constraints。
   本メモ §3 は head 比較だけで、site source expressions、固定 field、宣言 arity の検証をまだ供給しない。
3. **nominal 実生成問題の全 instance solver。**
   任意独立 rows と全 node values の Models iff 返却 scheme と無条件 parameters による
   同じ rows / 全 values の要求同値までの回収。任意返却 scheme・任意 parameters の Models も必要。
   既存 source 生成 theorem の文法条件を成功仮定として公開 theorem に移さない。
4. **`common_cast_plan_exact_and_pure`。**
   任意検証済み有限 cast 宣言、既知 source/target、元式・環境・行について、
   実 keep/search/failure と型付き executable plan を接続する。
   検証済み source body から purity と型保存を導出し、境界挿入後の同じ行、
   arrow wrapper が変換した引数で元関数を呼ぶ request tree を保存する。
   `PureCasts.Plan` や site `CastContract` を外から受け取るだけの接続は代用にならない。
5. **`common_construction_sites_exact`。**
   任意検証済み constructor 宣言・全元 site 式について、固定 field、共有 invariant parameter、
   pure cast、元順序、一度だけの評価を保つ独立 Typing と finite generation の iff。
   その全 Models を solved family と module/EOF の weak slot 決定へ接続する。

作業順は、B1 の list と B2 の nominal pattern が依存する head/ground 基礎を先にした。
full carrier への追加は既存の全 Common 型を使う A1/A2/solver にも影響するため、
単に head theorem が通った段階で公開 `Core.infer` の範囲を増やしていない。

## 7. 仕様上の問い

新しい `notes/questions/` はない。ここで選んだのは内部の段階分けと有限 ground adapter の対象文法であり、
利用者が書く Yulang の挙動を変更していない。未決の source 規則を nominal の実装都合で決定していない。
