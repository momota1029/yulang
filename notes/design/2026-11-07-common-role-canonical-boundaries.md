# Common role registry と全公開 interface の残る境界 (2026-11-07)

状態: B4 / A2 の元の statement は未完。B4 の regular goal に対する停止案の一つを、既存定義上の反例で除外した。

このメモは [前回結果 §7](../handoff/2026-11-07-core-common-coverage-results.md) と
[effect / role / nominal 契約 §5](2026-11-07-common-effect-role-nominal-contracts.md) の量化を変更しない。
今回の [nominal head / ground 基礎](2026-11-07-common-nominal-head-ground-foundations.md) を、
全 regular carrier や全 public interface の完成とは扱わない。

## 1. B4: 元の目標と既存証明の境界

必要な `common_role_registry_exact` は、任意の有限 declaration / visible registry `D/V` と
独立した well-formedness、実宣言に従って型・行が確定した任意の有限 goal description `g` に対し、

```text
resolveCommon D V g = resolved
  ↔ ActualRoleEvidence D V (interpretGoal D g)
```

を満たす実装である。成功時の実 dictionary、`noImpl` と ambiguity の独立判断との iff も含む。
同じ根の呼び出し側 `V` をすべての nested `where` に使い、nominal identity、regular graph の共有、
associated equation の既存 bounds を保つ。実 source が生成する全確定 goal を覆う必要がある。
任意 decoder、成功、fuel、有限展開 depth を新しい前提にしない。

`CheckedRoles.resolve_exact` は任意の有限 `List Roles.Impl` と有限木 `Roles.Goal` に対して既に閉じている。
しかし `Roles.Term` は `var` / `app` からなる有限木である。
`Roles.size_decreases` は代入値 `σ v : Roles.Term` の有限な `size` と variable occurrence の数を使う。
有限 graph を一つの有限構造体に包むことは、その代入サイズの等式を保存する証明にはならない。

## 2. 実 Paterson check を通る regular chain

`CommonRoleRegularObstructions.lean` は、次の一つの宣言を実 `Roles.Impl` として持つ。
`F` は pair、`G` は固定 tag `7` の variant の、内部で解決済みの constructor identity を表す。
以下は Yulang の表面構文ではない。

```text
R(F(G(G a), b))  requires  R(F(a, G b))
```

`declaration_sizes` は head が `5`、child が `4` であることを示す。
`declaration_accepted : CheckedRoles.checkImpl declaration = true` と
`declaration_wellFormed : declaration.WellFormed` は、変数出現回数の検査も含む既存 checker / 条件そのものを検証する。
この三つの theorem に追加の前提はない。

`interpretPattern` はこの例の pair と variant だけを既存 `Common.Ty` に解釈する。
それ以外の constructor は `none` になる。全 Common 型を任意の有限木へ押し込む decoder ではない。
`InstanceStep source target` は、ある `Nat → Common.Ty` の代入と二つの解釈結果が存在し、
実 head / child pattern の解釈がその二つを返し、それぞれが source / target と要求同値になる、という独立した一段関係である。
resolver の返却値や cache は定義に現れない。

既存 `CommonSyntax.State.block` の一 node / 一 back edge で `A = G A` を表す。
`loop_unfold` はその型 `loop` に対し、前提なしで

```lean
Common.Equivalent loop (Common.variant 7 loop)
```

を示す。さらに `growing n = Gⁿ int`、`chain n = F(A, Gⁿ int)` と置く。

### `chain_step`

任意の `n : Nat` について、前提なしで

```lean
InstanceStep (chain n) (chain (n + 1))
```

となる。head へ `a := A`、`b := Gⁿ int` を代入すると、`G(G A) ≈ A` により `chain n` に一致し、
child が `chain (n + 1)` になる。各 `n` の型は有限な Common regular 構文である。

### `chain_equivalent_iff` / `chain_fresh`

任意の `n m : Nat` について、前提なしで

```lean
Common.Equivalent (chain n) (chain m) ↔ n = m
```

となる。また任意の `n : Nat` について、

```lean
∀ earlier ∈ (List.range n).map chain,
  ¬ Common.Equivalent earlier (chain n)
```

となる。raw syntax の identity だけの相違ではない。要求同値で正規化する既訪問検査でも、
この chain は以前の goal と一致しない。

### `no_natural_descent_measure`

前提なしで、

```lean
¬ ∃ measure : Common.Ty → Nat, ∀ source target,
  InstanceStep source target → measure target < measure source
```

を示す。したがって、この regular 一段関係の全 child 展開が減少するような自然数 measure はない。
旧 finite-tree size を graph の node 数へ置換するだけでは、必要な停止定理にならない。

これらは直接再帰と既訪問だけの案に対する反例である。独立 evidence の有限な記号的判定、別の正確な solver、
B4 全体の可能性を否定しない。決定不能も主張しない。
この regular `A` を実 Yulang source の確定 role goal として生成するコードは、今回確定していない。
したがって利用者向けの新しい仕様質問にはせず、内部の停止設計の不足として記録する。

## 3. B4 の不足補題

次の項目は未証明であり、定理の入力前提へ移さない。

1. **有限 goal の生成と意味保存**: 任意の検証済み有限 `D/V` と実 source が確定させた goal に対し、
   nominal identity、行式、regular graph と共有 slot を保存する有限 description を構成し、
   その解釈が元の goal と要求同値になること。semantic row の任意述語を Bool checker の入力としない。
2. **regular head matching exactness**: 任意の上記 description と実 declaration head に対し、
   matcher の返す代入が独立した head instance と一致すること。意味的な同値と raw graph / tree equality を混同しない。
3. **regular 解決の停止と evidence exactness**: 任意の元の well-formed registry と全対象 goal に対し、
   有限に計算する resolver の成功 / 拒否 / 曖昧性を独立した evidence / overlap 判断と双方向につなぐこと。
   §2 により、単純な子への size 減少・既訪問検査だけでは閉じない。
   有限な記号的状態空間を新たに使うなら、その表現の完備性と停止を証明する必要がある。
4. **dictionary と associated equations**: 任意の成功 goal、関連型名、共有 slot、既存 store、任意の Common 代入 `σ` に対し、
   実 dictionary を生成し、追加後の Models が元の Models と選択された関連型との要求同値の連言になること。
   既存 bounds の上書きや dictionary existence だけによる ambiguity 無視は許さない。
5. **未確定 goal の有限生成と全 family**: 元の `generate_common_qualified_finite_exact` の
   任意 `D/V, ρ, sΓ/Γ, e, out` と唯一の環境対応 `EnvRel ρ sΓ Γ` の下で、独立 Typing iff 有限制約を閉じ、
   任意の返却 scheme と任意の自由 parameters の健全性を示すこと。
   未解決 `Satisfies` を parameters の追加条件にしない。

receiver のない member の K1 は既存の未決である。今回の停止障害はそれを選ぶ必要がなく、追加質問もない。

## 4. A2: 元の目標は未完

必要な `public_interface_canonical_exact` は元のままである。

```text
任意の有限な公開 interface I/J について、
  既存の公開 instance 意味における等価性
  ↔ computableCanonicalEncoding I = computableCanonicalEncoding J
```

一般 domain、constructor 結果、mixed head、record/default/mask、一般行式と行 parameter、
任意の正負共起と再parameter化、weak/captured metadata、regular graph、nominal / role obligations を含む。
比較する一般化 parameter 数の一致や全単射は前提にしない。
実 inference scheme の readback、export / EOF、display を同じ既存意味へ接続する必要も残る。

現時点の `CommonCanonicalCurriedFamilies.canonicalEncoding_exact` は、同じ有限 arrow depth、
variable domain、scalar result、固定 row identity、空 obligations の完全な部分文法を扱う。
代入する parameter が任意 Common regular 型であることは、interface の本体に任意 regular graph を書けることと異なる。
`QualifiedInference.Interface` の旧 `Inference.TyTerm` も、default / mask / nominal / regular graph を含む全文法ではない。

### 既存の反例が禁止する短縮

`CommonCanonicalObstructions` により、以下は既に kernel で確認されている。

- 同数で全て使われる generalized variables でも、instance 同値は alpha 同値より広い。
  `same_arity_used_parameters_not_alpha` が、単なる変数の並べ替えでは完備にならないことを示す。
- 共有 parameter の pair 像は、単に二つの endpoint 間の interval にはならない
  (`positive_pair_image_not_interval`)。
- arrow の入力と出力の同じ parameter を独立にすると instance 集合が変わる
  (`mixed_polarity_sharing_matters`)。負の出現を含む変数の一律 bottom 消去も不正である。
- captured slot を generalized slot と交換すると、既存 instance 意味が変わる
  (`captured_slot_cannot_be_generalized`)。

さらに `CommonCanonicalArrowModule.Examples` は、absorbed captured occurrence を加えても family code は同じだが、
その slot を未確定にしたとき実 `finishModule` が異なることを示す。
既存の `exportCanonicalEncoding` が raw support を別に保持するのは、この実 EOF 動作のためである。
family の意味と EOF の意味を無言で取り替えて、同じ canonical exactness と呼ぶことはできない。
全 interface でも元の意味を保持した readback / export の橋を証明する必要がある。

### 不足補題

1. **全有限公開文法と readback exactness**: 任意の実返却 scheme から、上記全構成要素と共有 identity を保つ
   有限 interface を読み戻し、すべての ambient / row / generalized assignment と target で既存 instance 意味が一致すること。
2. **共有を保つ全 family canonical exactness**: 任意の二つの全有限 interface に対し、一般化数や正負の共有を制限せず、
   存在量化された parameter family の既存意味を、有限で計算可能な同一 code に完全に特徴付けること。
   同じ graph の rename だけ、有限展開 depth だけ、scalar endpoint だけでは不足する。
3. **一般行式と regular graph**: 任意の有限な行式と finite regular graph 本体を code に含め、
   任意の意味的行代入・全観測 depth に対する同値を保存かつ反映すること。
   semantic `Occurrence → Prop` に計算可能な等号を仮定しない。
4. **nominal / obligations の接続**: invariant な値・行引数、実 role obligation、呼び出し側 evidence と dictionary を
   そのまま既存 instance 意味へ接続すること。今回の scalar-ground nominal 正規化や任意 `Theory` を、完成した B4 の代用にしない。
5. **export / EOF / display**: 任意の partial ambient assignment を含む実 finish 操作と実利用の意味を保ち、
   code の readback と表示に同じ公開 instance 意味を与えること。既存 support / weak / captured 判定を落とさない。

全 A2 を閉じる見込みは、この全 family の有限判定手続きを構成してから評価すべきである。
今回の小さな canonicalizer の追加で元の量化を満たしたとはしない。これらの不足は内部証明・表現の問題であり、
新しい Yulang コード上の仕様分岐は確定していないため `notes/questions/` への追加はない。

## 5. 検証と次の着手

`CommonRoleRegularObstructions.lean` は Lean 4.35.0 の `lean --trust=0` で警告なく通過した。
`declaration_wellFormed`、`loop_unfold`、`chain_step`、`chain_equivalent_iff`、`chain_fresh`、
`no_natural_descent_measure` の直接公理表示は、すべて `[propext, Quot.sound]` のみだった。
全体の `lake build --wfail` と `Audit.lean` への import / 登録は統合側で行う。

B4 は実 source から有限 regular goal へ到達する橋と、その全 graph に対する停止手続きを先に切り分ける。
§2 の例を排除するなら source 生成器の性質として証明し、元の goal 量化を有限木へ狭める前提にはしない。
A2 は全 family の判定方式が未構成なので、既存の部分文法の拡張を完了扱いせず、独立した B1 / B2 / B5 の不足へ進む。
