# B4r2: constructor 検査拒否と、消える field のサイズ

状態: **承認済み K2 の独立 semantics と、その下でも残る E2 の記録**。
K2 の言語決定は [spec 6](../../spec/06-roles.md)、同名 field の型同値は
[spec 4.3](../../spec/04-types.md) が正本。旧 root-only E2 は変更しない。

## 1. 追加された拒否と、優先順位の作業上の選択

承認済み K2 は、role の引数が名前の無い構造的再帰型である root に到達した場合に加え、
impl head の非変数 pattern が、そのような型の constructor を検査する時点にも拒否する。
単なる変数による捕捉は検査しない。nominal 宣言 body は展開しない。

今回の新規 `CommonRoleInspectedSemantics` は、int/pair/variant、field 名0の record、
有限 Ground と有限 Tree data、および一 node graph μ=variant 7 μ の有限 countergrammar を扱う。
型の解釈は固定 Common constructor であり、入力に意味的型や row predicate の oracle を含めない。
root 再帰性は旧 countergrammar と同じく、μ とその tag 7 による有限 unrolling である。
record や pair の下の μ は、それだけで外側の root を再帰型にはしない。

head の `blocked` は次の規則を持つ。

1. 変数 pattern は常に非 blocked。μ を代入像として捕まえてよい。
2. 非変数 pattern は、現在の対象 root が再帰型なら blocked。
3. それ以外は、対象の constructor と pattern の外形が一致する場合に、pattern が要求する
   子の検査へ降りる。異なる外形なら、その下まで検査する必要はない。
4. 同名 field の隠れる payload は、head の検査対象から除く。これは型同値の既存規則に従う。
   ここで正規化するのは検査対象の選択であり、宣言の Paterson サイズ検査は既存のままである。

`blockedImpl` は同じ role の visible impl を対象にする。`Ready V g` は root が非再帰的で、
全対象 head の禁止検査がないことを要求する。
`HeadOutcome` の rejected は ¬Ready、selected / ambiguous / absent は Ready を前提にする。
したがって、**禁止検査による拒否を曖昧性より先にする**。
この優先順位は spec が黙っているので [一問](../questions/2026-11-07-b4r2-rejection-priority.md) に記録した。
visible の列挙順に依存させず、安全な候補があることを理由に禁止検査の報告を避けないための推奨であり、
ユーザー確定事項として spec へ追記していない。今回の E2 は全 target が有限木なので、逆の優先順位でも成立する。

独立 `Dictionary` は Ready、実 visible 所属、実 head fields の解釈による Common 一致、
**任意 Common 代入**での候補一意性、および実 where fields を同じ有限記述代入で解釈した全 child を要求する。
各 child も同じ visible を使う。辞書は帰納的な有限 Type であり、消去は実 impl と全子を持つ
既存 `RoleDictionaries.Plan`。`not_ready_no_dictionary` は拒否される場合に成功辞書がないことを示す。

この module を full Common grammar の matching algorithm や全 graph 再帰検査器とは扱わない。
E2 の入力部分集合で独立意味を定義し、普遍的な全域 resolver の必要成分を否定する。
一般の型・row、nominal declaration、source inference への統合や一般的一致は別の未証明事項である。

## 2. 新しい拒否は旧反例を止めるが、raw なサイズは別問題

旧 root-only の反例は、head が nested clock の constructor を調べるので、新規則では拒否される。
今回の構成は recursive clock を一切使わない。任意の線形有限 data rewrite rule left→right を、
実 `Roles.Impl` の次の fields へ翻訳する。

```text
head:  R {x:left, x:G^k int}
where: S {x:right}
k = rawSize(right) + 1
```

data grammar は固定 int/pair/variant。第二の x の payload は閉じた有限木で、型変数を持たない。
関連型 RHS は定数 int である。すべての変数は可視 data pattern にあり、
過去の「隠れた head 変数が where を任意にする」障害ではない。

Common では実 head の解釈は `{x:left}` と要求同値になる。
`common_shadowed_head_equivalent` と `required_equivalent_iff` により、実 head の照合 iff
source role が一致して left が data と要求同値になることを証明した。
しかし既存 Paterson checker は、消える第二 field も raw な構文サイズに数える。
k を増やせば、right が大きくなる rule まで raw size の真の下降と変数出現回数の検査を通せる。

生成した全宣言について実 WellFormed、既存 checker=true、拡張した固定 grammar の非自明な実 head を使った
HeadDeterminesAssociated、関連型 signature/scope/completeness、全 where の宣言済み arity=1 を証明した。
HDA は任意二つの Common 代入を量化し、head/RHS の格納 field を直接解釈する。
旧 grammar が record を解釈できないことによる空虚な HDA は使わない。

各有限 machine configuration c の goal は `{x:finiteData(c)}`。
すべて有限木なので、任意の visible head に対して root 拒否も禁止された constructor 検査も起きない。
`finite_ready` は任意有限 V と任意有限 target についてこれを証明する。
旧有限線形 interpreter の任意 program の停止を、そのまま有限実辞書の存在へ還元できる。
これが `CommonRoleFiniteShadowObstruction.finite_tree_registry_undecidable` の E2 である。

既存の `Roles.resolve` の raw first-order matcher をこの正規化済み goal で実行したとは主張しない。
それなら余分な field を持つ raw head は一致しない。対象は B4 が要求する、Common の型同値を保つ
実 head matching と独立 evidence / dictionary への exactness である。
Common 同値を読む核へ拡張することと、既存 raw サイズ検査だけで全域を保証することが両立しない。

## 3. 任意 Common 代入と辞書の範囲

`CommonRoleFiniteShadowHalting.matched_step` は、任意 Common 代入による実 head 一致から
有限 data capture と実 machine step を回収する。right の使用変数は left に含まれるため、
right もその有限 capture と同じ意味になる。候補一意性は、有限 rule compiler の独立 no-overlap から導く。
成功・停止・安全性を外部前提として最終 theorem へ渡していない。

`CommonRoleFiniteShadowSemantic` は、両拒否と候補一意性を取り除き、代入像を任意 Common 型・行に広げた
上位の独立 Derives を、実 head/where fields から定義する。
その存在も program の停止と同値である (`arbitrary_common_exact`)。
有限 Description 代入の guarded 辞書の存在と、この大きい判断の存在も同値である
(`guarded_iff_arbitrary_common`)。したがって有限記述で表現できる代入だけに制限したための E2 ではない。

`Dictionary.all_visible` / `actual_plan_exact` は全実 impl ID と全 where child を含む Plan を保持する。
Common 同値な goal の全 plan が必ず等しいという、別の強い契約は使っていない。
単に一つの有効な辞書を返す total resolver も、成功 bit の決定不能性で排除される。

## 4. qualified 制約生成の正確な残り

今回の E2 は registry の全域 use-site resolution 成分に対するもの。
有限 qualified 制約を構文として生成すること自体が不可能とは証明しない。
元 B4 §7.6 に含まれる full-language の未証明 lemma は、次の数学的 interface statement である。
未実装の identifier を Lean に宣言したという意味ではない。

```text
任意有限 registry D、任意 caller-visible V⊆D、任意有限検証済み method 表 M、
任意有限自由名集合 A、任意有限 scheme 環境 Γ over A、
任意 full Common 式 e、任意有限結果型・行項 out over A に対し、
  WellFormed D ∧ HeadDeterminesAssociated D ∧ VerifiedMethods D M
なら、実 generator は有限 package C を返す。
C は e の実 method ID 列、普通の型・行等式、未解決 role goal 列、
各名の weak/captured/generalized 分類をそれぞれ保持する。
任意代入 ρ : A → (Common.Ty × Common.Row) に対し、
  IndependentQualifiedTyping D V M (Γ.eval ρ) e (out.eval ρ)
  ↔ ∃ ι : C.localNames → (Common.Ty × Common.Row),
       C の普通の有限型・行制約が (ρ,ι) で成立し、
       全 role obligation が承認済み root+constructor 検査 semantics の有限辞書 evidence を持ち、
       captured は同じ ρ を共有し、generalized は各使用で独立に具体化する。
```

左辺は実 method 宣言と独立した式 typing を読む判断であり、生成後の充足性の別名ではない。
ρ は有限 description へ制限せず、任意 Common 型・行を含む。Satisfies を ρ の外部適用条件にしない。
関連型の確定時には普通の等式を既存 bounds/store へ連言し、それまでの等式と矛盾すれば拒否する。
全自由 parameter family はこの全称 ρ の双方向であり、一つの解の存在だけではない。

既存 QualifiedInference の抽象 Model/Theory 上の theorem は、この full Common/source method/associated の
実 generator への橋を既に供給したものではない。上の interface、実 generator、独立 typing とその iff、
全 family は未証明のまま。この単独 lemma を否定せず、全域 resolver も含む B4 の連言への E2 として終える。
