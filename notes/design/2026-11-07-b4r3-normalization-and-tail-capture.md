# B4r3: 宣言の正規化と、代入後に初めて隠れる tail

状態: **列挙された core 前提に対する E2**。source から生成された閉じた head だけの定理は反証していない。
出典は [spec 6.3 / K2](../../spec/06-roles.md)、[spec 4.3](../../spec/04-types.md)、
既存 `Roles.Term` / `WellFormed` / `AssocWellFormed` / `CommonRoleHeadDetermination.verify`。

## 1. 対象の量化と source の境界

今回の依頼は、有限 core registry に normalized Paterson、HeadDeterminesAssociated と既存 checker を要求する。
これらの実 API は、record の tail に変数を置く宣言を排除しない。
`CommonRoleFiniteTailExamples.old_verified_api_accepts` は、既存の名前付き `VerifiedDeclaration` 検査も
最小反例を実際に受理することを示す。新しい意味 constructor や任意 decoder を追加してはいない。

一方、[surface record type grammar](../../syntax-reference/ja/src/types/named-record-type.md) §2 は
spread を型注釈に含めない。したがって、以下の `{x:int,..a}` は **core 型の数学的表示** であり、
直接書ける Yulang impl の code block ではない。source-to-registry 到達可能性は未証明。
この差を隠して source-valid な反例とは呼ばない。
現在の列挙された前提の外に source-generated / closed-spine 条件があるとも仮定しない。
その条件を付ける場合は、量化範囲と必要な elaboration bridge を変える amended statement になる。

## 2. N の定義と意味保存

新規 `CommonRoleNormalizedDeclarations` は、既存固定 countergrammar
（変数、int、pair、variant、empty record、field 名0の record）について N を定義する。
field 名を複数持つ全言語の N を完成したという主張ではない。E2 の入力はすべてこの部分集合にある。

N は `Pattern.visible false`。record tail へ降りるときは同名 field が既に隠れたことを記憶し、
その後の明示的な同名 field を除く。payload、pair の子、variant payload は新しい record 文脈で再帰的に N する。
tail が変数になれば、そのまま残る。そこへ後で何が代入されるかを宣言検査時には決めない。

実 `normalizeTerm` は固定 decoder で Pattern を読み、N 後に同じ grammar で encode する。
`normalizeGoal` は各引数、`normalizeImpl` は実 head と全実 where を正規化する。
role ID と impl key は保存する。
decode できない Term を合格させるために使わず、checker は全 head/where の decode 可能性も検査する。

`normalize_meaning` は任意 Common 代入について意味保存を示す。
tail では record kind などを誤って比較せず、既存 `RecordTailLe [0]` の双方向関係を使う。
`normalized_head_match_exact` は任意 Common goal と任意 Common 代入について、
N 前の head 解釈が goal と要求同値 iff N 後も要求同値であることを示す。

新 checker は有限構文上の Bool 関数である。
N をかけた実 impl を既存 `CheckedRoles.checkImpl` に渡し、関連型は実 stored RHS が int である十分検査を使う。
`checkEnvironment_sound` は受理なら N(cores) が実 WellFormed かつ元 stored head/RHS の
HeadDeterminesAssociated を満たすと示す。HDA は任意二つの Common 代入を量化する。
全 HDA 宣言を受理する checker の完全性は主張しない。

## 3. 構文に duplicate が無くても、捕捉後には隠れる

最小 core impl は次である。

```text
head  R {x:int, ..a}
where R a
associated value = int
```

role 一つ、impl 一つ、変数一つ、recursive graph なし。
宣言の head には x が一度しかないので N は変えない。N 後の head/child サイズは 3/1 で受理される。
有限 goal C={x:int} に対し、a:=C と捕まえると、

```text
head[a:=C] = {x:int, x:int} ≈ C
child[a:=C] = C
```

となる。さらに a:=emptyRecord でも同じ head に一致するが、child は C と同値でない。
`requirements_not_determined` は、head から where の引数の意味が一つに決まらないことを示す。
関連型 RHS は int なので、承認済み HDA は満たす。

`normalization_does_not_commute_with_capture` は、N(head) を捕捉した構文と、捕捉後に N した構文が違うことを示す。
`post_capture_sizes` は捕捉後 raw head 5、捕捉後 N(head) 3、child 3 を示す。
型同値の新法則を導入したのではなく、同じ first-field-wins が代入後に初めて作用する。

## 4. 同一 goal の検出を越える強い E2

最小ループだけでは、cache を持つ別算法を排除できない。
強い E2 は旧有限線形 interpreter の任意 program に対する実停止問題還元である。
一つの C を任意個、独立した pair slot に並べた有限 clock を使う。

```text
head clock slot:  {x:int, ..fresh}
child clock slot: fresh
goal clock slot:  C
capture fresh := C
```

各 slot は独立した record 文脈なので、宣言のどの spine にも明示的 duplicate はない。
全 head/where は N 固定。slot 一つにつき head/child の raw サイズ差が2あり、
全 rule の right.size より大きい有限 slot 数を選べば任意の線形 data rule を受理できる。
全 clock slot の同じ fresh を、実 data Pattern の bound より大きい変数名にするため、
data の代入を妨げない。fresh の出現回数は head/child で同じである。

実 goal は pair(clock,data)。clock も data も有限木で、構造的再帰型はない。
root 拒否も head の禁止 constructor 検査も作用しない。
拒否対曖昧性は [既存の推奨案](../questions/2026-11-07-b4r2-rejection-priority.md) の拒否先行を作業上の選択にするが、
反例の全候補は Ready なので、優先順位の回答に E2 は依存しない。確定事項にはしない。

`dictionary_exact` は任意有限 P,input について実 finite Dictionary の存在 iff P の有限停止評価。
全子が同じ visible を使い、`actual_plan_exact` は実 impl ID と全 where child の Plan を保持する。
任意 Common 代入を許して両 gate と一意性を落とした上位 evidence でも同じ成功集合となる。
有限 Description で表せない代入を捨てたための障害ではない。
有限実 registry・signature・clock/data goal を入力とする finite tape machine の成功 bit を対角化で否定する。

これは旧 raw syntactic matcher を実行した結果ではない。対象は Common 同値を保存する matching と独立辞書への exactness。

## 5. 他の型同値も調べた範囲

duplicate-field removal は、Common 全体のサイズを消す同値の唯一のものではない。
`another_size_erasure` は union(int,int)≈int を示し、`union_padding_scope` は既存の別 union grammar の実 interpreter まで
つないで、record 用 N では消えない有限 union padding を示す。
同時にその encoding が今回の declaration checker に拒否されることも示す。
一般 union 注釈は spec 4.8 で禁止されるので、これを source-valid な追加 E2 とすり替えない。

既存 `CommonCanonicalShapes` には pair/variant/required の union grouping もある。
variant の行の区切りと producer union は spec 4.7b で別物なので、二つを同じ constructor と解釈して
variant row の source 反例を作らない。行の tag 一意化・payload 合流が既にどの declaration 段階で行われるかを
無視した反例も主張しない。
nominal body は今回の確定規則では展開しないため、nominal recursion を padding に使っていない。
透明 alias の実 lowering と全 row 正規化を完成したとも言わない。

主 E2 に実際に必要なのは、union でも nominal unfolding でもなく、受理される未知 tail の捕捉後の消去である。
構文に見える duplicate を取り除くだけでは、任意 Common 代入下の意味的サイズ下降は導けない。

## 6. qualified と full-language の正確な残り

registry E2 は、単独の有限 qualified 制約生成器の非存在を意味しない。
元 §7.6 の未証明 lemma は以下の数学的 interface statement のままである。
ここで新しい identifier を Lean 宣言したという意味ではない。

```text
任意有限 D、caller-visible V⊆D、有限検証済み method 表 M、有限自由名集合 A、
有限 scheme 環境 Γ over A、任意 full Common 式 e、有限結果型・行項 out over A に対し、
  NormalizedWellFormed D ∧ HeadDeterminesAssociated D ∧ VerifiedMethods D M
なら、実 generator は有限 package C を返し、e の実 method ID 列、普通の型・行等式、
未解決 role goal 列、weak/captured/generalized の分類をそれぞれ保持する。
任意 ρ : A → (Common.Ty × Common.Row) に対し、
  IndependentQualifiedTyping D V M (Γ.eval ρ) e (out.eval ρ)
  ↔ ∃ ι : C.localNames → (Common.Ty × Common.Row),
       C の普通の有限制約が (ρ,ι) で成立し、
       全 role obligation が両K2規則と作業上の拒否先行を含む独立有限辞書を持ち、
       captured は同じρを共有し、generalized は各使用で独立に具体化する。
```

左辺は独立な式 typing と実 method 宣言を読み、生成後の Satisfies の別名ではない。
ρ を有限 description や成功する解に制限せず、Satisfies を外部の追加前提へ移さない。
関連型の確定で ordinary equation を既存 store/bounds に連言し、矛盾は拒否する。
実 generator とこの iff、および全自由 parameter family は未証明。
full Common N、一般 finite-tree agreement、nominal agreement、source-to-registry rigidity bridge も未証明である。
