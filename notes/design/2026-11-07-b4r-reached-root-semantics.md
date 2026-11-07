# B4 redo: 到達した型 root の再帰性と有限 evidence

状態: **核の反例に用いる内部定義と証明の記録**。新しい言語規則を確定する文書ではない。
意味の出典は [spec 6.3 / K2](../../spec/06-roles.md)、今回の作業契約は
[M1 completion contract](../handoff/2026-11-07-m1-completion-contract.md) と B4 redo の依頼。
実装は `lean/Yulang/CommonRoleReachedRoot.lean` ほか五つの新規 module に置いた。

## 1. 拒否する root と、型の内部にある循環を区別する

K2 の最終決定は、`Len (list μ)` の `where` が空なら受理し、`Show (list μ)` から
`Show μ` へ降りたときに拒否する、というものである。したがって「引数の下のどこかに
循環がある」という検査ではなく、「いま role を解決する引数そのものが、構造的な
再帰型である」という検査が必要になる。

一般の有限 graph で言えば、型引数の root が構造的な循環成分に属することと、
root から別の循環成分へ到達できることは異なる。名前付き型の宣言 body へは辺を張らない。
`enum tree` の名前は、宣言 body が tree を参照していても通常の名として終わる。
この方針では `pair(μ,int)` の pair root は再帰的でない。μ の graph は pair root を指さない。

今回 E2 を証明するのに必要な有限 description grammar は次だけである。

```text
Description ::= finite Ground | data Tree | clock
              | pair Description Description | variant Nat Description
Ground      ::= int | pair Ground Ground | variant Nat Ground
clock       ::= 一 node / 一 back edge の graph μ = variant 7 μ
```

`data Tree` は有限 int/pair Ground 木の固定略記である。意味的 Common 型や row predicate を
入力葉に置く constructor ではない。各 description は有限構文であり、`clock` だけが循環を持つ。
`finite` / `data` / `pair` の根は循環成分に属さない。`variant 8 clock` の根も循環成分に属さない。
唯一の循環は tag 7 だけからなり、tag 8 や pair へ戻る辺がないためである。

この grammar では、構造的再帰型を次の **正確な定義** にした。

```text
clockOnly(clock)          = true
clockOnly(variant t p)    = (t == 7) && clockOnly(p)
clockOnly(その他)        = false
StructuralRecursive(p)   ↔ clockOnly(p) = true
```

clock の有限 unrolling も再帰型として拒否する。graph の root を新しい同形 node で
書き直すだけで拒否が消える定義にはしていない。pair の根と variant-only の循環成分は、
同値な graph node を共有しても混ざらない。有限の pair context は、無限の variant 7 列と同値ではない。

これは全 Common 型構文の graph 検査器を完成したという主張ではない。全域 exact resolver の
必要な入力部分集合で、K2 と固定 Common 解釈を同時に実現した E2 用の独立 semantics である。
一般の graph、record tail、union、row、nominal 宣言に対する full checker をこの module に仮託しない。

代案として、下に一つでも循環があれば root も拒否する検査なら、今回の反例は排除される。
しかし `Len (list μ)` の確定した受理規則を変更する。head 照合で循環部分の constructor を
検査した時点も拒否する案も、現在の「goal へ到達」の意味を広げるため、別の承認が必要である。

## 2. 「到達」は resolution judgment の呼び出し

`Goal` は role ID と一つの有限 `Description` を持つ。独立 `Dictionary visible goal` は、
現在の root が再帰型でないことを最初に要求し、所属する実 `Roles.Impl` の head と where fields を読む。
head の有限 Pattern を代入して Common に解釈し、goal と要求同値であることを照合に用いる。
同じ visible 内で head 候補が一意でなければ dictionary constructor は使えない。
where の各実 goal を同じ代入で解釈し、同じ visible の child dictionary をすべて要求する。
辞書は帰納的で、消去先は既存 `RoleDictionaries.Plan` の全有限木である。

「到達」は root でこの判断を呼ぶこと、または一意に選んだ impl の実 where child で判断を呼ぶこと。
head の内部を有限に照合すること自体は、別の role goal の解決ではない。
`Rejects visible goal path` は別判断で、再帰型 root で終了するか、実 where index を通って再帰する。
path は各段階の実 impl と where index を保持する。拒否を成功や曖昧性に読み替えない。

この E2 では全 selection/rejection/ambiguity 結果の正確な全域算法は存在しないので、それを定義したり、
全 Common 言語の各失敗理由の完全性を証明したりはしていない。独立した成功辞書と再帰型拒否の判断だけで、
全域 exactness の必要成分が否定される。

## 3. nested clock が検査を通過する仕組み

旧 B4 の program 還元の二引数 `R clock data` を、一引数 `R (pair clock data)` に置き換える。
実 head と全実 where child を同時に包む。head/child の構文サイズにそれぞれ 1 を加え、
全変数の出現回数を保存するので、実 `CheckedRoles` の受理と `Roles.WellFormed` が保存される。
すべての associated RHS は実 Term の `int` であり、任意 Common 代入に対する
`HeadDeterminesAssociated` を満たす。一引数 signature の scope/completeness も別に証明する。

全 where child の引数は pair なので、任意の Description 代入と任意の有限 path に対して
再帰型拒否へ到達しない (`CommonRolePackedHalting.no_rejection`)。
しかし pair 内の clock は head の padding を無限に供給できる。
実 packed fields を読む guarded 有限辞書の存在 iff 元 program の有限停止評価である。

Description で表現できる代入だけを選んだから生じる障害でもない。
`CommonRolePackedSemanticReflection` では代入像を任意 Common 型・行へ広げ、root 拒否と
head 候補一意性さえ取り除いた大きい独立 Derives を実 unary fields から定義した。
その存在も同じ停止評価と同値である。有限記述の guarded 辞書と任意 Common 代入の大きい判断が
同じ成功集合を持つことを Lean で証明した。

source の receiver-less method、RoleRank、fuel、無限辞書は使わない。名付き再帰型は使わないので、
その例外を維持してもこの反例は残る。公開 `Core.infer` への統合や Rust の変更は行わない。

## 4. qualified の残りを正確に分ける

[元 B4 §7.6](../handoff/2026-11-07-common-demand-and-foundations-results.md) は registry だけでなく、
qualified の有限生成と全自由 parameter family も含む。今回の E2 は registry 成分の非存在であり、
単独の制約生成器の非存在ではない。

残る full-language lemma の数学的 statement は次である。以下の型・judgment 名は必要な interface の
指定であり、この作業で未実装の識別子を Lean 宣言したという意味ではない。

```text
任意有限 registry D、任意 caller-visible V ⊆ D、任意有限検証済み method 表 M、
任意有限自由 parameter 名集合 A、任意有限 scheme 環境 Γ over A、
任意 full Common 式 e、任意有限結果型・行項 out over A に対し、
  WellFormed D ∧ HeadDeterminesAssociated D ∧ VerifiedMethods D M
なら、実 generator G は有限 constraint package C を返し、
  C.methodIds = e の解決済み method ID 列、
  C.ordinaryEquations = e の生成した普通の型・行等式、
  C.roleGoals = e の未解決 role goal 列、
  C.bindingClasses = 各名の weak/captured/generalized の実分類
を保ち、任意代入 ρ : A → (Common.Ty × Common.Row) に対し、
  IndependentQualifiedTyping D V M (Γ.eval ρ) e (out.eval ρ)
  ↔ ∃ ι : C.localNames → (Common.Ty × Common.Row),
       C の普通の有限制約が (ρ,ι) で成立し、
       C の全 role obligation に独立した有限辞書 evidence があり、
       captured は同じ ρ を共有し、generalized は各使用で独立に具体化する。
```

左辺の独立 typing は普通の式 constructor と実 method 宣言を読む判断であり、生成結果の
充足性を別名にしたものではない。associated RHS の確定による等式は普通の等式として既存 store と連言する。
ρ は regular description に制限せず、任意 Common 型・行を含む。role obligation の充足を
「この ρ にだけ定理を適用する」という外部前提に移さない。したがって双方向が全自由 parameter family を保つ。

既存 `QualifiedInference.generate_models_iff_typing` は抽象 Model/Theory と旧式構文の結果であり、
この full Common/source method/associated interface の橋を既に証明したことにはならない。
上の full lemma、対応する新実 generator の実装と橋、全 Common 型上の amended evidence の完成は残る。
本 E2 はその lemma 単体を否定しない。registry と全域 use-site resolver も含む B4 の連言は、
今回の規則のままでは成立しない。
