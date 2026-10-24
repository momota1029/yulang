# 低い捕捉先への replay と公開後の二使用

BIRTH-LEVEL-REPLAY-20261024/r1。著者 primary。Baseline `7af2bbfe9588128e90f6706f99243e91b63a7ae3`。本稿は原 Simple-sub の有限な具体的 store と freshening map を導出し、争点の等式を追加した場合の帰結を比較する。等式の資格・実 source-event 所属は[別稿](2026-10-24-birth-level-replay-intrusion.md)の証拠を必要とする。凍結 r1 は独立査読で記載範囲に BLOCKING/MAJOR 指摘なし。査読後の変更はこの状態行と別稿の状態注記のみ。全 Yulang の反例や健全性完了を主張しない。

## 1. 一つの固定 source と前提

```text
let top = lambda h.
  let rec f = lambda x.
    (lambda z.{a=x})(h(f x))
  in {a=succ((f 0).a), b=(f true).a}
in top
```

これは原 `syntax.scala` の Let/Lam/App/Rcd/Sel/Var/Lit だけを使う。top は boundary0 の非再帰 let、h は level1、f は boundary1 の再帰 let である。参照実装の `Typer.scala` と `syntax.scala` の固定 hash は [sprint contract](../../tasks/agent-loop/sprints/birth-level-replay-20261024.md) にある。source 表記の括弧は上の AST を一意に指定するためのものとし、Yulang parser 受理を断言しない。

birth(H)=1、birth(F)=2。F は自分と h を参照する。新しい[生成レベル別規則](../design/2026-10-24-birth-level-scc-intrusion.md)では F/F は資格を持ち、F/H は持たない。**後述の replay-created pair の occurrence がどちらかは、この source graph だけからは決まらない。**

## 2. f の公開直前の native store

h の型を H:1、f の再帰 placeholder を o:2、x を B:2、`f x` の結果を R:2、`h(f x)` の結果を S:2、wrapper の z を Z:2、その application の結果を W:2 とする。

1. 自己呼出しは `o <: Function(B,R)`。全 payload が level2 なのでコピーを作らない。
2. h の呼出しは `H <: Function(R,S)`。negative extrusion が C,D:1 を作り、`R <: C`, `D <: S`, `H <: Function(C,D)` を保持する。
3. wrapper は `Function(Z,Record(a:B)) <: Function(S,W)`。分解して `S <: Z`, `Record(a:B) <: W`。前者の replay `D:1 <: Z:2` は rhs-Variable branch で D を Z の lower に入れる。型変数同士では一方の level 比較が成立するので、この比較は extrusion を起こさない。
4. 再帰 completion は `Function(B,W) <: o`。既存の upper demand と比較し `W <: R`。W の lower を replay して `Record(a:B) <: R`、さらに R の upper から `Record(a:B) <: C:1`。
5. 最後の lhs は level2 の構造型なので positive extrusion が実際に B の copy T:1 を作る。`B <: T` と `Record(a:T) <: C` を保持する。**この実 pair (T,B,+,target1) の資格が争点である。**

元 Scala の各分岐を順に適用して得る store は次の通り。表は物理的な lower/upper list であり、全不等式を両側に重複記録するものではない。

| row | level | lower list | upper list |
| --- | --- | --- | --- |
| H | 1 | ∅ | Function(C,D) |
| o | 2 | Function(B,W) | Function(B,R) |
| B | 2 | ∅ | T |
| R | 2 | Record(a:B) | C |
| S | 2 | D | Z |
| Z | 2 | D | ∅ |
| W | 2 | Record(a:B) | R |
| C | 1 | Record(a:T) | ∅ |
| D | 1 | ∅ | ∅ |
| T | 1 | ∅ | ∅ |

上の二回の extrusion は、原 reference での新 copy をすべて含む。二回目の T 作成時、B の lower は空なので追加再帰 copy はない。C に入れる Record(T) は level1。以後この公開 cut まで wrong-level 構造比較はない。finite comparisons の cache は同じ variable pair の再処理を止め、異なる source event の存在をこの scalar cache から読み出さない。

## 3. 等式なしの公開・使用を構成する

**PR1（実 freshening map）。** 争点の B=T を追加せず、元 boundary1 の `PolymorphicType(1,o)` を公開する。各使用 i で、実 `freshenAbove` は一つの memo によって

```text
o ↦ o_i, B ↦ B_i, W ↦ W_i, R ↦ R_i;
C ↦ C, T ↦ T.
```

とする。新 row の level は1である。H,D,S,Z は o の公開 root から到達せず、新たに複写しない。旧 store には残る。

証明。o の lower/upper を辿ると B,W,R に到達する。B.upper は T、R.upper は C で、いずれも level≤boundary の早期 return によって共有される。W/R の lower の Record(B) は同じ memo による Record(B_i) になる。高い変数への再訪は既存 memo を返す。この有限 graph の全隣接を列挙したので、他のコピーはない。□

**PR2（独立二使用）。** この正確な store では、第一使用と第二使用は原 native algorithm で primitive mismatch を生じない。

証明。第一使用は `o_0 <: Function(Int,V_0)`、lower function を比較して `Int <: B_0`, `W_0 <: V_0`。field selection は `V_0 <: Record(a:Q_0)`。W_0 の lower を経て `B_0 <: Q_0`。succ は `Q_0 <: Int`, `Int <: A_0`。第二使用は同様に `Bool <: B_1`, `W_1 <: V_1`, `V_1 <: Record(a:Q_1)` から `B_1 <: Q_1`。B_i の共有上界 T へ Int と Bool が流れるが、T に第一使用の Q_0 上界を付ける操作はない。C も共有するが、その lower Record(T) から B_i へ逆向きの制約は生成されない。

全使用時の新変数と構造 payload は level1 以下であり、追加 extrusion はない。比較はこの有限 graph の variable link、同名 record field と Int/Int の primitive case に帰着する。型 valuation は `B_0=Q_0=Int`, `B_1=Q_1=Bool`, `T=Int∨Bool`, `C=Record(a:T)`、`W_i=R_i=V_i=Record(a:B_i)` と取れる。共有 H の入力 C と D は一つのまま保つ。残る旧 B は例えば T、旧 W/R は Record(T)、S/Z/D は同じ任意の型に置けば公開前の全 clauses も満たす。最後の top publication/use は通常の一 memo による freshening であり新しい constrain demand ではない。□

この事実は native の多相型・constraint store の導出である。h の完全な効果契約や source pending continuation の証拠を省略して whole Yulang の membership と呼ばない。

## 4. 争点の親子等置を公開前に加えた場合

**PR3（固定 anchor への同一化の帰結）。** 公開前に actual B=T を等置し、元制約をすべて保持し、同値類の level を最小値1にすると、同じ二使用は `Bool <: Int` を要求する。

証明。B/T の同値類は boundary1 以下なので、以後の各 freshenAbove は同じ class t を返す。o,W,R は使用ごとに複写できても、各 input と record field は同じ t である。第一使用と selection/succ から `Int <: t <: Q_0 <: Int`、第二使用から `Bool <: t`。第二入力を蓄積すると t の upper Q_0 とその upper Int への replay が Bool と Int の primitive mismatch を生む。D や h の結果型を取り替えても、この包含列は変わらない。□

この proof は、実際の資格が成立することや、実装がこの時点までに等置を消費することを仮定なしで結論しない。公開後の既存 instance への propagation も別の実 consumer を調べる必要がある。

PR1–PR3 は、birth(F)=birth(F) でも、そこで帰属を判断する type pair の level が2と1になり得る具体的な source-generated scalar store を与える。ただし pair の source occurrence はまだ別証拠を要する。同じ birth から「generic/fixed 分類が一致する」と推論することはできない。

## 5. 元の証明への適用条件

生じた選択肢は source typing の検索候補ではない。実際の occurrence 所属を調べた結果が、どの定理を適用できるかを決める。

- 実 replay の正当な occurrence が F/H のみなら、この pair は新資格を持たず、PR1–PR2 の独立使用が残る。その排除を元の全 constructor に一般化する不変条件が必要となる。
- 実 replay に F/F occurrence を付ける正当な対応があり、その pair が公開前に等置されるなら、PR3 の拒否が成立する。これを元の source coverage の反例とするには、同じ完全 source の独立 typing witness または必要な受理契約も要る。
- 実装の集約 source set に F/F が含まれるだけで、actual occurrence の証拠がない場合は、source attribution の対応不足である。これを生成レベル別 SCC という意味論自体の反証にしない。

この適用は新規則の BL-JOINT を実際の公開 store の一点へ戻す。前回の抽象 factorization 条件を仮定して親を閉じたとはしない。型健全性・完全 Call・全 source coverage・combined inference 停止は、各元の義務を保持する。

## 6. 凍結 trace の適用

[別稿](2026-10-24-birth-level-replay-intrusion.md)の査読対象の凍結 SHA-256 は `020da82308ef03c3e5123f03c30bdedd93b1a47fa544be7a4784125275aedc1d`（統合版は査読状態行だけを更新）。同稿の J は本稿の S と同じ行であり、他の公開前の行・物理 bounds・コピーは一致する。同稿 §2 の有限 native 導出を PR1–PR2 に適用できる。

同稿 BR1 は実 contextual relation の生成について source support の集合和を証明した。示された scalar 投影の replay path が生成されれば、`Record(B) <: C` の support は少なくとも e_r=F/F と e_h=F/H を含む。実 pair retention と `any` consumer は、その support を受けた場合に F/F の資格で T=B を発行する。しかし BR1 の結論は依存元集合の計算であり、その各 seed が新コピーの actual occurrence を所有するという結論を含まない。

従って本稿への適用結果は次の通りである。

1. PR1–PR2 の native store と独立二使用は構成できた。
2. PR3 は資格ある等置が公開前に消費される場合の正確な帰結である。
3. 実 source の完全 Call/receipt/effect から当該 contextual path が生成される対応、および新コピーと再利用 occurrence の source 所属 BR-ATTR は残る。実装の source support だけで PR3 の前件を満たしたことにはしない。
4. そのため PR3 を新規則の無条件な反例にはせず、PR2 をすべての qualified source に一般化もしない。旧局所 diagonal lift は、この不足する所属・公開対応を補わない。

これは BL-JOINT の閉包に至らないが、未証明の適用箇所を一つの source の実 pair、生成経路、公開 map まで具体化する。直接の依存は contract の原 reference、生成レベル別規則・BL4/BL5、source Generalize と上記 trace。コード変更・tests/build/probe はない。査読範囲と最終 hash は [sprint outcome](../../tasks/agent-loop/sprints/birth-level-replay-20261024-outcome.md) に記録する。
