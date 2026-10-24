# 遅延した bound 展開の可換性と公開後の解の引戻し

REPLAY-RECEIVER-PROOF-20261024/r1。著者 primary。凍結 r1 の EC1–EC4 は記載した限定範囲で独立査読を通過した。査読後の変更はこの状態行のみ。元の receiving-occurrence 問題を解くため、型制約の可換性、occurrence 記録、一般化後の解を実際に構成する。[契約](../../tasks/agent-loop/sprints/replay-receiver-proof-20261024.md)の元の source・Call・scope・A/B を維持する。

## 1. 比較する二つの有限 native 構成

前稿の実 replay では、h の demand `H₁ <: Function(R₂,J₂)` が `(C₁,R₂,+,1)` と `(D₁,J₂,−,1)` を生成し、その後の `Record(a:B₂) <: R₂` が `Record(a:B₂) <: C₁` へ replay され `(T₁,B₂,+,1)` を生成する。

以下で比較するのは、この局所 constraint fragment の二つの処理順序である。source 評価や原 Scala の構文走査順を交換してよいという定理ではない。初期 row は B,R,J:2 と H:1、全 bound は空。入力は

```text
d = H <: Function(R,J)
c = Record(a:B) <: R.
```

元 `Typer.scala` の constrain/extrude を、E では c;d、L では d;c の順で適用する。各 extrusion invocation の polar memo は最初空である。

### E：下界が先にある場合

1. c の rhs-variable case が R.lower に Record(B) を加える。R の upper は空なので追加比較なし。
2. d の negative Function extrusion は引数を正極性で処理し C を R の copy として作る。R.upper に C を加え、既存 lower の Record(B) を同じ invocation 内で正極性 extrusion する。
3. B の正極性 copy T を作り B.upper に T を加える。B.lower は空なので再帰なし。C.lower に Record(T) を保存する。
4. J の負極性 copy D を作り J.lower に D を加える。J.upper は空。H.upper に Function(C,D) を保存する。

### L：下界が後から届く場合

1. d の extrusion は C と D を作り、R.upper=C、J.lower=D、H.upper=Function(C,D) を保存する。R.lower は空なので T はまだ作らない。
2. c は R.lower に Record(B) を追加し、R.upper=C と比較する。
3. Record(B):2≤C:1 の正極性 extrusion が別 invocation の空 memo で T を作り、B.upper=T、C.lower=Record(T) を保存する。

**EC1（この finite fragment の制約可換性）。** E と L の終了後の物理 store は fresh row の単射改名を除いて一致する。

| row | lower | upper |
| --- | --- | --- |
| H | ∅ | Function(C,D) |
| R | Record(a:B) | C |
| B | ∅ | T |
| J | D | ∅ |
| C | Record(a:T) | ∅ |
| D | ∅ | ∅ |
| T | ∅ | ∅ |

証明。上記全 branch を展開すると表を得る。E の作成順は C,T,D、L は C,D,T であるが、意味名 C,T,D を対応させる bijection が両 store の全行・全 bound・最終 demanded Function を一致させる。全 row/構造比較は列挙したものか level≤1 の保存であり、追加の extrusion はない。□

前稿の全 source-derived store には o,W,Z と再帰/ wrapper の clauses もある。上の同型を B,R,J,H,C,D,T に適用し、他の元の座標は恒等とすれば、それらの同じ clauses も保つ。この事実は二つの全 source 推論履歴が存在することを意味しない。実 source 履歴は L であり、E は局所 constructor 比較のための構成である。

## 2. occurrence を含めると同じ同型は得られない

E の一つの extrusion invocation の pair list は `{C/R, T/B, D/J}`、L の初回は `{C/R,D/J}`、後発 invocation は `{T/B}` である。polarity と target は前節の通り。したがって invocation identity と「どの invocation がどの pair を作ったか」を保つ全単射はない。1個の非空 group と2個の非空 group は対応しない。

**EC2（消去だけから provenance 可換性は出ない）。** EC1 の同型は、actual occurrence identity、source origin/receiver association の一致を結論しない。

証明。既に group 個数が異なるため occurrence を含む同型への自動拡張はできない。L の二つの実 occurrence を E の一つの source demand に写す refinement map を別途構成することは可能だが、その写像は型 row の改名とは別のデータである。特に L の後発 pair の source association を h の元 association と同一にする条件は、EC1 の式の中に現れない。型構造の帰納だけでそれを導くステップは存在しない。□

これは「遅延した extrusion は意味保存できない」という命題ではない。必要なのは actual occurrence を消さず、元 source boundary への対応を導出することだと特定する。元の Call contribution の Origin や receipt の恒等性を、別 sort のこの対応に無証明で代入しない。

## 3. この実 store の親子等置と任意有限回の使用

前稿 PR1 の f 公開 root は o、boundary は1である。P を公開前の全 store、q を B=T の同一化とし、共通 class を t:1 とする。他の同値類は singleton、元の clauses は全て保持する。old store で複写される o,B,W,R のうち、qP では B の class t だけが固定になる。

元の shared C の lower は Record(T)、T は空 bound、q 後は t.upper の自明な t が残るだけで、固定 class から未複写の高い W/R への bound はない。したがってこの具体例では、fixed anchor の下に fresh use ごとの依存が取り残されることはない。任意の quotient に最小 level を付けるだけでこの性質が成立するとは主張しない。

m≥0 回の native freshenAbove を考える。元の各使用 i の写像は

```text
o↦o_i, B↦B_i, W↦W_i, R↦R_i; C↦C, T↦T.
```

qP の各使用は o,W,R を i ごとに複写し、t,C を固定する。元の全 m 使用 graph から後者への写像 q_m を

```text
q_m(B)=q_m(T)=q_m(B_i)=t,
q_m(o_i)=o'_i, q_m(W_i)=W'_i, q_m(R_i)=R'_i,
q_m(C)=C,
```

とする。全他元座標は対応する同じ座標へ写す。各 row は有限 memo で一度複写され、cycle の各再訪はその同じ座標を使う。

**EC3（有限使用 graph の可換性）。** m 回使用後の元の全 store に q_m を作用させると、qP から m 回使用した全 store と同じ clauses を得る（同一 clause の重複は無視する）。公開 root の型も一致する。

証明。元 base store の clauses は q の定義で一致する。各 i の o_i の lower/upper Function、B_i.upper=T、W_i.lower=Record(B_i)、W_i.upper=R_i、R_i.lower=Record(B_i)、R_i.upper=C を一つずつ代入すると、qP の実 freshening の各 clause が得られる。B_i.upper=T は t≤t になり、base の同じ自明 clause に重複する。逆に qP の高い clone o'_i,W'_i,R'_i はすべてこの列挙にあり、t,C 以下は shared base の clauses である。root は同じ o'_i。m=0 は base の式、m+1 は同じ列挙を一つ加える。□

**EC4（同じ有限 client に対する健全な向き）。** これらの m 個の公開 root に、任意の有限 native client constraint L を加える。L の外部座標は q_m で変えない。等置後の graph とその client を満たす valuation η があれば、`ρ(v)=η(q_m(v))` は等置前の m 使用 graph と同じ client を満たす。全公開 root の解釈も等しい。ここで client は有限な制約の集合であり、任意の実行順の solver、追加の let 一般化や全 Yulang の context を量化しているのではない。

証明。Function/Record/Primitive 型の構造帰納により `⟦q_m(t)⟧η=⟦t⟧ρ`。EC3 がすべての store clause の対応を与える。client は同じ公開 root と外部座標を使うので、その全 clause にも同じ等式を適用する。Function の引数の反変性は型の解釈そのものが一致するため問題を生じない。cycle は有限変数への valuation で扱う。任意有限 m に対して同じ構成を使える。□

EC4 は、この実 store における親子等置が有限使用後の native 解を元の解へ戻せるという主張を閉じる。元の任意 client が等置後にも受理されるという逆向きは、既存 PR2/PR3 の Int/Bool 二使用で成立しない。全 Yulang の source typing witness、依存する effect/Call 証拠、source-generalization の全 telescope をこの有限 native valuation 定理から省略しない。

## 4. 元の receiving-occurrence 証明への適用

[source placement 稿](2026-10-24-replay-receiving-occurrence-proof.md)の RP1 を適用すると、内側 f の constituent origin を保ったまま、外側 h の Call argument slot への receiving incidence を構成できる。入力は同稿に明記した authentic Call inputs と local typed field maps である。元の retained graph の upper-boundary query は、その h-call の association F/H に戻る。従って source placement の生成と、その境界を取り出す有限 query は得られた。

一方、RP2 の二つの構造は、新たな delayed solver occurrence の解釈欄だけを変え、source Call の実 field、ordered replay、pair identity、source union と native any consumer をすべて保つ。これは同稿が列挙した構造公理に対する限定的な非含意である。二つの full Yulang semantics や、完備な source typing witness を持つ二実行の構成ではない。RP2 を source 保存の不可能性へ拡張しない。

今回の原義務への適用結果は次の通り。

1. **制約の局所可換性は EC1 で閉じる。** ただし EC2 により、この同型から occurrence の対応を自動的には得ない。
2. **この具体的な公開 store の健全な向きは EC3–EC4 で閉じる。** m を固定した例だけでなく、任意有限 m と任意有限 client 制約に対して実 q_m と valuation の引戻しを与えた。資格が成立するかどうかに関係なく、ここで指定した等置が解を増やさないことが分かる。
3. **元の全解を保つ向きは別である。** PR2/PR3 の二使用は、この等置が元の解を失わせ得ることを示す。採用規則がこの pair を実際に等置するか、いつ消費するか、全 source の typing witness が成立するかを示さずに、主型性の反例とはしない。
4. **RG-OWNER は未証明のまま残る。** 必要な式は `ReceiverOfCopy(p,T/B)=ReceivingValue(UpperBoundary(p,u,r_h))`。RP1 の signature receiving incidence と solver occurrence は異なる sort であり、対応を宣言して証明の代わりにしない。RP2 は監査した構造規則だけでこの式を決定できないことを示した。

従って original Simple-sub A/B、全 source-scoped BL-JOINT、source/Call/event/effect の保存、全体の主型性・combined termination は閉じていない。今回閉じた EC3–EC4 を一般の source Generalize の証明に読み替えない。source-labelled commutation という当初の目標は未達成であり、その名称を RG-LABEL-COMMUTE に変えたことを進捗とは数えない。

直接入力は契約に固定した native reference、source/Call/association 規則と前稿。コード変更、tests/build/compiler/probe はない。独立査読と正確な残項は [outcome](../../tasks/agent-loop/sprints/replay-receiver-proof-20261024-outcome.md) に記録する。
