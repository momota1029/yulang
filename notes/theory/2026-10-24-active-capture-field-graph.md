# 同じ捕捉関係の固定二 view と元の source 判断

2026-10-24。ORIGINAL-RAW-POSTFIXED-20261024/r1。著者 `/root`。Baseline `e698efa92f35a71a3c3cc6e6880aedc8ffa745d0`。FG1–FG3 は明記した前提の下で独立査読された条件付き結果である。本稿の source 導出に必要な complete memberships は未導出である。[査読範囲と修正記録](../../tasks/agent-loop/sprints/original-raw-postfixed-20261024-outcome.md)を参照。

## 1. 判定対象と変更する証明方法

```text
let rec f = lambda x.
  let g = lambda y. (lambda z.y)(f y)
  in {a=succ(g 0), b=g true}
in f
```

U=Int∨Bool、V={a:Int,b:Bool}。同じ r_f、一つの f invocation h における同じ r_g(h)、元の source/型/event scope と complete Call を保つ。

[前回の判定](2026-10-24-active-capture-generalization-closure.md)では、g の普通の parameter description A を一般化する actual field action が未構成だった。ここでは、独立 source checking が既に持つ **same-value intersection と monomorphic Bind/Name** を適用する。この source 判断は [Source-Generalize](2026-10-08-source-generalize-definition-and-proof.md) §3 に定義され、scheme/export/instance map を定義に含まない。従ってこの別の source 証明に、先に polymorphic J_pub を証明するという前提はない。

必要なのは、同じ actual g と同じ world における二つの完成した complete Function memberships である。Parameter に二つの異なる型 assignment を与える方法ではない。

## 2. 一つの actual inlet と二つの checked view

f と g の source Parameter endpoint は U に一度固定する。g の actual stored inlet も I_U に一度固定する。A∈{Int,Bool} は以下の二つの **定数として選んだ checked view** の添字であり、新しい generic parameter ではない。

```text
I_A = I_U ∧ Ret_A
G_A = complete checked Function view at checked inlet I_A,
      retaining the same g provider, source body and all original phases
G_cap = G_Int ∧ G_Bool
```

[CA1](2026-10-24-original-call-admission-construction.md) は、任意の independently admitted I_A carrier を同じ actual I_U inlet へ送る。actual Return で束縛される一つの y は U の証拠と、その checked challenge の A の証拠を持つ。普通の Parameter declaration の assignment は U のままであり、y の actual event tuple に対する追加の証拠を使う。

各 G_A の Function membership は、全 actual observations を元の descriptor で検査して導く必要がある。広い `U→U` という表示から `Int→Int` を結論してはならない。また raw source が y を返すという事実だけでは、任意の別の complete production relation の全 alternative が同じ相関を持つとは言えない。以下の適用は、この区別を保持する actual complete memberships を入力に取る。

## 3. 固定使用に対する全 field graph と action

field graph の有限 schema は、R1 の実 declaration registry と各 source constructor の **全 operand telescope** を使って作る。未知の field を除外して小さな graph にしない。各 latent invocation の actual event は schema の parameter であり、有限個の runtime events という仮定は置かない。

| owning constructor / node | actual fields と edge | 二使用での action |
| --- | --- | --- |
| recursive registration f | `MemberEntry(C_f,r_f)`、actual provider/capture、`Internal(C_f,r_f)` と complete joint relation | 同じ node と relation。g の C_g に付け替えない |
| g Lambda / capture | R1 の r_g(h)、`Resolve(use_f,f)`、同じ r_f と全 relation への ActiveCapture | 同じ captured reference。先行 scheme や completed external capture を仮定しない |
| Parameter x,y,z | 元の Desc と original type scope。ここで選ぶ assignment は U,U,V | 一つの assignment を共有。Int/Bool ごとに y の Desc を再割当しない |
| checked G_Int/G_Bool | 二つの既存 structural constant、全 domain/checking/observation 証拠 | 同じ r_g(h) の conjunction。各証拠を明示した側へ射影 |
| g initializer / Bind | 一回の Lambda allocation、actual Return/world、同じ g の G_cap 証拠 | 実 initializer と return tuple は共有し再実行しない |
| q_g0 / q_gtrue | 別の実 Call occurrence、元の callee/whole carrier/receipt/Force/body/return ports | それぞれの元の occurrence を保持。Name は同じ g の証拠を読む |
| g invocation / wrapper | actual y、current world、r_w(h,k)、z の actual Return、pending suffix | EventField は同じ actual event のまま。異なる Call の event を同一視しない |
| logical checking proof | original ViewLogic/EventProof/Check、全 dependency telescope | 原位置を保持。実行済み Shared/OneShot evidence は複製しない |
| primitive、inherited effect/permission、future | 元の declaration、whole contract、全 response/provider/future maps | 同じ field を恒等で運ぶ。新しい blanket permission を付けない |

表は各 constructor の全 dependent fields を包含する graph constructor を指定する。たとえば Internal edge の対象は f の表示型だけではなく、元の全 joint relation である。再帰参照は登録済み node に戻り、field を無限に展開して新しい witness を選ばない。

**補題 FG1（固定使用の全 field 恒等作用）。** 上の graph に完成した同一 joint evidence があれば、g の monomorphic Name 二使用は raw root、全 Shared/OneShot evidence、型 assignment と既存 event fields を共有したまま、G_Int と G_Bool の証拠をそれぞれ与える。

**証明。** Bind は actual Return の同じ値/root/world と G_cap の証拠対 `(d_Int,d_Bool)` を一度だけ格納する。Name の規則は格納した binding の同じ current-event restriction を返す。左使用で π₁、右使用で π₂ を取る。積の restriction は成分別なので `π_A(d|e)=π_A(d)|e`。他の全 fields は元の binding projection に残り、射影は provider/world を選び直さない。Internal/ActiveCapture の参照先も同じであり、各再帰辺に恒等を使う。新しい invocation は元の Call の Event constructor だけが作る。以上は型 assignment や未実行の future ごとの existential witness を別々に選ぶ操作を含まない。□

FG1 は一般の ActiveCapture に対する polymorphic retain/fix classification を完成したという主張ではない。全 field を持つ固定された source 証拠の monomorphic use を構成する。そのため「A が fix walk に到達しない」という未証明の事実を使わない。

## 4. 独立 source 導出への具体的合成

**補題 FG2（二つの complete memberships からの source body）。** 原 recursive constructor が同じ f/world と各 actual g に対する G_Int/G_Bool の membership を同時に構成し、元の local source/primitive laws を満たすなら、元の source checking 規則でこの body の V 結論を、同じ r_f と同じ joint witness strategy の下に導ける。

**証明。** 有限の source rule tree は次の順に作る。

1. g の actual Lambda/source body proof を保ち、同じ value/world に対する二 membership を §3.2 の intersection introduction で G_cap に結合する。Lambda の actual inlet/Parameter assignment は §2 の一つのまま。
2. 元の Bind が g の一回の RHS Return を同じ環境へ入れる。FG1 により q_g0 の Name は G_Int、q_gtrue の Name は G_Bool を得る。両 Name は新しい f や g を allocation しない。
3. literal0 と true の original ground laws、selected Name/Return/Delay 構成、CA1/CA2 により、それぞれ I_Int/I_Bool の source argument と full original checked challenge を構成する。完全な Function elimination は、この段階では **構成済み** membership にのみ適用する。
4. q_g0 の complete result は Int、q_gtrue は Bool。succ の authentic Int input/output law と元の Call/Bind を合成し、field a:Int、field b:Bool を得る。元の record field constructor と ordered source composition を使い V を得る。latent data fields の強制を追加しない。
5. f の recursive introduction は supplied joint constructor の同じ member/world conclusion を用いる。最後の Name は同じ f を返す。source tree の証明参照 cycle は、この independently justified recursive rule でのみ閉じる。

全 source checking は original scopes で行い、二つの使用が independent Shared witnesses を持つことはない。q_fy や wrapper の Call は g の actual body proof に残る。return の型だけを取り出して途中の complete operation を捨てない。□

FG2 の前提を証明するのが [raw-observation 構成](2026-10-24-original-raw-observation-postfixedness.md) である。その稿が閉じていない premise を FG2 に代入して閉じたとはしない。

## 5. Native history との比較で必要な結論

上の独立 source witness が完成すれば、元の parent theorem の「正当な source typing を推論が被覆する」という量化に入る。特定の polymorphic witness に限定されていないので、固定 G_cap による source 証明も対象である。推論器へ intersection search や別の型生成を追加する提案ではない。

[native history](2026-10-13-nested-live-root-generalization-derivation.md) §4 と [SCC 資格](2026-10-24-value-scc-qualification-proof.md) の固定結果では、q_fy の G/F extrusion は C=B,D=R を加える。C の level は1、g publication boundary も1。B=C の class は freshenAbove で共有される。第一使用は `B<:S0<:V0<:Int`、第二使用は `Bool<:B` を要求する。従って `Bool<:Int` が必要になり、original disjoint ground constructors の規則に反する。D=R はこの矛盾には不要だが、元の operation から削除しない。

従って **original joint source witness が得られた場合**、この lawful history に対する source coverage の主張は反駁される。その場合の disposition は REFUTED であり、健全性全体を PROVED にするものではない。この条件は raw-observation 稿の最終適用判定と独立査読で判定する。

### FG3: 必要な受理結果に対する独立の含意

`RequiredAccept(P)` を、ユーザーが明示した自然な推論の受理契約とし、`Infer_intr(P)` を元の level/freshening と選択済み intrusion を持つ推論結果とする。上の P0 について、次の含意は full source membership の導出とは独立に成立する。

```text
RequiredAccept(P0)
  ⇒ ¬(∀P. RequiredAccept(P) ⇒ Infer_intr(P) succeeds).
```

証明。前段の retained native constraints から `Bool<:Int` が必要になる。元の primitive constrain case は distinct Bool/Int の比較を受理しない。従って `Infer_intr(P0)` は成功しない。P=P0 を全称結論に代入すると矛盾する。□

FG3 は RequiredAccept(P0) を本稿で仮定なしに成立済みとするものではない。reference Simple-sub の受理は確認済みの native 事実だが、Yulang の当該受理契約や元の CompleteMem witness と同一ではない。ユーザーへの直接質問でこの一件の意図を確認している。回答がまだ無い間、FG3 の前件を成立済みと扱わない。これは `'e?` の意味の再質問ではない。

## 6. 今回の適用判定

raw-observation 稿 r1（査読対象 SHA-256 `23fdc511113c927452a710b43f02d1b063fc7db36a65e5eab4ad6ee0d61993fb`）を適用した結果、g/wrapper の返却相関 RP1/RP2、record の原 field provenance RP3、prefix/suffix RP4、任意の exact H に対する relative lift RP5、candidate-relative input RP6 は明記した範囲で構成された。しかし actual source observation から元の full `P_F*[S]` への map（RP-FULL）に加え、各 f/g/wrapper の formation/profile、各 source world の joint guard、carrier/retained-field の全 case が未導出である。独立査読の MAJOR 指摘を受け、同稿 §6 はこの全 owner-indexed family を列挙するよう修正した。従って FG2 の recursive constructor 前提と G_Int/G_Bool の完成済み memberships を代入するところには到達していない。

固定二 view は polymorphic J_pub の前提を使わない source 証明方法であり、FG1 の全 field 恒等作用は構成できた。しかし元の parent coverage に対する反例はまだ確定しない。FG3 も、明示的な受理契約への回答前は条件付きである。全言語の保存・進行、主型性、combined inference 停止の完了を結論しない。

依存は sprint contract の25固定入力。実装・テスト・compiler execution は変更・実行していない。最終成果物 hash、独立査読と親判定は sprint outcome に記録する。
