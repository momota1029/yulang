# Scoped weight の parallel join と継続観測

Assignment-ID: SCOPED-WEIGHT-JOIN-20261024/r1
Author: `/root/astra_scoped_join`; descendants: none.
Status: 未査読の構成的数学。source/native realization と production authority は OPEN。
Post-freeze review: r1 の定理 1–3 は明記された観測言語の範囲で独立査読 ACCEPTED、BLOCKING/MAJOR 指摘なし。[査読記録](../../tasks/agent-loop/sprints/cooccurrence-source-20261024-outcome.md)を参照。この receipt のみ primary が査読後に追加した。
Contract: `tasks/agent-loop/sprints/cooccurrence-source-20261024.md`, SHA-256 `f2c29073586fad9ac2ec260505f5b58ac83eab12290de664de51bf8a13073e60`。
Baseline: `5fb43a1e61336153496f745e51d6782816561f88`。
Requested model/effort: Astra/medium; observed model/effort: UNKNOWN。

## 1. 親、状態、観測の区別

親は元の承認済み source 領域の任意の型導出と有限実行 prefix に関する全言語健全性である。Simple-sub A/B、主型性、停止性、F1/FK1 を含む独立した foreign continuation の量化は変更しない。本稿は CO-3 の「どの parallel aggregate なら保護観測を保存するか」を具体化する。実行前の引数保護と正確な共変位置の共起が先であり、`'e?` を独立の意味論にしない。任意の A_all を採用しない。

固定した完全な非 scope 座標 w ごとに、有限な状態 x=(T,U) を考える。T は input-route tag、U は protection scope の集合。w には attachment、provider、receipt、receiver、residual lineage、joint witness、origin、grant、query 用のその他の全座標を残す。別の w を本稿の join で同一視しない。receiver activity や Match が異なる行も別 fiber のままである。

継続 C は次の三操作の任意の有限列である。

```
StampInput(u)(T,U)    = (T ∪ {u}, U)
ProtectBody(s,u)(T,U) = (T, U ∪ {s})  if u ∉ T; otherwise (T,U)
Release(s)(T,U)       = (T, U \ {s})
```

空継続も含む。名目 token は任意の有限 support に対して fresh token を取れるものとする。これは数学的名前モデルの前提であり、有限整数 ID allocator の無限実行保証ではない。操作は既に正当化された同じ w に適用するものとし、生成、許可、実 source 到達性を与えない。

代替集合 A に対して観測を三段階で区別する。

* M_s(A): ある x∈A で s∈U_x。
* M_K(A): 有限 K について、ある同じ x∈A で K⊆U_x。
* E_{P,N}(A): 互いに素な有限 P,N について、ある同じ x∈A で P⊆U_x かつ N∩U_x=∅。

空 K/P/N は非空性を観測する。M_s の別々の真値を同じ witness 上の連言と読み替えない。実際の P_j/PF_j は D_j、Live、F_j の同じ tuple での連言であり、その tuple による選別が固定された後に限り M_s 型の結果を適用できる。

## 2. 座標 union の最小 discriminator と正しい単独観測 summary

座標別 union j∨(A)=(⋃T_x,⋃U_x) は一般には不適切である。

```
x1=({u},∅), x2=(∅,∅), C=ProtectBody(s,u)
M_s(C[{x1,x2}]) = true
M_s({C(j∨({x1,x2}))}) = false
```

同一 w の二状態、一 tag、一 scope、一操作である。代替一つでは座標 union は恒等、操作ゼロでは M_s は union により保存されるので、その二尺度で最小である。これは抽象的座標 union の反例であり、Oracle `parallel_union` の解釈も actual source reachability も証明していない。

非空有限 A について代わりに

`α(A)=(I,V)=(⋂_{x∈A} T_x, ⋃_{x∈A} U_x)`

と定め、空集合には別の bottom を用意する。bottom を状態 (∅,∅) にしない。

**定理 1（単独 may 観測の完全 summary）。** 任意の C,s に対して

`M_s(C[A]) ⇔ s∈U_{C(α(A))}`。

さらに α(C[A])=C(α(A))。証明は生成子ごとに行う。Stamp は `(⋂T_x)∪{u}=⋂(T_x∪{u})`。Release は `(⋃U_x)\{s}=⋃(U_x\{s})`。Protect で s が現れる条件は `(∃x.s∈U_x) ∨ (∃x.u∉T_x)`、すなわち `s∈V ∨ u∉I`。他 scope は不変。非空性は各生成子で保存される。継続長への帰納で得る。□

parallel join は `(I1,V1) ⊔ (I2,V2)=(I1∩I2,V1∪V2)`、bottom は単位元となる。従って可換、結合的、冪等であり、各生成子と任意の合成 C はこの join に分配する。追加の状態相関を仮定せず、任意の有限継続を扱う。

これは M_s と非空性に対して必要十分な summary でもある。V の差は空継続で検出できる。I の差にある tag u は、両集合の全初期 U にない fresh s に ProtectBody(s,u) を施して検出できる。よって全 C,s の同じ観測は I,V と非空性の一致と同値である。

**系（座標 union の適用判定）。** 非空 A の j∨ が全 C,s の M_s を保存する必要十分条件は `⋃T_x=⋂T_x`、つまり全代替の T が等しいことである。十分性は j∨=α。必要性は不一致 tag と fresh scope による上記 discriminator。これは固定 tag/guard congruence の実際に確認可能な条件を与える。許される future guard tag を G に限定する場合は全 `T_x∩G` の一致が同じ十分条件となるが、親の unrestricted 継続をこの制限で置換しない。

**限界。** A={(∅,{s}),(∅,{t})}, s≠t では M_{ {s,t} }(A)=false だが α(A) の単一状態では true。α は joint protection、exact state、受領ごとの選択を保存する表現ではない。

## 3. 正の joint 観測には有限 antichain が必要十分

`x ≼ y ⇔ T_y⊆T_x ∧ U_x⊆U_y` と定義する。y は x より多くの正の保護観測を満たし、missing-tag guard も少なくとも同じだけ成立させる。各生成子はこの順序に関して単調である。Stamp は tag 包含を維持し、Release は scope 包含を維持し、Protect で x に新しい s が付けば y は既に s を持つか、u∉T_y により新しく得る。よって全 C が単調。

有限 A の極大元だけの集合を Max(A) とする。同一状態の重複は set 化するが別 w はまとめない。

**定理 2（正の joint 観測の特徴付け）。** 有限 A,B について、任意の有限 C,K で M_K(C[A])=M_K(C[B]) となる必要十分条件は、

```
∀x∈A. ∃y∈B. x≼y
かつ
∀y∈B. ∃x∈A. y≼x
```

すなわち下方閉包の一致、同値に Max(A)=Max(B) である。

十分性: 各 x の対応 y を C の単調性で運び、K⊆U_C(x) なら K⊆U_C(y)。逆包含も対称。

必要性: x∈A に対して B に x を支配する状態がないとする。H を A∪B の全 tag support とする。各 u∈H\T_x に、互いに異なり全初期 protection support にない fresh scope q_u を選ぶ。C は各 ProtectBody(q_u,u) を一度実施する列、K=U_x∪{q_u | u∈H\T_x} とする。x は K を満たす。B の y が K を満たせば U_x⊆U_y かつ全 u∈H\T_x が T_y にないので T_y⊆T_x。これは x≼y に矛盾する。空集合の差は K=∅ で検出する。対称方向も同じ。□

従って単なる powerset image の言い換えではなく、正の joint 観測に関する最大の「状態削除による」圧縮を得る。実際の同一 w の B が A の代替なら、この条件は具体的に検査可能である。

antichain の join と作用を

`A ⊔ B=Max(A∪B)`, `C⋆A=Max(C[A])`

と置くと、join は可換・結合的・冪等、空集合が単位元。さらに

```
C⋆(A⊔B)=(C⋆A)⊔(C⋆B)
D⋆(C⋆A)=(D∘C)⋆A
identity⋆A=A  (A は antichain)
```

が成立する。理由は有限集合で削除された元は残った極大元に支配され、その関係が C,D の単調性で維持されるため。途中の Max は最終 Max を変えない。

## 4. 負の joint 条件まで読む場合の関係表示

上の antichain は E_{P,N} を保存しない。例えば (∅,∅)≼(∅,{s}) だが、前者だけが N={s} を満たす。従って実 consumer が同じ代替の不在と存在を混ぜるなら、正の antichain を無条件に採用できない。

**定理 3（完全な protection pattern には全相関が必要）。** 有限 A,B が全 C,P,N で E_{P,N} を一致させる必要十分条件は A=B。

十分性は自明。必要性では x∈A\B を取り、H を全 tag support、S を全初期 scope support とする。各 u∈H に fresh q_u を選び、C を全 ProtectBody(q_u,u) の列とする。P=U_x∪{q_u | u∉T_x}、N=(S\U_x)∪{q_u | u∈T_x} と置く。初期 U の全座標と T の全座標がこの pattern に符号化されるため、C(y) が満たす iff y=x。従って A では真、B では偽。対称差の逆方向も同じ。□

この観測言語に対しては有限関係 R_w⊆TagSet×ScopeSet が十分であり、異なる状態を削除する圧縮は不可能である。ただし DAG 等による同じ関係の圧縮保存を禁止する主張ではない。関係 union と pointwise 作用は、空関係、identity、結合的な順序付き合成を持ち、`C[R∪S]=C[R]∪C[S]`、`D[C[R]]=(D∘C)[R]`。定理 1–3 は、この既知の関係表示から何を捨ててよいかを観測ごとに正確に減らしている。

全ての表現で、C が触れない独立 scope r は各状態で元の membership を保持する。Release(s) は s だけを消す。α/antichain は許された観測についてのみその独立 scope を保存し、完全関係は joint pattern も保存する。scope を family 名や static class に統合しない。共同の injective tag/scope renaming は包含、交差、union、極大元、各生成子と可換なので三構成に持ち上がる。所有権 capture 稿の global freshness、external ID 固定、shared map、sealed inventory または persistent extension の前提は必要なままである。

## 5. CO-3 への適用と actual owner

旧稿は完全 tuple を保持すれば安全と示した。本稿は CO-3 の aggregate に対して三つの精密な判定を与えた。単独 existential query だけなら (intersection tags, union protections) が完全、正の joint query なら dominance coverage が必要十分、任意の protection pattern なら全状態相関が必要である。共起による static class ごとに、元 w の区別を保持した各 fiber に適用できる。これにより「全情報を保持すること」という未分解の前提を、実 consumer の観測と aggregate の具体的方程式へ分解した。

`candidate_scope.rs` を直接読んだ。`ScopeTransformer::{stamp_input,protect_body,release}` は §1 の生成子を構築し、`AddCondition::holds` は初期 tag の missing disjunction、`evaluate` は初期 input を guard に使う。`then` は既存稿の J/keep/B の順序付き合成である。本ファイルには parallel join API も witness table もない。従って本稿の aggregate が実装されたとは言わない。既存 ordered-composition 証明をその三生成子の有限列という前提内で再利用した。

旧 CO-3 稿が調べた Oracle の `rewrite_type_vars` → `push_compact_var_with_unioned_weight` / `merge_compact_vars` → `ConstraintWeight::parallel_union` は未解決の source owner である。その filter intersection と entry 挿入を T/U のどちらかと同定する証拠はない。本稿は Oracle を再読せず、これら locator は frozen CO-3 audit に帰属させる。座標 union 反例をその実装の失敗とは記録しない。

| TODO | 入力、owner、必要な出力、正確な falsifier |
|---|---|
| CO3-OBS | Primary/source consumer owner: P_j/PF_j の D_j/Live/F_j を固定 w と変動 T/U に分解する。必要なのは同じ aggregate fiber 内で全 selection predicate が一定という証拠。異なる receiver/route を summary 後に選別する一例が falsifier。 |
| CO3-JOIN | 上記 Oracle aggregate owners: concrete weight/origin の解釈 γ と query 対応を提示し、採用する観測クラスに応じ α equation、dominance coverage、または relation equality を証明する。§2 の二状態または §2 末尾の joint discriminator がその解釈で actual constructor から出れば反証。 |
| CO3-CONT | native relation/replay と `ScopeTransformer::then/evaluate` consumer: arbitrary future continuation が同じ fiber に作用し、遅延 fact と edge の joint pairing を失わないこと。別 route の guard を共有したり、release 後に旧未変換 alias を同じ観測へ送ることが falsifier。 |
| CO3-FRESH | `prepare_candidate_fresh_use`, `candidate_context.rs::rename_fresh_contexts`, capture owners: ownership 稿の単一 injective map と latent inventory を提供する。fresh local ID と external scope の衝突、または同じ guard の別写像が falsifier。 |

これは read-only correspondence TODO であり、instrumentation/production edit の承認ではない。実装はユーザーにより除外されている。CO-1/CO-2/CO-4、source 全構文、levels/extrusion/qualifying intrusion/generalization、foreign continuation 構成、自然な推論と主型性は残る。一つの C に対する局所作用を F1/FK1 の discharge としない。

## 6. 依存、帰属、検査、停止

以下の SHA-256 は現 worktree の bytes に対して全て一致を確認した。

| Input | SHA-256 |
|---|---|
| cooccurrence clarification | `c9eb9b8d274172f02bc82088896c30dd92e219a02adf6ba22418b2cc34207d12` |
| cooccurrence preservation | `0c5731f1b287c1016d08b645707533a482832aa44dce6b93aae899375c721c84` |
| compose scoped construction | `773a1ed4c2ebe7503438c57a06acd23e03fbc1fd0d6ae30260848c4430fe676e` |
| ownership capture | `44d69d6506f14c1658d7670ef68c46348d1315ce98ff1d2677f68993c5e00ea6` |
| source type safety tex | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| candidate_scope.rs | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |

cooccurrence preservation の author は `/root/astra_cooccurrence_proof`、査読後 receipt 追記は primary。以前の algebra/ownership の帰属は各 frozen artifact に従い、本 producer の成果にしない。再利用したのはその明記された有限 algebra、共同 renaming、所有権仮説付き構成のみ。旧 binder-only A_all、独立 marginal witness、withdrawn bypass は再利用しない。

三段階: dependency/source audit、join/観測特徴付け、親への適用と凍結。上限 190 秒、三段階、全予約を charge し observed active duration は UNKNOWN。検査は dependency hash、直接 source inspection、数学的導出、artifact whitespace/fence inspection のみ。tests/build/compiler/network/Git は実行していない。独立査読は未実施であり primary が別に割り当てる。

新規・scratch path は本ファイル一つのみ。handoff は最終メッセージ一つ。r1 を凍結し書込み終了、descendants ゼロ。次は Luna intake、独立査読、CO3-OBS/CO3-JOIN の owner 対応である。worker は STOPPED、親は OPEN。
