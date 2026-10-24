# 無注釈の native source introduction の profile 構成

NAME-RECURSION-PROFILE-20261024/r1。Author primary。Status: PF1/PF2 は selected native licensed projections と記載した独立入力の範囲で独立査読により受理。
Baseline `18222ed99cc1ec963e12198d03a7d6e05257a30b`。
査読対象 `e4fb9567e01197afc9d5fd3474bbbb994f27a2e3915af711e335e7506aeb2803`。査読後はこの status/receipt のみ変更。[outcome](../../tasks/agent-loop/sprints/name-recursion-profile-20261024-outcome.md)に適用範囲を固定する。

## 1. 埋める元 field と意味の境界

[GC1–GC4](2026-10-24-generated-call-descriptor-typing.md) は actual Call の whole field maps、由来の分割、operand certificates に対する uniform local law を構成した。残る native local profile formation を、[選択済み native signature 定義](../design/2026-10-08-native-signature-formation-definition.md) §§2–4 と [構成の §3.4/§8](2026-10-08-source-signature-incidence-construction.md) から実際に作る。

対象は原 source

```
let top = lambda h.
  let rec f = lambda x. lambda y.
    {first=h x, next=f {a=y}}
  in f
in top
```

の Lambda、Name、Call、Record、Result の original introductions と、その reference/operand placements。無注釈の genuinely local governed projections に full protection/no concrete removal を置き、他の成分は元の policy を持つ。これを未指定の foreign profile の真理や runtime authority と同一視しない。元の独立 primitive/history/arm laws、実 admission、現在の receipt/authority はそのまま別の semantic inputs である。

## 2. 型付き profile の構成域

元の source/contract interface graph と registered recursive roots を固定する。Theorem IF/GC1 が全 dependent slots を生成し、native §3.4 が各元 introduction、field、origin partition Ω、元 license-field correspondence を作る。各 actual static boundary β の annotation presence と governed fields はその original source declaration から取る。

同じ root/slot の複数の license witness を潰さず、native §8 の family をそのまま使う。

```
App_N(I,β_r) = Σ Ω,s,p,c. L(I;Ω,β_r,s,p,c)
Key(I,β_r)  = (ℓ,k,field,w)
```

Key はこの App_N の **licensed** constituent/field projection。w はその original governed-license evidence を含む。support の schema だけから Key は作らない。whole contribution ℓ のすべての field を β_r-owned ともしない。

各 local introduction n の元 boundary を β(n) とする。元 field injection により `Own_n` は「実際に n で導入され、そこで no-annotation policy が適用される field」を選ぶ。これは owner と receiver の識別子の一致テストではない。capture/reference/operand 経由の inherited field は、同じ印刷名や β を持っていても、受領先の新規 Own_n に入れない。

### 構成 NP

元 grammar に沿って profile package を作る。

1. **真正 primitive/外部入力。** 元の typed primitive contract の whole profile/license packet を保持する。h、entry carrier、独立 arm の独立入力を、source default で置換しない。
2. **genuinely local unannotated introduction。** その original governed field ごとに、既に選択済みの `FullProtection` と `NoConcreteRemovalGrant` を置く。これらは native source policy の値であり、元 license w を作る constructor ではない。元 introduction/field/scope/evidence を同じ package に残す。
3. **Operand/Ref/Scope/Rename/Insert。** 完全な元 packet を同じ dependent injection/substitution で輸送する。receiver/route の変更だけで policy を再初期化しない。binders、actual provider、current-world index と witness は全体で同じ写像を使う。
4. **Union/Conjunction。** 元 branch tags または同じ whole tuple 上の両 projection を保持した tagged family を作る。schema は全 branch を残し、license のない branch に w を追加しない。別々に選んだ world/hidden witness を Pair にしない。
5. **Op/Bind/Call/Record result。** 元 complete operand interfaces と各 field injection を取り、inherited profiles をそのまま各 constituent へ入れる。新規 local field にだけ 2 を適用する。Op の `typing_q` と original license fields は下の PF2 により供給する。

NP の値は、全 Key へ対応する元 protection/removal/license/scope packet を返す dependent family である。無限の future events や all-view assignments を有限列挙する手続ではない。有限 source graph の constructor schema と、実際に与えられた有限 license derivation に対する fold で表示する。

## 3. 由来、再帰 graph と全 field の保存

### PF1（NP の構成・一意な局所 policy）

原 primitive/inherited/annotation inputs が固定されると、NP は実 source graph の全 native licensed projections に対する型付き family を構成する。任意の Own_n field で選択済み local policy を持ち、任意の inherited field で元の packet を保つ。登録再帰はこの構成を妨げない。

証明。source-interface の two-pass registration により、先に全 declared schema/Ref slot を作り、後に clause と field injections を付ける。Ref のために参照先の本体を無限展開しない。各 actual license witness については、native の有限 L/DeclContribution derivation の高さへ帰納する。

primitive は supplied packet。local introduction はその実 n/field の policy。Operand/Ref/Scope/Rename/Insert は子の同じ packet に元の whole injection を適用する。Union は witness の実 tag、Conjunction は同じ tuple の二つの証拠を残す。Op は実 complete interface の constituent partition を保持し、LocalOrigin と Operand を元 constructor の区別どおりに処理する。従って各 field は一つの original introducing/transport case を持ち、shared slot や equal owner だけで上書きされない。

cycle が schema にあっても、実 w の derivation が有限なら帰納は減少する。無限の unfolded reference tree、全 future の列挙、cycle 上で新しい license を仮定する操作は使わない。license のない fiber には schema と未適用の family を保持するだけであり、その inhabitance を結論しない。

各 field の型は元 dependent telescope の同じ witness/index の型である。GC1/IF の commuting squares により、その protection/removal field と license/provider/scope field の依存関係も保存する。各 Own_n に別の許可値を置く余地は selected no-annotation policy によってない。これは fixed inherited inputs 上の局所一意性であり、異なる opaque primitive completions 全体の唯一性ではない。□

### PF2（元 operator law の供給と static licensing）

元の genuine independent primitive/arm license fields が与えられると、今回の local operators の `typing_q` を、完成済み recursive f certificate を前提にせず構成できる。

* Name は、元 binding certificate から同じ actual value/provider を current event に restrict する関数。
* Record は、**評価後の**各 actual child result certificate から、同じ world で元 field map を組み立てる普通の Record introduction。child computation の効果/pending は元 ordered evaluation/Bind law がその前に扱う。Record formation が latent returned field を追加 Force することはない。
* Result は、その同じ value/world を元 Return-result clause へ包む関数。
* h/f の Name Call は、それぞれの **型付き operand を入力とする** GC3 の uniform 関数。実際にある independent arms は GC4 と各原 law を使う。F の候補に actual f を入れただけで f の完成済み membership を取得することとは違う。
* Lambda/Value-entry は元 Strict constructor の phase composition と原 source Lambda introduction rule。capture/body の actual certificate がある場合の導入関数を保存する。今の recursive component がその前提を実現するという主張を、この static law に含めない。

証明。各関数は元の local operator/source rule と GC の証明で構成される。例えば f の Call の law は

`Π genuine typed operands at F. source Call observation → ReadInvoke(F) evidence`

であり、`ValueMem(F,f)` 自体を結論したものでも、その存在をこの law の生成時に仮定したものでもない。型付き operand の証明引数を λ 束縛している。この関数は tested candidate relation S を参照する guard ではない。実際の recursive body の一段証明では別途 actual f realization を構成しなければならない。

native Op constructor はこの independent law、元 operand **interfaces** と `original_license_fields` を持つ suspended contract である。これらをそのまま入れて original DeclContribution を構成し、元の L-Declared/Reference/Insert rules に沿って、生成できる各 static license の profile を NP で形成する。値の membership、world、現在の受領を license の存在から逆算しない。foreign primitive law または独立 arm law が欠ける場合、その fiber の license を構成したとは言わない。□

この PF2 は、body が sound だから f 自身が typed だという循環を隠すものではない。元 local typing rule の関数を作ることと、その前提を actual recursive source で実現することを分ける。native signature §3.4 の Op が suspended contract であることをこの同じ区別で使う。

## 4. 実 source への全ケース適用

| 実 occurrence | NP と local law の適用 |
| --- | --- |
| outer/inner Lambda | 元 source introduction の local governed fields にだけ default。capture h/f/x の full inherited partition は同じ Ref に残す。inner activation の fresh root を新しい static declaration としない。 |
| Name h / Name f / Name x / Name y | 実 Resolve と original dependency-closed capture/import route。受領先で再度 FullProtection を seed せず、元 packet を輸送する。 |
| `h x` | GC3 の ReadInvoke law、実 H* の whole input/result/profile、q_h の実 LocalOrigin/upper exposure。h の inherited provider/result を q_h-owned にしない。 |
| `f {a=y}` | registered F の Name Call の uniform lawと元 whole argument slot。f の raw root は同じ。未来の actual f Return/inner closure membership は recursive constructor proof が別に供給する。 |
| argument `{a=y}` | actual y の Name certificate と同じ Record field introduction。a field の inherited y evidence と、本当に新しい record-owned fields を分ける。 |
| body `{first=h x,next=f {a=y}}` | first/next の全 child computation の ordered phase interfaces を残す。両 actual Return を得た時点の同じ world/result tuple で Record を形成。h result と fresh inner closure の future はそれぞれ本来の provider に依存する。 |
| 各 Return/future | 元 result path の same-value/provider injection。new record/closure の local fields と inherited field/future の各 origin を保持する。 |

PF1–PF2 を各行へ適用すると、実 source の **native local profile formation** と local default permission component が構成される。GC §4 の「actual local rule がまだ与えられていない」という残余のうち、この selected native no-annotation constructor 部分を埋める。複合 field map を別途入力とする必要はなく、GC/IF の生成図から得る。

一方、型付き source derivation の全部が実現されること、全独立 arm の license、unknown foreign profile predicate、actual event での authority/role-refinement/annotation realization は、NP だけの結論にはしない。G_call の abstract TypedCallCert を全 unknown fields ごと定義し直すこともない。

## 5. 動的保護・解除および source 親への接続

PF1 が保存するのは original origin-bearing licensed packet 全体である。実引数を実行する前の entry protection は元の entry/receipt rule、後の scoped release はその実 dynamic evidence と共起対応を必要とする。local default の NoConcreteRemovalGrant は、別 origin の元から正当な inherited grant を削除する意味ではない。反対に inherited grant があっても、今回の local β が新しい grant を得たことにはならない。

[ユーザーの共起訂正](../design/2026-10-24-cooccurrence-release-clarification.md)どおり、同じ共変位置への集約は source の保護・解除と対応させる。NP は type variable の同一性を理由に receipt、receiver、guard scope、異なる w を同一化しない。ここでは非正則共起 class の算法や concrete compaction の正当性を追加で主張しない。

recursive introduction の immediate native **formation** field には PF1–PF2 の package を供給できる。そこで本当に必要な dynamic admission/world/typed-path guard は、同じ independent context と actual transition law から得る必要がある。candidate membership からそれらの guard truth を捏造しない。この区別により、static Op law の存在を completed recursive f membership と読み替える循環を防ぐ。

元 A/B、全 source-scoped strategy、publication と独立使用、receiving occurrence、combined termination は同じ親義務のまま。本稿はその一つの native source-formation supplier を具体化する。

## 6. 凍結と証拠

契約 `tasks/agent-loop/sprints/name-recursion-profile-20261024.md` SHA-256 `bfb886777e4ef069af70a1f809e6b11baac175eb136285f2e211efbfc2e34c5e` に20直接入力を固定する。中心依存は native signature の選択と構成 §3.4/§8、GC1–GC4、Strict/source source-rule schemas、ユーザーの共起訂正。moving recursive producer の結論を前提にはしない。

primary 単著。紙上の constructor/finite-proof induction と静的読取りのみ。test/build/probe/compiler/implementation は作成・実行していない。査読では、full policy を inherited field に再適用していないこと、schema から license を作っていないこと、uniform local law とその actual semantic premises を混同していないことを確認する。
