# Generated pure-read Call: descriptor, field maps, and local typing

Independent review accepted GC1–GC4 in their stated scope and HC-RESULT for the selected immutable Name/ReadInvoke constructor, with no BLOCKING/MAJOR findings. Frozen input `63b754e2b5e211df41a13d15c52c9169b47fa26bbbe785bc5df8887ead2723c4`; only this receipt was added after review. Actual profile/permission formation, missing independent arm laws and recursive operand realization remain open. The candidate/pending wording below records producer freeze time. See the [outcome](../../tasks/agent-loop/sprints/generated-call-operator-20261024-outcome.md).

GENERATED-CALL-OPERATOR-20261024/r1 — candidate proof, independent review pending.
Author: `/root/astra_corrected_machine`; requested Astra/medium; observed UNKNOWN.
Baseline: `5228829724182a87ae3aaf0bfcff68607557dbb1`.

## 1. 対象と追加された実際の構成子

元の source は fresh-valuebind-complete-call §1 の `h x`、callee は immutable `Name h`、argument は `Delay(Name x)`。同稿 VB1 の実際の新しい dynamic binding と resulting world を用いる。以前の x/root/world を値置換しない。H* はこの入力の既存の完全な declaration、F_h=H* は同一値 checking instance、inlet は既存の `Comp(empty,A)`、A=Record(a:Int)。以下の議論はこの型の特別な形には依存しない。

今回の実質的追加依存は authoritative `pure-read-call-result-constructor` §§3–5 である。これは既に選択された source constructor であり、任意の P_H* を新しい Comp 表現へ埋め込む仮定ではない。元 q_h の result occurrence に、同 §4 が指定する

```
R_h := ReadInvoke(H*,D_h,IF_h)
```

という完全な decorated descriptor を構成する。D_h は H* の独立な complete checked-challenge telescope、IF_h は元 Application から構成する complete frame。H* の body result を invocation result と同一視しない。元 endpoint E_h,A_h の syntax 上の occurrence は保持する。この constructor の complete descriptor 解釈を採るのであり、任意の別途固定された Comp interpretation との同値性は主張しない。既存 complete Comp port を持つ場合は §5 の別 instance を使える。

これは declaration/schema の存在である。h の membership、actual whole-carrier admission、各 independent arm の semantic law は schema の存在から得られない。

## 2. 実際の generated diagram と field actions

IF construction §4, Call case (398–407) に従い、子の Name frames、whole Delay slot、actual CalRet からの dependent Bind、ExecuteCallable frame、return/future references、全 ArmDecl の IF-Insert/Use をこの順で構成する。registered reference は元 registration と substitution を保持する。新しい result envelope、source arm の選別、owner=receiver の仮定を加えない。

任意の dependent record T、元 source occurrence s に対し `tag_s(t)=(s,t)` とする。これは predicate を満たす値を発明する関数ではない。source-signature §3.2 の operand/use/insertion injections の具体的 instance であり、元全 field を残す。以下は全 schema の写像と、実際に到達した observation の evidence action を区別する。

| 元 field family | generated map / evidence action |
| --- | --- |
| callee telescope, provider/root, role, entry, profile, hard guard | `tag_callee`。Name Return の時だけ同一 actual h と current C1 を取り出す。callee を実行する前に provider acceptance を作らない。 |
| whole carrier, captured paths, argument dependencies | `tag_arg`。actual Delay は同じ Name body と capture を保持。carrier の将来の Force を formation 時に実行しない。 |
| checked challenge, other environment, holes, admission | 子証拠を同じ joint index で original challenge constructor に渡す。domain は固定 D_h。source Delay はその diagonal instance で、任意に admitted な穴の domain を縮めない。 |
| receiver receipt, entry, body, designated consumer | actual receiver branch へ `tag_receiver`。receipt は actual receipt transition、entry と consumer は H* の actual producer の対応する phase。body と consumer は別 slot。 |
| Bind result/rebind | 実 Return `(v,r,C')` を元 result-to-rebind constructor に渡す。値、root、world はその三つ組の projection。Return 前の suspended suffix は関数のまま保持する。 |
| request, response, raw continuation | operation instance、origin、response endpoint、handle を恒等に保存。suffix のみ元 Bind によって合成。resume は actual current C' で同じ raw handle を再開し、receipt を replay しない。 |
| returned value and output-dependent future | `tag_result` と `tag_future(v,r,C')`。実際に返った provider の元 dependent family を使い、h 自身の future family に置換しない。 |
| inherited guards, scopes, authority, nu/K/D | 同じ tuple の元 evidence を各 tagged field に移す。future restriction は元 hereditary action。時点依存 guard は後の実 event で必要。 |
| W/Z and other declarations | 各 actual arm に独立 `tag_arm(a)`。元 output/change relation、provider、future、hard guard と license を丸ごと保持。source trace から arm witness を生成しない。 |
| genuinely local Call introduction | 元 q_h formation と adopted upper seed/exposure のみ LocalOrigin。source u_f と checking u の incidence を別に保持。 |

**GC1 (dependency squares).** 上の maps は original dependent incidence と可換する。

証明。record slot projection p に対して `p_s(tag_s(t))=p(t)`。二つの shared fields の equation は元の一つの tuple の equation を両側に使う。Bind では source side の result projection も target side の rebind projection も同一 actual `(v,r,C')` を返す。Request の場合は、元 Bind の equation `Req(q,C,k)>>=s = Req(q,C,λa.k(a)>>=s)` の両側が同じ q,C,k,s を保つ。provider-dependent future はその同じ result projection を index にするため可換。Ref/Scope/Rename は元 substitution を全 field に一度適用する。有限 registered cycle は pointer と同じ substitution を保つので、この証明は cycle を unfold しない。primitive の opaque predicate を勝手に変換する場合は含まない。□

**GC2 (partition).** generated partition は全 Operand/Ref partitions と実 local introduction の tagged union である。GC1 の projections を source-signature §3.4 の各 constructor に適用すると PortProv とその field correspondence を得る。shared equation は origin を合併しない。特に result provider を q_h-owned と再分類しない。未選択 arm の schema は残るが license は増えない。無注釈という事実は q_h 自身の formation にだけ作用し、輸入した H*/argument/arm の profile や hard guard を消さない。ここでは「無注釈なら全欄が FullProtection」という規則を導入しない。□

GC1/GC2 は source-generated diagram の実際の field maps を与える。別途固定された foreign profile への semantic correspondence ではない。

## 3. 独立な局所 theorem の正確な量化

j を original joint index、e を arbitrary independently admitted event とする。`Operands_h(j,e)` は次の **子の** judgments の dependent package：

1. valid immutable environment/world と同じ actual h の hereditary H* membership（identity VIncl）；
2. actual argument carrier の complete inlet judgment と元 challenge constructor が要求する独立な context/hole/whole-carrier admission；
3. 元 phase transitions/Bind の operational rules、typed primitive leaves、および必要な既存 scope/authority/hard-guard evidence；
4. whole operation の非 source arm を論じる場合だけ、各 actual arm の独立 local typing/admission/license law。source branch の theorem にはその branch の実行証拠を要求しない。

この package は q_h の結果 typing、composite C0、完成済み TypedCallCert、recursive f membership を含まない。h の complete membership は正当な operand judgment である。その証明を actual source の外側で取得できるかは別の introduction obligation である。

**GC3 (uniform source local typing).** 原 source relation M_E の任意の有限 observation derivation δ、任意の original joint witness w に対して

```
typing_h : Π j,e. Operands_h(j,e) →
           Π δ : M_E(q_h,O,w;j,e).
           DescMem(ReadInvoke(H*,D_h,IF_h),O,w;j,e)
```

を構成できる。全 original compatible response/future extensions について同じ関数を使う。M_E derivation を作ること、event の authority を schema から作ることは結論ではない。

証明は δ の phase inversion と有限 response/resume development に関する帰納法である。

(a) initial/lookup prefixes：Name formation と元 binding obligation を保持し、未実行の suffix は dependent function として保存。ここで checked d、receipt、Force を捏造しない。これが ReadInvoke §3 の第一 clause。

(b) callee Return：Name/Return inversion で同じ h/provider/current world。identity VIncl はその decomposition を変更しない。actual Delay を作った場合だけ NameDelay lemma D を適用し、同じ carrier を元 challenge constructor に渡す。これは R の acceptance theorem の前提を満たす。D_h の範囲を実際の source argument 一個に縮めない。

(c) receipt/entry/receiver developments：同じ h の full membership の R/E eliminators を使う。R は independently formed d の acceptance、E は actual entry/body/consumer と pending/future observations を与える。source type に望む出力をこれらの前提に加えない。

(d) Request：GC1 の Bind equation で untouched rebind/body/consumer suffix を保持。任意の independently legal response と現在の world に対し、短い resumed derivation に帰納仮定を適用する。Return の場合に限り VB1/W により actual result を新しい binding に入れる。divergence には全 finite prefixes だけを与え、result を作らない。

(e) completion/future：E の元 actual returned provider とその future evidence を GC1 で運ぶ。別 provider を h に置換しない。ReadInvoke-Desc (§4) はまさに (a)–(e) の staged evidence と保存した guards を要求するので適用できる。各有限展開の証拠は同じ構造再帰関数の出力であり、展開ごとに無関係な策略を選ぶ compactness 議論ではない。□

**GC4 (arm composition).** 元 operation が source/other arms の実際の Union を持つ場合、complete local law は source branch で GC3、各 other arm でその original local law を適用する case function。Conjunction の場合は同じ shared tuple に両 law を適用して Pair を作る。W は changed-coordinate relation、Z は independent witness を保つ。従って composite typing を前提にせず、genuine independent primitive/arm laws から当該 Op の suspended law を構成する。arm law 自体の存在/真理は証明していない。source image だけで whole production C0 を閉じない。

## 4. DeclContribution と certificate の供給範囲

GC1/GC2 と GC3、必要な場合 GC4 を source-signature §3.4 の
`Op(q_h,k,intro_h,typing_h,operand_interfaces,original_license_fields)`
に入れる。typing_h は §3 で構成した関数であり、出力 tuple の typing を仮定した同語反復ではない。Op の suspended contract として、operand judgments が未実現でも関数自体を格納できる。従って source-only ReadInvoke result/phase の DeclContribution を実際に構成できる。full Op license は元 independent arm/license fields をなお要求する。

G_call の original conjunct addresses に対応すると、WF は元 H* formation、VIncl は identity、argument は NameDelay/独立 admission、CIncl は GC3、operation/source observation correspondence は GC1 と phase induction が供給する。receipt は実 phase の時だけ、pending certificate は suffix 関数として供給する。source-generated profile の **incidence/partition** は GC2 により供給済みである。

ただし G_call §5 の TypedCallCert_Dec は exhaustive dependent record 宣言ではなく、supplied decorated profile 等を要求する predicate として記されている。GC1/GC2 から任意の独立 profile predicate の truth は従わない。最初の未供給 field がある場合、それは **actual q_h の profile/permission formation judgment と既存 Call profile rule の適用証拠**である。輸入 field は元 operand evidence があるが、元 local rule にない profile predicate を ReadInvoke の定義で自動的に真にはできない。本稿は指定した constructor envelope の suspended typing/result field を完成させ、未列挙の全 TypedCallCert fields の完成を宣言しない。full W/Z の未供給 primitive law もその各 owner に残る。

## 5. 既存 parent への適用

VB1 の actual fresh ValueBind instance では h certificate の hereditary restriction と newly returned x の A evidence を §3 に渡せる。HC1 の actual admission、HC2 の ordered suffix が GC3 の (b)–(d) を実現する。従って **HC-RESULT は immutable Name callee の selected ReadInvoke case で解消**する。H* が抽象 P を持つことだけをこの case の障害とする旧議論は使わない。

別の accepted complete-port instance で H* の元 complete invocation port が O_h=Comp(E_out,A_out) なら、元 E_h,A_h にその endpoints を用いる。fresh-valuebind §5.1 の ResultPort の各 case と GC3 の同じ phase evidence を合成し、当該 Comp result への CIncl を得る。body-only port ではこの合成は不可。ReadInvoke と任意 foreign Comp を無条件に同一視しない。

source h link の result/phase evidence と inherited field correspondence が得られたため、source-indexed derivation の Call-result slot を conditional local function で埋められる。recursive f の entry realization、actual captured x が A を持つこと、publication、source/native receiving association はこの関数の適用可能性を別途証明する必要がある。親の元独立 hole/future/foreign continuation quantifiers は削除していない。新しい意味規則、ordinary inference の弱化、intrusion qualifier の変更はない。

## 6. Frozen handoff / checks

Assignment/revision: GENERATED-CALL-OPERATOR-20261024/r1. Contract SHA-256 `cbff651522318a4949e6c12de5b4357ab320d8c55c2242d80cd8271b2951fdb5`。契約の19 direct input hashes を byte hash で照合し全件一致。追加 read は primary の明示許可を受けた `notes/design/2026-10-08-pure-read-call-result-constructor.md`, SHA-256 `8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488`、照合一致。同文書は authoritative reviewed constructor、今回 GC1–GC4 は author candidate で fresh independent review が必要。

Reused: VB1/HC1/HC2, NameDelay R/E, IF/native signature constructors. Rejected: runtime whole-substitution of an existing x/root; arbitrary P representation obstacle for the already selected Name constructor; inference of license/guard truth from incidence. Parent application: pure-read generated result and local suspended operator law above. Remaining owner: original profile formation/TypedCallCert declaration and any missing independent arm law; outer source introduction for actual recursive operand realization. Primary owns these integration decisions; no new authority requested or changed.

Checks: documentary constructor/phase proof and input hashing only; `python` executable absent, repeated with `python3` successfully. No tests/build/probes/compiler/Git/network, no production edits, no descendants. Three bounded stages (input/constructor, maps/local law, application/freeze); requested Astra/medium, observed UNKNOWN; exact active elapsed unobserved. Sole new path is this note; no scratch paths. File digest is returned outside this self-hashed artifact. Writer STOP at freeze; no background work or retained lease after handoff.
