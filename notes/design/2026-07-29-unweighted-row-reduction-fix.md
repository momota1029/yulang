# unweighted effect-row reduction の incremental solver 修正設計

日付: 2026-07-29

状態: **ユーザ承認済み（v6、2026-07-30）**

調査基準は `c40a5cb49ab5`。根因の確定記録は
`notes/bugs/2026-07-28-local-var-effect-residual-transport-gap.md` の「25回目」を正本とする。
v1 / v2のコード行番号は同 commit の working tree に対して 2026-07-29 に再確認した。
v3で追加したコード行番号とtraceは`4ec031b3`のworking treeに対して2026-07-30に再確認した。
v4のcross-source経路、現行provenance carrier、v3 test 2 controlは`0264e950`のworking treeに
対して2026-07-30に再確認した。
v5のreduction-own unmatched-lower routing、`RowDerivation` carrier、shared enqueue helperの
call-site境界は`09237c6b`のworking treeに対して2026-07-30に再確認した。
v6のordinary lower保存、compaction、positive alias expansion、scheme provenance、
finalization、generalize compact cacheの各経路は`bc1dc55a`のworking treeに対して
2026-07-30に再確認した。v3〜v5のproduction試作は各stop conditionでrollback済みであり、
`bc1dc55a`にはpreflight testと設計だけが残る。v6の型名・API名は、v3〜v5を再導入する
implementation sliceで既存命名へ合わせる。

## 改訂履歴

### 2026-07-30: v6 — scheme projectionをclaim / coverage / lineageへ接続

承認済みv5のURR-G一度目では、§5.8〜§5.10をproductionへ試作し、initial unmatched routeが
作った`1522 -> 1669` claimを、exact `RowDerivationId(196)` carrier、originating reduction root、
`covered = true`として登録できた。§8のv1〜v5 accumulated 18 testもすべてgreenになり、
generic replayの
二重routeは止まった。それでもnested integration gateではinner familyが残ったため、
production差分はrollbackした。記録は`73c5e850`を正本とする。

`bc1dc55a`までの二つのread-only investigationで、残った経路を正確に切り分けた。
`step_subtype`の通常のVar–Var branchは`1522 <: 1669`から、
`TypeBounds::add_lower`を通して`1669 <- Var(1522)`をordinary lower recordとして保存する。
`VarBounds::projection_lowers`はevidence lowerとordinary lowerを無条件に連結し、
`compact_var_bounds` / `compact_lower_bounds`はその全件をcompact graphへ入れる。
`compact_pos_bound_id`は`Pos::Var(1522)`をpositive secondary variableへするため、
generic replayを抑止してもaliasからinner familyへ到達できる。
`positive_aliases_within_scheme`も同じunfiltered lower graphを推移的に辿り、
`capture_generalized_witnesses`も`generalized_projection_lowers`の全recordをscheme provenanceへ
採る。一方`finalize_generalized_compact_root`はmachine boundsを読まず、すでに構築済みの
`CompactRoot`をscheme arenaへfreezeするだけである。

lowering側でこのaliasを作らせない代案も反証済みである。`TypeVar(1522)`は
`inner_r.update (\_ -> before)` / `inner_r.get()`に対応する正当なblock-aggregate effectであり、
lowering時点では後でどのfamilyへ具体化するか分からない。これを消すにはlocal-var v5の
prepare / finish判断を巻き戻す、callback bodyだけを特別扱いする、または全block aggregationを
再設計する必要があり、いずれもsolver relationのownership gapを解かない。

v6は§5.8〜§5.10のclaim identity、compressed coverage root、作成時self-taggingを置き換えない。
Var–Var admissionで同じlogical claim IDをmirror lower recordにも対応づけ、compaction、
positive alias expansion、scheme provenanceが共有する
**scheme-projectable bound view**を追加する。viewはraw recordを削除せず、recordにclaim linkageが
なければ従来のlowerをそのまま返す。claim linkageがあれば各claimのcompressed rootを
projection時に`live_coverage_by_root`へ照会し、少なくとも一つuncovered claimがあるrecordだけを
一回返す。返すprovenanceはuncovered claimだけに限定する。同じcanonical recordにcovered claimと
independent claimが同居する場合、endpointは一回projectし、independent claimだけをschemeの
根拠にする。

coverage rootの最後のlive stateが消えたときは、raw relationがまだactiveなら再びprojectableに
なる。したがってlivenessはclaim作成時のbooleanではなく、projection時のcompressed-root lookupで
判定する。現行`CompactCollector`のcacheとpositive-alias cacheは一回のimmutable pass内だけなので
個別invalidationは不要だが、analysis sessionには`(root TypeVar, ConstraintEpoch)`でkeyされた
`GeneralizeCompactCache`が実在する。raw boundsを変えずにprojectabilityだけが変わるliveness
transitionも`ConstraintEpoch`と該当owner dependencyを更新し、stale compact rootの再利用を
禁止する。

compactionはすべてのfinalized schemeで共有されるため、v6はv3〜v5より小さい
URR-H1 / H2 / H3へ分ける。H1はviewとliveness / cache contractをtest-firstで固定し、
production compactionはまだ切り替えない。H2でcompactionだけをviewへ切り替え、full
characterizationと287-case contract suiteをgateにする。H3でpositive alias expansionとscheme
provenanceを同じviewへ揃え、同じfull gateをもう一度通す。v6は新しい実質的設計変更なので、
v1〜v5の承認履歴を維持したまま文書全体を未承認・ユーザレビュー待ちへ戻す。

### 2026-07-30: v5 — reduction-own unmatched route の作成時self-tagging

承認済みv4のURR-F一度目では、§8.1 / §8.2の六testを
`051be5fc`のpreflightからred / green / redで固定した後、§5.8のclaim-local coverageと
§5.9のproof-carrying lineageをproductionへ試作した。v3の対象二test、v4の対象二test、
両versionのcontrol二testはすべてgreenになった。それでも最終integration gateの
`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`ではinner family漏れが
残ったため、production差分はrollbackされた。記録は`4107919e`を正本とする。

最初のtraceでは、漏れたclaimのproducer `ConstraintRecordId(6472)`が
`StructuralDerivation` / `BinaryReplayDerivation`を持たず、`RowDerivationId(196)`だけを持つことから、
v4が見ていない別種のcross-source propagation carrierが必要に見えた。しかし
`09237c6b`のread-only investigationで、この読みを狭めた。`RowDerivationId(196)`は別claimから
covered reductionへ到達する発見済みproof edgeではなく、**reduction自身がinitial lower snapshotを
matched / unmatchedへ振り分けたときに作った副産物**である。

具体的には、`TypeVar(1524)`のreductionが`&buffer` itemを消費した時点で、
`PosId(1725) = Var(TypeVar(1522))`はunmatchedだった。現行
`add_unweighted_effect_row_upper_bound_from_existing_lowers`末尾のrouting loop
（`row_effect.rs:328-334`）は、このlowerをreduced upper
`NegId(2055) = Var(TypeVar(1669))`へ送るため、
`enqueue_row_derived_subtype(1725, ..., 2055, RowDerivationId(196))`を発行した。これが
`ConstraintRecordId(6472)`であり、そのresultが作った1522側のupper claimは、reductionが
最初から所有するrouteなのにroot-self / uncoveredとして登録された。後から1522へmatching
`&buffer` lowerが到着すると、その誤分類されたclaimだけがgeneric replayを要求してfamilyを漏らした。

したがってv5は、別sourceからのlineageを新しいderivation graph走査で発見しない。
initial reduction自身の**unmatched arm**がrow-derived subtypeをenqueueする時点で、
そのresult constraintが作るclaimへreduction自身のclaim IDをexplicit parentとして渡し、
作成時から同じcompressed coverage rootを持たせる。`RowDerivation`はN-ary hyperedgeだが、
result `ConstraintRecord`はexact `RowDerivationId`を保持するため、carrierは
`(result ConstraintRecordId, RowDerivationId)`で一意に説明できる。これはv4のcross-source
lineage discoveryを広げる変更ではなく、v4のclaim identity / root compressionへfirst-party
byproductを一箇所から登録する、よりnarrowな追加である。

`enqueue_row_derived_subtype` helper自体は、weighted residual、row invariant、row-item matchにも
共有されている。`09237c6b`時点で確認した`row_effect.rs:334`のlexical call siteはinitial
unweighted reductionのsnapshot routing専用だが、同じloopはmatched armもoriginal upperへ送る。
よってself-taggingはhelper全体にもloop全体にも適用せず、unmatched armから明示的なowner claimを
渡す。v5は新しい実質的設計変更なので、v1〜v4の承認履歴を維持したまま、文書全体を
未承認・ユーザレビュー待ちへ戻す。実装sliceはURR-F一度目を再試行せず、URR-Gとして分ける。

### 2026-07-30: v4 — proof-carrying edge に沿う cross-source claim lineage

承認済みv3のURR-E一度目では、§8.1の三test（`0db4bf91`）を
red / green controlとして固定した後、claim / coverage modelをproductionへ試作した。三testと
既存URR contractはすべてgreenになったが、最終integration gateである
`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`だけはinner family漏れを
残した。試作したproduction差分はrollback済みであり、v3 testは正しいpreflightとして残っている。

一度目のtraceでは、covered stateを持つ`TypeVar(1524)`とは別sourceの
`TypeVar(1670)`に、同じresidual endpointを指すupperがあるところまでを確認した。この時点では
1670を独立producerと読んだが、commit `0264e950`のread-only investigationで、その読みを訂正した。
`ConstraintRecordId(6611)`の`1670 <: 1524`はarena interningの偶然でも無関係なdirect constraint
でもない。`inner_r.update`のscheme instantiationでfresh化されたeffect componentが、callback
bodyへ入るUnion decompositionとfunction return effect decompositionを通った、正当なsubtype
relationである。

現行コードでこの証明は、`propagate.rs`の`enqueue_derived_subtype`がchild
`ConstraintRecord`へ登録する`StructuralDerivation`として表される。実際のvariant名は
`StructuralDerivationRule::UnionBranch`と`StructuralDerivationRule::FunctionReturnEffect`である。
その`1670 <: 1524` boundと1524のcovered upperを結ぶcross-source transfer自体は、
`bounds.rs`の`BoundReplayAction`が持つ
`BinaryReplayDerivation { pivot, lower, upper, rule }`であり、result constraintの
`ConstraintRecord.replay_derivations`へ登録される。したがってv4は
`FunctionReturnEffect`という文字列やvariantをcoverage条件にせず、この既存のexact replay edgeを
claim propagationのproof carrierとして使う。

v3 §10.1(16)の意図——endpoint一致だけでcoverageを無関係なsource / producerへばらまかない——は
正しかった。しかし「別sourceへの伝播」を一律に禁止したため、`1670 <: 1524`のような証明済み
derivation chainまで遮断していた。v4は、**lineageを持たないcross-source propagation**と、
**すでに登録されたderivation edgeに沿ってoriginating claimを引き継ぐcross-source
propagation**を区別する。target claimはcoverage setのcopyを持たず、originating claimとexact
replay edgeへのlink、およびroot claimへの圧縮済み参照だけを持つ。

この規則はendpoint-based coverageではない。investigationで確認した
`ConstraintRecordId(6483)`の`PosId(1681) <: NegId(2056)`のように、covered reductionとは別に
導入されたdirect producerは、同じ`NegId` endpointを共有しても、covered claimから始まる
`BinaryReplayDerivation`を持たない。そのclaimはlineage rootが自分自身のuncovered claimのまま
なのでgeneric replayされる。v3 §8.1 test 2はこの境界を守るcontrolとして期待値無変更で残す。

v4はclaim identityとhot-path coverage lookupへ新しい実質的設計を加えるため、v1〜v3の承認履歴を
維持したまま、文書全体を未承認・ユーザレビュー待ちへ戻す。実装sliceはURR-Eを作り直さず、
rollback済みattemptをbaselineにしたURR-Fとして分ける。

### 2026-07-30: v3 — canonical upper の claim と reduction coverage を分離

LVB-B attempt 11 の prerequisite gate で、v2 実装後も
`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization` の hand-built nested
caseだけにinner family漏れが残ることが判明した。`YULANG_TRACE_VAR_BOUNDS=1524`で再確認すると、
問題のsourceは18本のlowerと0本のordinary upperを持つ状態からinitial reductionへ入り、
`after row-match upper`で`NegId(2055) = Var(TypeVar(1669))`を初めてordinary upperとして
materializeする。`store_upper_bound_without_replay`
（現行`crates/infer/src/constraints/row_effect.rs:610-689`）の分岐に照らすと、この遷移は
pre-existing active upperへの`SubsumedBy`ではなく`Inserted(record)`である。

co-ownershipはその後、同じsemantic keyのcanonical recordへ
`FunctionReturnEffect`由来の別proofがprovenance-onlyに合流して成立する。
`TypeBounds::add_bound`（`constraints/mod.rs:523-577`）は同じkeyならrecordを増やさず
`derivations`へ追加し、`semantic_changed = false` / `provenance_changed = true`を返す。
evidence-only合流は`apply_bound_replay_evidence_actions`
（`machine/bounds.rs:1213-1288`）からこの経路へ入り、追加の`BoundDisposition`を作らない。
ordinary `add_upper_bound`のactive-upper subsumption
（同`:581-640`）は`SubsumedBy`を記録するだけでsurvivorのderivationを追加しないため、
今回のco-owned recordを作る遷移ではない。したがってv2とbug noteにあった
「reduced upper自体が既存active upperへsubsumedされた」という用語を訂正し、確認済みの
lifecycleを **`Inserted` → later same-key provenance/evidence merge（second dispositionなし）**
とする。

現行`upper_record_requires_generic_replay`（`machine/bounds.rs:941-952`）は、
canonical upperの全`BoundDerivation`を、そのrecordに現在登録された
`UnweightedRowReductionOwner.derivation`とのidentity一致だけで分類する。このため、
live stateがすでにincremental routeとして覆う同じlogical residual-tail relationの別proofと、
別constraintが本当に直接要求する`source <: tail`を区別できない。前者を「独立derivation」と
みなすとmatched late lowerをplain residualへ二重routeし、後者まで抑止すると正しいsubtype
relationを失う。

v3では、derivation identityをreplay ownershipの正本にしない。各canonical upperへ
producer-root付きのlogical replay claimを記録し、各live reduction stateへ、自分がincremental
routeで覆うclaimのcoverage token/setを記録する。generic replayは、upper recordに同居する
claimのうち、どのlive stateのcoverageにも含まれないclaimだけから作る。これはv2のstate model、
initial-matching限定、source-local hot pathを維持した追加sliceであり、URR-A〜Dの実装済み範囲を
作り直さない。v3は新しい実質的設計変更なので、文書全体を未承認・ユーザレビュー待ちへ戻す。

### 2026-07-29: v2 — initial matching 成立後の incremental replay に限定

ユーザーの明示的な承認により、URR-B の保証範囲を、row upper 到着時に一件以上の matching
lower がすでに存在し、initial reduction が成立した source に限定する。

v1 の全面的な insertion-order invariance を目指した三回の実装結果は次の通りだった。

- すべての source に eager な dormant state を作る案はtestを通したが、repository stdだけで
  `UnweightedReduction`が54から191、tombstoneが0から93へ増え、poly hashも一件変わった。
- initial matching成立時だけpersistent recordを作る案は、zero-lowerでupperが先行する一順序を
  除くtarget test、既存三test、characterizationをcleanに通した。repository stdでは
  `UnweightedReduction`が54から77、tombstoneは0のまま、lower replay inputsは
  492,998から493,009、upper replay inputsは388,053から387,997で、全poly/check hashが不変だった。
- zero-lower caseをlate lower到着時にlazy activationする案は、無関係なordinary `Neg::Row`
  upperまで拾い、`UnweightedReduction`が54から176、tombstoneが0から35へ増え、
  `config-read-false-positive-repro`のpoly hashも説明なく変えた。

第三案が広く発火した根因は、「このreduction mechanismのzero/no-match branchから来たordinary
`Neg::Row` upper」と「compiler内の無関係なordinary `Neg::Row` upper」を区別する構造的なtagが
ないことにある。このtagの設計なしにzero-lower caseまで広げない。

実際の報告bugはbug noteの「24回目」「25回目」に記録された通り、row upper到着前に
`TypeVar(1524)`が18個のlowerをすでに持ち、initial matchingが成立する順序である。したがって
zero-lower / UpperFirstをdeferしても実bugは未修正のまま残らない。deferする抽象的な
solver-generality propertyは§6.6に明示し、将来、reduction-eligible upperを構造的に識別する
設計から再開する。

### 2026-07-29: v1 — 初版

`add_unweighted_effect_row_upper_bound_from_existing_lowers` が、処理時点の lower snapshot だけを
使って effect-row upper を一度だけ簡約し、その後に到着する lower と元の row prefix の関係を
失う順序依存を、独立した solver bug として設計対象にした。

local-var effect boundary の調査が発見経路ではあるが、本書は
`notes/design/2026-07-28-local-var-effect-boundary-fix.md` の local-var mechanism を改訂しない。
修正対象は、すべての empty-weight `Pos::Var <: Neg::Row` が共有する solver hot path である。

## 0. 決定の要約

本設計で選ぶ方向は次の通り。

1. row upper到着時に一件以上のmatching lowerがすでに存在し、unweighted row reductionが
   成立したsource variableについて、reductionをplainなresidual upper一本へ不可逆に潰さない。
   元のrowと現在のresidualの関係を表すpersistent reduction stateをsolver内へ持つ。
2. state は少なくとも original items / tail、消費済み items、残り items、現在の
   reduced-upper record、元 upper と寄与 lower の provenance を保持する。同じ source に
   複数の row upper がありうるため、source index の値は一つの record ではなく active record
   の集合とする。
3. reduction 後に semantic に新しい lower が source へ追加されたら、その lower を各 active
   state の **original items** に対して独立に照合する。現在の remaining items だけに照合しては
   ならない。
4. original prefix に一つでも一致した late lower は original upper へ送る。一致しなかった
   late lower は現在の reduced upper へ送る。一致によって新しい item が消費された場合は、
   remaining items と materialized reduced upper を同じ state transition で更新する。
5. current reduced upper を通常の lower-bound replay にも同時に流して二重処理しない。
   reduction-owned derivation は incremental path が所有し、同じ canonical bound record に
   reduction と無関係な derivation が共存する場合だけ、その独立した relation の通常 replay を
   残す。
6. zero-lowerまたはinitial no-matchのsourceへspeculative / dormant stateを作らない。late-lower
   transitionは、initial matching成立時に作られたrecordだけへ適用する。
7. lowering、local-var boundary、generalize / instantiate、specialize を回避策として変更しない。
   persistent recordが成立するorder familyの内側では、構文の出処やlate lowerの到着順によらず
   同じfixpointを持たなければならない。真のzero-initial-lower UpperFirstは§6.6へdeferする。
8. covered claimをupper parentとする既存binary replayが別sourceのupper claimを作る場合、
   target claimへoriginating claimのlineageを残す。coverageそのものはcopyせず、圧縮済みroot
   claimを通じてlive stateを参照する。同じendpointを共有するだけの別source / 別producer
   claimにはlineageを作らず、generic replayを残す。
9. initial reduction自身のsnapshot routingがunmatched lowerをreduced upperへ送って作るclaimは、
   enqueue時にreduction自身のclaimをexplicit parentとして受け取り、同じcompressed rootへ
   作成時から属する。`RowDerivation`を後から逆走査して親を発見せず、shared
   `enqueue_row_derived_subtype`の他用途やmatched armへこのself-tagを広げない。

## 1. 問題

### 1.1 現行関数の役割と入口

`ConstraintMachine::step_subtype` は、
`crates/infer/src/constraints/machine/propagate.rs:104-148` で lower が
`Pos::Var(source)` の場合を扱う。upper が `Neg::Row(items, tail)` なら、
同ファイル `:130-137` から `add_effect_row_upper_bound` を呼ぶ。solver 内の直接の親 call site は
ここ一箇所である。

`crates/infer/src/constraints/row_effect.rs:88-117` の `add_effect_row_upper_bound` は、
weights が empty なら `:96-107` で
`add_unweighted_effect_row_upper_bound_from_existing_lowers` を先に試す。対象関数本体は
同ファイル `:236-325` にある。役割は次の relation を source の既存 concrete lower に対して
簡約することにある。

```text
source <: [expected-items; tail]
```

現行実装は `row_effect.rs:246-253` で source の lower と record ID の snapshot を取る。
各 lower について `:262-282` で original `items` の clone を作り、
`consume_row_items_from_lower_bound` へ渡す。この clone により、それぞれの lower は original
prefix に対して独立に照合される。一方、全 lower の寄与は `remaining` へ合流し、消費された
item が最終 residual から除かれる。

この snapshot に対する計算自体は正しい。一つ以上の lower が一致すると、
`row_effect.rs:287-308` は original upper、reduced upper、`UnweightedReduction` と
`RowItemMatch` の derivation を作る。欠陥は `:309-314` で reduced upper だけを
`store_upper_bound_without_replay` へ渡す点にある。ここで保存される upper は、元の
`items` / `tail` と incremental matching rule を持たない plain type である。

### 1.2 確定した TypeVar-level time series

`c40a5cb4` の read-only trace で確定した hand-built nested-boundary case を、処理点ごとに
展開すると次の8段階になる。

```text
1. TypeVar(1524) には18個の lower がすでにある。
2. FunctionReturnEffect 由来の 1524 <: [inner-family; 1669] が到着する。
3. unweighted reduction が18個の lower snapshotを取得する。
4. snapshot内の既存 inner-family lower が original prefixを消費し、
   remaining itemsはemptyになる。
5. original upper [inner-family; 1669] と reduced upper 1669 が作られる。
6. 1524 <: Neg::Var(TypeVar(1669)) が plain upper として保存される。
7. その後、PosId(2133) = [inner-family] が1524の19個目のlowerとして到着する。
8. 通常の lower-bound replay は保存済み Neg::Var(1669) だけを見て、
   original prefixと再照合せず、PosId(2133)を1669の14個目のlowerとして直送する。
```

`TypeVar(1669)` は clean であるべき residual だが、8段階目で `inner-family` を受け取る。
これは residual と別名を取り違えた問題でも、4段階目の消費計算が間違っている問題でもない。
reduction が一度成功したあと、その logical upper を plain residual としてしか保存せず、
late lower を元の row と照合する情報と入口を失うことが根因である。

parsed lowering で同じ family が漏れなかったのは、family lower が reduction の発火前に揃い、
initial snapshot に含まれたためである。同じ constraint relation の fixpoint が到着順で変わる
以上、これは lowering shape の差ではなく solver の順序依存である。

### 1.3 既存 unit contract と盲点

`crates/infer/src/constraints/tests/case_02.rs` には、現行 unweighted reduction の重要な
contract がすでに三つある。

- `unweighted_row_upper_uses_concrete_lower_item_before_residual_tail`
  （`case_02.rs:140-184`）は、concrete lower item が row prefix を満たしたとき、residual
  lower が tail だけを upper として受け取ることを固定する。
- `unweighted_row_upper_consumes_pop_only_weighted_lower_item`
  （`:187-262`）は、filter がなく push count が0の pop-only lower も prefix を消費し、
  matched item を residual tail へ流さないことを固定する。
- `unweighted_row_upper_matches_each_lower_independently`
  （`:392-475`）は、alias と direct concrete row を含む複数 lower を original items に対して
  独立に照合し、全 contributing lower record を `UnweightedReduction` hyperedge の parent として
  保持することを固定する。

三つとも row upper を追加する前に対象 lower を用意する。したがって
`row_effect.rs:246-253` の initial snapshot に対する規則は強く固定しているが、
`row_effect.rs:309-314` の保存後に lower を追加する case は一つもない。本修正はこの blind spot
を埋め、三つの既存 contract は期待値を変えずに維持する。

### 1.4 v3で確定したclaim co-ownership gap

v2実装後の現行構造は次の通りである。

- `UnweightedRowReductionRecord`は`source`、original items / tail、current materialization、
  processed lower、provenance headを持つ（`constraints/mod.rs:368-379`）。
- current upperとの対応は
  `BoundRecordId -> [UnweightedRowReductionOwner { state, derivation }]`
  で持つ（同`:381-398`、`row_effect.rs:458-527`）。
- `add_lower_bound`はincremental routeを先に作り、同じupperをgeneric replayが覆うと判定した場合は
  incremental actionを省く（`machine/bounds.rs:478-525`）。
- generic replayの要否は`BoundRecord.derivations`にownerのderivationと一致しない要素が一つでも
  あるかだけを見る（同`:896-952`）。

`BoundDerivation`は`Constraint(ConstraintRecordId)`、`ReplayEvidence(BinaryReplayDerivation)`、
`Row(RowDerivationId)`などのproof identityであり（`constraints/mod.rs:1058-1066`）、
logical relationのidentityではない。reduction自身のcurrent materializationは通常
`BoundDerivation::Row(provenance_head)`で、ownerにも同じ値が入る。一方、canonical same-key mergeは
同じ`source` / endpoint / weightsの`BoundRecord`へ、別の`Constraint`または`ReplayEvidence`を
追加できる。後者がstateのoriginal producerへ遡る同じresidual-tail claimでも、enum値が違えば
現行判定は「state外」とする。

ここで区別すべきものは次の二つである。

1. **同じrelationの別proof**: stateのproducer constraintが要求した
   `source <: [original_items; original_tail]`をreductionした結果として、
   current endpointへの別derivation / replay evidenceが同じcanonical recordへ合流したもの。
   proof IDが違っても、そのlate-lower routeはstateがすでに所有する。
2. **真に独立したrelation**: 別のproducer constraintが、reductionのoriginal rowと無関係に
   `source <: tail`を直接要求したもの。このclaimはcurrent endpointが同じでもstate coverage外で、
   generic replayを残さなければならない。

`FunctionReturnEffect`は`StructuralDerivationRule`であり（`constraints/mod.rs:1581-1628`）、
それだけでは1と2を分類できない。producer constraint identityと、そこから生じたlogical
row relationへのlinkageが必要である。

## 2. 発見文脈と責務の切り分け

この bug は local-var effect boundary project の nested case から見つかった。bug note の
13〜22回目では、helper application、deferred resolution、callback body aggregation、
callback parameter の concrete ref 接続時点を順に切り分けた。v5 の deferred parameter
binding により、単一 boundary と outer family の discharge は正しくなった。

23〜24回目で残った inner family を solver 内まで追うと、
`FunctionReturnEffect` の relation が unweighted reduction へ入り、plain residual 保存後の
lower replay で contamination が起きていた。25回目は、この挙動が local-var 固有の前提違反では
なく、late lower を扱えない一般的な one-shot logic gap だと確定した。

したがって、発見用 repro と修正責務を分ける。

- local-var project は、callback parameter を body lowering 中は placeholder のまま保ち、
  helper applicationで concrete refへ接続する v5 mechanismを引き続き所有する。
- 本 project は、`Pos::Var <: Neg::Row` relation の到着時に一件以上のmatching lowerがすでに
  存在する場合、その後のlate lowerを元のrowへ再照合することを所有する。
- local-var loweringが constraint orderを変えてこのbranchを避ける案は採らない。その案では、
  surface syntaxやprogrammatic constructionの違いがsolver semanticsへ漏れる。

## 3. blast radius

### 3.1 call graph と発火頻度

直接の call graph は狭い。

```text
step_subtype
  -> add_effect_row_upper_bound
       -> add_unweighted_effect_row_upper_bound_from_existing_lowers
```

現在の参照位置は `propagate.rs:130-137`、`row_effect.rs:88-117`、
`row_effect.rs:236-325` である。ただし入口の意味範囲は狭くない。
solver が扱うすべての empty-weight `Pos::Var <: Neg::Row` が同じ branch を通る。
local-var family、特定の module、特定の fixture の専用 path ではない。

current characterization の `unweighted_multi_parent` は、
`crates/infer/src/constraints/tests/characterization.rs:844-979` の std-backed five-case
baseline で54、64、78、128、91回である。repository std だけでも54回発火し、
fixtureを加えた既存 workload では最大128回に達する。したがって record lookup と late-lower
matching は source-indexed にし、全 reduction state のglobal scanを lower insertionごとに
行ってはならない。

### 3.2 semantic blast radius

意味論的に変わるのは、次の三条件をすべて満たす relation だけである。

1. empty-weight row upper の initial reduction が一つ以上の既存 lower により成立する。
2. その reduction state が live な間に、同じ source へ semantic に新しい lower が追加される。
3. その late lower が original prefix と一致する、またはその一致が remaining prefix をさらに
   縮める。

初期 lower がすべて揃っている case、items がemptyの case、既存 lowerがない case、
initial snapshotで一件も一致しない case、weighted row reductionの結果は変えない。
修正は、original prefixで受理されるべき late itemが residualへ漏れることを止める
**narrowing** であり、新しい effect や subtype を許可する capability追加ではない。

ただし hot path の発火頻度が高いため、「現在 passing の出力には影響しない」とは仮定しない。
passing programに latent late-lower shapeがあれば、これまで residualへ誤って混ざっていた
effectが消え、finalized scheme、canonical constraint数、bound / replay count、
row-derivation provenance census、poly dump hashが変わりうる。これらは正しい narrowing の
結果である可能性がある一方、期待値を新しい実装出力へ合わせるだけでは正当化できない。
各差分は late-lower relationまで遡って説明する。

### 3.3 performance blast radius

initial reduction はすでに source の全 lower snapshotを走査する。選ぶ設計は、この一回の
走査を減らすものではない。追加コストは、late lower一件につき、その sourceに登録された
active unweighted reduction state と original prefixを照合する分である。

hot pathへ許容する index は `TypeVar -> reduction record IDs` であり、sourceと無関係なstateの
走査、CST / ASTの再走査、lowering由来pathの照合は入れない。state record数、late-lower
incremental match数、reduced-upper replacement / reuse数は timing censusへ追加し、
correctness changeとaccidental replay増加を区別できるようにする。

### 3.4 v3のblast radius

v3が意味を変えるのは、live unweighted reduction stateのcurrent upper recordに複数のreplay
claimが同居する場合だけである。single-owner record、weighted row、zero-lower / initial
no-match、別sourceのrecord、current endpointが異なるrecordは変えない。

hot pathへの追加は、`add_lower_bound`で既に取得するsource-local reduction statesと、そのcurrent
upperに付いたclaimの差集合計算である。constraint graphやprovenance graphをlate lowerごとに
逆走査してproducerを復元してはならない。claim / coverage linkageはadmissionまたは
materialization時に一度作り、canonical recordとstateから直接参照する。

### 3.5 v4のblast radius

v4が追加で意味を変えるのは、claim-awareなbound replayが、covered claimのcurrent upperを
parentとして別sourceのcanonical upperを導く場合だけである。endpointが同じでも、ordinary
constraint admission、structural decompositionだけ、または別producerから直接作られたboundは
変えない。`1670 <: 1524`を作った`UnionBranch` / `FunctionReturnEffect`も、そのsubtype relation
自体も変更しない。

追加metadataはreplay planning / admission時のoriginating claim IDと、target claim作成時の
lineage linkである。late lowerごとのstructural / replay provenance逆走査は行わない。
coverage checkはclaimに保存したroot IDとlive coverage indexのlookupで完結させる。claim数は
canonical `(target bound, root claim)`の数、lineage link数はそのclaim数でboundedにし、
同じsemantic replayのproof追加やconstraint graphのcycleに比例させない。

### 3.6 v5のblast radius

v5が追加で意味を変えるのは、
`add_unweighted_effect_row_upper_bound_from_existing_lowers`がinitial reductionを成立させた後、
同じsnapshot内の**unmatched lower**をcurrent reduced upperへ送る一箇所だけである。
matched lowerのoriginal-upper route、late-lower transition、weighted residual、row invariant、
row-item matchは変更しない。generic `enqueue_row_derived_subtype`の全callerを
`RowDerivationRule`やendpoint shapeから分類しない。

追加metadataは、unmatched armがすでに知っているreduction claim IDとaggregate
`RowDerivationId`を、canonical result constraint admissionへ渡すdirect ownership linkである。
result constraintがnewでもduplicateでも、target upper claimが登録される時点までこのlinkを
保つ。late lowerごとのproof graph走査、`RowDerivation` parentの探索、cross-source propagation
candidateの追加発見は行わない。claim canonicalizationとcoverage lookupはv4の
`(target BoundRecordId, coverage_root)` / compressed rootをそのまま使うため、追加costはこの
initial unmatched routeごとの定数時間metadata admissionに限る。

### 3.7 v6のblast radius

v6のsemantic対象は、§5.10のexplicit parent、または§5.9のexact replay lineageによって
unweighted reductionのcoverage rootへ属するclaimが作った**lower-side mirror record**である。
そのrootを一つ以上のlive reduction stateがcoverする間だけ、claim由来のrelationをscheme
projectionから除外する。同じrecordにuncovered claimがあればrecordは一回projectし、そのclaimを
根拠として残す。claim linkageを一度も持たないlower、weighted-row由来lower、direct ordinary
lower、上界側projectionの意味は変えない。

変更対象のbound集合は狭いが、viewのconsumerは広い。`compact_type_var_for_scheme`と
`compact_type_var_recording_merge_constraints_for_scheme`はあらゆるdefinitionのscheme構築で
使われ、positive alias expansionとgeneralized witness captureも同じgeneralization pipelineに
ある。local-var fixtureだけでなく、全programの全finalized schemeが回帰範囲である。
したがって「対象claimが少ない」ことを「compactionのblast radiusが小さい」ことと混同しない。

ordinary pathの性能契約は、machine全体にprojection claimが一件もなければraw iteratorへ即時
passthroughし、claimがあっても対象ownerにlinkがなければboundごとのroot lookupを行わない、
という二段fast pathである。対象ownerだけがrecord-localなsmall claim setを分類する。
root判定は§5.9の圧縮済み`coverage_root`から`live_coverage_by_root`を一回引き、
parent chainや`RowDerivation` / constraint graphを歩かない。

cacheのblast radiusも明示する。`CompactCollector.cache`はcollector一回だけの
`(TypeVar, Polarity, ConstraintWeight)` cacheで、collectorはimmutableな`ConstraintMachine`を
借りる。positive aliasの`TypeVar -> Vec<TypeVar>` cacheも一回のimmutable expansionだけである。
この二つはpass途中のinvalidationを必要としない。一方、analysis sessionの
`GeneralizeCompactCache`は`(root TypeVar, ConstraintEpoch)`を跨いで保持するため、
raw boundsが同じでもcoverage livenessによってviewが変わるtransitionをepoch mutationとして
公開しなければstale schemeを返す。これはv6 correctnessの一部であり、後続最適化へdeferしない。

## 4. 必須 invariant

### 4.1 logical relation

reduction 後も、solver が所有する logical relation は

```text
source <: [original-items; original-tail]
```

である。`source <: [remaining-items; original-tail]` は、既知 lower に対して計算した現在の
projectionであって、元 relation と無関係な plain aliasではない。remainingがemptyなら
materialized endpointはtail単体になるが、logical relationまで`source <: tail`へ置き換わった
わけではない。

### 4.2 independent matching

active reduction recordが作られた後に到着する各lowerは、original itemsの完全なcopyから
照合を開始する。
先に別の lower が消費した remaining itemsだけを入力にしてはならない。これは既存
`unweighted_row_upper_matches_each_lower_independently` がinitial snapshotについて固定した規則を、
late lowerへ延長するものである。

original / consumed / remaining はsetではなく、row itemの順序と重複を保つ列として扱う。
現行 `consumed_row_items` と `remove_first_row_item`
（`row_effect.rs:962-982`）と同じmultiplicityを維持する。別lowerが同じoriginal itemへ
独立に一致しても、そのlowerはmatchedとしてoriginal upperへ送る。一方、global remainingから
同じ一個を二重に除去しない。

### 4.3 matched / unmatched routing

一つの lower 内で一個以上の original item が一致すれば、その lower 全体を original upperへ
送る。row lowerがmatched itemとunmatched itemの両方を持つ場合、unmatched portionはoriginal
rowのtailへ通常のrow decompositionで流れる。lower全体をcurrent residualへも送ってはならない。

一個も一致しない lower はcurrent reduced upperへ送る。lowerのweightsは現行 replay と同じ
compositionで保持する。matching eligibilityは現在の
`constraint_weights_are_alias_neutral` / `stack_weight_is_alias_neutral`
（`row_effect.rs:400-405`）を変えない。filterを持たずpush countが0なら、pop-only lowerも
引き続きmatching対象である。

### 4.4 fixpoint と idempotence

row upper到着時に一件以上のmatching lowerが存在するorder familyでは、同じsemantic
lower / upper集合は、先行lowerの個数や残りのlowerの到着順によらず同じfinal boundsと
effect-row shapeへ収束する。canonical dedupで同じlower recordが再観測されても、stateの
consumed / remaining、provenance、incremental counterを二重更新しない。

row upperがzero lowerで到着する真のUpperFirst caseはこのinvariantへ含めない。その時点では
recordを作らず、後着lowerからordinary `Neg::Row`を形だけでreduction recordへ昇格させない。
これは未解決caseを正しいとみなすものではなく、§6.6の明示的なfollow-upである。

### 4.5 provenance

initial matchingに寄与したproducer constraintと全lower bound recordを失わない。
late matchingでは、late lower record、original upper producer、item matchを同じ説明chainから
辿れることを必須とする。payload-bearing familyのargument invarianceは、initial pathと同じ
`RowItemMatch` derivationから両方向のconstraintを作る。

provenance historyはappend-onlyとする。既存`RowDerivation`をin-placeで書き換えて
`row_derivation_index`のhash keyと内容を不一致にしない。late matchは、直前のreduction
derivationと新しいlower recordをparentに持つsuccessor derivationを作り、stateのcurrent
provenance headだけを進める。

### 4.6 bound lifecycle

current reduced upperが置換、equivalent dedup、subsumption、pruneを受けても、stateがstaleな
`BoundRecordId`だけをactive endpointとして保持してはならない。materializationの結果と
`BoundDisposition`をstateへ反映し、tombstoneはhistoryとしてだけ参照する。

logical reduction stateは、current materialized boundが別boundにsubsumedされたという理由だけで
失わない。late lowerのoriginal-row matchingとprovenanceは引き続き必要である。一方、
subsuming boundがreductionと独立したrelationを表すなら、そのrelationの通常replayは残す。

### 4.7 logical claim coverage

generic replayの単位は`BoundRecord`でも`BoundDerivation`でもなくlogical claimである。
同じrecordにcovered claimとuncovered claimが同居できる。live stateが覆うclaimはincremental
routeだけが処理し、uncovered claimだけがgeneric replayを作る。一つでもuncovered claimがある
ことを理由にrecord全体をgeneric replayしてはならない。

coverage token / setそのものはsource、original row、producer-rootをまたいでcopyまたはunion
しない。subsumption、equivalent merge、evidence promotion、endpoint一致だけを理由に別claimを
coveredへ昇格させない。別claimがcoverage rootを継承できるのは、(a) originating claimを
parentに持つexact replay derivationがcanonical constraintへ登録され、そのconstraintがtarget
bound claimを導いた場合、(b) 同じedgeがtarget evidence boundの`ReplayEvidence`として登録された
場合、または(c) initial reduction自身のunmatched armが、自分のrouting byproductへ
reduction claimをexplicit parentとして渡した場合だけである。(c)は別sourceのproof edgeを
発見する規則ではなく、routeを作ったownerによる作成時登録である。target claimはcoverageの
copyではなくlineage rootへの参照を持つ。

同じstate-owned claimのproof identityだけが変わった場合はcoverageを失ってはならない。
同じroot claimから同じcanonical target boundへ再到達した場合もclaimを増やさず、既存lineage
claimへcoalesceする。一方、同じendpointへのdirect claimは、sourceまたはproducerが違えば
自分自身をrootとする別claimであり、covered rootへのproof-carrying edgeがない限りuncoveredで
ある。

### 4.8 claim lineage

lineageはsemantic subtype relationを新しく作る規則ではない。既存solverがすでに作ったrelation
について、「このtarget claimはどのoriginating claimをupper parentとするreplayから来たか」、
または「どのreduction claimが自分のinitial unmatched routeとして直接作ったか」をadmission時に
固定するaccountingである。lineage linkはexact parent claimと、exact replay edgeまたは
`(result ConstraintRecordId, RowDerivationId)`のdirect route carrierを持ち、carrierが存在しない
shape-based推測を許さない。

lineage graphはappend-onlyかつacyclicにする。derived claimのparentは必ず先に確定したclaim IDで
あり、childはparentより後にallocateする。各claimはroot claim IDを作成時にpath-compressして
保持し、coverage checkでparent chainを歩かない。constraint graphがcycleして既存
`(canonical target bound, root claim)`へ戻った場合は新しいclaim / parent linkを作らず、
既存claimへproofをcoalesceする。

### 4.9 reduction-own routing ownership

initial reductionのunmatched routeから生じるclaimは、routeを発行したreduction claimのchildで
あり、独立direct claimではない。このownershipはresult constraintのrow derivationを後から
探索して推測せず、unmatched armがenqueue admissionへparent claimを明示した場合だけ成立する。
childの`coverage_root`はparentの圧縮済みroot、`depth`は`parent.depth + 1`とし、root stateが
liveでなくなればv4と同じ`live_coverage_by_root` lookupでuncoveredになる。

同じcanonical target upperに、以前から別producerのdirect claimが存在しても、そのclaimを
coveredへ昇格させない。reduction routeは同じrecord上へroot別のderived claimを追加または
coalesceするだけである。matched arm、trivial constraint、explicit parentを持たない
row-derived constraintは、この規則からclaimを作成または再分類しない。

### 4.10 scheme projection ownership

schemeへprojectするlogical relationの単位もclaimである。raw `BoundRecord`はcanonical subtype
storageとauditの正本として残し、scheme projectionの可否をrecord stateへ焼き付けない。
claim linkageのないactive lower recordは常に従来どおりprojectableである。linkageがあるrecordは、
各claimについて

```text
root = claim.coverage_root
projectable(claim) = live_coverage_by_root[root] is empty
```

をprojection時に評価する。recordはunclaimedなら一回、またはprojectable claimが一つ以上なら
一回だけconsumerへ返す。全linked claimがcoveredなら返さない。同じrecord上のcovered /
uncovered claimを一つのrecord-wide booleanへ潰さず、provenanceにはprojectable claimだけを渡す。

covered claimをschemeから除外できる根拠は、そのlive reduction stateがoriginal rowとcurrent
reduced-upper materializationを所有し、同じlogical inputをincremental routeで既に表している
ことにある。unmatched routeが作ったlower-side aliasをもう一度raw graphからprojectすると、
stateが受理・除外した情報を別経路でaggregateへ戻し、v6のconfirmed leakになる。

最後のlive stateがrootから外れた場合、この根拠は消える。raw lower recordがactiveならclaimは
再びprojectableになる。historical materializationが一度同値情報を含んだという理由で
suppressionを残さない。同値relationが本当に不要なら通常のbound lifecycleがtombstone /
pruneする責務であり、stale coverageで隠す責務ではない。v6は新しいstate expiry policyを
導入せず、既存または将来のlifecycleが`live_coverage_by_root`の最後のstateを外したときの
projection semanticsだけを定める。

## 5. 選んだ設計: source-indexed persistent reduction state

### 5.1 state model

実装名はslice内で既存命名へ合わせるが、必要な意味形は次である。

```text
UnweightedRowReductionRecord {
    source
    original_items
    original_tail
    consumed_items
    remaining_items
    current_reduced_upper
    processed_lower_records
    provenance_head
}

unweighted_row_reductions_by_source:
    TypeVar -> [UnweightedRowReductionRecordId]
```

`current_reduced_upper` はendpointだけではなく、現在の materialization resultを持つ。
少なくとも「ordinary recordとしてinsert済み」「既存recordとequivalent」
「別recordにsubsumed」「旧recordはtombstoneとなり新recordへ置換」を区別できなければならない。
これにより、replay planningとprovenanceが死んだrecordをlive boundとして扱うことを防ぐ。

record keyをsourceだけにしない。同じsourceへ異なるoriginal items / tail / producerを持つ
複数row upperが入りうる。それぞれは別logical relationであり、source indexから該当する
全active recordを引く。

`processed_lower_records` はincremental hookのidempotence frontierである。canonical lowerが
equivalentとして再挿入された場合、bound recordの追加derivationは通常どおりmergeしてよいが、
同じsemantic lowerをもう一度row item消費へ数えない。

### 5.2 initial transition

`add_unweighted_effect_row_upper_bound_from_existing_lowers`
（`row_effect.rs:236-325`）のinitial snapshot matching ruleは維持する。

1. itemsがempty、lower snapshotがempty、または一件もmatchしない場合は現在どおり`false`を返す。
2. 一件以上matchした場合、現在と同じoriginal items単位の独立matchingを行う。
3. original / consumed / remaining、snapshot内で観測したlower record IDs、
   initial `UnweightedReduction` derivationをpersistent recordへ保存する。
4. current reduced endpointを`effect_row_upper(remaining, tail)`で作り、
   projection / generalizationから見えるupperとしてmaterializeする。
5. snapshot内のmatched lowerはoriginal upperへ、unmatched lowerはcurrent reduced upperへ送る。
6. materialized upperを「reduction-owned logical relation」としてreplay plannerから識別できる
   linkageを作る。plain `BoundDerivation::Row`を後から型形状だけで推測し直さない。

initial snapshotに対するbound shape、row-item constraint、hyperedge parentは既存三テストと同じに
する。persistent state化を理由に、初期結果やテスト期待値を変更しない。

`false`を返すbranchではrecord、source index entry、dormant ownershipを作らない。後からlowerが
到着しても、このbranchをordinary `Neg::Row`のshapeだけから遡ってactivationしない。

### 5.3 late lower transition

新しいlowerの入口は`ConstraintMachine::add_lower_bound`
（`crates/infer/src/constraints/machine/bounds.rs:416-496`）である。semantic insertionが成立し、
stableなlower `BoundRecordId`が確定した後、通常の
`lower_bound_replay_actions`を作る`bounds.rs:478`より前に、source indexからactive
unweighted statesを引く。

initial matching成立時にすでに作られた各stateについて次を行う。source indexにrecordが
なければ追加処理をせず、ordinary replayだけを従来どおり行う。

1. lowerのweightsがmatching対象になりうるかを現行規則で判定する。
2. `local_remaining = original_items.clone()`から開始し、現行
   `consume_row_items_from_lower_bound`（`row_effect.rs:327-373`）でlowerを独立に照合する。
3. 一件もmatchしなければ、stateのcurrent reduced upperに対するreplay actionを一件作る。
4. matchしたら、lowerをoriginal upperへ送る。各payloadに`RowItemMatch`を作り、
   late lower recordを新しいprovenance successorへ加える。
5. このlowerが消費したitemをstateのglobal remainingから`remove_first` semanticsで除く。
   remainingが変われば新しいreduced endpointをmaterializeし、旧current recordとの
   disposition / tombstone transitionを記録する。
6. remainingが変わらなくても、late lowerがoriginal rowへmatchした事実とprovenanceは記録する。
7. lower recordをprocessed frontierへ入れ、同じstateで再処理しない。

current reduced upperの更新に伴って、既存lower全件を再走査・replayしない。既存matched lowerは
すでにoriginal upperへ送られ、既存unmatched lowerは古いremaining rowのtailまで分解済みである。
新たにmatchしたlate lowerだけをoriginal upperへ送り、reduced endpointを差し替えれば足りる。

### 5.4 ordinary replay との所有権

現在の`lower_bound_replay_actions`は`bounds.rs:853-890`でsourceのprojection upperを列挙し、
すべてをplain relationとしてreplayする。このままstate hookを前置きするだけでは、
late matched lowerがoriginal upperとcurrent residualの両方へ送られ、同じbugを再現する。

したがってreplay planをlogical derivation単位に分ける。

- live unweighted reductionが所有するreduced-upper derivationは、incremental transitionが
  replayを生成するため、generic plain replayの対象から外す。
- 同じcanonical endpoint recordにunweighted reductionと無関係なderivationが共存する場合、
  その独立relationのgeneric replayは残す。たとえば別constraintが直接
  `source <: tail`を要求するなら、late `F`がtailへ流れるのはその別constraintの正しい結果である。
- endpoint equalityや`Neg::Var` shapeだけでsuppressionしない。state record IDとderivation
  linkageから所有権を判定する。
- replay stats、duplicate / trivial disposition、evidence recordは、incremental actionも通常
  actionと同じaccountingへ通す。correctnessのためにaudit pathを飛ばさない。

この分離は、current reduced upperをgeneralizationから隠すことを意味しない。
bound projectionは現在のremaining rowを引き続き見せる。変更するのはlate lowerとの
replay semanticsだけである。

### 5.5 reduced-upper replacement と prune / subsumption

current implementationの`store_upper_bound_without_replay`
（`row_effect.rs:408-476`）は、extrude、existing upperによるsubsumption、row prune、
bound insertion、provenance / disposition、event、neighbor記録をまとめて行う。
persistent stateはこのlifecycleを迂回せず、同じ責務を持つstate-aware materialization
entrypointを使う。

`prune_upper_rows_subsumed_by_reduced_upper`
（`crates/infer/src/constraints/machine/bounds.rs:1350-1387`）はpruned recordをtombstoneにする。
state transitionは次をatomicに扱う。

1. old current materializationをhistoryへ移す。
2. new reduced endpointをinsert / equivalent / subsumedの通常判定へ通す。
3. stateのcurrent endpoint、materialization result、provenance headを同時に更新する。
4. source indexからold live ownershipを外し、new ownershipを登録する。

subsumed resultではlogical stateとcurrent endpointを保持し、survivor recordへのdispositionを
記録する。survivorが持つ独立derivationのplain replayと、stateが持つoriginal-row incremental
matchingを混同しない。prune / subsumptionのためにstateを捨てる最適化は、同値性を別testで
証明するまで入れない。

### 5.6 provenance representation

initial stateは現行と同じく、producer constraintとsnapshot内の全contributing lower boundを
parentsに持つ`UnweightedReduction`をprovenance headにする。late matched lowerごとに、

```text
previous UnweightedReduction
    + late lower BoundRecord
    -> successor UnweightedReduction
         -> RowItemMatch
         -> current reduced-upper derivation
```

というappend-only successorを作る。remainingが同じでもsuccessorは必要である。そうしないと、
late lowerがoriginal prefixによってresidualから除外された理由を説明できない。

state-aware replayが作るconstraintは、通常のbinary replay evidenceに加え、どのreduction
state / provenance headがmatched / unmatched routeを選んだかを辿れるようにする。
provenance completenessを保てない場合、`IncompleteReplay`で隠してlandingしない。

### 5.7 hot-path representation

追加tableは`ConstraintMachine`が一inference session内で所有し、source indexから直接引く。
同じoriginal upperのduplicate admissionで新recordを増やさず、canonical relationへderivationを
mergeする。recordの解放を急ぐためのglobal compactionはinitial sliceへ入れない。

最初のperformance contractは次である。

- late lower insertionの追加探索は、そのsourceのactive stateだけに比例する。
- 一state、一semantic lowerにつきincremental matchingは高々一回である。
- remainingが変わらなければreduced endpointを再alloc /再insertしない。
- provenance successorは一late matched lowerにつき高々一つであり、過去parentsの全copyを
  毎回作らない。
- current std-backed characterizationへstate / transition censusを追加し、global replay totalの
  意図しない増加を検出する。

### 5.8 v3: replay claim と coverage token/set

必要な意味形は次である。実装時の型名は既存命名へ合わせてよい。

```text
UnweightedRowLogicalRelation {
    source
    original_items
    original_tail
    producer_constraint
}

UpperReplayClaim {
    id
    source
    endpoint
    weights
    producer_constraint
    logical_relation: Direct | Reduced(UnweightedRowLogicalRelationId)
}

UnweightedRowReductionRecord {
    ...v2 fields...
    covered_claims: small set<UpperReplayClaimId>
}

claims_by_upper_record:
    BoundRecordId -> small set<UpperReplayClaimId>
```

tokenが識別する正本は、単なる`(source, current endpoint)`ではない。
`source <: [original_items; original_tail]`という元relationと、それを導入した
`producer_constraint`を含む。current endpointとcurrent recordはmaterialization lifecycleで
変わりうるためtoken identityへ含めず、claim側の現在位置として持つ。itemsは順序と重複を保つ。

claimはupper-bound derivationをcanonical recordへ加える入口で作る。reduction materializationの
claimはstateのlogical relation IDとproducerを持つ。同じproducer-rootから生じた
structural / row / replay-evidenceの別proofがsame-key mergeされる場合、新しいproof identityを
追加しても同じclaimへcoalesceする。別constraintが直接`source <: tail`を導入した場合は
`Direct`かつ別producerの新claimとし、state coverageへ入れない。producerが不明な
`Origin(unknown_internal)`を形だけで既存tokenへ吸収せず、uncoveredとして保守的にgeneric
replayする。

`lower_bound_replay_actions`はprojection upper recordごとに、
`claims_by_upper_record[record] - union(live_state.covered_claims)`を求める。差集合がemptyなら
generic actionを作らず、incremental routeを使う。差集合がnon-emptyなら、その**未covered
claimだけ**を根拠にgeneric actionを一件作り、全claim IDをprovenance / accountingへ残す。
同じsemantic subtype actionをclaim数だけ重複enqueueしない。

lifecycle規則は次の通りである。

1. **insert**: materialized recordへclaimを付け、stateのcovered setへ同じclaim IDを入れる。
2. **same-key equivalent / evidence merge**: proofを既存claimへcoalesceできるのは
   source、weights、producer-root、logical relationが一致するときだけである。別producerなら
   survivor recordへuncovered claimを追加する。
3. **subsumption**: attempted materializationのclaimをsurvivorへ移す。state-owned claimなら
   state coverageも同じclaim IDを保持するが、survivorに以前からある別claimをcoveredへ昇格
   させない。
4. **replacement / prune**: state-owned claimのcurrent record indexをnew recordへ移し、
   tombstone側はhistoryだけに残す。logical tokenとproducer identityは変えない。
5. **複数stateのcoalescing**: 各stateは自分のclaimだけをcoverする。setはclaim IDでdedupし、
   record上の全claimを相互にcoverしたことにしない。

一recordあたりのclaim数、same-key coalesce数、covered / uncovered generic replay planning数、
subsumption / replacement時のclaim移送数をtiming censusへ加える。setがproof追加回数に比例して
無制限に増えるなら、claim canonicalizationが失敗しているのでlandingしない。

この方向を選ぶ理由は、claim admission時ならproducer-rootとlogical relationを定数時間で
構造化して残せるからである。derivation identityの比較は同じrelationの別proofを誤分類し、
record-wide suppressionは真に独立したdirect tail relationを失い、replay時のprovenance逆走査は
hot pathを非局所化する。coverage setはこの三つを避けながら、v2のsource-indexed stateと
canonical replay dedupをそのまま利用できる。

### 5.9 v4: proof-carrying replay edge と claim lineage

`0264e950`時点のproductionには、rollbackされたURR-E試作のclaim型は残っていない。現在の
materialized ownershipは`UnweightedRowReductionOwner { state, derivation }`、
canonical boundのproofは`BoundRecord.derivations`、canonical constraintのproofは
`ConstraintRecord`の`structural_derivations` / `replay_derivations`へ保存される。v4は§5.8の
claim modelを再導入する際、この既存proof recordへ小さいcross-linkを足す。別のprovenance graphを
並行して構築しない。

必要な意味形は次である。実装名とsmall collectionの型は既存命名へ合わせてよい。

```text
UpperReplayClaim {
    ...v3 fields...
    current_record: BoundRecordId
    coverage_root: UpperReplayClaimId
    lineage: Original | Derived(UpperReplayClaimLineage)
}

UpperReplayClaimLineage {
    parent_claim: UpperReplayClaimId
    carrier: ReplayConstraint {
        result: ConstraintRecordId
        replay: BinaryReplayDerivation
    } | ReplayEvidence {
        replay: BinaryReplayDerivation
    }
    depth: u32
}

ReplayClaimParent {
    claim: UpperReplayClaimId
    replay: BinaryReplayDerivation
}

replay_claim_parents_by_constraint:
    ConstraintRecordId -> small set<ReplayClaimParent>

derived_claim_by_record_and_root:
    (BoundRecordId, UpperReplayClaimId) -> UpperReplayClaimId

live_coverage_by_root:
    UpperReplayClaimId -> small set<UnweightedRowReductionRecordId>
```

root reduction claimのoriginal row / producer説明は、stateがすでに持つ
`provenance_head: RowDerivationId`と、既存の`RowDerivationParent::{Constraint, Bound,
RowDerivation, ...}`を正本にする。lineage linkはこれらと同じID参照方式で、
cross-source replay部分だけを`ConstraintRecordId` / `BinaryReplayDerivation`へ接続する。
original row、structural chain、binary replayをclaim内へ複製しない。

original reduction claimと独立direct claimは`lineage = Original`、`coverage_root = self`である。
reduction stateだけが自分のoriginal claimを`live_coverage_by_root`へ登録する。derived claimは
coverage setをcopyしない。`coverage_root = parent.coverage_root`とし、親claim、result
constraint、exact replay edgeを一件だけwitnessとして保持する。root stateがreplacement /
subsumptionを経てもliveならindexを維持し、stateがliveでなくなればindexから外す。これにより
derived claimのcoverageはstate lifecycleへ追随し、target claimへstaleなbooleanを焼き付けない。

#### 5.9.1 現行derivation recordとの対応

`propagate.rs`は`Pos::Union`を
`StructuralDerivationRule::UnionBranch { branch }`で分解し、function subtypeのreturn effectを
`StructuralDerivationRule::FunctionReturnEffect`で分解する。どちらも
`enqueue_derived_subtype`を通り、result `ConstraintRecord`へ
`StructuralDerivation { parent, rule }`を登録する。confirmed nested caseの
`ConstraintRecordId(6611)`、`1670 <: 1524`はこのchainから来る。

そのlower relationを使って1524のupperを1670へ運ぶ直接のedgeは、structural ruleではなく
既存のbinary bound replayである。`BoundReplayAction`は
`BinaryReplayDerivation { pivot, lower, upper, rule }`を持ち、
`enqueue_replay_subtype` / `merge_replay_derivation`がresult
`ConstraintRecord.replay_derivations`へ登録する。`lower`は`1670 <: 1524`を表すlower
`BoundRecordId`、`upper`は1524のcovered upper record、`pivot`は1524を識別する。result
constraintが`Pos::Var(1670) <: Neg::Var(1669)`なら、`step_subtype`が1670側のcanonical upper
recordを作る。

lineage carrierはこの`BinaryReplayDerivation`である。`ReplayClaimParent`は
`BoundReplayAction`が実際に根拠にしたclaim IDとedgeをresult constraintへ対応づける。
`UnionBranch` / `FunctionReturnEffect`は`carrier.replay.lower`から既存bound /
constraint provenanceを辿れば説明できるが、coverage判定ではrule名を読まない。これにより、
function return effectだけを通すspecial caseではなく、solverがすでに登録した任意の正当な
binary replayへ同じ一般規則を適用できる。

lineageを有効とみなすには、次をすべて満たす。

1. ordinary / duplicate constraint pathでは、carrierの`replay`が
   `carrier.result.replay_derivations`にexactに登録済みである。evidence-only pathでは、target
   boundが同じ`BinaryReplayDerivation`の`BoundDerivation::ReplayEvidence`を持つ。
2. carrierの`replay.upper`が、action作成時に`parent_claim`を保持していたcanonical upper
   recordである。
3. ordinary / duplicate pathのtarget upper boundが
   `BoundDerivation::Constraint(carrier.result)`を持つ。evidence-only pathでは、前項の
   `ReplayEvidence`がこの役割を持つ。
4. replay planningがそのactionの根拠として`parent_claim`を明示的に渡している。upper recordに
   claimが同居するというだけで全claimをparentにしない。

`ReplayDerivationInsert::Incomplete`でcanonical exact edgeが保存されなかった場合、または
evidence budget dropでtarget boundが`BoundDerivation::IncompleteReplay`になった場合、そのedge
からcoverageを継承したことにしない。必要なconfirmed pathがbudget dropへ落ちるなら、generic
replayへ黙ってfallbackした状態をlandingせず、§10.1のstop conditionとしてprovenance budget /
representation設計へ戻る。

#### 5.9.2 admission と duplicate / evidence path

v3のreplay planningは、一つのsemantic actionをclaim数だけenqueueせず、そのactionを根拠づける
claim ID群をaccountingへ残す。v4ではこのclaim ID群を`BoundReplayAction`相当のsnapshotへ載せる。
covered stateのincremental unmatched routeは、そのrouteを所有するcovered claimを載せる。
uncovered generic routeは、generic actionを要求したuncovered claimだけを載せる。

new canonical replay constraintでは、edge登録と同時に`ReplayClaimParent`をconstraintへ登録し、
後続のvar-var bound admissionでtarget upper claimを作る。すでにcanonical constraintが存在して
queueへ再投入されないduplicate pathでもparent metadataをmergeする。deterministicなtarget
upper boundがすでに存在すれば同じ時点でlineage claimをmergeし、まだ存在しなければ後続の
original queue admissionがparent metadataを読む。evidence-only pathでも
`apply_bound_replay_evidence_actions`が作るupper evidence recordへ同じlineageを付け、ordinaryへ
promotionされたときにclaim identityを失わない。trivial actionはtarget boundを作らないため
lineage claimも作らない。

target claimのcanonical keyは`(target BoundRecordId, coverage_root)`である。同じroot claimが
same-key proof、duplicate replay、別のsemantic pathから同じtarget recordへ再到達しても、
新しいclaimを作らず既存claimへcoalesceする。alternate proofの完全な説明は既存
`ConstraintRecord.structural_derivations` / `replay_derivations`と
`BoundRecord.derivations`へ残し、claim側へ全proofをcopyしない。別rootのdirect claimは同じ
record上でも別claimのまま残る。

§5.8のlifecycle規則はderived claimにもそのまま適用する。replacement / pruneでは
`current_record`と`derived_claim_by_record_and_root`のkeyをsurvivorへ移し、lineage parent /
root / carrierは変えない。same-key merge、subsumption、evidence promotionで別rootのclaimが
同じsurvivorへ集まってもrootごとに別claimを保ち、survivor全体をcoveredへ昇格させない。

#### 5.9.3 coverage lookup とcycle bound

canonical upper recordのclaimを分類するときは、各claimについて次だけを行う。

```text
root = claim.coverage_root
covered = live_coverage_by_root[root] is non-empty
```

自分自身のsourceにlive reduction stateがあるかは必要条件ではない。これにより、1524のcovered
claimからexact replay edgeで派生した1670のclaimは、1670自身がreductionを一度も起こして
いなくてもcoveredになる。一方、`ConstraintRecordId(6483)`の
`PosId(1681) <: NegId(2056)`はcovered claimをparentにするreplay edgeを持たないため、
`coverage_root = self`のuncovered direct claimであり、endpointを共有してもgeneric replayする。

parent chainのwalkはcoverage hot pathへ置かない。derived claim作成時にparentの
`coverage_root`をcopyしてroot参照を圧縮し、`depth = parent.depth + 1`をchecked arithmeticで
記録する。parent claim IDはchildより小さいことをassertし、既存
`(target record, root claim)`に戻るedgeは新しいclaimを作らない。したがってconstraint graphに
alias cycleがあってもclaim lineage自体はDAGであり、coverage checkはO(1)で停止する。

claim / link数の上限は、replay回数やproof追加回数ではなくcanonical
`(target bound, root claim)`数である。maximum depth、rootあたりのderived claim数、
duplicate / cycleでcoalesceした回数をtiming censusへ加える。claim数がcanonical semantic
bound × logical rootで説明できず増える、depth overflowが起きる、またはcoverage checkが
parent graphを歩く必要が出た場合はlandingしない。

### 5.10 v5: initial unmatched route のexplicit parent

`09237c6b`時点の現行codeでは、initial reductionはreduced upperをmaterializeし、
`register_unweighted_row_reduction`でstate / ownerを登録した後、
`row_effect.rs:328-334`のloopでsnapshot lowerをrouteする。matched lowerは
`original_upper`、unmatched lowerは`reduced_upper`を選び、どちらも最後は
`enqueue_row_derived_subtype(lower.pos, lower.weights, upper, aggregate)`へ入る。このlexical
call siteはinitial unweighted reduction専用だが、helper本体
（`machine/entry.rs:1361-1407`）はrow invariant、weighted residual、row-item matchからも
呼ばれる。

v5では、state登録時に確定したreduction自身のoriginal claimを`root_claim`として取り出し、
loopを次の意味形へ分ける。実装名は既存admission APIへ合わせてよいが、owner metadataを
`RowDerivationRule`やendpointから推測してはならない。

```text
for snapshot lower:
    if matched:
        enqueue_row_derived_subtype(lower, original_upper, aggregate)
    else:
        enqueue_initial_unmatched_reduction_subtype(
            lower,
            reduced_upper,
            aggregate,
            parent_claim = root_claim,
        )
```

`enqueue_initial_unmatched_reduction_subtype`は別のsemantic subtype ruleではない。
generic row-derived admissionへ、明示的なclaim parentを追加するnarrow wrapperまたはparameterで
ある。canonicalization後にnon-trivial resultが得られたら、new / duplicateのどちらでも次を
exact result constraintへmergeする。

```text
ReductionRouteClaimParent {
    claim: UpperReplayClaimId
    derivation: RowDerivationId
}

reduction_route_claim_parents_by_constraint:
    ConstraintRecordId -> small set<ReductionRouteClaimParent>
```

§5.9の`UpperReplayClaimLineage.carrier`には次の第三variantを加える。

```text
ReductionRouteConstraint {
    result: ConstraintRecordId
    derivation: RowDerivationId
}
```

carrierを有効とみなす条件は、(1) `result`の
`ConstraintRecord.row_derivations`へexact `derivation`が登録済み、(2) explicit
`parent_claim`が、同じrouting loopを発行したlive reduction state自身のclaim、(3) routeが
unmatched armからcurrent reduced upperへ向く、の三つである。`RowDerivation`は
`parents: Vec<RowDerivationParent>`を持つN-ary hyperedgeだが、親集合をcoverage判定でwalkしない。
result constraintとexact aggregate IDのpairは説明carrier、explicit claim IDはownershipの正本と
して役割を分ける。

result constraintが後続`step_subtype`でcanonical upper recordを初めて登録するとき、
`(target BoundRecordId, parent.coverage_root)`をkeyにderived claimを作る。claimは
`parent_claim = root_claim`、`coverage_root = root_claim.coverage_root`、
`depth = root_claim.depth + 1`、carrierを上記pairとする。通常のconfirmed shapeではreduction
claim自身がrootなので、childのrootはそのreduction claimである。constraintがduplicateでtarget
record / claimがすでに存在する場合は、semantic queueの再実行や後日のedge discoveryに頼らず、
同じadmission中に既存derived claimへmetadataをcoalesceする。target recordがまだ無ければ、
constraint-local parent metadataを後続の最初のbound admissionが読む。trivial constraintは
result recordもtarget claimも作らない。

この経路で作るchildは「別claimから証明edgeを見つけて継承したclaim」ではなく、reductionが
自分で発行したfirst-party byproductである。したがってv4の
`BinaryReplayDerivation` discovery条件を緩めず、`ReplayClaimParent`の候補探索へ
`RowDerivation`全体を追加しない。root compression、same-record上のroot別claim、
replacement / prune、live-root lookup、cycle / duplicate boundは§5.9をそのまま再利用する。

over-taggingについて、`09237c6b`時点ではself-tag対象のlexical call siteはinitial reduction
routing専用であり、unmatched armは必ずそのreduction自身のdirect byproductを作るため、
explicit taggingは無条件に安全と判断する。ただし実装開始時に次を再確認する。

1. dedicated wrapper / explicit parent parameterを呼ぶのが、このunmatched armだけである。
2. matched armと、helperを共有するweighted residual / row invariant / row-item matchは従来の
   generic admissionを使う。
3. canonical duplicate上の既存direct claimをderivedへ書き換えず、root別childだけを
   add / coalesceする。

もし同じtagged call siteまたはwrapperがunrelated constraint purposeからも呼ばれているなら、
この安全仮定は破れ、taggingは広すぎる。その場合はlandingせず、call siteを分離してexplicit
ownerをunmatched branchだけへ戻す。helper全体へのimplicit tagging、`UnweightedReduction`
rule名だけでのtagging、row-derivation parent walkによる後付けclassificationは代案にしない。

### 5.11 v6: claim-aware scheme-projectable bound view

#### 5.11.1 current bypassとAPI境界

`bc1dc55a`時点の`step_subtype`はVar–Var constraintで、targetへ
`add_lower_bound(..., BoundDerivation::Constraint(parent))`、sourceへ
`add_upper_bound(..., BoundDerivation::Constraint(parent))`をこの順に呼ぶ
（`machine/propagate.rs:104-128`）。前者の`TypeBounds::add_lower`
（`constraints/mod.rs:435-455`）は`BoundRecordState::Ordinary`を指定し、
same-keyなら`add_bound`がcanonical recordへderivationだけをmergeする。

`VarBounds::projection_lowers`（同`:669-671`）はrecord IDを返さず、evidence / ordinary
lowerを無条件に連結する。record ID付きの
`generalized_projection_lowers`（同`:687-691`）もfilterは行わない。
claim / livenessは`VarBounds`だけでは判定できないため、既存`projection_lowers`の意味を
全consumer向けに変更しない。`ConstraintMachine`が所有するscheme専用viewを新しい境界にする。

必要な意味形は次である。型名とsmall collectionはimplementation時に既存命名へ合わせてよい。

```text
SchemeProjectionClaimLink {
    lower_record: BoundRecordId
    claim: UpperReplayClaimId
}

scheme_projection_claims_by_lower_record:
    BoundRecordId -> small set<UpperReplayClaimId>

scheme_projection_lower_records_by_root:
    UpperReplayClaimId -> small set<BoundRecordId>

scheme_projection_claimed_lower_owners:
    small set<TypeVar>

SchemeProjectableLower {
    record: BoundRecordId
    bound: WeightedLowerBound
    reason:
        Unclaimed
        | UncoveredClaims(small non-empty set<UpperReplayClaimId>)
}

ConstraintMachine::scheme_projectable_lowers(TypeVar)
    -> iterator<SchemeProjectableLower>
```

`UpperReplayClaimId`は§5.8〜§5.10のlogical claim identityをそのまま使う。lower用の第二claim
graphやendpoint tokenを作らない。名前はupper replay admissionから始まった歴史を持つが、
v6では同じVar–Var logical relationのlower-side scheme projectionもこのIDへlinkする。
`scheme_projection_lower_records_by_root`はliveness transition時に影響ownerをglobal scanなしで
列挙するreverse indexであり、coverage判定のhot pathでは使わない。

現行`add_lower_bound` / `add_upper_bound`はstable `BoundRecordId`をcallerへ返さない。
claim-aware Var–Var admissionは、既存のinsert / evidence / replay / event順を変えず、
両側のcanonical record IDをnarrow internal resultとして受け取れるようにする。
§5.9 / §5.10がtarget upper claimをnew / duplicate / evidence promotionで作成または
coalesceした同じadmission中に、そのclaim IDをmirror lower recordへlinkする。
後日のderivation graph walk、producer文字列、endpoint shapeからlinkを復元しない。

#### 5.11.2 per-claim filtering

viewはownerにraw `VarBounds`がなければemptyを返す。machine全体のlink tableがempty、または
ownerが`scheme_projection_claimed_lower_owners`に無ければ、
`generalized_projection_lowers`と同じrecord順、evidence / ordinary順、endpoint、weightsを
そのまま`Unclaimed`として返す。これはordinary programのno-op fast pathである。

linkを持つrecordでは、linked claimごとに圧縮済み`coverage_root`を読み、
`live_coverage_by_root[root]`がemptyのclaimだけを`uncovered`へ入れる。

```text
links(record) == empty
    => yield(record, Unclaimed)

links(record) != empty && uncovered(record) != empty
    => yield(record, UncoveredClaims(uncovered(record)))

links(record) != empty && uncovered(record) == empty
    => suppress from scheme projection
```

canonical lower recordに、reduction-own covered claimと別producerのindependent claimが同居する
場合、同じendpointをclaim数だけcompactへ重複投入しない。recordを一回yieldし、
`UncoveredClaims`にはindependent claimだけを入れる。covered claimはraw record /
claim table / lineageへ残るが、schemeのsemantic inputにもgeneralized witnessのparentにも
数えない。これは§8.1 test 2と§8.2 test 2のco-ownership境界をscheme projectionへそのまま
延長する規則である。

linkの欠落、存在しないclaim ID、壊れたroot参照を「covered」とみなしてrelationを消さない。
release buildでは情報を失わない側へfail-openしてprojectし、timing / completenessへ
incompleteを記録する。ただしreduction-own routeにこの状態が一件でも出た実装は§10.1の
stop conditionによりlandingしない。fail-openは破損metadataを正しいと認めるfallbackではなく、
unsoundなscheme narrowingを避ける最後の防波堤である。

#### 5.11.3 liveness、lifecycle、epoch

coverageはlink作成時にcopyしない。queryのたびに
`claim.coverage_root -> live_coverage_by_root`を引くため、replacement / subsumptionでstateが
別materializationへ移ってもrootがliveならsuppressionを保ち、last stateがcomplete / expire /
pruneでindexから外れれば同じraw relationを再びprojectする。root非live化後も
「以前coveredだった」というbooleanをlower recordへ残さない。

v6はstateをいつcomplete / expireさせるかを新しく決めない。現行設計がstateをliveに保つcaseは
そのまま保つ。liveness-transition regressionは、production lifecycleが最後のstateを外す
narrow helper、または同じhelperを使うtest-only constructionでviewの前後を観測する。
testのためだけに新しいexpiry policyをproductionへ追加しない。

claim linkのinsert / move / coalesce、evidence promotion、lower recordの将来のsubsumption /
pruneでは、root別claimを維持する。survivorへ移す場合も、survivorに以前からある別claimを
coveredへ昇格させない。tombstone recordのlinkはaudit historyとして保持してよいが、
active raw iteratorに出ないためviewへは出さない。

projectabilityが変わるmetadata mutationはraw lower vectorを変えなくてもscheme semanticsの
mutationである。implementationには、意味形として

```text
record_scheme_projection_mutation(owner: TypeVar)
```

を置き、少なくとも次をatomicに行う。

1. global `ConstraintEpoch`をbumpする。
2. ownerのbound / projection epochを同じ値へ進める。
3. owner dirty schedulingがactiveなら`DependencyKey::ConstraintBounds(owner)`をpublishする。
4. projection metadataの変更として`ProvenanceEpoch`もbumpする。

rootのlive setがnon-emptyから別のnon-emptyへ変わるだけならprojectabilityは変わらないため、
compact invalidationは不要である。empty/non-emptyを跨ぐtransition、またはrecordの
unclaimed / all-covered / partly-uncovered分類が変わるlink mutationだけが、reverse indexから
影響するactive lower ownerを列挙して上記mutationをpublishする。claim-qualified provenance
だけが変わりcompact endpoint集合が同じ場合も`ProvenanceEpoch`は進める。live setのmemberが
non-emptyのまま入れ替わる場合も、audit上のowner stateが変わるため`ProvenanceEpoch`は進める。

`CompactCollector.cache`とpositive-alias cacheはimmutable machineを借りる一pass内cacheなので、
pass途中のliveness changeは起きず、key追加や手動clearをしない。
`GeneralizeCompactCache`は`analysis/mod.rs:297-365`と
`analysis/session/generalize.rs:580-600`で確認した通り
`(root TypeVar, ConstraintEpoch)`をkeyにするため、上記global epoch bumpで必ずmissする。
将来per-variable projection cacheを追加する場合も、raw `VarBounds::epoch`だけでなくこの
scheme-projection mutationをkey / dependencyへ含めるまで有効化しない。

#### 5.11.4 compaction、alias expansion、provenanceの共有

三consumerはfilterを別々に再実装しない。

- `compact_var_bounds` / `compact_lower_bounds`はpositive sideで
  `ConstraintMachine::scheme_projectable_lowers(var)`を使い、yieldされた`bound`だけを現在と同じ
  weight処理、stack-family coexistence、`compact_pos_bound_id`へ渡す。negative upper collectionと
  concrete node compactionは変更しない。
- `positive_aliases_within_scheme`も同じiteratorを使い、その後に現在どおり
  alias-neutral weight、`Pos::Var`、`allowed`を判定する。covered-only recordをtransitive alias
  cacheへ入れない。cache keyは一pass内の`TypeVar`のままでよい。
- `capture_generalized_witnesses`は同じiteratorのrecord / endpoint / `reason`を使う。別の
  provenance-only projectability判定を持たない。

最初の二consumerは`reason`を無視してendpointを一回処理できるが、provenanceはclaim granularityを
保存する必要がある。`Unclaimed`では既存
`GeneralizationParent::Bound(record)`をそのまま使う。
`UncoveredClaims`では意味形として

```text
GeneralizationParent::BoundClaim {
    bound: BoundRecordId
    claim: UpperReplayClaimId
}
```

をclaimごとに使い、covered claimのderivationをscheme witnessへ入れない。
explanation / occurrence-provenance / portable exportのexhaustive consumerはこのparentを
claimのproducer / lineage carrierへ辿れるようにする一方、raw `BoundRecord`と全derivationは
audit APIから引き続き参照できる。mixed recordをplain `Bound(record)`として登録し、
説明時に全derivationを展開する形ではper-claim filteringにならないため採らない。

claim-qualified generalized parentはscheme provenanceの精度変更であり、quantifier /
freshening規則の変更ではない。incoming edge budgetはprojectable claim数でboundedにし、
同じ`(bound, claim)`をdedupする。claim-qualified parentを既存portable provenanceへ安全に
表現できない場合は、covered proofをplain bound parentとして混ぜたり黙ってdropしたりせず、
H3を止めてprovenance representationを再設計する。

## 6. 採らない方向

### 6.1 lowering-side order workaround

local-var helperやhand-built applicationのconstraint順をparsed loweringへ似せ、family lowerを
reduction前に揃える案は採らない。同じrow relationの意味がconstruction pathに依存し、
別のsyntax / lowering pathで同じbugが再発する。

### 6.2 quiescenceまでreductionを遅らせる

「今後lowerが来ない」時点までrow upperを保留する案は、streamingなbound replayと
generalization lifecycleへ新しいglobal phaseを加える。late lowerをsource-localに処理できる
問題に対してblast radiusが大きく、hot path全体を再設計する理由にならない。

### 6.3 original row と plain residual の両方をordinary upperとして保存する

original upperを残すだけでは、late matched lowerがplain residualにも通常replayされる。
二本のordinary upperは過剰制約を作り、replay ownershipの問題を解かない。

### 6.4 provenanceからoriginal rowを毎回復元する

late lower到着時に`RowDerivation` graphを逆走査してoriginal itemsを復元する案は、
hot pathへ非局所探索を置き、prune / subsumption後のlifecycleも不明瞭にする。original rowは
stateの主データとして直接保持する。

### 6.5 fresh residual variableや後段cleanupを足す

fresh varを一段増やしても、late lowerがoriginal prefixと再照合されなければcontamination先が
変わるだけである。compact / finalize / specializeでfamilyを消す後段cleanupも、誤ったsolver
relationを隠すため採らない。

### 6.6 zero-lower / UpperFirstのlazy activation

row upperがzero lowerで先に到着し、lowerが一件ずつ後から来るcaseを、本sliceでは扱わない。
このcaseは抽象的なsolver-generality propertyとして未解決のまま残す。

ordinary `Neg::Row` upperへmatching lowerが後着したことだけをtriggerにlazy recordを作る案は
採らない。実装attemptで、reductionのzero/no-match branch由来のupperだけでなく、compiler内の
無関係なordinary `Neg::Row` upperにも広く一致し、reduction / tombstone増幅と説明不能なpoly
hash変化を起こしたためである。

再開条件は、reduction-eligibleなordinary row upperと無関係なordinary row upperを、型形状の
推測ではなく構造的なtag / definition kind / ownership linkageで区別できる設計を先に作ること。
そのtagのlifecycle、dedup、prune / subsumption、provenance、characterization costを別projectで
設計する。bug note「24回目」「25回目」の実reproはupper到着前に18 lowerを持つため、このdeferで
実bugの修正範囲は失われない。

### 6.7 v3で採らないownership判定

- `BoundDerivation`のvariantや`FunctionReturnEffect`の有無だけでcovered / independentを決めない。
- `UnionBranch` / `FunctionReturnEffect`をlineage propagationのwhitelistにしない。必要なのは、
  それらが作りうるlower relationをparentに持つexact `BinaryReplayDerivation`である。
- survivorにreduction ownerが一つあれば全derivationを抑止するrecord-wide suppressionをしない。
- ownerのderivation identityと違えば常にindependentとするv2判定を延命しない。
- replay planning時にprovenance graphを逆走査してproducerを推測しない。
- subsumption / equivalent mergeでsurvivorの全claimへcoverage tokenをばらまかない。
- 同じ`NegId` endpointを共有する別sourceのclaimを、lineage edgeなしでcoveredへ昇格させない。

### 6.8 v6で採らないprojection workaround

- `projection_lowers`自体からrecordを削除し、solver replayやauditまで同時に変えない。
- lower endpointへ`covered: bool`をcopyし、rootがnon-liveになった後も隠し続けない。
- 一つのcovered claimを理由にcanonical lower record全体を隠さない。
- compactionだけをfilterし、positive alias expansionまたはscheme provenanceにraw graphを
  残さない。
- `finalize_generalized_compact_root`で完成済み`CompactRoot`から特定family / variableを
  cleanupしない。根因はfreezeより前にある。
- local-var callback body、`inner_r`、`&buffer`、block aggregationへcase-specificな
  suppressionを入れない。
- state completion後も「materializationが一度代替した」という履歴だけでrelationを
  non-projectableにしない。
- cacheを無効化せず、testではcacheをoffにして正しさを装わない。

## 7. この設計で変更しないもの

- `notes/design/2026-07-28-local-var-effect-boundary-fix.md` のv5 local callback parameter
  lifecycle、private helper、runtime `ArgEffectContract`を変更しない。
- local-var lowering、application lowering、block aggregationのconstraint挿入順を
  solver回避のために変更しない。
- weighted row reduction、`RowResidualKey` / `RowResidualRecord`の意味を変更しない。
- effect-family classification、payload invariance、pop-only matching eligibility、
  independent-lower matchingを弱めない。
- `generalize` / `instantiate` のlevel、quantifier、freshening規則を変更しない。
- specializeのcandidate比較や`ConflictingTypeCandidates`を緩めない。
- co-occurrence analysis、polarity elimination、residual desugaringへrigid variable、
  blocked pair、protected-variable setを追加しない。
- `Any`を未解決fallbackとして使わず、`Never` / `Unknown`の意味も変更しない。
- path、module、function、fixture名によるspecial caseをinferenceへ追加しない。
- initial snapshotだけを扱う既存三テストの期待値・テスト名・意図を変更しない。
- current characterization baselineの差分を、実装出力に合わせるだけの更新でgreenにしない。
- zero-lower / UpperFirst用のspeculative stateや、ordinary `Neg::Row`のshapeだけを見るlazy
  activationを追加しない。
- claim linkageを一度も持たないordinary lowerは、compaction、positive alias expansion、
  scheme provenanceのすべてで従来と同じ順序・weights・endpointをprojectする。
- weighted row reduction、generalize / instantiateのquantifier / freshening、
  specialize candidate comparison、finalizerのfreeze semanticsをv6のために変更しない。
- raw `projection_lowers`、canonical `BoundRecord`、全derivationをaudit / explanation sourceから
  削除しない。scheme viewだけをclaim-awareにする。
- compaction cacheの正しさをlivenessが不変という仮定へ置かない。projectability transitionは
  epoch / dependency mutationとして明示する。

## 8. regression tests

次の7 testを`crates/infer/src/constraints/tests/case_02.rs`の既存unweighted-row-upper test群と
同じ構造で用意する。test名は実装sliceで既存命名へ最終調整してよいが、各semantic contractを
一つずつ分離する。最初に正しい期待値でtestを書き、現行実装で対象caseがfailすることを確認して
からsolver implementationへ進む。期待値を現行の誤ったresidual contaminationへ合わせない。

1. **matching late lowerの基本case**  
   `lower F -> upper [F; ρ] -> late lower F`の順に追加し、late `F`が`ρ`のlowerにならないことを
   固定する。late lowerがoriginal upperへrouteされ、late bound recordが
   `UnweightedReduction` / `RowItemMatch` provenanceから辿れることも確認する。
2. **constraint insertion order不変**  
   同じlower / upper集合を、row upper到着時に一件以上のmatching lowerがすでに存在する
   「全lowerがupperより前」「一件以上がupperより後」の少なくとも二順序で投入し、semantic
   bounds、residual row、payload constraintが同じfixpointになることを固定する。record IDや
   queue順そのものは比較しない。zero-lowerの真のUpperFirst permutationはgreen contractへ
   混ぜず、§6.6を参照する明示的なknown-gap witnessとしてtest codeに残す。
3. **unmatched late familyのresidual transport**  
   initial `F`で`[F; ρ]`をreductionした後にlate `G`を追加し、`G`は正しく`ρ`へ流れる一方、
   `F`は流れないことを固定する。unmatched routeでlower weightsが失われないことも確認する。
4. **partial / multi-item rowのincremental consumption**  
   upper `[F, G; ρ]`、initial lower `F`、late lower `G`の順で、current reduced upperが
   `[G; ρ]`から`ρ`へ縮むことを固定する。late lowerがoriginal `[F, G; ρ]`に対して照合され、
   old `[G; ρ]` materializationがlive recordとして残らないことも確認する。
5. **payload-bearing family invariance**  
   `F(P_lower)`をlate lower、`F(P_upper)`をoriginal itemにし、path一致だけで消費せず、
   payloadの両方向constraintが`RowItemMatch`から生成されることを固定する。matched familyが
   residualへ漏れないこととpayload provenanceを同時に確認する。
6. **alias経由 / pop-only late lower**  
   一つのtest内の独立subcaseで、(a) late concrete familyがalias variableのlower graphを介して
   到着する場合、(b) late familyがfilterなし・pushなしのpop-only weightを持つ場合を固定する。
   どちらも現行initial matchingと同じeligibilityでoriginal prefixを消費し、residualへ流れない。
7. **prune / subsumption後のstateとprovenance**  
   reduction state作成後にcurrent reduced upperがreplacement、equivalent dedup、
   `prune_upper_rows_subsumed_by_reduced_upper`の少なくとも代表的なtransitionを受け、その後に
   late matching lowerを追加する。stateがtombstoneをlive endpointとして使わず、
   original-row matching、current materialization、producer / lower provenanceがstaleに
   ならないことを固定する。

### 8.1 v3で先に追加する3 regression tests

URR-Eのproduction codeを変更する前に、次の三つを同じ`case_02.rs`へ追加する。producer
constraint ID、claim ID、canonical bound record IDをtest helperから観測し、derivationの有無や
endpoint equalityだけで判定しない。

1. **later same-key mergeはcoveredのまま**
   initial matchingで`source <: [F; ρ]`を`source <: ρ`へreductionし、reduced upperを
   `Inserted(R)`としてmaterializeした後、同じproducer-rootから得た別proofをsame-key
   provenance/evidence mergeで`R`へ追加する。その後late matching `F`を追加しても`ρ`へ届かず、
   generic replayは0、incremental matched routeだけが存在することを固定する。
2. **真に独立したdirect tail relationはreplayする**
   test 1と同じreductionに加え、別のreal constraintとして`source <: ρ`を導入する。二つのclaimが
   別producer constraint IDを持ち、reduction claimだけがcovered、direct claimはuncoveredである
   ことを確認する。late matching `F`はoriginal row routeに加え、独立claimのgeneric replayにより
   正しく`ρ`へ届く。単にrecordに複数derivationがあることをtest oracleにしない。
3. **確認済みlifecycleを直接固定する**
   nested witnessを最小化し、ordinary upper 0本からreductionが`R`を`Inserted`し、その後の
   same-key provenance/evidence mergeがrecord identityを変えず
   `semantic_changed = false` / `provenance_changed = true`となり、二つ目の
   `EquivalentTo` / `SubsumedBy` dispositionを作らないことを固定する。merge後もstate tokenが
   claimをcoverし、late matching lowerがresidualへgeneric replayされないことまで確認する。

test 1と3は現行実装でinner-family contaminationまたは誤ったgeneric replay countによりred、
test 2はcoverageをrecord-wideに広げる誤修正に対するgreen controlでなければならない。三つを
一つのfixture名や`FunctionReturnEffect`文字列へspecial case化しない。

### 8.2 v4で先に追加する3 regression tests

URR-Fのproduction codeを変更する前に、次の三つを同じ`case_02.rs`へ追加する。investigationの
arena IDは説明にだけ使い、test oracleへ`TypeVar(1670)` / `ConstraintRecordId(6611)`の数値を
hard-codeしない。claim ID、root claim ID、parent claim ID、result constraintに登録された
`BinaryReplayDerivation`、target bound recordをtest helperから構造的に観測する。

1. **証明済みcross-source replayはcovered lineageを継承する**
   source `α`で`α <: [F; ρ]`のinitial reductionを成立させ、別source `β`から`β <: α`を、
   nested Union branchのfunction return effect decompositionで導く。`β <: α`のcanonical
   constraintに`StructuralDerivationRule::UnionBranch` /
   `StructuralDerivationRule::FunctionReturnEffect`のparent chainがあり、そのlower boundと
   `α`のcovered upperから作られたresult constraintに、`pivot = α`、parent upper record一致の
   exact `BinaryReplayDerivation`があることを先に固定する。resultの`β <: ρ` upper claimは
   `β`にreduction stateがなくても、`α`のcovered claimをparent、同じclaimをcoverage rootとして
   持つ。`β`のmatching family lowerはgeneric replayで`ρ`へ届かず、cross-source claim由来の
   generic replay countが0になる。これはconfirmed `1670 <: 1524` shapeの最小testであり、
   lineage未実装ではredでなければならない。
2. **別sourceのsame-endpoint direct producerはuncoveredのまま**
   test 1と同じcovered `α <: ρ` materializationを持つ一方、reductionと無関係な別source `γ`へ
   real direct constraint `γ <: ρ`を導入する。二つは同じ`NegId(ρ)` endpointを使うが、
   `γ`のconstraint / boundには`α`のclaimをparentにするexact replay edgeがないことを確認する。
   `γ`のclaimは`coverage_root = self`、別producer、uncoveredであり、late lowerはgeneric replayで
   `ρ`へ届く。このcontrolはinvestigationの
   `ConstraintRecordId(6483): PosId(1681) <: NegId(2056)`に対応し、endpoint-wide suppressionを
   必ず検出する。§8.1 test 2の同一source上のclaim co-ownership controlも期待値無変更で残す。
3. **multi-hop lineageはroot-compressされ、cycleで増殖しない**
   covered root claim `α`から二つのcanonical replay hopで`β`、`γ`のupper claimを作る。
   両derived claimの`coverage_root`が`α`のoriginal claimへ直接圧縮され、depthが1、2、
   parent IDが常にchild IDより小さいことを固定する。その後、既存targetへ戻るreverse alias /
   replay edgeを追加してsemantic constraint graphにcycleを作り、同じ
   `(target BoundRecordId, root claim)`のclaimが増えず、coverage lookupとqueue drainが停止する
   ことを確認する。proof merge後のclaim count、maximum lineage depth、cycle coalesce countも
   固定し、parent graph walkをtest helperのcovered判定へ持ち込まない。

test 1と3のlineage assertionはproduction lineage未実装でred、test 2はendpoint-based誤修正を
入れない限りgreen controlでなければならない。三testとも、fixture / function名、
`FunctionReturnEffect` variant単体、endpoint equalityをcoverage oracleにしない。

### 8.3 v5で先に追加する2 regression tests

URR-Gのproduction codeを変更する前に、次の二つを同じ`case_02.rs`へ追加する。§8.2で使った
claim / root / carrier observation helperを、`ReductionRouteConstraint`も区別できる形へ拡張する。
test helperは`RowDerivation` graphをwalkしてcoverageを推測せず、production admissionが記録した
explicit parentとcarrierを直接観測する。

1. **initial unmatched routeのresult claimは作成時からreduction rootに属する**
   source `α`へ、original item `F`に一致するconcrete lowerと、reduction時点では`F`に一致しない
   variable lower `β`を先に追加する。その後`α <: [F; ρ]`を追加してinitial reductionを成立させ、
   `β`がunmatched armからreduced upper `ρ`へrouteされるshapeを作る。result
   `β <: ρ` constraintがaggregate `UnweightedReduction`のexact `RowDerivationId`を持ち、
   `BinaryReplayDerivation`を必要としないことを確認する。queue drain直後、後続のlineage
   discoveryや追加constraint投入を行う前に、`β`のupper claimが`α`のreduction claimを
   `parent_claim` / `coverage_root`に持ち、
   `ReductionRouteConstraint { result, derivation }`をcarrierとするdepth 1のderived claimである
   ことを固定する。`β`自身にはreduction stateがないことも確認する。

   その後`β`へmatching `F` lowerを追加し、`β`のlate lowerとrouted-to upperのpairから
   generic replayが0本であること、`F`が`ρ`へ漏れないことを確認する。initial matched lowerの
   original-upper routeと、`α`側のincremental ownershipは従来どおり残す。このtestはconfirmed
   `PosId(1725) -> NegId(2055)` shapeをarena数値なしで固定し、self-tag未実装ではclaimの
   `coverage_root = self`とgeneric replayによりredでなければならない。
2. **shared row-derived enqueueのunrelated constraintはuncoveredのまま**
   reduction stateを持たない別source `γ`について、`RowDerivationRule::WeightedResidual`の
   non-reduction derivationを作り、現行でも共有されている`enqueue_row_derived_subtype` admissionで
   `γ <: ρ`を導く。result constraintがexact `RowDerivationId`を持つ一方、initial-unmatched-routeの
   explicit parent metadataを持たないことを確認する。`γ`のclaimは
   `lineage = Original`、`coverage_root = self`、uncoveredであり、late `F` lowerはgeneric replay
   一本で`ρ`へ届かなければならない。このcontrolはhelper全体、`RowDerivationRule`全体、または
   row-derived constraint全体をcoveredにする誤修正を検出する。

test 1はself-tag未実装でred、test 2はnarrow call-site taggingを守るgreen controlでなければ
ならない。両testとも、production graphのarena ID、fixture名、endpoint equalityをoracleにせず、
exact parent claim、compressed root、`(result ConstraintRecordId, RowDerivationId)` carrierで判定する。

### 8.4 v6で先に追加する4 regression contracts

URR-Hのproduction consumerを変更する前に、次の四つを固定する。test 1〜3は
`case_02.rs`の既存claim / root / carrier / canonical record helperを拡張し、
raw bounds、scheme view、compact / finalized resultを別々に観測する。test 4は一個の小さいfixture
ではなく、既存five-case characterizationとfull contract corpusをno-op oracleとして使う。

1. **covered unmatched-route lowerはrawに残るがschemeへprojectされない**
   §8.3 test 1と同じ`α`、unmatched variable lower `β`、residual `ρ`を作り、v5のexplicit
   reduction-route parentによって`β <: ρ` claimがcovered rootへ属することを確認する。
   `ρ <- Var(β)`のcanonical lower recordが`BoundRecordState::Ordinary`のままraw
   `projection_lowers`と`BoundRecord` auditに存在する一方、
   `scheme_projectable_lowers(ρ)`には出ず、positive compact graphと最終schemeへ`β`由来familyが
   入らないことを固定する。generic replay countが0というv5 assertionだけではこのtestを
   greenにしない。current codeではraw compaction bypassによりredでなければならない。
2. **同じcanonical lowerのindependent claimだけをprojectする**
   test 1の`β <: ρ`と同じsemantic keyへ、別producerのreal direct constraintを追加し、
   mirror lower record一件にcovered reduction claimとuncovered direct claimを同居させる。
   raw record identityとendpointは一件のまま、viewもendpointを一回だけ返し、
   `UncoveredClaims`がdirect claim IDだけを含むことを確認する。compact resultにはrelationが残り、
   generalized witnessはdirect `BoundClaim`だけをparentにし、covered claimをscheme provenanceへ
   混ぜない。record-wide suppressionとclaim数ぶんの重複projectionを両方検出する。
3. **last live stateが外れるとrelationは再びprojectableになる**
   covered-only recordを持つrootについて、live stateありのview / compact結果とepochを保存する。
   production lifecycleと同じnarrow helperで最後のstateを`live_coverage_by_root`から外し、
   raw lower recordを変更しないまま、viewが同じrecordを
   `UncoveredClaims`として返し、compact / schemeへrelationが戻ることを固定する。
   `ConstraintEpoch`、owner epoch、`ProvenanceEpoch`が進み、cache-enabledな
   `GeneralizeCompactCache`が旧rootをhitせず再構築することも確認する。materializationが過去に
   equivalent informationを持ったという理由でrelationを隠し続ける期待値にはしない。
   productionにstate expiry policyがまだ無ければ、testはliveness indexのtransition helperを
   直接使い、新しいexpiry policyを導入しない。
4. **ordinary bound projectionはbroad corpusでbyte-for-byte no-op**
   `crates/infer/src/constraints/tests/characterization.rs`のstd-backed five caseについて、
   v6実装前のpoly / check hash、formatted scheme、constraint / bound / replay censusを保存する。
   reduction claim linkageを持たない全recordのview countがraw countと一致し、H2 / H3後も
   target nested local-var case以外のhash / scheme / diagnosticがbyte-for-byte不変であることを
   比較する。さらに`tests/yulang/cases.toml`のfull contract suite 287件を一つの必須gateとして
   通す。`cargo test -p infer`だけをこのno-op controlの代用にしない。

test 1はcompaction consumerを切り替えるまでred、test 2はper-claim viewとclaim-qualified
provenanceが揃うまでred、test 3はprojection-time liveness / epoch contractが無ければredである。
test 4はunrelated compaction driftを一件でも出した時点でredとし、expected hashを実装出力へ
合わせてgreenにしない。

この19 testに加え、次の既存testは名前も期待値も変更せず通す。

- `unweighted_row_upper_uses_concrete_lower_item_before_residual_tail`
- `unweighted_row_upper_consumes_pop_only_weighted_lower_item`
- `unweighted_row_upper_matches_each_lower_independently`

## 9. 実装 slicing plan

本書がユーザ承認済みになるまで、どのsliceも開始しない。各sliceは一つ前のgateを満たしてから
進め、後続sliceを先に混ぜない。

### URR-A: red regression と baseline 固定

production solver codeを変更する前に、§8の7 regressionを正しい期待値で書く。

手順:

1. 現行実装でtest 1とtest 2のlate-lower orderがfailし、`F`が`ρ`へ入ることを確認する。
2. test 3のunmatched `G`、既存三テスト、weighted-row controlsが現行でpassすることを確認する。
3. test 4〜7について、どのassertionが現行gapを直接示し、どれがfix後のlifecycle contractかを
   分けて記録する。
4. current five-case characterizationのscheme hash、constraint / bound / replay count、
   row-derivation coverage、wall time baselineを実装前の値として保存する。
5. `TypeVar(1524)` trace相当の最小testで、late lower追加前後のsource / residual boundsと
   provenanceをdumpできるtest helperを用意する。production loggingは追加しない。

check:

- targeted existing three unweighted tests
- targeted seven new regression tests（bug witnessはexpected failureを確認）
- current constraint characterization suite

URR-Aはtest-first preflightであり、正しい期待値をwrong outputへ合わせて単独greenにしない。
solver fixと同じ作業単位の中でredを確認してからURR-Bへ進む。

### URR-B: persistent state と incremental replay

変更:

- `ConstraintMachine`へsource-indexed record tableを追加する
- current initial reduction成功時だけpersistent stateを作る
- `add_lower_bound`のsemantic insertion後・generic replay plan前へsource-local hookを置く
- original itemsに対するindependent late matching、matched / unmatched routing、
  remaining updateを実装する
- reduction-owned replayと同一endpoint上のindependent ordinary replayをderivation単位で分ける
- state / late match / replacement / reuse timing censusを追加する
- zero-lower / initial no-match branchではrecordを作らず、ordinary `Neg::Row`からのlazy
  activationも行わない

gate:

- §8 test 1〜6がpassする
- 既存三テストが期待値無変更でpassする
- initial snapshotだけのbounds / derivation shapeが変わらない
- weighted row reductionのrecord / timing contractが変わらない
- row upper到着時に一件以上のmatching lowerが存在する§8 test 2のpermutationが同じfixpointになる
- zero-lower / UpperFirst known-gap witnessが§6.6を参照して残り、誤ってgreen contractに
  取り込まれていない

URR-Bの途中でplain reduced upper replayも残す暫定二重routeをlandingしない。

### URR-C: materialization lifecycle と provenance

変更:

- reduced-upper replacementを`store_upper_bound_without_replay`と同じextrude / subsumption /
  prune / disposition / event / neighbor lifecycleへ統合する
- stateのcurrent materializationをinsert / equivalent / subsumed / replacedで明示する
- tombstone transitionとsource ownership indexを同期する
- late match用append-only `UnweightedReduction` successorと`RowItemMatch`を記録する
- incremental replayをexisting replay accounting / explanation pathへ接続する

gate:

- §8 test 7がpassする
- late matched / unmatched両routeをproducer constraintとlower bound recordまで説明できる
- payload argumentの両方向constraintを`RowItemMatch`まで辿れる
- prune / subsumption後にstale live record、dangling state owner、`IncompleteReplay`がない
- existing constraint explanation / provenance testsが期待値無変更でpassする

provenanceを後付けTODOとしてURR-Dへ送らない。semantic pathと説明pathを同じsliceで閉じる。

### URR-D: production characterization と closeout

変更:

- five-case characterizationへpersistent state / transition censusを追加する
- baseline差分をlate-lower narrowing、追加audit record、意図しないreplayの三つに分類する
- latent late-lower shapeでscheme / poly hashが変わったcaseは、source、original row、
  late lower、旧contamination先を記録する
- implementation diffからunrelated refactor、lowering workaround、test-specific branchを除く

check:

- targeted §8 seven tests
- targeted existing three unweighted tests
- constraint characterization / explanation suites
- `timeout 180s cargo test -p infer`
- `timeout 180s cargo test -p specialize`
- `timeout 240s cargo test -p yulang`
- `timeout 300s cargo test --workspace`

URR-D closeout 実施記録（2026-07-30）: `215ba17f` push 後の CI で
`contract shard 4/4` が `parser_pattern_rest_public_signature` の型
不一致で fail した。read-only investigation の結果、URR fix が
無関係な parser fixture の spurious residual role demand
（関数の型のどこにも現れない `where 'a: ParseError(...)`）を正しく
discharge した narrowing だと確定——回帰ではない。期待値を更新
（`1b6a83da`）。契約スイート全体（287件）と `cargo test -p yulang`
（377 passed、既知の flaky test 1件は単独実行で pass 確認済み）を
再検証し、他に影響を受けた case は無いことを確認した。`cargo test
-p infer`（1012 passed）は前日に確認済み。`-p specialize` と
`--workspace` full run は CI の各 job（`workspace build`、
`yulang tests`、`runtime tests`、`user cache isolation test`
等）でカバーされている。

local-var known-gap contractの反転は、本projectのsolver fixが完了した後、
`notes/design/2026-07-28-local-var-effect-boundary-fix.md` の残りsliceとして扱う。
URR-Dでlocal-var lowering mechanismやexpected production outputを同時に書き換えない。

### URR-E: logical replay claim coverage

v3がユーザ承認済みになるまで開始しない。URR-A〜Dのlanded implementationをbaselineとし、
§8.1の三testを先に追加してred / controlを確認する。

変更:

- reduction stateへlogical relation IDとcovered claim setを追加する
- canonical upper recordへproducer-root付きclaim setを対応づける
- insert、same-key provenance/evidence merge、subsumption、replacement / pruneでclaimとcoverageを
  §5.8の規則どおり移送する
- `upper_record_requires_generic_replay`のrecord-wide booleanを、未covered claimを返す
  source-local planningへ置き換える
- incremental / generic actionのsemantic dedupを保ったまま、claim IDをprovenanceとtimingへ残す

gate:

- §8.1 test 1でlater same-key merge後のlate matching lowerがresidualへ届かない
- §8.1 test 2で別producerのdirect `source <: tail`だけはgeneric replayされる
- §8.1 test 3で`Inserted -> same-key provenance/evidence merge`のrecord identity、
  disposition count、coverageが固定される
- §8の既存7 regressionと既存三contractが期待値無変更でpassする
- nested hand-built characterizationからinner familyが消え、parsed controlと同じisolationを持つ
- single-boundary、weighted row、zero-lower known-gapのscopeが変わらない
- claim lookupはsource / current upper localで、late lowerごとのprovenance graph走査がない
- repository-stdでclaim setの最大長、generic replay総数、wall time / memory差分を説明できる

URR-Eではlocal-var production wiringを再開しない。solver gateが閉じた後、LVB-Bを別sliceとして
再開する。

URR-E一度目の実施記録（2026-07-30）: §8.1の三testは`0db4bf91`で追加され、
production試作では三test、既存URR contractともgreenになった。しかしnested hand-built
characterizationだけはcross-source経路からinner familyを漏らしたため、production差分はcommitせず
rollbackした。§8.1 testは保持し、同じURR-E実装を再試行しない。

### URR-F: proof-carrying cross-source claim lineage

v4がユーザ承認済みになるまで開始しない。`0264e950`のclean production baselineと、
§8.1のlanded preflight三testを起点にする。URR-E一度目のclaim / coverage実装はrollback済みなので、
URR-Fは§5.8のclaim-local coverageと§5.9のcross-source lineageを一つのatomic sliceとして実装する。

test-first preflight:

1. §8.2 test 1で、`β <: α`のstructural proofと、covered upperをparentにするexact
   `BinaryReplayDerivation`が現行provenanceへ存在する一方、target `β` claimのcovered lineageが
   無くgeneric replayされることをredとして確認する。
2. §8.2 test 2で、別sourceのdirect same-endpoint claimにcovered parent edgeがなく、generic
   replayされるgreen controlを確認する。§8.1 test 2も期待値無変更でgreenのまま固定する。
3. §8.2 test 3で、semantic alias cycle自体は現行queueで停止するbaselineを確認し、lineage
   root / depth / claim-count assertionだけをredとして分離する。
4. nested hand-built characterizationのinner-family漏れと、parsed controlのisolation baselineを
   実装前に保存する。expected schemeを現行漏れへ合わせない。

変更:

- §5.8の`UpperReplayClaim`、record-local claim index、state coverageをreintroduceする
- claimへ§5.9の`Original | Derived` lineage、parent claim、exact replay edge、compressed rootを
  追加する
- `BoundReplayAction`相当へ、そのsemantic actionを根拠づけたclaim IDのsmall setを載せる
- `enqueue_replay_subtype` / `merge_replay_derivation`のexact edge登録と同じadmissionで
  `ReplayClaimParent`をresult constraintへ対応づける
- new、duplicate、prefilter duplicate、evidence-only / promotionの各pathでtarget upper claimへ
  lineageを移し、trivial actionではclaimを作らない
- `(target BoundRecordId, coverage_root)` indexとmonotonic parent IDでduplicate / cycleを
  coalesceし、coverage checkをcompressed rootと`live_coverage_by_root`のlookupにする
- claim count、rootあたりderived count、maximum depth、cycle coalesce、lineage付きreplay
  provenance budgetをtiming censusへ追加する

gate:

- §8.2 test 1で、different-source target claimがexact replay edgeとcovered rootを持ち、
  generic replayされない
- §8.2 test 2と§8.1 test 2で、same endpointでもunrelated direct claimだけはuncoveredとして
  generic replayされる
- §8.2 test 3で二hopのroot compression、acyclic parent ID、cycle dedup、queue / coverage lookupの
  停止性が固定される
- §8.1 test 1〜3、§8の既存7 regression、既存三contractが期待値無変更でpassする
- `v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`からinner familyが消え、
  parsed controlと同じisolationを持つ。これをURR-Fの最終integration gateとする
- single-boundary、weighted row、zero-lower known-gapのscopeが変わらない
- covered classificationはroot index lookupで完結し、`StructuralDerivationRule`名のbranch、
  endpoint-wide token、late-lowerごとのprovenance graph逆走査がない
- lineage-bearing exact replay edgeが`IncompleteReplay`へ落ちず、claim / link数がcanonical
  `(target bound, root claim)`数で説明できる
- repository-stdでclaim / maximum depth / replay census、wall time、memory差分を説明できる

URR-Fではlocal-var production wiringを再開しない。nested characterizationはsolverのintegration
gateとしてだけ使い、solver gateが閉じた後にLVB-Bを別sliceとして再開する。

URR-F一度目の実施記録（2026-07-30）: §8.1 / §8.2の六testは`051be5fc`のpreflightから
red / green / redで固定され、production試作では対象四testとcontrol二testがすべてgreenになった。
しかしnested hand-built characterizationだけは、reduction自身のinitial unmatched routeが作った
claimをroot-selfとしたためinner familyを漏らした。production差分はcommitせずrollbackした。
`4107919e` / `09237c6b`の調査結果により、URR-Fのproof-discovery範囲をさらに広げず、
first-party byproductの作成時taggingをURR-Gへ分離する。

### URR-G: reduction-own unmatched route self-tagging

v5がユーザ承認済みになるまで開始しない。`09237c6b`のclean production baseline、
§8.1 / §8.2のlanded preflight六test、URR-F一度目で確認したgreen / nested-red結果を起点にする。
URR-Gは§5.8 / §5.9のclaim-local coverageとroot compressionを再導入したURR-F implementationへ、
§5.10のexplicit parent admissionだけを加えるatomic sliceとする。新しいcross-source
propagation discoveryや`RowDerivation` graph walkを同じsliceへ混ぜない。

test-first preflight:

1. §8.3 test 1で、initial reductionのunmatched armが作るresult constraintにexact aggregate
   `RowDerivationId`がある一方、target claimがroot-self / uncoveredで、late matching lowerを
   generic replayする現行gapをredとして確認する。
2. §8.3 test 2で、shared `enqueue_row_derived_subtype`を通るunrelated
   `WeightedResidual` constraintがexplicit reduction parentを持たず、root-self / uncoveredとして
   generic replayするgreen controlを固定する。
3. URR-F一度目と同じ六testを再実行し、v4のexact replay lineageとdirect-claim controlsの
   baselineを変えない。
4. `v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`のinner-family漏れと
   parsed controlのisolationを、URR-F一度目と同じ期待値で保存する。expected schemeを漏れへ
   合わせない。

変更:

- initial reduction state / original claimの登録結果から、route ownerとなるclaim IDを取得する
- `row_effect.rs:328-334`のloopをmatched / unmatched admissionへ分け、unmatched armだけが
  reduction claimとaggregate `RowDerivationId`をexplicitに渡す
- generic row-derived admissionのsemantic dedupを変えず、new / duplicate result
  `ConstraintRecordId`へ`ReductionRouteClaimParent`をmergeできるnarrow wrapperまたはparameterを
  追加する
- target upperのnew admissionではconstraint-local metadataからderived claimを作り、duplicateで
  target recordが既存なら同じadmission中に`(target BoundRecordId, coverage_root)`へcoalesceする
- §5.9のlineage carrierへ
  `ReductionRouteConstraint { result: ConstraintRecordId, derivation: RowDerivationId }`を追加し、
  root / depth / lifecycle / timingは既存compressed-root modelを再利用する
- matched arm、weighted residual、row invariant、row-item match、trivial constraintには
  reduction-route parentを付けない

gate:

- §8.3 test 1でrouted result claimが作成直後からreduction claimをparent / rootに持ち、
  late matching lowerをgeneric replayせず、residual contaminationを起こさない
- §8.3 test 2でunrelated row-derived claimがroot-self / uncoveredのままgeneric replayされる
- §8.1 / §8.2の六testが期待値無変更でpassし、v4のexact replay carrierとv5のdirect route
  carrierが混同されない
- §8の既存7 regressionと既存三contractが期待値無変更でpassする
- `v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`からinner familyが消え、
  parsed controlと同じisolationを持つ。これはURR-Fがすでに要求した**同じ最終integration
  gate**であり、URR-Gでは新しい期待値へ置き換えず、今度こそ実際に満たす
- single-boundary、weighted row、zero-lower known-gapのscopeが変わらない
- self-tagging callerがinitial unmatched arm一箇所に限られ、helperの他callerとmatched armに
  explicit parent metadataがない
- carrierの`result` / `derivation`がcanonical recordのrow proofとexact一致し、childのrootが
  routeを発行したreduction claimのcompressed rootと一致する
- new / duplicate admissionのどちらもsemantic queue再実行やpost-hoc graph discoveryを要求せず、
  claim数がcanonical `(target bound, root claim)`数で説明できる

URR-Gでもlocal-var production wiringを再開しない。nested characterizationはURR-Fから継続する
solver integration gateとしてだけ使い、solver gateが閉じた後にLVB-Bを別sliceとして再開する。

### URR-H: claim-aware scheme projectionの段階導入

v6がユーザ承認済みになるまで開始しない。`bc1dc55a`のclean production baseline、
§8.1〜§8.3のlanded preflight八test、URR-G一度目で確認した18-test green /
nested-red結果、§8.4の新しいcontractを起点にする。URR-F / Gのproduction実装はrollback済みなので、
URR-Hはlanded Gへ小さいpatchを足す作業ではない。H1の最初に§5.8〜§5.10を同じ意味で再構築し、
18 testが再びgreenになるcheckpointを作ってからv6 metadataへ進む。以前rollbackした実装を
設計変更なしに再試行するのではなく、v6 viewが必要とするclaim IDを同じadmissionから供給する
controlled reconstructionとして扱う。

URR-Hは一つのatomic diffにしない。H1 / H2 / H3を順に進め、各gateを満たすまで後続consumerを
切り替えない。H1のinert viewだけをlandingできるか、H2を単独landingできるかは各gateの
baseline次第であり、partial landingを事前に約束しない。

#### URR-H1: claim model再構築とinert scheme view

test-first / characterization:

1. §8.1〜§8.3の八testと既存十testを再実行し、clean baselineで既知のred / greenを保存する。
2. §8.4 test 1〜3を追加し、raw lower storage、view classification、compact / final scheme、
   claim-qualified provenance、epoch / cache assertionのどこがredかを分けて記録する。
3. five-case characterizationのpoly / check hash、formatted scheme、constraint / bound / replay /
   provenance census、wall time / peak memoryを保存する。
4. full contract corpus 287件のbaselineを保存する。H1では期待値を変更しない。

変更:

- §5.8〜§5.10のclaim-local coverage、proof-carrying lineage、initial unmatched self-taggingを
  URR-G一度目と同じsemantic contractで再構築する
- Var–Var admissionからmirror lower `BoundRecordId`をnarrow resultとして受け取り、
  同じ`UpperReplayClaimId`へlinkする
- lower-record / root reverse index、claimed-owner fast path、
  `scheme_projectable_lowers`を追加する
- projectability transition用のconstraint / owner / provenance epoch mutationを追加する
- raw / view count、unclaimed passthrough、all-covered suppression、mixed-claim yield、
  liveness transition、invalid metadata fail-openをtiming / test inspectionへ出す
- compaction、positive alias expansion、scheme witness collectionはまだraw iteratorのままにする

gate:

- §8.1〜§8.3の八testと既存十testが期待値無変更でpassする
- §8.4 test 1のraw record / all-covered view、test 2のuncovered claim set、
  test 3のliveness / epoch部分がpassする。compact / provenance consumer assertionは、
  未配線箇所を明示したままredである
- no-claim ownerではviewのrecord ID、順序、state、endpoint、weightsがraw
  `generalized_projection_lowers`と完全一致する
- root lookupは対象recordのsmall claim setだけに比例し、machine全体 / provenance graphを
  scanしない
- five-case hash / schemeと287-case contract outputがbaselineから変わらない
- claim / lower-link / reverse-index数がcanonical `(lower bound, root claim)`で説明でき、
  proof mergeやcycle回数に比例しない

H1でview consumerを一つだけ先行変更しない。inert metadataでもordinary workloadのwall time /
memoryが説明できない場合はH2へ進まない。

#### URR-H2: scheme compactionだけをviewへ切り替える

H2の前に`CompactCollector`のentrypoint ownershipを監査する。`bc1dc55a`では
`compact_type_var_for_scheme`、`compact_negative_type_var_for_scheme`、
`compact_type_var_recording_merge_constraints_for_scheme`がscheme用の名前を持つ一方、
collector constructorはgeneric entrypointと同じ`CompactCollector::new`を使う。
generalization中のreachable role predicate collectionもscheme出力へ入るが、entrypoint名だけでは
scheme modeと分からない。したがってcollectorへ
`Raw | SchemeProjection`の固定mode、または同等に明示的なscheme constructorを置き、
finalized schemeを構築する全call siteを列挙する。generic `compact_type_var`やscheme外のrole
solveを一括でclaim-awareへ変えない。exact call-site集合に不確実性が残る場合はH2を止める。

変更:

- scheme-mode collectorのpositive `compact_var_bounds` / `compact_lower_bounds`だけを
  `scheme_projectable_lowers`へ切り替える
- negative upper collection、raw-mode collector、weight composition、stack-family coexistence、
  recursive detection、`compact_pos_bound_id`自体は変更しない
- collector modeは一instanceで不変とし、local cache keyへmodeを足す必要がない構造にする
- cache-enabled generalizationでcoverage liveness transition後のrebuildを観測する

gate:

- §8.4 test 1のcompact assertionがgreenになり、covered-only `Var(β)`がsecondary compact
  variableにならない。raw recordは引き続きordinaryとして存在する
- §8.4 test 2でmixed recordを一回projectし、independent claimのrelationはcompactへ残る
- §8.4 test 3でlast-live-state transition後のcompact resultが再構築される
- §8.1〜§8.3の八test、§8の既存七regression、既存三contractが期待値無変更でpassする
- production five-case characterizationをfullで実行し、target nested relation以外のpoly /
  check hash、scheme、diagnostic、census shiftがない。target差分もraw claim/rootまで説明する
- `timeout 900s cargo run -q -p yulang -- --std-root lib contract tests/yulang/cases.toml`で
  full 287 casesを実行し、全件passする。shard一部や`cargo test -p infer`だけで代用しない
- `timeout 240s cargo test -p infer`とcache-enabled generalization testsがpassする
- ordinary no-claim workloadのcompact node / cache hit / wall time / memory差分が測定誤差を越えて
  悪化しない

H2時点ではpositive alias expansionとscheme provenanceはまだraw graphを読むため、
finalized nested gateを完了と宣言しない。nestedが偶然greenになった場合も、alias /
provenanceが同じviewを使うH3を省略しない。

#### URR-H3: alias expansionとscheme provenanceを同じviewへ揃える

変更:

- `positive_aliases_within_scheme`をH2と同じ`scheme_projectable_lowers`へ切り替える
- `capture_generalized_witnesses`も同じentryのrecord / endpoint / reasonを使う
- unclaimed entryは既存`GeneralizationParent::Bound`を保ち、claimed entryはprojectable claimだけを
  `BoundClaim` parentとして記録する
- explanation、occurrence provenance、portable exportのexhaustive consumerへclaim-qualified
  parentを追加し、raw bound auditとのlinkを保つ
- incoming budget、dedup、completeness、portable round-tripを`(bound, claim)`単位で計測する
- `finalize_generalized_compact_root`は変更しない

gate:

- §8.4 test 1でraw aliasがpositive alias cacheから再流入せず、confirmed nested leak caseの
  finalized schemeからinner familyが消える
- §8.4 test 2でmixed recordのgeneralized witnessがindependent claimだけをparentにし、
  covered claimを含まない。raw auditでは両claimを引き続き観測できる
- §8.4 test 3のliveness transitionでview、alias、provenance、cached compactが同じsnapshotを
  表す
- §8の19 contractと既存三testが期待値無変更でpassする
- production five-case characterizationをH2後にもう一度fullで実行し、nested local-var caseの
  principal narrowing以外のpoly / check hash、formatted scheme、diagnosticが変わらない
- full repository contract suite 287件をH2と同じunsharded commandで再実行し、全件passする
- constraint characterization / explanation / portable provenance suites、
  `timeout 240s cargo test -p infer`、`timeout 240s cargo test -p specialize`、
  `timeout 300s cargo test -p yulang`、`timeout 600s cargo test --workspace`がpassする
- claim-qualified provenanceがbudget drop / `IncompleteReplay`へ落ちず、ordinary
  `GeneralizationParent::Bound`の既存expectationを不要に更新しない
- repository-stdでscheme-view query、covered suppression、mixed yield、liveness invalidation、
  compact cache hit、wall time、peak memoryを説明できる

URR-H3の全gateが閉じるまでlocal-var production wiringを再開しない。full contract suiteで
target nested case以外のbaseline shiftが一件でも出たら、expectedを更新せずH2 / H3のどちらで
初めて変わったかへ戻して切り分ける。

## 10. stop / rollback conditions

### 10.1 stop conditions

次のいずれかが判明した時点でsemantic implementationを止め、design reviewへ戻す。

1. §8 test 1 / 2が現行one-shot mechanismを再現せず、late lower以外の条件が必要になる。
2. persistent stateを入れるために、既存三テストの期待値、名前、independent matching rule、
   pop-only eligibilityを変更する必要がある。
3. initial snapshotだけで完結するcaseのbounds、row item constraints、provenance parentが変わる。
4. late matched lowerがcurrent residualにもreplayされる、またはlate unmatched lowerが
   current residualへ届かない。
5. row upper到着時に一件以上のmatching lowerが存在するorder familyで、同じsemantic
   constraint集合のinsertion orderを変えると、final row shape、payload constraint、
   schemeのいずれかがまだ変わる。
6. fixのためにlowering order、local-var helper、block aggregation、generalize / instantiate、
   specialize candidate comparisonを変更する必要がある。
7. state lookupがsource-indexedにならず、lower insertionごとに全stateまたは全constraint graphを
   走査する必要がある。
8. equivalent constraint admissionごとにstate recordが増え、canonical semantic relation数では
   なくreplay回数に比例してmemoryが増える。
9. prune / subsumption後にstateがtombstoneをlive endpointとしてreplayする、またはindependent
   surviving upperのreplayを誤って抑止する。
10. late matching provenanceを完全にするために既存derivationをin-place mutationする、
    provenanceをdropする、または`IncompleteReplay`へ落とす必要がある。
11. current characterization / contract-suite baselineが、late-lower narrowingと追加provenanceで
    一件ずつ説明できる範囲を越えて動く。この場合、expected valueを実装出力へ更新せず止める。
12. currently-passing programのschemeが変わり、その変化をoriginal row、late lower、
    旧residual contaminationの四点で説明できない。
13. lower / upper replay総数が、source-local incremental actionで説明できない形で増える。
    global replay amplificationをcounter更新として受け入れない。
14. repository-std baselineで、state lookup自体が支配的になるwall-timeまたはmemory regressionが
    再現する。正しさfixをglobal scanのままlandingせずindex設計へ戻る。
15. testをgreenにするため、fixture、path、module、function名のspecial case、
    `Any` fallback、後段family cleanupが必要になる。
16. originating claimをparentとするexact `BinaryReplayDerivation`、または§5.10のinitial
    unmatched armが明示するexact reduction-route carrierなしに、endpoint equality、source
    alias、same-key mergeだけでcoverageが別claimへ伝播する。またはその誤伝播により、真に
    独立した別source / 別producerの`source <: tail`を抑止する。
17. same-key merge、subsumption、replacement / pruneのいずれかでstate-owned coverageを失い、
    matched late lowerが再びplain residualへ二重routeする。
18. claim / token setがcanonical logical relation数ではなくproof追加、equivalent admission、
    replay回数に比例して増え続ける。
19. covered / uncoveredの分類にlate-lowerごとのprovenance graph逆走査、derivation rule名、
    `FunctionReturnEffect`のspecial caseが必要になる。
20. replay lineage carrierのedgeがresult constraintまたはtarget boundの`ReplayEvidence`へ
    登録されていない、edgeの`upper`がparent claimのrecordと一致しない、または
    `IncompleteReplay`へ落ちたedgeをcovered inheritanceの証明として使う必要がある。v5のdirect
    route carrierについては、result constraintへexact `RowDerivationId`が登録されていない。
21. new constraintではlineageを保持できるが、duplicate / prefiltered duplicate、
    evidence-only / promotionのいずれかで同じexact edgeのlineageを失い、semantic queueの再実行を
    correctnessのために要求する。
22. coverage checkがcompressed root lookupで完結せずparent chainを都度歩く、parent IDがchild
    ID以降を指す、constraint cycleでlineage cycle / non-termination / depth overflowが起きる。
23. derived claim / lineage linkがcanonical `(target bound, root claim)`数ではなく、alternate
    proof、duplicate replay、semantic cycleの周回数に比例して増え続ける。
24. reduction-route self-taggingがgeneric `enqueue_row_derived_subtype` helper、matched arm、
    weighted residual、row invariant、row-item matchのいずれかへ広がり、unrelated
    row-derived claimをcoveredにする。
25. initial unmatched routeのchildが、routeを発行したreduction claim以外をparent / rootにする、
    root-selfのまま残る、またはsame canonical record上の独立direct claimを同じrootへ
    書き換える。
26. new admissionではself-tagを保持できるがduplicate admissionで失う、またはduplicateを
    coveredにするためsemantic queueの再実行、`RowDerivation` graphのpost-hoc walk、
    rule-name / endpoint-based inferenceが必要になる。
27. unweighted reductionのclaim linkageを一度も持たないlowerについて、compact node、positive
    alias、formatted scheme、generalized witness parentのいずれかが変わる。
28. compaction、positive alias expansion、scheme provenanceが別々のprojectability判定を持ち、
    同じrecord / liveness snapshotについてconsumer間でinclude / excludeが食い違う。
29. same canonical lower record上のcovered claimを除くためにindependent uncovered claimまで
    失う、またはindependent claim数だけ同じendpointをcompactへ重複投入する。
30. coverage rootがliveな間にcovered-only relationがschemeへprojectされる、またはlast live
    stateが外れた後もactive raw relationがnon-projectableのまま残る。
31. coverage livenessのempty / non-empty transition後に`ConstraintEpoch` / owner dependencyが
    更新されず、`GeneralizeCompactCache`が旧`CompactRoot`をhitする。cacheをoffにしたtestだけで
    correctnessを示す場合も同じstop conditionとする。
32. production five-case characterizationまたはfull 287-case contract suiteで、confirmed nested
    local-var narrowing以外のscheme / poly hash / check hash / diagnosticが動く。各差分を
    claim rootまで説明できても、v6 scope外ならexpected更新前に止める。
33. scheme用collectorを識別するためにgeneric `compact_type_var`、scheme外role solve、
    negative upper projectionまで一括でclaim-awareへ変える必要がある。
34. raw `projection_lowers` / `BoundRecord` / derivationを削除・書換えしないとscheme viewを
    実装できない、またはaudit queryがcovered proofを見られなくなる。
35. mixed recordのscheme provenanceをclaim-qualifiedにできず、plain
    `GeneralizationParent::Bound`からcovered derivationまでscheme parentとして展開する、
    portable exportでclaim identityをdropする、またはbudget不足をcompleteとして扱う。
36. ordinary no-claim fast pathでもboundごとのhash lookup / allocationが必須になり、
    repository-stdのwall time / peak memory / compact cache hit regressionが再現する。

### 10.2 rollback unit

- URR-Aの正しいregressionは、根因を再現する限り保持する。実装が失敗してもwrong expectationへ
  戻さない。
- URR-Bでstate modelとreplay ownershipのどちらかが成立しなければ、片方だけをlandingせず
  URR-B全体を戻す。plain residualとpersistent stateの二重ownerを残さない。
- URR-Cでlifecycleまたはprovenance gateに失敗したら、semantic routingだけを先行landingしない。
  tombstone safetyと説明可能性はsolver hot-path fixの一部である。
- URR-Dでunexplained baseline shiftが出たらcharacterization expectationを更新せず、
  原因をURR-B / Cへ戻して切り分ける。
- URR-Eでclaim identityとcoverage lifecycleのどちらかが成立しなければ、record-wide suppression
  だけをlandingしない。三つのv3 regressionは正しい期待値のまま保持し、URR-Eのsemantic
  implementation全体を戻す。
- URR-Fでclaim-local coverage、exact replay-edge lineage、compressed-root lookupのどれかが
  成立しなければ、cross-source token copyやendpoint-wide suppressionだけをlandingしない。
  §8.1 / §8.2の六regressionは正しい期待値のまま保持し、URR-Fのsemantic implementation全体を
  戻す。
- URR-Gでinitial unmatched armだけのexplicit parent admission、exact reduction-route carrier、
  unrelated row-derived controlのどれかが成立しなければ、helper-wide taggingや
  `RowDerivationRule` special caseをlandingしない。§8.3の二regressionは正しい期待値のまま保持し、
  URR-F / Gのsemantic implementationをpartialに残さない。
- URR-H1でlower-side claim link、per-claim view、liveness / epoch contractのどれかが成立しなければ、
  raw record-wide flagやendpoint suppressionを残さない。§8.4の正しいregressionは保持し、
  H1 metadata implementationを戻す。再構築したURR-F / G codeも18-test checkpointを単独で
  再現できなければ同じrollback unitへ含める。
- URR-H2のscheme collector modeまたはno-claim passthroughが成立しなければ、generic compactionへ
  filterを広げずH2 wiringを戻す。H1のinert viewはbaseline / performanceが完全no-opの場合だけ
  独立に残せる。
- URR-H3でalias expansion、claim-qualified provenance、portable explanationのどれかが
  同じviewへ揃わなければ、compactionだけをsemantic landingしない。H2 / H3のconsumer wiringを
  一つのrollback unitとして戻し、raw graphとfiltered graphが混在するreleaseを作らない。
- H2またはH3のfull five-case / 287-case gateでunexplained shiftが出たら、期待値を更新せず、
  初めてshiftしたstage全体を戻す。
- performanceだけが不合格でもglobal scanをdefault-onで残さない。source indexまたはstate keyを
  再設計し、意味論を変えるcache / early returnは入れない。

## 11. completion contract

本projectは次をすべて満たしたときだけ完了する。

1. §8の7 regressionがすべてpassする。
2. `lower F -> upper [F; ρ] -> late lower F`で、late `F`が`ρ`のlowerにならない。
3. 同じsemantic lower / upper集合が、row upper到着時に一件以上のmatching lowerが存在する
   §8 test 2の挿入順で同じfixpointになる。zero-lower / UpperFirstは§6.6を参照するknown-gap
   witnessとしてtest codeに残る。
4. late unmatched `G`はcurrent residualへ流れ、matching eligibility外のlowerも従来どおり
   residual relationを受ける。
5. partial / multi-item rowでremainingがincrementally縮み、old materializationがlive replay
   ownerとして残らない。
6. payload-bearing familyのargument invarianceがinitial / late両pathで同じ
   `RowItemMatch`規則から導かれる。
7. alias経由とpop-onlyのlate lowerがinitial snapshotと同じ規則でoriginal prefixへmatchする。
8. 既存
   `unweighted_row_upper_uses_concrete_lower_item_before_residual_tail`、
   `unweighted_row_upper_consumes_pop_only_weighted_lower_item`、
   `unweighted_row_upper_matches_each_lower_independently`
   が名前・期待値無変更でpassする。
9. persistent recordがoriginal items / tail、consumed / remaining items、current reduced-upper
   materialization、processed lower frontier、provenance headを持つ。
10. lookupはsource-indexedで、一state / 一semantic lowerのincremental matchingが高々一回である。
11. reduction-owned current upperはgeneric plain replayと二重処理されず、同じendpointにある
    independent ordinary relationのreplayは失われない。
12. replacement、equivalent dedup、subsumption、prune後もstateがstale recordを使わず、
    logical original-row relationを保持する。
13. producer constraint、initial / late contributing lower、item match、current reduced upperを
    append-only provenance chainから説明でき、`IncompleteReplay`がない。
14. initial snapshotだけで完結するcaseとweighted row reductionのsemantic resultが変わらない。
15. currently-passing programのscheme / constraint / provenance差分は、late-lower narrowingまたは
    そのaudit recordとしてcaseごとに説明されている。
16. sourceと無関係なstateのglobal scan、CST / AST再走査、path / fixture special case、
    fresh-var workaround、後段cleanupがない。
17. local-var mechanism、generalize / instantiateのlevel / quantifier / freshening、
    specialize candidate comparisonに本fix由来の変更がない。generalizeの変更はscheme-viewを
    使うpositive alias collectionとclaim-qualified provenanceに限られる。
18. targeted tests、constraint characterization / explanation suites、`cargo test -p infer`、
    `cargo test -p specialize`、`cargo test -p yulang`、workspace gateに加え、production
    five-case characterizationとfull 287-case contract suiteが通る。
19. implementation diffがpersistent unweighted reduction、bound replay / lifecycle、
    scheme-projectable bound view、scheme-mode compaction、positive alias、scheme provenance /
    cache invalidation / timing、そのtestsだけに限られ、原因と無関係なrefactorを含まない。
20. zero-lower / initial no-match sourceへspeculative / dormant recordを作らず、ordinary
    `Neg::Row` upperのshapeだけをtriggerにlazy activationしない。
21. §8.1の三regressionがpassし、同じproducer-rootのlater same-key proofはcovered、
    別producer constraintのdirect tail claimはuncoveredとして区別される。
22. nested witnessのreduced upper lifecycleが
    `Inserted -> same-key provenance/evidence merge（second dispositionなし）`としてtestで固定され、
    inner familyがresidualへ届かない。
23. insert、equivalent / evidence merge、subsumption、replacement / prune後も、claimとcoverageが
    original source、logical original row、producer identityを保ち、derived claimはtarget sourceと
    root claimの両方を区別する。
24. generic replayは未covered claimだけから計画され、covered claimとの同居を理由にcanonical
    record全体をreplayまたは抑止しない。
25. claim / token setがcanonical logical relation数でboundedになり、source-local lookup、
    replay accounting、explanation completenessを維持する。
26. §8.2の三regressionがpassし、confirmed `1670 <: 1524` shapeのcross-source claim、
    unrelated same-endpoint direct claim、multi-hop / cycleを別々のoracleで固定する。
27. proof-discovered cross-source inheritanceは、originating claim IDと、result
    `ConstraintRecordId`へ登録済みのexact `BinaryReplayDerivation`、またはtarget boundのexact
    `ReplayEvidence`で説明できる。initial unmatched routeのfirst-party inheritanceは、explicit
    reduction claim IDと、resultへ登録済みのexact `RowDerivationId`で別に説明できる。
    `UnionBranch` / `FunctionReturnEffect`はlower relationの既存structural provenanceとして残り、
    coverage用special caseにならない。
28. covered rootから別sourceへ派生したclaimは、target sourceにlocal reduction stateがなくても
    compressed root lookupでcoveredになる。一方、別sourceのdirect same-endpoint claimは
    lineageを持たずgeneric replayされる。
29. lineage parent IDはstrictly olderで、coverage rootは作成時に圧縮される。duplicate proofと
    constraint cycleは`(target BoundRecordId, root claim)`へcoalesceし、claim増殖、unbounded
    parent walk、cycle non-termination、depth overflowがない。
30. new / duplicate / prefiltered duplicate / evidence-only / promotionの全pathでlineage identityが
    同じであり、必要なedgeが`IncompleteReplay`へ落ちない。
31. §8.3の二regressionがpassし、initial unmatched routeのself-taggingと、shared helperを使う
    unrelated row-derived constraintの非coverageを別々のoracleで固定する。
32. initial unmatched routeが作るresult claimは、後続discoveryなしに作成時からreduction
    claimをparent、同じcompressed claimをroot、
    `(result ConstraintRecordId, RowDerivationId)`をcarrierとして持つ。new / duplicateの両admissionで
    このidentityを失わず、same record上のdirect claimをcoveredへ書き換えない。
33. self-taggingはinitial reduction routingのunmatched armだけに限られ、matched arm、weighted
    residual、row invariant、row-item matchへ広がらない。
34. §8.4の四contractがpassし、covered-only mirror lowerはraw ordinary recordとして残る一方、
    live root中はscheme-projectable view、compact graph、positive alias、scheme provenanceから
    除外される。
35. same canonical lowerにcovered / uncovered claimが同居するとき、endpointは一回だけprojectされ、
    semantic relationとgeneralized witness parentはuncovered claimだけを根拠にする。raw auditでは
    両claimと全derivationを引き続き観測できる。
36. coverage判定はprojection時のcompressed-root lookupであり、last live stateが外れればactive
    raw relationが再びprojectableになる。stale boolean、parent-chain walk、historical
    materializationによる永久suppressionがない。
37. projectabilityのempty / non-empty transitionは`ConstraintEpoch`、owner dependency、
    `ProvenanceEpoch`へ反映され、cache-enabled `GeneralizeCompactCache`がstale
    `CompactRoot`を再利用しない。
38. compaction、positive alias expansion、scheme provenanceが一つのview APIを共有し、
    raw `projection_lowers`はsolver replay / audit用に維持される。
39. scheme-mode collectorのcall siteが明示され、generic compaction、scheme外role solve、
    negative upper collection、finalizer freeze semanticsは変わらない。
40. claim linkageを持たないordinary lowerのrecord順、weights、compact output、alias、
    generalized witness、formatted schemeがbyte-for-byte不変であり、ordinary fast pathに
    global scanまたはper-bound allocationがない。
41. URR-Fから継続したnested characterization gateが新しい期待値への変更なしで実際にpassし、
    inner familyがouter finalizationへ漏れない。production five-caseのそれ以外のcaseとfull
    287-case contract suiteにbaseline shiftがない。

---
著者: Claude (Sol xhigh, via Codex MCP, supervised by Claude Sonnet 5)
状態: ユーザ承認済み（v6、2026-07-30）
