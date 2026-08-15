# URRとlocal-var effect boundaryのclaim propagation

更新基準: 2026年7月31日、`main`の`95b95586`

文書状態: 開発者向け初稿

本書は、unweighted row reduction（URR）からscheme projectionまでをつなぐclaim propagationの現行構成を説明する。
設計の改訂履歴や試行順ではなく、現在の実装が何を表し、どこまで正しく動き、何が未解決かをまとめる。
行番号は更新基準のcommitに対するものである。

## 解決する問題

local mutable stateは、局所effect familyをhandlerの外へ漏らしてはならない。
一つの局所familyを`F(P)`、callbackに残り得るほかのeffectを`ρ`とすると、境界が表す関係は次の形になる。

```text
callback effect:       [F(P); ρ]
handled result effect: [ρ]
```

`F(P)`はcallback内のlocal ref操作が起こすeffectである。
`ρ`はhandlerが処理しない残差である。
したがって、handlerを出た結果には`F(P)`だけが残ってはならない。

問題を露出させるプログラムは、概念上、次の入れ子を持つ。
次のコードは元の再現例から関係する部分だけを残した疑似コードである。

```yu
my text_with_mock(backing, f) = {
    my $buffer = backing
    my r = ref { ... $buffer ... }
    my result = f r
    (result, $buffer)
}

my run(backing) = {
    my $store = backing
    text_with_mock $store: \&text ->
        &text = $text + " dirty"
        edit_err::abort.throw
}
```

内側の`$buffer`は`text_with_mock`の局所状態であり、外側の`run`のschemeへ現れてはならない。
境界情報が途中で失われると、`$buffer`のfamilyが外側のeffect rowへ再流入する。
元のCLI再現例では、specializeがfamilyを含む候補と含まない候補を比較し、`ConflictingTypeCandidates`を報告する。

local-var v5のcallback boundaryは、callback parameterをbody lowering中はfreshな変数のまま保つ。
private helperへの第2applicationが、後からexactなlocal ref型へ接続する。
これにより境界の型構造は作れるが、solverがその後にrowを簡約し、別のboundへ派生させる間も「どの論理関係に由来するか」を保つ必要がある。
claim propagationは、この後半を担う。

## 現在の基本モデル

現在の実装は、rawなsubtype relationと、schemeへ採用してよいrelationを分ける。
中心にある区別は次の三つである。

- **raw bound**：solverが作ったcanonicalなlowerまたはupper recordであり、監査と説明の正本として残る。
- **claim**：一つの論理関係がreplayや派生を経ても同じ由来を持つことを示すidentityである。
- **coverage**：liveなURR stateが、そのclaimのrelationをincremental routeで既に表しているという事実である。

coveredなraw boundは削除しない。
同じrelationをscheme側へ重複して持ち込まないよう、projection時だけ除外する。
最後のlive coverage stateが外れれば、activeなraw relationは再びprojectableになる。

`UpperReplayClaim`という名前にはupper-bound replayから始まった経緯が残っている。
現在のclaim IDは共通identityである。
upper replay、mirror lower、structural child、one-sided lowerのscheme projectionを一つのIDで結ぶ。
定義は`crates/infer/src/constraints/mod.rs:409-470`にある。

## 全体のデータフロー

現在の処理は次の一本の流れとして読める。

```text
source <: [F(P); ρ]
        |
        v
URR stateとroot claimを登録
        |
        +-- binary replay ------ lower側とupper側のclaimを継承
        |
        +-- structural child --- exact StructuralDerivationとclaimを継承
        |
        +-- one-sided lower ---- stable BoundRecordIdへproofをlink
        |
        v
with_legacy_projection_query（top-level traversalごとに一scope）
        |
        v
ScopedLegacyProjectionQuery::scheme_projectable_lowers_in_scope(owner)
        |
        +-- projectable supportなし ---- schemeから除外
        |
        +-- uncovered claimあり ------- endpointを一回採用
        |
        +-- independent proofあり ----- endpointを一回採用
        |
        v
compaction、positive alias expansion、generalized witness collection
```

ここでclaim propagationは新しいsubtype relationを作らない。
既存solverが作ったconstraintとboundへ、由来を表すproof qualificationを付けるだけである。

## 制約機械のclaimとcoverage

### URR stateとroot claim

対象はempty-weightの`Pos::Var <: Neg::Row`である。
既存lowerがrow prefixに一致すると、solverはpersistentな`UnweightedRowReductionRecord`を作る。
recordはoriginal itemsとtail、consumed items、remaining itemsを保持する。
現在のreduced upper、処理済みlower、provenance headも同じrecordに置く。
型と登録処理は`crates/infer/src/constraints/mod.rs:365-386`と`crates/infer/src/constraints/row_effect.rs:223-505`にある。

このstateは元の関係をplainな`source <: ρ`へ置き換えない。
元の`source <: [F(P); ρ]`を所有したまま、現在のlower集合に対するmaterializationだけを`ρ`として持つ。
後着lowerはoriginal itemsへ再照合されるため、matching `F(P)`は`ρ`へ送られず、unmatchedなeffectだけが`ρ`へ送られる。

state登録時には`UpperReplayClaimKind::Reduced`のroot claimを作り、そのrootを`live_coverage_by_root`へ登録する。
claimは`coverage_root`を作成時に保持するため、coverage queryでparent chainを歩かない。
claim tableとlive coverage indexは`crates/infer/src/constraints/mod.rs:794-810`にある。

initial unmatched routeと後着lowerのincremental routeは、reduction自身が作る副産物である。
これらはexactな`RowDerivationId`を持つ`ReductionRouteConstraint`として、元のreduction claimを明示的なparentにする。
入口は`crates/infer/src/constraints/row_effect.rs:313-340`、`crates/infer/src/constraints/row_effect.rs:510-529`、`crates/infer/src/constraints/machine/bounds.rs:1059-1084`にある。

### binary replayの両側継承

`BinaryReplayDerivation`は、replayに使ったexactなlower recordとupper recordを持つ。
現在のreplay planningは両recordからclaimを集め、各parentへ`Lower`または`Upper`のsideを付ける。
一つのsemantic replayをclaim数だけenqueueせず、一つのactionにsmall parent setを載せる。

lower側収集とupper側収集は`crates/infer/src/constraints/machine/bounds.rs:1296-1420`にある。
new、prefiltered duplicate、queue duplicate、evidence-onlyは同じmetadataを使う。
各経路がparent metadataをcanonical resultへ登録する。

`ClaimQualifiedParent::ReplayConstraint`はparent claim、side、exact replay carrierを保持する。
定義は`crates/infer/src/constraints/mod.rs:487-523`にある。
dedup keyにはresult、compressed root、sideに加えてexact `BinaryReplayDerivation`も含む。
このcarrierをkeyへ含める修正が、現在のHEAD `95b95586`である。

### structural childの継承

構造分解の共通入口は`enqueue_derived_subtype`である。
function、tuple、constructor、record、variant、union、intersection、rowがこの入口を使う。
入口は親constraintのclaim-qualified parentsを読む。
exactな`StructuralDerivation { parent, rule }`とともにchildへ移す。
row familyや`MarkerAggregateToUpperTail`だけの特別扱いではない。

new child、canonical duplicate、secondary derivationは同じmerge処理を使う。
実装は`crates/infer/src/constraints/machine/entry.rs:1253-1390`にある。
row aggregateがone-sided lowerへ到達する実際の分解は`crates/infer/src/constraints/machine/propagate.rs:708-795`にある。

### one-sided lowerとproof ledger

`Pos::Row(...) <: Neg::Var(target)`のようなconstraintはlower boundだけを作る。
mirror upperを作らないため、Var–Var専用hookだけではclaimをlower recordへ結べない。

現在の`add_lower_bound`はcanonical insertion後のstable `BoundRecordId`を内部で得る。
producer constraintにclaim-qualified parentがあれば、そのrecordへclaim supportをlinkする。
同じrecordへ独立derivationが合流した場合は、そのexact carrierもindependent supportとして記録する。
入口は`crates/infer/src/constraints/machine/bounds.rs:418-548`と`crates/infer/src/constraints/machine/bounds.rs:832-1001`にある。

claimが触れたlower recordだけに`SchemeProjectionProof` ledgerを遅延構築する。
supportは`Claimed(UpperReplayClaimId)`と`Independent(ProjectionProofCarrier)`に分かれる。
型は`crates/infer/src/constraints/mod.rs:541-588`、ledger更新は同ファイル`1226-1321`にある。

この分離により、同じcanonical lowerにcovered proofとindependent proofが同居できる。
covered proofだけならschemeから除外する。
independent proofまたはuncovered claimが一つでもあれば、endpointを一回だけprojectする。

## scheme projectionの共有判定

`ScopedLegacyProjectionQuery::scheme_projectable_lowers_in_scope`は共有classification APIである。
schemeへ入れるpositive lower relationは、このscoped facadeだけが決める。callerはtop-level traversal全体を
一回の`ConstraintMachine::with_legacy_projection_query`で包み、同じscope-local evaluation roundを再帰全体で
共有する。scope外へ出せるのはwitness draftやcompact rootなどのowned resultだけであり、machineのraw read
authorityやevaluator memoは出せない。実装は
`crates/infer/src/constraints/structural_kernel/access.rs`の`ScopedLegacyProjectionQuery`にある。

判定は次の通りである。

| recordの状態 | projection結果 |
| --- | --- |
| claim ledgerがない | `Unclaimed`としてraw順序のまま採用 |
| covered claimだけがある | 採用しない |
| live coverageのないclaimがある | `Qualified`として一回採用 |
| independent supportがある | `Qualified`として一回採用 |
| claim metadataが壊れている | typed `ProofFailure`としてscopeをdenyし、gatewayがattempt-terminal latchへ記録 |

`Qualified`は、projectableな`uncovered_claims`と`independent_supports`だけを返す。
raw `BoundRecord`と全derivationは消さない。
scheme provenanceがcovered siblingを再展開しないための境界がここにある。

deny時にwitness/compactionが返すempty/`Incomplete`/`CompactRoot::default()`はattempt-local poisonであり、
型意味上のfallbackではない。proof-semantic failureはgateway内でterminal latchへ先に記録され、checked compiler
boundaryとhover/completion/member-completionのfinal-output gateがそのattemptの結果を破棄する。

coverageはquery時にcompressed rootから`live_coverage_by_root`を引いて判定する。
emptyとnon-emptyをまたぐliveness transitionはepoch mutationである。
record inclusionの変化も、constraint epoch、owner epoch、dependency、provenance epochへpublishする。
したがって`GeneralizeCompactCache`は古いprojectabilityで作ったcompact rootを再利用しない。

## H1、H2、H3の現在の役割

H1、H2、H3は現在の三つの実装層を指す名前として読める。
改訂順を覚える必要はない。

| 層 | 現在の責務 | 主な入口 |
| --- | --- | --- |
| H1 | claim identity、compressed root、live coverage、replay lineage、initial unmatched self-tag、mirror lower link | `constraints/mod.rs`、`row_effect.rs`、`machine/bounds.rs` |
| H2 | 四つのscheme用compaction surfaceを同じscoped claim-aware viewへ接続 | `compact/surface.rs`、`compact/collect/` |
| H3 | positive alias expansionとgeneralized witness collectionを同じviewへ接続 | `generalize/mod.rs:543-577`、`generalize/provenance.rs:174-225` |

H2の`CompactCollector`は`Raw`と`SchemeProjection`のmodeをinstanceごとに固定する。
positive root、negative root、merge-constraint recording、reachable role-constraint recordingの四つのscheme用
entrypointだけが`new_for_scheme`または`new_recording_for_scheme`を一つのHRTB scope内で使う。negative upper
collectionを含む再帰的なshape/bounds readも同じscopeのowned getterを通る。scheme外のgeneric compactionは
`Raw` modeのままである。entrypointは`crates/infer/src/compact/surface.rs`にある。

H3のalias expansionとwitness captureはそれぞれtop-level traversalを一scopeで包み、
`scheme_projectable_lowers_in_scope`から得たprojectable relationだけを推移的にたどる。
generalized witness collectionは`Unclaimed`を従来の`Bound` parentとして扱う。
`Qualified`はclaimを`BoundClaim`、independent supportを`BoundProjectionProof`として保存する。
これらのparentはraw mixed record全体ではなく、選ばれたexact carrierだけへ解決される。
型と解決処理は`crates/infer/src/constraints/mod.rs:1737-1864`にある。

## DCP-AからDCP-Dの現在の役割

derived claim propagation（DCP）は、H1が作ったidentityを下流のderived boundへ運ぶ。
現在のHEADにはDCP-AからDCP-Dと、その後に見つかったexact-carrier修正2件が入っている。

| slice | 現在の内容 | 状態 |
| --- | --- | --- |
| DCP-A | replay、structural child、one-sided lower、mixed proof、duplicateのcontractを固定 | 完了 |
| DCP-B | binary replayのlower側とupper側からside付きparentを継承 | 完了 |
| DCP-C | 全structural derivationへ共通のclaim propagationを追加 | 完了 |
| DCP-D | stable one-sided lower linkageとmixed proof ledgerを追加 | 完了 |
| DCP-E | motivating integrationとbroader closeout | 未完了 |

追加の2修正も現在のarchitectureに含まれる。
`86071060`はincremental row routeへexact `ReductionRouteConstraint`を登録した。
`95b95586`はreplay parentのdedup keyへexact carrierを加えた。
どちらも新しいsubtype ruleを足さず、既存proofをclaim qualificationへ正確に対応づけた。

## 確認済みの範囲

ordinary type inferenceへの影響は、最終出力と内部contractを分けて確認している。
現在までの根拠は次の通りである。

| 検証 | 確認できたこと | 適用範囲 |
| --- | --- | --- |
| five-case characterization | DCP-D後も5ケースすべてでpoly dump hashとcheck report hashが不変 | DCP-D final gate時点 |
| DCP constraint contracts | 最新2修正後も`case_02`は63 pass、1 known-ignore | 現行HEAD |
| 287-case contract suite | H1とH2で287/287、H3完了baselineでも安全を確認 | H3完了baseline |
| specialize suite | 163 pass | H3 completion gate時点 |
| yulang suite | 376 pass、既知flaky 1件は単独再実行でpass | H3 completion gate時点 |

five-caseでは、DCP-Dにより2つのlocal-ref fixtureでcanonical constraintとordinary lowerが各3件増えた。
replay accountingは生成、accept、duplicateの合計まで閉じ、全5ケースの最終polyとcheck hashは変わらなかった。
これら5 workloadの推論結果は変わっていない。
内部差分は、claim-covered one-sided lowerを正しい段階で除外した結果と整合する。

ただし、287-case、specialize、yulangの表にあるbroader runはDCP-AからDCP-D後の再実行ではない。
DCP-D後の2つのexact-carrier修正についても、five-caseは再実行していない。
DCP-D後の287-caseとfull infer、specialize、yulang gateは、motivating testが未解決のためDCP-Eへ残っている。
したがって、現行HEADをproject完了またはfull regression完了とは扱わない。

287-case内の元のCLI再現例はknown-gap expectationとして固定されている。
287/287はordinary contractの非回帰を示すが、motivating bugの解決を示す値ではない。

H2の10 covered recordは、5個の標準ライブラリーdefinitionまでrecord単位で追跡済みである。
DCP-D後に増えた各3 recordは、accounting closureとhash不変までは確認済みだが、各recordをclaimへ一対一に対応づける検証は未完了である。
これは安全性の反証ではないが、残る検証上のriskである。

## 現在も未解決の点

motivating integration test
`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`
は、現行HEADでも失敗する。
parsed側のouter schemeはinner familyを含まない。
hand-built側は次のeffect rowを残す。

```text
["&buffer#36:0"('a & 'b), std::control::var::observe('b | 'a)]
```

最新のtraceでは、最初のcovered aliasと、そこから先のexact replay carrier欠落は修正済みである。
inner rowのcanonical lower `BoundRecordId(10439)`では`independent_supports`も空になった。
それでもrecordはprojectableであり、理由は9個のuncovered claimである。

一回のtraceで観測したrootは次の通りである。
これらの数値は診断用のarena IDであり、実装条件やtest oracleではない。

```text
22202 22308 22206 22217 22208 22222 22226 22251 22229
```

9個はいずれもlive coverageを持たず、元のcovered reduction root `36823`とも異なる。
現在の`scheme_projectable_lowers_in_scope`はper-proof contractどおり、このuncovered supportがあるendpointを残す。
したがって、projectionをさらに強く抑止することは修正にならない。
独立relationを消し、現在のmixed-proof safetyを壊すためである。

残る問いは、9個のrootの意味上の由来である。
少なくとも二つの可能性をまだ区別できていない。

1. 9個のclaimは元のreductionから正当に派生しており、まだ見つかっていないexact carrierに沿って`36823`へ圧縮すべきである。
2. 9個は上流で誤って独立proofとして生成されており、その生成規則を原因側で直すべきである。

次の調査候補も二つ残っている。
`enqueue_row_derived_subtype`のgeneric経路には未確認点がある。
weighted residualまたはrow-item-matchがclaim-qualified parentから作られる場合の契約である。
evidence-only replayのpromotionにも未確認点がある。
ordinary lowerへのpromotion後、`ReplayEvidence`がindependent supportへ再分類されないかはproduction traceで未確認である。
どちらも仮説であり、残る9rootの原因だとはまだ確定していない。

現在の完了境界は明確である。
DCP-AからDCP-Dとexact-carrier修正は着地済みだが、DCP-Eと元のlocal-var motivating failureは未完了である。

## 詳細な経緯と設計判断

本書は現行構成を一度で把握するための入口であり、改訂履歴と不採用案は繰り返さない。
判断の理由や通らなかった方向が必要な場合は、次の文書を参照する。

- [local mutable stateのeffect boundary修正設計](../design/2026-07-28-local-var-effect-boundary-fix.md)：local-var v5 lifecycle、private helper、deferred concrete-ref connectionを扱う。
- [unweighted effect-row reductionのincremental solver修正設計](../design/2026-07-29-unweighted-row-reduction-fix.md)：URR v1～v6、persistent state、claim、H1～H3の設計判断を扱う。
- [derived structural boundのclaim propagation修正設計](../design/2026-07-30-derived-row-claim-propagation-gap.md)：DCP-A～E、両側replay、structural propagation、mixed proof ledgerを扱う。
- [local mutable stateのeffect residual調査記録](../bugs/2026-07-28-local-var-effect-residual-transport-gap.md)：全trace、各停止点、arena IDを含む時系列の調査記録である。

「なぜこの案になったか」や「どの代案が反証されたか」は設計文書とbug noteにある。
「今のコードをどう読むか」は、本書を現行状態に合わせて更新する。
