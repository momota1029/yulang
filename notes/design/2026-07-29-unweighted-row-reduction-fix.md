# unweighted effect-row reduction の incremental solver 修正設計

日付: 2026-07-29

状態: **未承認・ユーザレビュー待ち（v3。v2 狭域スコープは2026-07-29承認済み）**

調査基準は `c40a5cb49ab5`。根因の確定記録は
`notes/bugs/2026-07-28-local-var-effect-residual-transport-gap.md` の「25回目」を正本とする。
v1 / v2のコード行番号は同 commit の working tree に対して 2026-07-29 に再確認した。
v3で追加したコード行番号とtraceは`4ec031b3`のworking treeに対して2026-07-30に再確認した。

## 改訂履歴

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

coverageはsource、original row、producer-rootをまたいで推移させない。subsumption、
equivalent merge、evidence promotionでendpointが一致しても、producer linkageを確認せず
token setをunionしてはならない。逆に、同じstate-owned claimのproof identityだけが変わった
場合はcoverageを失ってはならない。

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
- survivorにreduction ownerが一つあれば全derivationを抑止するrecord-wide suppressionをしない。
- ownerのderivation identityと違えば常にindependentとするv2判定を延命しない。
- replay planning時にprovenance graphを逆走査してproducerを推測しない。
- subsumption / equivalent mergeでsurvivorの全claimへcoverage tokenをばらまかない。

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

## 8. 実装前に用意する7 regression tests

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

この10 testに加え、次の既存testは名前も期待値も変更せず通す。

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
16. coverage tokenが別source、別original row、別producer constraintのclaimへ伝播し、
    真に独立した`source <: tail`を抑止する。
17. same-key merge、subsumption、replacement / pruneのいずれかでstate-owned coverageを失い、
    matched late lowerが再びplain residualへ二重routeする。
18. claim / token setがcanonical logical relation数ではなくproof追加、equivalent admission、
    replay回数に比例して増え続ける。
19. covered / uncoveredの分類にlate-lowerごとのprovenance graph逆走査、derivation rule名、
    `FunctionReturnEffect`のspecial caseが必要になる。

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
17. local-var mechanism、generalize / instantiate、specializeのsemantic codeに本fix由来の変更が
    ない。
18. targeted tests、constraint characterization / explanation suites、`cargo test -p infer`、
    `cargo test -p specialize`、`cargo test -p yulang`、workspace gateが通る。
19. implementation diffがpersistent unweighted reduction、bound replay / lifecycle、
    provenance / timing、そのtestsだけに限られ、原因と無関係なrefactorを含まない。
20. zero-lower / initial no-match sourceへspeculative / dormant recordを作らず、ordinary
    `Neg::Row` upperのshapeだけをtriggerにlazy activationしない。
21. §8.1の三regressionがpassし、同じproducer-rootのlater same-key proofはcovered、
    別producer constraintのdirect tail claimはuncoveredとして区別される。
22. nested witnessのreduced upper lifecycleが
    `Inserted -> same-key provenance/evidence merge（second dispositionなし）`としてtestで固定され、
    inner familyがresidualへ届かない。
23. insert、equivalent / evidence merge、subsumption、replacement / prune後も、claimとcoverageが
    source、logical original row、producer identityを保つ。
24. generic replayは未covered claimだけから計画され、covered claimとの同居を理由にcanonical
    record全体をreplayまたは抑止しない。
25. claim / token setがcanonical logical relation数でboundedになり、source-local lookup、
    replay accounting、explanation completenessを維持する。

---
著者: Claude (Sol xhigh, via Codex MCP, supervised by Claude Sonnet 5)
状態: 未承認・ユーザレビュー待ち（v3。v2 狭域スコープは2026-07-29承認済み）
