# CPK 追補: replay routing decision・exact parent・failure・performance 契約

日付: 2026-08-06

状態: **ユーザ承認済み（2026-08-06、リカバリ可能なcheckpointとして承認）**

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定

**署名についての注記**: Fable 5 が一時的に利用できないため、`CLAUDE.md`
「Fable 5 不在時の起案担当」に従い、本書は Codex `gpt-5.6-sol`（xhigh）が
本文を起案した。Claude (Sonnet 5) は、現行code・既存正本文書との照合
（独立したgpt-5.6-terraによるfact-checkで見つかった4件の記述精度も修正済み）、
invariant / stop condition の査読を行った。

**承認の性質についての注記**: 計画全体の複雑さを踏まえ、ユーザは本書を
「一度承認し、問題が見つかればcommit単位でrevertして再設計する」という
リカバリ可能なcheckpointとして承認した（2026-08-06）。これは個々の設計判断を
逐一精査した上での承認ではなく、CPK-0以降このセッションで確立された設計路線
（承認済み文書群・shadow-first検証規律・stop-and-report習慣）への信頼に基づく
承認である。実装側は、本書§10のスライス規律（Slice A〜E、各段階でshadow parity
green後にのみ次へ進む）と§13のstop conditionsを、通常以上に厳格に守ることで
この承認の性質に応える。

本書は
`notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md`
（以下 CPK 計画）§10.1 / CPK-7 の `prepare_replay_route` / `ReplayRouting` sketchを、
production authorityへ切り替え可能なcontractへ補完する追補である。また、
`notes/design/2026-08-02-replay-claim-parent-factorization.md`
（以下 RCPF 文書）のexact parent relation・representative・canonical entry order、
`notes/design/2026-08-05-cpk-0-projection-admission-addendum.md`
（以下 CPK-0 追補）のcomplete pre-event / whole-attempt規律、
`notes/design/2026-08-06-cpk-projection-decision-addendum.md`
（以下 projection decision追補）のtyped `ProofFailure` / clean retry規律を、
replay routing queryへ具体化する。

本書が正式に決定するのはCPK-7のreplay-routing decision cutoverだけである。
CPK-8のlegacy proof machinery removal、CPK-9のcloseout/performance gateは対象外とする。

## 0. 本書が下す決定の要約

1. `prepare_replay_route`はCPK計画§10.1どおり
   `Result<PreparedReplayRoute, ProofFailure>`を返す。missing/dangling/incompleteな
   mandatory routing factを`Generic`へfail-openしない。
2. `PreparedReplayRoute`は3-way routing summaryと、generic pairおよび各incremental
   routeへ渡すexact parent payloadを一体でpreflightする。coreはclaim/root/lineageを
   解釈せず、typed routingとopaque prepared workだけを消費する。
3. 一つのprepared parentは`side`、canonical `coverage_root`、exact
   `representative_claim`、typed `lineage`を保持する。`representative_claim`が
   replay parent relationにおけるexact claim IDであり、loser claimやraw admission
   permutationはidentityへ含めない。
4. parent sequenceはlower sideを先、upper sideを後とする。各side内は
   `coverage_root`昇順、次に`representative_claim`昇順とする。これはRCPF §6.3/6.4の
   canonical parent-set orderを再利用する。incremental semantic route自体の順序は
   current input orderを維持し、parent orderで並べ替えない。
5. `Generic`はgeneric pair replayが必要、`IncrementalOnly`はgeneric reasonがなく
   incremental routeまたはcovered-parent attachment workだけが必要、
   `SkipAlreadyCovered`はそのpairに実行すべきreplay workがないことを表す。
6. no upper claimは現行どおり正当な`Generic`である。coverage state entryがないことも
   正当なuncoveredでありfailureではない。一方、claimが指すcoverage root claim自体の
   欠落、dangling incremental claim、parent identityの再構成不能は`ProofFailure`とする。
7. queryは全`upper_claims`または全`live_coverage`をpairごとに走査しない。
   upper-record claim index、claim-ID occurrence index、coverage-root live index、
   lower-record claimed-parent indexをwriterと同じtransactionで維持する。
8. complexityはexpected `O(1)`または`O(log N)` lookupに、当該pairが実際に返す
   parent数と当該upper向けincremental route数を加えたものとする。global store sizeに
   比例するper-pair scan、全量sort、全量cloneを禁止する。
9. CPK-5の現行shadow oracleはcutover gateとして不十分である。mirror mismatch時の
   early returnを禁止し、routing、pair/incremental work、exact claim/root/side/lineage、
   canonical sequence、input/generated/accepted/disposition、worklist traceを比較する。
10. routing failureはprojection failureと同じmachine-local sticky terminal failureへ
    接続する。ただしroutingはsolver hot loop内にあるため、一natural bound eventの
    全pair/routeを先にpreflightし、一件でもfailureならそのeventのreplay actionを
    一件も実行しない。
11. bound insertion以前のsemantic workまでlocal rollbackしない。machine/attempt全体を
    discardし、新しいmachineを`LegacyRollback(first_failure)`に固定してsourceから
    clean retryする。同じmachineまたは同じworklistの途中からretryしない。
12. 本書はquery core、index、strengthened oracle、authority cutoverを別sliceにする。
    oracleがgreenになるまでproduction routing authorityを切り替えない。

## 1. 背景と対象範囲

### 1.1 CPK §10.1に残っていた未決定

CPK計画§10.1は次の骨格を定めていた。

```rust
fn prepare_replay_route(
    &self,
    lower: BoundRecordId,
    upper: BoundRecordId,
    incremental_routes: &[IncrementalRouteKey],
) -> Result<PreparedReplayRoute, ProofFailure>;

struct PreparedReplayRoute {
    routing: ReplayRouting,
    proof_event: PreparedReplayParents,
}

enum ReplayRouting {
    Generic,
    IncrementalOnly,
    SkipAlreadyCovered,
}
```

一方、以下は未定義だった。

- `PreparedReplayParents`のexact type shape
- exact claim / root / side / lineageのidentityとcanonical sequence
- generic pairとincremental routeのparent payloadの分離
- routing-specific missing/dangling/canonicality failure
- queryがsolver loop中に失敗した場合のevent boundary
- production indexとper-pair complexity
- CPK-5 shadow oracleのexact cutover gate

CPK-5/CPK-6aでproduction compileされた現行queryは、3-way enumのshadow parityだけを
目的とする暫定実装である。`PreparedReplayRoute`を直接返し、parentをrootの
`FxHashSet`へ縮約し、claim lookup失敗を`filter_map`で消す。また、upper recordごとの
indexを使わず全`upper_claims`をqueryごとに走査し、coverage判定もindexなしの
`live_coverage.iter().any(...)`で行う。後者はmatch時にshort-circuitするが、各claimに
ついてworst-caseで`live_coverage`全体を線形走査する。この暫定shapeをproduction
contractとしない。

### 1.2 Replay routingがsemantic serviceである理由

`lower_bound_replay_actions` / `upper_bound_replay_actions`はproof stateを読んで、
次を決める。

- opposite frontierのどのlower/upper pairをreplayするか
- generic replayがincremental reduction routeを包含するか
- covered claimをincremental route側へ委ねるか、pair replayでparent attachmentするか
- worklistへ入るinput/generated/accepted workの件数

したがってroutingはdiagnostic metadata queryではない。誤った`SkipAlreadyCovered`は
必要なsemantic workを失い得る。誤った`Generic`は不要なwork、duplicate/evidence、
queue順およびterminationを変え得る。CPK計画§5.2 / CPK-7どおり、CPK-7は
semantic queueを変え得る唯一のauthority cutoverとして単独で扱う。

### 1.3 対象call path

本書は次のLegacy readを一つのtyped queryへ置き換える。

1. `lower_bound_replay_actions`
2. `upper_bound_replay_actions`
3. `upper_record_requires_generic_replay`
4. `uncovered_upper_replay_claim_parents`
5. `covered_claims`
6. incremental routeによるcovered claim除外
7. `lower_record_replay_claim_parents`

`push_replay_constraint_or_prefilter`以降のsemantic admission、canonical duplicate、
trivial、evidence-only、row/reduction mergeの意味は変更しない。

### 1.4 Non-goal

本書は以下を変更しない。

- subtype rule、bound identity、canonical constraint identity
- semantic lower/upper frontier order
- incremental row routeの生成規則または順序
- replay carrierの`pivot/lower/upper/rule`
- replay admission disposition
- parent first-winner / representative選択規則
- projection OR/AND、generalization、SCC、simplifier
- CPK-8のlegacy store/adapter削除
- CPK-9の最終performance acceptance threshold

## 2. Legacy routingのcurrent ground truth

本節の記述はHEAD `908de50d`付近を基準とする。行番号は移動し得るため、実装時には
関数名とdata flowも再確認する。

### 2.1 New lower event

`ConstraintMachine::add_lower_bound`はsemantic lower insertion後、同じownerの
incremental row-reduction routesを列挙し、`lower_bound_replay_actions`を呼ぶ。

`lower_bound_replay_actions`は同じownerのupper recordsをsemantic frontier orderで
列挙する。各upper pairについて:

1. upper recordにclaimがない、または一つでもuncovered rootがあれば
   `requires_generic = true`。
2. upper parentはuncovered claimを全て含む。
3. lower endpointが`Pos::Var`なら、covered claimのうち同じupper/claimを扱う
   incremental routeがないものもupper parentへ含む。
4. `should_replay = requires_generic || !upper_parents.is_empty()`。
5. lower parentはlower recordのcanonical claimed projection relation全体。
6. `should_replay`のpairだけをfrontier順でgeneric pair admissionへ渡す。

その後、incremental routesをinput orderで処理する。対応upperでgeneric replayが
必要なら、そのincremental semantic actionをskipする。そうでなければ
`(route.upper, BinaryReplayDerivation)`のfirst-seen exact keyでdedupし、lower parentsと
route固有のoptional upper claimを付けてadmitする。

### 2.2 New upper event

`upper_bound_replay_actions`はnew upper recordのclaim coverageを一度評価する。

- no claimまたは一つでもuncoveredなら、同ownerの全active projection lowerを
  semantic frontier orderでreplayする。
- 全claimがcoveredなら、generic replay inputはゼロである。
- generic caseの各pair parentはlower recordのcanonical claimed relationを先、
  upper recordのuncovered claimsを後に連結する。

new upper eventには同時入力のincremental route listがないため、3-way summaryは
`Generic`または`SkipAlreadyCovered`だけになる。`IncrementalOnly`はnew lower event側の
pair/incremental workで使う。

### 2.3 Current parent identity

Legacy actionへ渡る`SideTaggedReplayClaim`はexact claim IDとLower/Upper sideを持つ。
このclaim IDはcanonical parent relationから選ばれた、そのrelationのwriter-fixedな
representative claim IDそのものである。別の`current representative` fieldをlookupする
段階はない。このIDが指すclaim occurrenceから次を一意に得る。

- canonical coverage root
- five-source lineage
- current upper record

RCPFのpersistent parent-set意味は

```text
(side, coverage_root) -> representative_claim
```

であり、各rootのwinnerはwriter/admission streamで確定済みである。queryはwinnerを
再選択しない。RCPF canonical materializerと§4.2の新しいprepared queryは、この
writer-fixedなfinite-map identityをcanonical sequenceとしてmaterializeする。現行の
direct assembly / snapshot recordingが常にそのcanonical sequenceを出すとは限らない。

### 2.4 Current ordering

現行Legacyのdirect replay parent assemblyは次の順である。

1. lower side parents
2. upper side parents

lower-side relationはwriterが維持するrelation順で読む。upper-side relationはまず
`uncovered_claims`を入れ、lower endpointが`Pos::Var`なら、incremental routeで既処理で
ないcovered claimsをその後ろへappendする。各subsequenceは入力relationの順を保つが、
uncovered/coveredが混在する全体についてcoverage-root昇順を保証しない。
`record_replay_parent_snapshot`も渡されたparentの入力順にpushし、ここではsortしない。
したがって、現行Legacy direct assemblyと現行CPK snapshot recordingの順序は
input/assembly orderであり、次のRCPF canonical materialization orderと同一とは限らない。

一方、各sideのlogical parent-setはRCPF §6.3のunordered finite mapである。RCPF §6.4の
deterministic materialization targetは次のcanonical orderであり、§4.2の新しい
prepared-parent contractはこの順序を採用する。

```text
coverage_root ascending
then representative_claim ascending
```

coverage rootはside内uniqueであり、第二keyはtotal orderのtie ruleである。
raw Legacy flat Vecのhistorical permutation、direct assembly順、HashMap iteration、
admission ordinalは新APIの順序にしない。これは新contractでcanonical materializationを
明示するものであり、現行Legacyがすでに常にこの順でassemblyしているという記述ではない。

incremental route sequenceはparent relationではなくsemantic action sequenceである。
現行input orderとfirst-seen dedupを維持し、coverage-root orderでroute自体をsortしない。

## 3. APIとdata model

### 3.1 Exact parent shape

CPK-7 prerequisite実装では次をproduction-compiled typeとする。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct PreparedReplayParent {
    pub(crate) side: ReplayClaimParentSide,
    pub(crate) coverage_root: UpperReplayClaimId,
    pub(crate) representative_claim: UpperReplayClaimId,
    pub(crate) lineage: ProjectionLineage,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) enum PreparedReplayParentBlock {
    #[default]
    Empty,
    Shared(Arc<[PreparedReplayParent]>),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct PreparedReplayParentSet {
    pub(crate) lower: PreparedReplayParentBlock,
    pub(crate) upper: PreparedReplayParentBlock,
}
```

`representative_claim`が、現行`SideTaggedReplayClaim::claim`へlosslessに戻せるexact
claim IDである。別のraw claim ID fieldは持たない。同じrootへ到着したloser claimは
logical parent-setのmemberではなく、admission history側のoccurrenceで保持する。

`lineage`はclaimから再lookup可能でもpayloadに保持する。CPK invariant 7どおり、
shapeからlineageを逆推定せず、prepare時にexact claim occurrenceと照合する。

`PreparedReplayParentBlock::Shared`は、一natural eventで同じlowerまたはupper parent
snapshotを多数のpair/routeが使う場合にentry storageを共有する。`Arc` cloneはblock
identityのO(1)共有であり、entry列をcopyしない。`Empty`はallocationなしのsentinelで
ある。backendが同じownership/lifetime/complexityを持つarena IDへ機械的に置き換わる
ことは許すが、owned `Vec`をpairごとに複製するshapeへ弱めてはならない。

`PreparedReplayParentSet`のlogical iteratorは`lower` block全体を先、`upper` block
全体を後に列挙する。各entryにもsideを保持し、block fieldとentry sideの不一致を
typed invariant failureとして検出する。

### 3.2 Pairとincremental route payload

一つのquery resultはgeneric/pair workとincremental workを区別する。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct IncrementalRouteKey {
    pub(crate) upper: NegId,
    pub(crate) upper_record: BoundRecordId,
    pub(crate) provenance: RowDerivationId,
    pub(crate) claim: Option<UpperReplayClaimId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PreparedIncrementalReplay {
    pub(crate) route: IncrementalRouteKey,
    pub(crate) parents: PreparedReplayParentSet,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct PreparedReplayParents {
    pub(crate) pair_replay: Option<PreparedReplayParentSet>,
    pub(crate) incremental_replays: Vec<PreparedIncrementalReplay>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PreparedReplayRoute {
    pub(crate) routing: ReplayRouting,
    pub(crate) proof_event: PreparedReplayParents,
}
```

既存`UnweightedRowReductionReplayRoute`を`IncrementalRouteKey`の実装型として再利用して
よい。名前を合わせる機械的変更は許すが、`upper/upper_record/provenance/claim`の
どれも落としてはならない。

`pair_replay`はLegacyの`should_replay`に対応する。両blockが`Empty`の
`Some(PreparedReplayParentSet::default())`は親なしgeneric pair replayを表す有効な
値であり、`None`と区別する。

`incremental_replays`はgeneric replayに包含されず実行されるrouteだけを、current
input order / first-seen exact-key orderで保持する。各routeのparent setはlower side
parentsを先に持ち、`route.claim`がある場合はそのexact upper parentを後に一件持つ。

### 3.3 Routing/payload consistency

3-way summaryとprepared workの整合性を次に固定する。

| routing | `pair_replay` | `incremental_replays` | 意味 |
| --- | --- | --- | --- |
| `Generic` | `Some` | empty | upperのgeneric reasonによりpair replayを実行し、同じupperのincremental semantic actionを包含する |
| `IncrementalOnly` | `Some`または`None` | non-empty、または`pair_replay = Some` | generic reasonはないが、incremental routeまたはcovered-parent attachment pairが必要 |
| `SkipAlreadyCovered` | `None` | empty | このlower/upper pairに実行すべきreplay workがない |

`Generic`の`pair_replay`はlower parentsに加え、uncovered upper parentsと、variable
lowerでincremental routeが扱わないcovered upper parentsを含む。

`IncrementalOnly`の`pair_replay = Some`は、全upper rootsがcoveredでも、variable
lowerへ未処理covered parentをattachmentするためLegacyがpair replay admissionを
実行する場合に使う。このworkを「semantic changeがないはず」と推測してqueryから
消してはならない。実際のcanonical duplicate/trivial/evidence/new-semantic dispositionは
既存admission layerが決める。

`routing`とpayloadがこの表に一致しないstore/query resultは
`ReplayRoutingInvariantViolation::RoutingPayloadMismatch`とする。

### 3.4 Core adapter boundary

coreは`ReplayRouting`でcontrol flowを選び、prepared pair/incremental descriptorを
既存replay admissionへ渡す。coreは次を行わない。

- claim IDからcoverage rootを再lookupする
- covered/uncoveredを再判定する
- parent winnerを再選択する
- sideまたはlineageをshapeから推測する
- CPK storageをquery以外から読む

`PreparedReplayParentSet`から現行`ReplayClaimParents`への移行adapterは、
`representative_claim -> claim`、`side -> parent_side`の一対一変換だけを行う。
adapterがcoverage、dedup、sort、fallbackを行ってはならない。

### 3.5 Query signatureとevent-local route index

CPK計画§10.1のfallible shapeを維持する。

```rust
pub(crate) fn prepare_replay_route(
    &self,
    view: &impl SemanticFactView,
    lower: BoundRecordId,
    upper: BoundRecordId,
    incremental_routes: &[IncrementalRouteKey],
) -> Result<PreparedReplayRoute, ProofFailure>;
```

`lower_is_var`をcaller-supplied boolとして受け取らない。同じ`SemanticFactView`のlower
endpointからderiveし、callerとの不一致余地をなくす。

new lower eventが持つ全incremental routesは、一度だけevent-localに
`upper_record -> input-order route slice`へgroupする。各pair queryへ渡すsliceは
全entryが引数`upper`に属することをpreflightする。全route vectorをupper pairごとに
再scanしてはならない。groupingはroute sequenceをsortせず、current input orderを保つ。

実装上、event-local groupingを`ReplayRoutingPreparationRound`等の型へ分けてもよい。
これはmachine/cacheへ永続化せず、一natural bound eventのprepare終了時に破棄する。

## 4. Canonical identity・ordering・dedup

### 4.1 Parent identity

logical parent keyは次である。

```text
(side, coverage_root) -> (representative_claim, lineage)
```

同じside/rootは一件だけである。lowerとupperに同じrootが現れることはsideが異なるため
有効である。異なるsideをdedupしてはならない。

`lineage`はwinner claimのtyped lineageと一致しなければならない。同じrootのloser
lineageをwinnerへ付け替えない。

### 4.2 Canonical parent sequence

一つの`PreparedReplayParentSet`は次のfull total orderを持つ。

1. `ReplayClaimParentSide::Lower`
2. `ReplayClaimParentSide::Upper`
3. 同一side内で`coverage_root`昇順
4. tie ruleとして`representative_claim`昇順

side/rootがuniqueであるためlineageをsort keyにしない。ただしexact equalityでは
lineageも比較する。

writer/indexはcanonical orderをincrementally維持する。query時にHashMap/FxHashSetを
列挙してから全量sortしてはならない。非canonical indexをread-time sortでrepairせず、
typed failureにする。

### 4.3 Incremental route order

incremental routeのorderはsemantic queue orderであり、parent-set canonical orderとは
別契約である。

- input route orderを維持する。
- current `(route.upper, BinaryReplayDerivation)` first-seen dedupを維持する。
- `FxHashSet` iteration orderをresult sequenceにしない。
- root/claim/provenance IDでrouteを並べ替えない。

permutation oracleはparent relationのcanonical invarianceと、semantic route input orderの
preservationを別々に比較する。

### 4.4 Representative update

same-root representativeはwriter boundaryで確定する。queryはcurrent canonical winnerを
読むだけで、claim IDの大小、arrival ordinal、lineage priorityから再選択しない。

upper-record claim indexとlower-record claimed-parent indexが同じrootについて異なる
winnerを正当に持つ場合、それぞれのrelationのwriter-fixed winnerを使う。異なるrelationを
一つのglobal winnerへ強制しない。ただし一つのprepared parent entry内部で
`representative_claim.coverage_root != coverage_root`ならfailureである。

## 5. Routing decision table

`prepare_replay_route`はsemantic target、internal index closure、claim/root identity、
incremental route identity、canonical orderをpreflightしてからroutingとpayloadを返す。

| 状態 | decision | 理由 |
| --- | --- | --- |
| lower recordがsemantic viewに存在しない | `Err(MissingSemanticFact)` | dangling caller/store ID |
| upper recordがsemantic viewに存在しない | `Err(MissingSemanticFact)` | dangling caller/store ID |
| lowerがactive lowerでない | `Err(InvalidReplayRouteTarget::LowerDirectionOrState)` | query domain外 |
| upperがactive upperでない | `Err(InvalidReplayRouteTarget::UpperDirectionOrState)` | query domain外 |
| lower/upper ownerが一致しない | `Err(InvalidReplayRouteTarget::OwnerMismatch)` | opposite frontier pairではない |
| CPK claim indexがrecord occurrenceと内部不整合 | `Err(MissingProofFact)`または`ReplayRoutingInvariantViolation::ClaimIndexMismatch` | partial mirrorをno-claimへ見せない |
| active upperにclaimが正当に一件もない | `Ok(Generic)` | current Legacyと同じno-claim generic replay |
| upper claim IDがclaim occurrenceに存在しない | `Err(DanglingProofReference)` | coverage/lineage/representativeを再構成不能 |
| claimのcoverage root claim occurrenceが存在しない | `Err(DanglingProofReference)` | root identity欠損 |
| coverage rootのlive-state entryが存在しない | uncoveredとして扱う | absenceは正当なnot-live state |
| coverage rootのlive-state setが空 | uncoveredとして扱う | current Legacyと同じ |
| coverage rootにlive-stateが一件以上ある | coveredとして扱う | current Legacyと同じ |
| 一つでもuncovered upper rootがある | `Ok(Generic)` | generic pair replayが必要 |
| all upper roots covered、incremental routeあり | `Ok(IncrementalOnly)` | genericをskipしincremental routeを実行 |
| all upper roots covered、unhandled covered parentあり | `Ok(IncrementalOnly)` | attachment pair replayを保持 |
| all upper roots covered、pair/incremental workなし | `Ok(SkipAlreadyCovered)` | exact no-work |
| lower projection claimed parent entryがない/空 | lower parent set emptyとして続行 | raw lower relationは有効 |
| lower projection claimed supportが存在しclaim occurrenceがない | `Err(DanglingProofReference)` | exact lower parentを再構成不能 |
| incremental routeの`claim = None` | valid routeとして続行 | routeにupper parentがない正規形 |
| incremental routeのclaim IDが存在しない | `Err(DanglingProofReference)` | exact route parent欠損 |
| incremental claimのrecord/rootがroute upperと整合しない | `Err(ReplayRoutingInvariantViolation::IncrementalClaimMismatch)` | wrong parent attachment |
| incremental routeの`upper_record`がquery upperと異なる | `Err(ReplayRoutingInvariantViolation::IncrementalUpperMismatch)` | event-local grouping違反 |
| inputに同じincremental exact keyが重複する | first-seen entryだけをprepared workへ残す | current semantic dedup/orderを維持 |
| prepared outputに同じincremental exact keyが重複する | `Err(ReplayRoutingInvariantViolation::DuplicatePreparedIncrementalRoute)` | query canonicality違反 |
| parentのsideを一意に構築できない | `Err(IncompleteMandatoryData::ReplayParentSide)` | sideをdrop/推測しない |
| parent lineageを解決できない | `Err(IncompleteMandatoryData::ReplayParentLineage)` | five-lineageをshape推測しない |
| same side/rootが重複する | `Err(ReplayRoutingInvariantViolation::DuplicateParentRoot)` | canonical parent-set違反 |
| representative claimのrootがentry rootと異なる | `Err(ReplayRoutingInvariantViolation::RepresentativeRootMismatch)` | exact winner relation違反 |
| parent列が§4.2のorderでない | `Err(NonCanonicalReplayParentOrder)` | read-time repair禁止 |
| routingとprepared workが§3.3に一致しない | `Err(ReplayRoutingInvariantViolation::RoutingPayloadMismatch)` | summary/payload divergence |
| prepare allocation/index reservation失敗 | `Err(ResourceExhausted)` | partial planを返さない |

### 5.1 Missing CPK mirrorの扱い

「active upperにclaimが正当にない」と「LegacyにはclaimがあるがCPK writerがmirrorを
落とした」は、CPK store単体のabsenceだけでは一般に識別できない。production queryが
absenceを見てLegacy tableへ照会する設計は、CPK計画§15のauthorized query boundaryと
CPK-8のsingle representation目標に反するため採らない。

移行期間はstrengthened shadow oracleが次をexact比較する。

- upper-recordごとのclaim root/representative/lineage sequence
- lower-recordごとのclaimed parent sequence
- live coverage root/state relation
- incremental route claim identity

Legacy non-empty / CPK emptyを観測したらoracle mismatchとしてcutoverを停止する。
early returnまたは`Generic` parity PASSにしない。

CPK store内部でclaim occurrenceとrecord/root indexの片側だけが存在するpartial stateは
production query自身がtyped failureにする。writer全体の完全な呼び忘れはCPK-0c census、
writer fixture matrix、shadow oracleでauthority cutover前に閉じる。単一representationが
自己自身の完全な欠落をoracleなしで検出できるとは主張しない。

## 6. `ProofFailure` vocabulary

### 6.1 既存variantの再利用

projection decision追補で導入済みの次を再利用する。

- `MissingSemanticFact`
- `MissingProofFact`
- `DanglingProofReference`
- `IncompleteMandatoryData`
- `ResourceExhausted`
- `ProofFactRef`
- `MandatoryProofField`
- `ProofOperation`

routing failureをstring、panic message、`Generic` fallbackだけで表さない。

### 6.2 Routing固有identity

最低限、次のtyped vocabularyを追加する。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProofFactRef {
    // existing variants ...
    ReplayClaims(BoundRecordId),
    ReplayParent {
        lower: BoundRecordId,
        upper: BoundRecordId,
        side: ReplayClaimParentSide,
        coverage_root: UpperReplayClaimId,
    },
    IncrementalReplayRoute(IncrementalRouteKey),
    LiveCoverage(UpperReplayClaimId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MandatoryProofField {
    // existing variants ...
    ReplayParentIdentity,
    ReplayParentSide,
    ReplayParentLineage,
    ReplayClaimIndex,
    IncrementalRouteClaim,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplayRouteTargetViolation {
    LowerDirectionOrState,
    UpperDirectionOrState,
    OwnerMismatch,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReplayRoutingInvariantViolation {
    ClaimIndexMismatch,
    DuplicateParentRoot(ReplayClaimParentSide),
    RepresentativeRootMismatch,
    IncrementalUpperMismatch,
    IncrementalClaimMismatch,
    DuplicatePreparedIncrementalRoute,
    RoutingPayloadMismatch,
}
```

`ProofFailure`へ次を追加する。

```rust
InvalidReplayRouteTarget {
    lower: BoundRecordId,
    upper: BoundRecordId,
    kind: ReplayRouteTargetViolation,
},
NonCanonicalReplayParentOrder {
    lower: BoundRecordId,
    upper: BoundRecordId,
    side: ReplayClaimParentSide,
},
ReplayRoutingInvariantViolation {
    lower: BoundRecordId,
    upper: BoundRecordId,
    kind: ReplayRoutingInvariantViolation,
},
```

`ProofOperation`へ次を追加する。

```rust
PrepareReplayRoutePreflight,
PrepareReplayRouteParentCollection,
PrepareReplayRouteBatch,
```

実装時のmodule都合によるvariant名の機械的調整は許すが、failure classを合併して
missing/dangling/canonical/order/targetの意味を失ってはならない。

### 6.3 Failure mapping上の注意

- live coverage entry absenceはuncoveredであり`MissingProofFact`ではない。
- root claim occurrence absenceはdanglingでありuncoveredへ変換しない。
- no upper claimはGenericでありmissing mirror failureとは限らない。
- CPK/Legacy mirror mismatchはoracle failureでありquery resultではない。
- `SkipAlreadyCovered`はwell-formed complete inputからだけ返す。
- mandatory routing failureを`Incomplete` provenance markerへ変換しない。

## 7. Performance contractとindex

### 7.1 Query complexity

global store sizeを`N`、当該upperのcanonical claim数を`Cu`、当該lowerのclaimed
parent数を`Cl`、当該upper向けincremental route数を`Ru`とする。

一pair queryの目標を次に固定する。

```text
expected O(1) or O(log N) indexed lookup
+ O(Cu + Cl + Ru)
+ returned payload size
```

`Cu/Cl/Ru`の列挙はquery outputとrouting semanticsに必要なため許す。次は禁止する。

- 全`upper_claims`のscan
- 全`live_coverage`のscan
- 全lower/upper bound recordのscan
- 全event incremental route vectorのpairごとのscan
- queryごとの全parent sort
- lower parent vectorのupper pair数倍の不必要なheap clone

### 7.2 Required logical index

`ProofOccurrenceStore`は少なくとも次のlogical indexを持つ。

```text
claim_by_id:
    UpperReplayClaimId -> UpperClaimOccurrence

claims_by_upper_record:
    BoundRecordId -> canonical sequence of representative claim IDs

claimed_parents_by_lower_record:
    BoundRecordId -> canonical sequence of representative claim IDs

live_states_by_coverage_root:
    UpperReplayClaimId -> live state set or nonzero live count
```

backendは`FxHashMap`、dense ID-indexed vector、small-vector、interned immutable blockを
選べる。意味契約は次である。

- point lookupはexpected O(1)またはO(log N)。
- record/root indexはclaim writer/move/coverage writerと同じtransactionで更新する。
- sequence indexは§4.2のcanonical orderをwriter側で維持する。
- empty/no-claim lookupのためだけにper-query heap allocationしない。
- claim moveはold/new record indexとclaim occurrenceをatomicに更新する。
- live stateのexact insert/remove/dedupとcovered boolを一致させる。
- no live-state entryとempty live-stateは同じuncovered resultを返す。

current `upper_claim_index`は`claim_by_id`として再利用できる。current
`projection_supports`はindependent supportを混在させるため、routing queryはclaimed
entryだけをcanonicalにfilterする局所走査を許す。ただしqueryごとのsortは行わない。

### 7.3 Event-local sharing

一new-lower eventではlower parent sequenceを一度preflightし、immutable shared blockを
全upper pairおよびincremental routeで再利用する。同じlower parent entriesをpairごとに
heap cloneする実装は採らない。

一new-upper eventではupper uncovered parent sequenceを一度preflightし、immutable
shared blockを全lower pairで再利用する。per-lower再走査を行わない。

このsharingはevent-localであり、persistent evaluator memoやsemantic cacheではない。

### 7.4 Performance gate

CPK-7 cutover前後で少なくとも次を測る。

- `std::text::parse` wall time / RSS
- `prepare_replay_route` call count
- claim/root index lookup count
- total-store scan count（ゼロ）
- prepared pair/incremental action count
- parent entry materialization count
- lower parent block reuse count
- semantic replay input/generated/accepted count

CPK-6aで発生したsuperlinear hot-write回帰、およびCDM-Bのunbounded rescanと同じ
shapeを再導入した場合、authority cutoverを停止する。最終performance acceptanceは
CPK-9で行うが、gross regressionをCPK-9まで先送りしない。

## 8. Prepare boundaryとwhole-attempt failure

### 8.1 Natural-event batch preflight

routingはsolver hot loop内にあるため、pair queryを一件成功するたび即座にsemantic
actionへ反映し、その後のpair failureを待つ形にしない。

new lower event:

1. semantic lower insertion後のimmutable routing viewを固定する。
2. incremental routesを一度列挙し、upper record別にinput orderを保ってgroupする。
3. opposite upper frontier全pairの`PreparedReplayRoute`をpreflightする。
4. 全pair成功後だけ、semantic frontier orderでpair/incremental actionを実行する。

new upper event:

1. semantic upper insertion後のimmutable routing viewを固定する。
2. opposite lower frontier全pairをpreflightする。
3. 全pair成功後だけ、semantic frontier orderでgeneric actionsを実行する。

preflight vectorのallocation failureを含め、一件でも`Err`ならそのnatural eventの
replay actionを一件も実行しない。

### 8.2 Bound insertion後failureの扱い

projection consumer failureと異なり、routing failure時点ではnew bound insertionや
過去のworklist処理が既に同じmachineへcommit済みであり得る。このpartial semantic
stateをlocal undoしない。

CPK計画§9.2 / invariant 20とprojection decision追補§6.3を、そのままattempt boundaryへ
適用する。

1. first `ProofFailure`をmachine-local terminal healthへlatchする。
2. current eventのprepared/partial routing outputを公開しない。
3. current eventのreplay actionsを実行しない。
4. drain/worklist、epoch/publication、generalization、compact、diagnostic出力を停止する。
5. machine、semantic queue、proof store、cache intent、outputをattemptごと破棄する。
6. 新しいmachineを`LegacyRollback(first_failure)` authorityに固定し、source/session input
   からclean retryする。
7. same machine、same queue cursor、current bound以降だけを再利用しない。
8. clean retry不能またはlegacy removal後はhard compilation failureを返す。

mid-worklist failureはprojectionより遅い時点で起き得るが、whole-attempt discard契約を
変えない。違いはlocal continuationをより厳しく禁止し、natural-event batchのpartial
executionも禁止する点だけである。

### 8.3 Authorityとorganic failure

CPK-7移行期間のauthorityはmachine lifetimeで一度だけ選ぶ。

```text
ProofReadAuthority =
    Cpk
  | LegacyRollback(first_failure)
```

- `Cpk` machineのroutingはCPK queryだけをauthorityとして使う。
- `LegacyRollback` machineはLegacy routing readだけを使い、CPK query結果をsemantic
  routingへ混ぜない。
- record/pair単位のfallbackを禁止する。
- CPK failure後に同じmachineで`Generic`へ保守fallbackしない。
- Legacy retry成功をCPK parity PASSに数えない。

誤ったGenericはwork explosion/order changeを、誤ったSkipはmissing workを起こし得る。
従ってrouting failureに局所fail-open/fail-closedの安全な既定値はない。

## 9. Strengthened shadow oracle

### 9.1 Existing CPK-5 oracleの判定

現行CPK-5 oracleはCPK-7 cutover gateとして不十分である。

- Legacy/CPK claim census mismatchでearly returnする。
- lower projection mirror mismatchでもearly returnする。
- route/pair levelではrouting enumをexact比較し、CPK parentのlower/upper件数をexactな
  observation値として記録するが、Legacy parent identityとの比較はしない。
- event levelでは`input_count`と`accepted_count`をexact比較し、accepted resultが
  replay finite mapに存在することも確認する。
- claim ID、coverage root、side、lineage、sequenceを比較しない。
- exact generic pair listとincremental work listを比較しない。

このoracleを残したままauthorityを切り替えてはならない。strengtheningは本書の
prerequisite scopeであり、別の未定義follow-upへ先送りしない。

### 9.2 Exact comparison surface

同じnatural eventのLegacy planとCPK prepared batchについて、最低限次を比較する。

- lower/upper semantic frontier input sequence
- pairごとの`Generic / IncrementalOnly / SkipAlreadyCovered`
- `pair_replay`のpresence（`Some(empty)`を含む）
- incremental route exact keyとsequence
- parentのexact `representative_claim`
- canonical `coverage_root`
- Lower/Upper side
- five-source lineage
- parent canonical sequence
- lower/upper replay input/generated/accepted
- canonical duplicate/trivial/evidence-only/incomplete disposition
- accepted result constraint IDとcanonical constraint count
- row/reduction route merge result
- semantic worklist event traceとtermination

Legacy raw historical parent orderを直接oracleにしない。LegacyとCPKをRCPF §6.4の
同じcanonical parent orderへnormalizeしてsequence比較する。ただしsemantic frontier
orderとincremental route input orderはnormalize/sortせずexact比較する。

### 9.3 Oracle mismatch policy

oracle active時のmirror mismatch、missing index、parent mismatchは全てtest failureにする。
比較をskipするearly returnは禁止する。

fixtureがLegacy-only low-level writerを意図的に使う場合は、次のどちらかを明示する。

1. production-mirrored machine-level fixture APIへ移行する。
2. Legacy internal characterizationと明記し、explicit Legacy-only routing entrypointを使う。

CPK oracleをinactiveにしてfixtureを通すこと、expected parent件数をCPK出力に合わせて
減らすこと、missing mirrorをvalid no-claimへ分類することを禁止する。

### 9.4 Fixture matrix

少なくとも次をcoverする。

1. no upper claim `Generic`
2. one/multiple uncovered root `Generic`
3. all covered + no incremental `SkipAlreadyCovered`
4. all covered + incremental route `IncrementalOnly`
5. all covered + variable lower + unhandled covered parent attachment
6. non-variable lowerでcovered fallbackを追加しないcase
7. lower parentのみ、upper parentのみ、mixed side parents
8. same-root representative replacement
9. five-lineage parent matrix
10. root/claim/incremental arrival permutation
11. target-late lower/upper creation
12. new-lower/new-upper direction parity
13. canonical duplicate/trivial/evidence-only/incomplete disposition
14. incremental route first-seen dedup/order
15. claim move between upper records
16. missing/dangling/noncanonical/index fault injection
17. Legacy-only direct fixture census
18. repository std / RMW / URR lightweight representative fixture

full repository-stdを新しいunscoped unit fixtureとして追加しない。既存のmemory-safeな
characterizationと`std::text::parse` timing/census invocationを使う。

## 10. Implementation slices

### 10.1 Slice A: type・failure・index foundation

一commitで次を追加する。

- §3のprepared parent/action type
- §6のrouting-specific failure vocabulary
- §7.2のrequired index
- writer/move/coverage updateのindex atomicity tests
- no global scan instrumentation

production routing authorityはLegacyのままにする。

### 10.2 Slice B: fallible query core

次を別commitで行う。

- `prepare_replay_route -> Result`
- semantic target / claim / root / route preflight
- canonical parent construction
- event-local incremental grouping
- routing/payload consistency validation
- decision table fault-injection unit tests

production routing authorityはLegacyのままにする。

### 10.3 Slice C: strengthened shadow parity

次を一つ以上のsmall commitで行う。

- early-return oracleの除去
- §9.2のexact comparison
- §9.4 fixture matrix
- fixture low-level writer census/hygiene
- worklist/replay/row/termination trace parity
- `std::text::parse` pre-cutover timing/call-count profile

Slice Cがgreenになるまでauthority cutoverへ進まない。

### 10.4 Slice D: CPK-7 authority cutover

単独commitで次を切り替える。

- `lower_bound_replay_actions`
- `upper_bound_replay_actions`
- incremental route generic-exclusion decision

projection CPK authority、Legacy rollback、shadow oracleを残す。CPK-8 deletionを混ぜない。
cutover後にtargeted、full scoped、broader integration、repository representative、
`std::text::parse` timingを実行する。

### 10.5 Slice E: soak/follow-up

CPK-7 exit条件を満たすまで、routing authorityとLegacy rollbackを並存させる。
Legacy removalはCPK-8の別判断であり、本書は認可しない。

## 11. Existing invariantとのcross-check

### 11.1 RCPF 23 invariant

- **Exact carrier/parent identity**: root、side、representative claim、lineageを保持し、
  loser permutationをidentityへ混ぜないため一致する。
- **Event-time snapshot**: natural-event batch preflightは同じimmutable routing viewを読む。
- **First representative / first witness**: winnerをquery時に再導出しない。
- **Covered/uncovered equivalence**: root live indexはLegacy finite relationとexact比較する。
- **Incremental exclusion**: genericが同upper routeを包含するcurrent ruleを維持する。
- **Canonical duplicate/trivial/evidence-only**: queryはadmission dispositionを予測で
  上書きせず、existing admission layerへprepared parentsを渡す。
- **Insertion-order invariance**: parent relationだけをcanonicalizeし、semantic route
  orderを保つ。
- **No-claim passthrough**: no claimはallocation-heavy proof failureでなくGeneric。
- **Failure atomicity**: event全体preflightとattempt discardを組み合わせる。
- **Diagnostic order isolation**: replay routing parent canonical orderを、explanationの
  category/edge順へ流用しない。

### 11.2 CPK計画§15

1. proof IDをsemantic `Hash/Eq`へ追加しない。
2. queryはsemantic map/queueをmutateしない。
3. semantic queueはtyped routing resultだけを読む。
4. exact replay carrierおよびparent sideを失わない。
5. mandatory routing factをbudget/drop/fallbackで隠さない。
6. no-claim queryのempty proof-parent blockにheap allocationを要求しない。Generic
   semantic action batch自体の必要なpreflight storageとは区別する。
7. exact no-workではreplay actionを生成しない。
8. coreは`prepare_replay_route`以外からproof storageを読まない。
9. consumer-visibleでないparent relationはfinite mapとして比較し、adapter sequenceだけを
   explicit canonical orderにする。
10. failed attemptからoutputを返さない。

### 11.3 CPK-0追補

- complete pre-event viewから一natural eventを準備する規律と一致する。
- claim workとindependent workを混同しない。
- representative selectionをevent後のglobal scanで再構成しない。
- whole-attempt Factored/LegacyRollback retryと一致する。
- mandatory routing/projectability factをdiagnostic budgetへ落とさない。

### 11.4 Projection decision追補

- `ProofFailure` / `ProofFactRef` / `MandatoryProofField` vocabularyを再利用する。
- machine-local sticky failureとfresh-machine retryを再利用する。
- valid absenceとmandatory missing-dataを区別する。
- organic CPK failureをLegacy retry成功でparity PASSにしない。

### 11.5 Tensionと解消

三つのtensionがあるが、解消不能な矛盾ではない。

1. **CPK計画の「coreはroutingだけを見る」とexact work payload**:
   coreはrouting summaryでcontrol flowを選ぶが、既存admissionへ渡すopaque prepared
   pair/route descriptorは必要である。coreがclaim/root/sideを解釈しない限り、
   authorized query boundaryを破らない。payloadを省略すると計画が置換対象に挙げた
   parent readsを残すため、`proof_event`をlosslessに具体化する方を採る。
2. **Parent canonical orderとsemantic route order**:
   RCPF canonical orderはlogical parent-set materializationへ適用する。incremental route
   action sequenceへ適用するとqueue orderが変わるため、route input orderは維持する。
3. **No-claim Genericとmissing mirror**:
   store単体では完全なwriter omissionを常に検出できない。queryからLegacyを読む
   fallbackではなく、writer censusとstrengthened shadow oracleをcutover prerequisiteに
   する。内部partial indexはtyped failureにする。

これ以外にRCPF 23 invariant、CPK計画§15、CPK-0追補、projection decision追補との
矛盾は見つからない。

## 12. 本書固有のcorrectness invariants

1. `prepare_replay_route`はactive lower/upperのsame-owner pairだけをdomainとする。
2. routing targetのsemantic validityをcaller boolで代用しない。
3. `Generic` / `IncrementalOnly` / `SkipAlreadyCovered`は§3.3のpayloadと一致する。
4. `SkipAlreadyCovered`はcomplete well-formed stateからだけ返す。
5. no upper claimは正当なGenericである。
6. live coverage entry absenceは正当なuncoveredである。
7. coverage root claim absenceはdangling failureである。
8. missing/dangling mandatory factをGenericへfail-openしない。
9. parentはside、root、exact representative claim、lineageを保持する。
10. exact claim IDはwriter-fixed representative claimである。
11. loser claim permutationをparent identityへ含めない。
12. same side/rootを重複させない。
13. lower/upper sideをcross-side dedupしない。
14. representative claimのrootとentry rootを一致させる。
15. lineageをshapeから逆推定しない。
16. lower side parentsをupper side parentsより先にmaterializeする。
17. side内はroot、representative claimの辞書式順にする。
18. parent canonical orderをsemantic route orderへ流用しない。
19. incremental routeのcurrent input orderとfirst-seen dedupを維持する。
20. generic routeが同upperのincremental semantic actionを包含する現行規則を維持する。
21. covered-parent attachment pairをqueryから推測で削除しない。
22. actual replay dispositionをrouting queryが予測して上書きしない。
23. claim/index/move/coverage stateをwriter transaction内で同期する。
24. pair queryは全claim/live-coverage storeをscanしない。
25. event route groupingをupper pairごとに再構築しない。
26. query時に全parentをsortしてcorruptionをrepairしない。
27. empty parent payloadだけのためにparent blockをheap allocationしない。
28. one natural eventの全routeをsemantic execution前にpreflightする。
29. route batchの一部だけを実行してから後続failureを返さない。
30. failureをmachine-local terminal stateへstickyにlatchする。
31. failure後にsame machine/worklist cursorを続行しない。
32. retryはfresh machineのwhole attemptである。
33. record/pair単位でCPK/Legacy authorityを混在させない。
34. organic CPK failureをLegacy retry成功でparity PASSにしない。
35. oracle active時のmirror mismatchをearly returnでskipしない。
36. oracleはparent件数だけでなくexact identity/side/orderを比較する。
37. semantic worklist/frontier/route orderをcanonical normalizationで隠さない。
38. proof queryはsemantic map/queueをmutateしない。
39. SCC、generalization core、simplifierを変更しない。
40. CPK-8/9の決定を本書から先取りしない。

## 13. Stop conditions

実装またはshadow parityで次を観測した場合、authority cutoverへ進まず本書へ戻る。

1. `ReplayRouting`の3 variantと§3.2 payloadでLegacy action選択をlosslessに表せない。
2. coreがclaim/root/lineageを解釈しなければroutingできない。
3. valid complete stateでLegacy/CPK routingが一件でも異なる。
4. valid complete stateでpair replay presenceが異なる。
5. valid complete stateでincremental route key/sequenceが異なる。
6. exact parent claim/root/side/lineage/sequenceが異なる。
7. same-root representativeをcanonical storeから一意に得られない。
8. upper-record relationとlower-record relationのwinner差をglobal winnerへ統合する必要がある。
9. covered/uncovered判定がlive root indexとLegacy finite relationで異なる。
10. no claimとmissing mirrorを区別するためproduction queryがLegacy storageを読む必要がある。
11. missing/dangling factに局所Generic/Skip fallbackが必要になる。
12. incremental route orderをcanonical sortしなければparityを得られない。
13. parent canonical orderを使うとsemantic queue orderが変わる。
14. one-event batchを全件preflightできず、partial semantic replay後にfailureが起こる。
15. failure後にsame machine/worklistを再利用しなければclean retryできない。
16. first failureをexisting attempt failure channelへ接続できない。
17. queue/work、canonical constraint、row/reduction state、terminationが異なる。
18. canonical duplicate/trivial/evidence-only/incomplete dispositionが異なる。
19. CPK-5 oracleのearly returnを除去すると新しいmirror mismatchが出る。
20. production fixtureが新CPK writerを通らず、Legacy-only stateを暗黙にauthority oracleにする。
21. pair queryが全`upper_claims`または全`live_coverage`をscanする。
22. per-pair full route scan、sort、cloneがprofileの新hot spotになる。
23. empty parent payloadだけのためにparent block allocationが増える。
24. `std::text::parse`のwall time/RSSがgross regressionする。
25. proof index更新のためsemantic key/orderを変える必要が出る。
26. claim move/index atomicityを一つのwriter boundaryで保てない。
27. CPK-7変更がprojection authority、SCC、generalization、simplifierを変更し始める。
28. Legacy removalまたはdual-write cleanupを同じcommitへ混ぜ始める。

stop conditionに該当した場合、fixture期待値、routing mapping、parent order、failure policyを
実装出力へ合わせて変更してはならない。原因を特定し、必要なら本書を改訂して再承認する。

## 14. CPK-7 completion gate

CPK-7をcompleteと呼ぶには次を全て満たす。

- query/index/failure vocabularyがproduction compileされる。
- strengthened shadow oracleが§9.2をexact比較し、early returnがない。
- §9.4 fixture matrixがgreen。
- lower/upper/incremental routingがCPK sole authorityである。
- Legacyはmachine-lifetime rollback authorityとしてだけ残る。
- semantic worklist traceがparity。
- replay input/generated/accepted/disposition censusがparity。
- canonical constraint count/orderがparity。
- row/reduction stateがparity。
- final type/scheme/outputがparity。
- terminationがparity。
- full scoped suiteに新failureがない。
- broader integration/characterizationがgreen。
- `std::text::parse`にtotal-store scanまたはgross regressionがない。
- organic CPK failureを伴うretryをPASSに数えていない。

## 15. CPK-8 / CPK-9との境界

### 15.1 CPK-8

CPK-8は次を別途扱う。

- Legacy claim/coverage/routing readerの削除
- CPK-5 shadow observationとmigration adapterの削除
- `LegacyRollback` authorityの削除
- dual-write proof stateの削除
- migration-only fixture/helperの削除

CPK-7がgreenでも、本書はこれらの削除を認可しない。

### 15.2 CPK-9

CPK-9は最終wall time/RSS/profile、旧dual-write costの消滅、application corpus、full
safety suiteを扱う。本書§7.4はCPK-7でgross regressionを止めるためのlocal gateであり、
CPK-9の最終closeoutを置き換えない。

## 16. 波及する文書

本書がClaude査読とユーザ承認を経て正本になった後、必要に応じて次へ参照を追加する。

- `notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md`
  - §10.1 / CPK-7から本書を参照する。
- `notes/design/2026-08-05-cpk-0-projection-admission-addendum.md`
  - mandatory routing factとwhole-attempt failureの具体化先として本書を参照する。
- `notes/design/2026-08-06-cpk-projection-decision-addendum.md`
  - shared `ProofFailure` / `ProofReadAuthority` vocabularyのrouting拡張として本書を参照する。
- `notes/design/2026-08-02-replay-claim-parent-factorization.md`
  - 変更不要。本書は§6.3/6.4/8.8のidentity/order precedentを参照する。

これらの文書更新は本書draftとは別変更として扱う。

---

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定

状態: **ユーザ承認済み（2026-08-06、リカバリ可能なcheckpointとして承認）**

本書はCPK-7 implementation contractの正本である。§10のスライス規律（Slice A〜E、
各段階でshadow parity greenを確認してから次へ進む）と§13のstop conditionsを
厳格に守り、問題が見つかればcommit単位でrevertして本書へ立ち戻る。
