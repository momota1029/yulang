# CPK 追補: `project_lower` decision・support payload・failure 契約

日付: 2026-08-06

状態: **ユーザ承認済み（2026-08-06）**

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定

**署名についての注記**: Fable 5 が一時的に利用できないため、`CLAUDE.md`
「Fable 5 不在時の起案担当」に従い、本書は Codex `gpt-5.6-sol`（xhigh）が
本文を起案した。Claude (Sonnet 5) は、コード・既存正本文書との照合、
invariant / stop condition の査読、体裁の統一および確定を担当した
（4 consumerの現行挙動記述をCodex gpt-5.6-terraで独立fact-checkし、
`ProjectionProofCarrier::Incomplete`の分類に関する矛盾を1件発見・修正済み）。
本書はClaudeの査読とユーザの明示的承認を経ており、CPK-6のGap 1
（`project_lower` / `ProjectionDecision` / `ProjectionSupportSet`）に関する
設計判断の正本である。

本書は
`notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md`
（以下 CPK 計画）§10.2 の `project_lower` / `ProjectionDecision` /
`ProjectionSupportSet` sketchを実装可能なcontractへ補完する追補である。
また、
`notes/design/2026-08-05-cpk-0-projection-admission-addendum.md`
（以下 CPK-0 追補）のcanonical support orderと、
`notes/design/2026-08-02-rcpf-quarantine-retry-authority-addendum.md`
（以下 RCPF quarantine 追補）のwhole-attempt failure規律を、このqueryへ
具体化する。

本書が正式に決定するのはCPK-6b着手前に必要なGap 1だけである。
explanation / portable provenance query（Gap 2）と、before/after owner /
publication plan query（Gap 3）は、本書のidentity・ordering・failure vocabularyを
再利用してよいが、それぞれ別の追補または署名付きsectionで決定する。

## 0. 本書が下す決定の要約

1. `ProjectionSupportSet`は、評価をtrueにした最小または最初のwitnessではなく、
   同一snapshotで現在qualifyingな**全support**を返す。これは現行
   `SchemeProjectableLowerReason::Qualified`のpayload contractを維持する。
2. claimed supportはcanonical coverage rootとexact representative claim IDの
   両方を保持する。independent supportはcanonicalized lineage keyへ縮めず、
   exact `ProjectionProofCarrier`を保持する。
3. payload orderは、claimedを先、independentを後とする。claimedは
   `coverage_root`昇順、independentは既存
   `canonical_projection_key::carrier_cmp`のfull total orderとする。
4. `Unclaimed`は、active lower recordに正当なprojection support ledgerが
   存在しない、または空である場合だけを表す。well-formedなproof graphを
   評価してfalseなら`Excluded`、trueなら`Included`を返す。
5. `Included { supports: ProjectionSupportSet::empty() }`を有効な結果として認める。
   formulaがroute経由で成立しても、現在直接qualifyingなclaimed / independent
   supportがゼロという状態を、`Unclaimed`へ再分類しない。
6. dangling claim、欠落coverage root、support/formula不整合、欠落premise、
   unresolvable opaque handle、非canonical support列は`ProofFailure`とする。
   これらを`Unclaimed`または`projectable = true`へ吸収しない。
7. `ProjectionProofCarrier::Incomplete`は、session evidence budgetによって
   underlying replay-evidence detailが省略されたことを表す既存typed markerである。
   mandatory projectability inputの欠損ではなく、通常のindependent supportとして
   payloadとprojectability formulaの双方に残す。他のindependent supportと同じく
   projectabilityを成立させ得るが、後続provenanceのdetail completenessは下がり得る。
   ただし、本来格納すべきsupport/carrier自体を新たに`Incomplete`へ置換してよい
   という意味ではない。
8. `ProjectionEvaluationRound`は、一つのimmutable evaluator-read snapshot上で、
   一つのconsumer traversalに属するtop-level query群だけを共有する。
   cycle cutが起きたqueryの結果は有効だが、その後はround内memo共有を永久に
   無効化し、各queryをfresh evaluatorで評価する。
9. cycle cutはsupport payloadを切り詰めない。`Included`なら、評価branchや
   short-circuitにかかわらず、同じsnapshotの全qualifying supportをcanonical順で返す。
10. 本書はAPI・oracle・failure contractだけを承認する。4 consumerのproduction
    authority cutover自体は、Gap 1実装とshadow parityが完了した後の別commitとする。

## 1. 背景と対象範囲

### 1.1 CPK §10.2に残っていた未決定

CPK 計画§10.2は次の骨格だけを定めていた。

```rust
fn project_lower(
    &self,
    view: &impl SemanticFactView,
    record: BoundRecordId,
    round: &mut ProjectionEvaluationRound,
) -> Result<ProjectionDecision, ProofFailure>;

enum ProjectionDecision {
    Unclaimed,
    Excluded,
    Included {
        supports: ProjectionSupportSet,
    },
}
```

一方、以下は未定義だった。

- `ProjectionSupportSet`のfieldとidentity
- all-support payloadかminimal witnessか
- supportの返却順序
- `Unclaimed` / `Excluded` / empty `Included` / `ProofFailure`の境界
- `ProofFailure`のvariantとattempt failureへの接続
- `ProjectionEvaluationRound`の共有範囲とcycle-cut後のpayload

CPK-2〜CPK-5のshadow oracleはprojectabilityのbool、cycle cut、affected owner、
publication classを比較したが、これらのpayload contractは比較していない。
したがってbool parityだけを根拠に4 consumerをcutoverしてはならない。

### 1.2 対象consumer

本書は、CPK-6bの7 consumerのうち、同じscheme-lower projection viewを読む
次の4 consumerだけを扱う。

1. `ConstraintMachine::scheme_projectable_lowers`
2. scheme compact collector
3. positive alias traversal
4. generalized witness capture

projectability invalidation、explanation / portable provenance、OCAST classifierは
本書の正式な決定対象ではない。

### 1.3 Non-goal

本書は以下を変更しない。

- subtype worklist、bound admission、row reduction、SCC、generalization core
- projection formulaのOR、`ReplayConjunction`のAND、tri-color cycle guard
- upper/lower boundのsemantic order
- livenessおよびcoverage rootの意味
- CPK storeのwriter semantics
- consumerのproduction authority
- diagnostic / portable exportの具体的query shape
- invalidationのbefore/after publication plan

## 2. 4 consumerの現行ground truth

本節の記述はHEAD `809c1911`を基準とする。行番号は後続変更で移動し得るため、
実装時には関数名も合わせて再確認する。

### 2.1 `scheme_projectable_lowers`

現行入口は`crates/infer/src/constraints/mod.rs:1739`にある。

record列:

- ownerの`evidence_lower_ids / evidence_lowers`を先に読む。
- 続いて通常の`lower_ids / lowers`を読む。
- 各vector内は現行のsemantic insertion orderを保つ。
- owner自体が存在しない場合は空iteratorになる。

classificationとpayload:

- ownerがclaimedでない、recordにproof ledgerがない、またはledgerが空なら
  `Unclaimed`としてrecordを採用する。
- claimed supportはclaim IDから`UpperReplayClaim`を引き、その
  `coverage_root`のlive coverageがない場合だけ`uncovered_claims`へ入る。
- independent supportは全て`independent_supports`へ入る。
- record inclusionのboolは`SchemeProjectionEvaluationRound`を通じて
  `SchemeProjectionEvaluator`が決める。
- boolがfalseならrecordをiteratorから除外する。
- boolがtrueなら、先に収集したpayload全体を`Qualified`として返す。
  成功したclauseだけへpayloadを縮める処理はない。

現行ordering:

- `projection_proofs_by_lower_record`はwriter側でcanonical positionへ挿入される。
- claimed supportはcoverage root昇順で、同一rootのrepresentative claim更新は
  positionを変えない。
- independent supportは`canonical_projection_key::carrier_cmp`順である。
- `scheme_projectable_lowers`はこの列を一回走査してclaimed / independentへ
  分けるため、各category内のcanonical orderを保つ。

現行の欠損処理:

- claim IDが`upper_replay_claims`に存在しない場合は`Unclaimed`へfail-openする。
- claimが指すcoverage root claimが存在しない場合も`Unclaimed`へfail-openする。
- evaluatorのFactored read failureはmachineをquarantineし、当該queryではfalseの
  inert placeholderを返す。RCPF quarantine契約上、そのattemptの出力は破棄される。
- legacy evaluator内部には、欠落bound / constraint / root / clause metadataを
  projectable側へ倒す古いfail-openが残る。

最後の三つは、完全なCPK storeをproduction authorityにする最終契約ではない。
CPK 計画§12とRCPF quarantine追補に従い、本書§6でattempt-level failureへ置き換える。

### 2.2 Scheme compact collector

現行入口は`crates/infer/src/compact/collect/mod.rs:645`付近の
`compact_lower_bounds`である。

- raw modeでは`VarBounds::projection_lowers()`を直接読む。
- scheme projection modeでは`scheme_projectable_lowers(var)`を呼び、
  `entry.bound`だけを`compact_lower_bounds_from`へ渡す。
- `reason`、claim ID、carrier、formulaを直接読まない。
- owner boundsが存在しなければ`CompactType::default()`を返す。
- lower record順は`scheme_projectable_lowers`のiterator順であり、merge結果、
  stack-family coexistence、compact rootへ影響し得る。

したがってこのconsumerが必要とするのは、recordの採否と既存record順の完全な
parityである。payloadを最小化する理由にはならない。

### 2.3 Positive alias traversal

現行入口は`crates/infer/src/generalize/mod.rs:543`付近の
`positive_aliases_within_scheme`である。

- `scheme_projectable_lowers(var)`の採用済みrecordを現行順で読む。
- `entry.reason`を読まず、boundのweightとpositive endpointだけを見る。
- alias-neutralでないbound、`Pos::Var`でないendpoint、allowed集合外のvarを除く。
- recursion cycleは`visiting`集合でそのrouteだけ空にする。
- aliasはfirst-seen順でdedupし、その順序をcacheへ保存する。

このconsumerもpayloadを直接必要としないが、projectabilityとrecord順の差は
alias expansionおよびfinal schemeを変え得る。

### 2.4 Generalized witness capture

現行入口は`crates/infer/src/generalize/provenance.rs:21`、lower collectionは
同fileの`WitnessCollector::collect_var`（`around line 165-220`）にある。

- `Unclaimed`なら`GeneralizationParent::Bound(record)`を一つ作る。
- `Qualified`なら、`uncovered_claims`を先に
  `GeneralizationParent::BoundClaim { bound, claim }`へ変換する。
- 続いて`independent_supports`を
  `GeneralizationParent::BoundProjectionProof { bound, carrier }`へ変換する。
- parent列はそのままwitness edge insertion、budget prefix、portable provenance、
  diagnostic orderingへ到達する。
- exact claim IDとexact carrierの双方が必要であり、coverage rootだけ、lineage kind
  だけ、成功clauseだけでは現行provenanceを再現できない。
- `ProjectionProofCarrier::Incomplete`も通常のindependent supportとしてexact
  typed markerのままpayloadに残り、projectability formulaへ参加する。後段で
  underlying replay-evidence detailを解決できない場合はprovenance completenessを
  下げる既存経路へ流れ、別のcarrierを推測しない。

現行`WitnessParents::Selected`にはempty sliceを拒む`debug_assert!`がある。
しかし現行`scheme_projectable_lowers`の型と処理は`Qualified` payloadのnon-emptyを
保証していない。これはsigned semantic contractではなく、§4.4で扱う実装上の
tensionである。

### 2.5 Consumer間の整合性

4 consumerは互いに異なるprojection判定を持たず、全て
`scheme_projectable_lowers`へ収束している。compact / aliasはpayloadを捨て、
generalized witnessだけがpayloadを全て保持する。

したがってconsumer間に解消不能なsemantic inconsistencyはない。最も情報量の多い
generalized witness contractを失わず、compact / aliasへ同じ採否とrecord順を返せば、
一つの`project_lower` contractで4 consumerを覆える。

## 3. APIとdata model

### 3.1 Exact type shape

CPK-6b前のGap 1実装では、次をproduction-compiledなproof query typeとして定義する。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ProjectionClaimSupport {
    pub(crate) coverage_root: UpperReplayClaimId,
    pub(crate) representative_claim: UpperReplayClaimId,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct ProjectionSupportSet {
    pub(crate) uncovered_claims: Vec<ProjectionClaimSupport>,
    pub(crate) independent_supports: Vec<ProjectionProofCarrier>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ProjectionDecision {
    Unclaimed,
    Excluded,
    Included {
        supports: ProjectionSupportSet,
    },
}
```

`coverage_root`と`representative_claim`は別identityである。

- `coverage_root`はliveness lookup、same-root dedup、canonical orderのkeyである。
- `representative_claim`は現行generalized witness、first-winner lineage、portable
  provenanceへ渡すexact claim identityである。

同一rootの後着representative更新は、CPK-0追補§6.2どおりcanonical positionを
変えず、`representative_claim`だけを更新する。payload consumerはrootをclaim IDから
再lookupしてはならない。

independent supportは`ProjectionProofCarrier`をそのまま保持する。
`ProjectionLineage`だけへの縮約、raw numeric tupleへの変換、formula categoryからの
逆推定は行わない。

### 3.2 Query signature

CPK計画§10.2のsignatureを維持する。

```rust
pub(crate) fn project_lower(
    &self,
    view: &impl SemanticFactView,
    record: BoundRecordId,
    round: &mut ProjectionEvaluationRound<'_>,
) -> Result<ProjectionDecision, ProofFailure>;
```

`self`はcanonical `ProofOccurrenceStore`、`view`は同じmachine snapshotの
semantic fact viewを指す。異なるmachine、異なるproof revision、before/afterの
異なるviewを一つのroundへ混ぜてはならない。

### 3.3 Outer record iterator

`project_lower`は一recordのdecisionだけを返し、owner内recordをsortしない。
CPK-6bで`scheme_projectable_lowers`を置換するouter adapterは現行どおり

```text
evidence lowers in semantic insertion order
then
ordinary lowers in semantic insertion order
```

を維持する。supportのcanonical orderをbound record orderへ流用しない。

## 4. Payload semanticsとordering

### 4.1 All qualifying supports

`ProjectionSupportSet`は、top-level resultを最初にtrueへしたclause、最小proof、
short-circuit prefixではない。同じsnapshotで現在qualifyingな全supportを返す。

claimed support:

- canonical rootにlive coverage stateが一件もなければqualifying。
- qualifyingなら`ProjectionClaimSupport { coverage_root,
  representative_claim }`を一件返す。
- live coverageが一件以上あればpayloadへ入れない。

independent support:

- well-formedなindependent supportは全てqualifying。
- exact `ProjectionProofCarrier`を一件返す。
- formula evaluatorが別のclauseでshort-circuitしても除外しない。

この規則は、MPCおよびURR-v3の「record inclusion判定を変更しても
`SchemeProjectableLowerReason::Qualified`のpayload計算は変更しない」という
既存決定を継承する。

### 4.2 Dedupとrepresentative

support relationはcanonical keyごとに一件とする。

- claimed key: `coverage_root`
- independent key: exact `ProjectionProofCarrier`

同じrootに複数claim IDが存在する場合、writer boundaryで固定された現行
representative claimだけを返す。query時にlargest ID、first iterator entry、
lineage depthからwinnerを再導出しない。

異なるexact carrierは、同じlineage kind、同じresult、同じrootへ到達しても
dedupしない。`pivot/lower/upper/rule`、structural rule payload、row/scheme handle、
result fieldを落とさない。

### 4.3 Canonical return order

返却順序は次に固定する。

1. `uncovered_claims`
2. `independent_supports`

`uncovered_claims`内:

- `coverage_root: UpperReplayClaimId`昇順。
- 同一rootは一件だけ。
- `representative_claim`の値はsort keyにしない。

`independent_supports`内:

- `canonical_projection_key::carrier_cmp`のfull total order。
- variant rankだけでなく、result、derivation、premise identityを含む既存keyを
  そのまま使う。

read-timeのHashMap iteration、admission ordinal、historical parent Vec順、
allocation addressを順序keyにしない。production storeはwriter側でこの順序を
維持し、queryごとの全量sortをhot pathへ追加しない。queryはcanonical orderを
検証できるが、非canonical列を黙ってsortしてcorruptionを隠してはならない。

この順序はlogical relation一般の順序を意味論化するものではない。generalized
witness、portable provenance、diagnostic budget prefixへ実際に流れるpayloadだけの
consumer-visible canonical orderであり、CPK計画§15 invariant 18/19と一致する。

### 4.4 Empty `Included`

`Included { supports: ProjectionSupportSet::default() }`は有効である。

これは次を表す。

- recordにはnon-emptyでwell-formedなprojection support/formula graphがある。
- formulaのOR/AND評価はtrueである。
- ただしpayload収集時点で直接qualifyingなuncovered claimed supportおよび
  independent supportはゼロである。

`Included(empty)`を`Unclaimed`へ変換してはならない。`Unclaimed`はproof ledgerが
正当に存在しないraw relationであり、proof graphを評価した`Included`とは
provenance意味が異なる。また`Excluded`へ変換するとformulaのOR/AND結果を
payload non-empty predicateで上書きすることになる。

generalized witness adapterはempty selected parentsをそのまま「このlower relationに
direct parent payloadなし」として扱い、`Bound(record)`を捏造してはならない。
現行`WitnessParents::Selected`の`debug_assert!(!parents.is_empty())`は、CPK-6b前に
次のいずれかで閉じる。

1. reachable fixtureを追加してempty selectionを正しく扱う。
2. signed invariantから構造的に到達不能と証明し、`project_lower`で
   `ProjectionInvariantViolation`にする。

本書は現在の型とevaluatorがnon-emptyを保証していないため、1を既定とする。
実装調査で2を証明できた場合は、本書の意味論変更になるため別の査読を要する。

## 5. Decision table

`project_lower`は、最初にtargetとmandatory referenceをpreflightし、次にpayloadを
canonical形で構築し、その後同じsnapshotのformulaを評価する。途中の欠損を
`Unclaimed`または`Included`へ変換しない。

| 状態 | decision | 理由 |
| --- | --- | --- |
| `BoundRecordId`がsemantic viewに存在しない | `Err(MissingSemanticFact)` | callerまたはstoreのdangling ID |
| recordがactive lowerでない（upper / tombstone / owner-direction不整合） | `Err(InvalidProjectionTarget)` | `project_lower`のdomain外 |
| support entryなし、formula entryなし | `Ok(Unclaimed)` | 正当なno-claim/raw relation |
| support entryありだが空、formula entryなしまたは空 | `Ok(Unclaimed)` | legacy empty-ledger互換。heap allocationは不要 |
| supportなしまたは空だがformulaがnon-empty | `Err(ProjectionInvariantViolation::OrphanFormula)` | formulaだけの公開は禁止 |
| supportがnon-emptyだがformula entryなしまたは空 | `Err(MissingProofFact::ProjectionFormula)` | supportだけのpartial stateは禁止 |
| claimed supportのclaim IDが存在しない | `Err(DanglingProofReference)` | exact representative claimを再構成不能 |
| claimの`coverage_root`に対応するroot claimが存在しない | `Err(DanglingProofReference)` | liveness identityを再構成不能 |
| claimed rootとrepresentative claimのrootが一致しない | `Err(ProjectionInvariantViolation::RepresentativeRootMismatch)` | same-root contract違反 |
| 同一coverage rootが重複する | `Err(ProjectionInvariantViolation::DuplicateClaimedRoot)` | writer canonicality違反 |
| 同一independent carrierが重複する | `Err(ProjectionInvariantViolation::DuplicateIndependentCarrier)` | writer canonicality違反 |
| supportに対応するclauseが一件もない | `Err(MissingProofFact::ProjectionFormula)` | atomic support/formula commit違反 |
| clauseが未知supportを参照する | `Err(ProjectionInvariantViolation::OrphanFormula)` | formula/support closure違反 |
| formula premiseのbound / constraint / rootが存在しない | `Err(DanglingProofReference)` | evaluator inputが不完全 |
| exact carrierのconstraint / origin / row / scheme handleを解決できない | `Err(DanglingProofReference)` | generalized witnessへlosslessに渡せない |
| row/reduction opaque handleが存在しない、generationが違う | `Err(DanglingProofReference)` | opaque handle invariant違反 |
| support列またはformula category列がcanonical orderでない | `Err(NonCanonicalProjectionOrder)` | read-time repairで不整合を隠さない |
| `ProjectionProofCarrier::Incomplete`が明示的に格納されている | 通常のindependent supportとして扱う | optional provenance detailのtyped incompleteness |
| 明示的な`Incomplete` supportのunderlying replay-evidence detailがbudgetで欠落 | 通常のindependent supportとしてformulaへ含める。後続provenance completenessは下がり得る | support自体はmandatory projectability inputとして存在する |
| well-formed graphを評価してfalse | `Ok(Excluded)` | valid proof graphのnegative result |
| well-formed graphを評価してtrue、qualifying supportあり | `Ok(Included { supports })` | canonical全supportを返す |
| well-formed graphを評価してtrue、qualifying supportなし | `Ok(Included { supports: empty })` | formula結果とpayloadを混同しない |

`support entryありだが空、formula entryも空`はtransition compatibilityとして
`Unclaimed`に含める。ただし新writerがempty entryを常設することを推奨するものではない。
no-claim allocation zeroを守るため、新kernelの正規形はentry自体を作らない形でよい。

## 6. `ProofFailure` vocabularyとwhole-attempt failure

### 6.1 Failure type

Gap 1実装では、string messageだけでfailure kindを表さず、少なくとも次のtyped
vocabularyを定義する。

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ProofFailure {
    MissingSemanticFact {
        fact: SemanticFactRef,
    },
    InvalidProjectionTarget {
        record: BoundRecordId,
        direction: BoundDirection,
        state: BoundRecordState,
    },
    MissingProofFact {
        fact: ProofFactRef,
    },
    DanglingProofReference {
        owner: ProofFactRef,
        target: ProofFactRef,
    },
    IncompleteMandatoryData {
        owner: ProofFactRef,
        field: MandatoryProofField,
    },
    NonCanonicalProjectionOrder {
        record: BoundRecordId,
    },
    ProjectionInvariantViolation {
        record: BoundRecordId,
        kind: ProjectionInvariantViolation,
    },
    ResourceExhausted {
        operation: ProofOperation,
    },
}
```

補助identityは次を最低限持つ。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProjectionSupportIdentity {
    Claimed(ProjectionClaimSupport),
    Independent(ProjectionProofCarrier),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ProofFactRef {
    Semantic(SemanticFactRef),
    ProjectionSupports(BoundRecordId),
    ProjectionFormula(BoundRecordId),
    ProjectionSupport {
        record: BoundRecordId,
        support: ProjectionSupportIdentity,
    },
    UpperClaim(UpperReplayClaimId),
    CoverageRoot(UpperReplayClaimId),
    Origin(OriginId),
    RowDerivation(RowDerivationId),
    RowReduction(UnweightedRowReductionRecordId),
    GeneralizedWitness(GeneralizedSchemeWitnessId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MandatoryProofField {
    SupportIdentity,
    RepresentativeClaim,
    CoverageRoot,
    LiveCoverage,
    Formula,
    FormulaPremise,
    ExactCarrier,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProjectionInvariantViolation {
    OrphanFormula,
    DuplicateClaimedRoot,
    DuplicateIndependentCarrier,
    RepresentativeRootMismatch,
    FormulaSupportMismatch,
    FormulaCategoryOrder,
    VisitingStateEscaped,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProofOperation {
    ProjectLowerPreflight,
    ProjectLowerSupportCollection,
    ProjectLowerEvaluation,
}
```

実装はvariant名をRust moduleの既存命名へ機械的に合わせてよいが、failure classを
合併して意味を失ってはならない。特に`MissingProofFact` /
`DanglingProofReference`を`Unclaimed`へ変換するadapterを置かない。

### 6.2 `Incomplete`の二種類を分ける

次を混同しない。

1. **明示的なbudget-truncated evidence incompleteness**:
   `ProjectionProofCarrier::Incomplete`は、session evidence budgetによりunderlying
   replay-evidence detailを保持できなかったことを表す。marker自体は通常の
   independent supportであり、projectabilityに必要なformula/premiseとともに
   完全に格納され、他のindependent supportと同じくformulaへ参加してdecisionを
   成立させ得る。欠落しているのは後続diagnostic / portable exportで展開する
   underlying detailであり、support自体ではない。
2. **mandatory dataの欠損**:
   claim/root/formula/premise/exact carrier identityの欠落。
   `ProofFailure::IncompleteMandatoryData`またはより具体的なdangling/missing variantを
   返し、attemptを失敗させる。

新writerがcaptureを省略した結果を`ProjectionProofCarrier::Incomplete`へ変換し、
mandatory failureをoptional detailに見せかけてはならない。

### 6.3 Attempt failureへの接続

RCPF quarantine追補§3のshapeをCPKへ再利用する。

```text
ProofReadAuthority =
    Cpk
  | LegacyRollback(first_failure)
```

CPK authorityのattemptで`project_lower`が一度でも`Err(failure)`を返した場合:

1. machine-local healthをterminal `Failed(first_failure)`へlatchする。
2. そのqueryのpartial decision / support payloadを公開しない。
3. 以後のsemantic queue、generalization、compact、diagnostic、epoch/cache
   publicationを進めない。
4. そのattemptが作ったscheme/output/diagnosticを全て破棄する。
5. legacy representationが移行用に残るCPK-6b/7期間は、新しいmachineを
   `LegacyRollback(first_failure)` authorityに固定してclean retryする。
6. 同一machineの途中からrecord/query単位でlegacyへfallbackしない。
7. clean retryを提供できない環境、またはlegacy removal後はhard compilation
   errorとして返す。

retryが成功して最終出力を得ても、organic CPK failureをparity PASSまたはcutover
gate成功として数えない。原因を直すまで次stageへ進まない。

これは現行`scheme_projectable_lowers`の局所metadata fail-openを明示的に
supersedeする。valid no-ledger状態の`Unclaimed`はfail-openではなく正規decisionであり、
引き続き許可する。

## 7. `ProjectionEvaluationRound`

### 7.1 Lifetime

一つのroundは次の全てを固定する。

- 一つの`ConstraintMachine` lifetime
- 一つのimmutable `SemanticFactView`
- 一つのimmutable `ProofOccurrenceStore` view
- 一つのcoverage/liveness snapshot
- 一つのproof read authority
- 一つのconsumer traversal

代表的なconsumer traversalは、一回の
`scheme_projectable_lowers(owner)`相当のowner内record列挙である。
compact、positive alias、generalized witnessが別々に同じownerを読む場合、
roundをconsumer間で持ち回らず、それぞれ新しいroundを作る。

mutation、epoch transition、publication、before/after boundaryをまたいでroundを
再利用しない。projectability invalidationのbeforeとafterはGap 3でも必ず別roundに
する。

### 7.2 Memoization

round-local evaluatorはacyclicな`Done`結果だけを同じsnapshotの後続top-level
queryへ共有してよい。永続cache、machine field、cross-round cacheへ昇格しない。

top-level return時に`Visiting`を残してはならない。残った場合は
`ProjectionInvariantViolation::VisitingStateEscaped`でattemptを失敗させる。

### 7.3 Cycle cut

tri-color cycle guardは既存規則を維持する。

- `Visiting` nodeへのre-entryは、そのcircular routeだけをfalseにする。
- 他のclause / sourceのOR評価は続ける。
- cycle cutを含むtop-level queryの最終decisionは有効である。
- cycle cutが一度でも起きたら、共有evaluatorを即座に破棄する。
- 同じroundの残りtop-level queryは一件ごとにfresh evaluatorを使う。
- 同じround内でmemo共有を再開しない。

support payloadはevaluation traceから収集しない。preflight済みcanonical support
viewから構築するため、cycle cut、clause short-circuit、query orderで変化しない。

- cycle cutを含む評価がfalseなら`Excluded`でpayloadを返さない。
- trueなら`Included`と全qualifying supportを返す。
- payloadが空でも§4.4どおり有効である。

### 7.4 Failure後のround

`project_lower`が`Err`を返したroundはterminalである。同じroundから別recordを
評価しない。attempt自体も§6.3に従ってterminalになるため、round内repairやmemoの
部分削除は行わない。

## 8. Query algorithm

実装は、意味として次の順序に従う。

```text
project_lower(view, record, round):
    1. recordが同じviewのactive lowerであることを検証
    2. support/formula entryのabsence/empty/orphanをdecision tableで分類
    3. support identity、representative claim、coverage root、carrier handle、
       formula support closure、premiseを全てpreflight
    4. support/formulaのcanonical orderとexact dedupを検証
    5. qualifyingな全supportをProjectionSupportSetへfallible collect
    6. 同じroundでformulaのOR/ANDを評価
    7. falseならExcluded
    8. trueならIncluded { supports }
```

fallible collectのallocation failureは`ResourceExhausted`とし、半分だけ作ったpayloadを
返さない。preflight後のevaluationがstore lookup failureを新たに起こさないquery
surfaceを優先する。

support payload構築とformula評価の順は、外部から観測できるallocation IDやepochを
発行しない限り実装上入れ替えてよい。ただし双方が同じsnapshotを読み、failure時に
partial outputを公開せず、cycle cutでpayloadを削らないという契約は固定する。

## 9. Consumer adapter contract

### 9.1 `scheme_projectable_lowers`

CPK-6bではouter record orderを維持し、各active lowerへ`project_lower`を呼ぶ。

```text
Unclaimed          -> recordを採用、reason = Unclaimed
Excluded           -> recordを除外
Included(supports) -> recordを採用、reason = Qualified(payload adapter)
Err                 -> attempt terminal。iteratorを部分公開しない
```

legacy compatibility adapterは

```text
ProjectionClaimSupport.representative_claim -> uncovered_claims
exact independent carrier                  -> independent_supports
```

と写す。coverage rootを捨てるのはlegacy `SchemeProjectableLowerReason`への一時adapter
だけであり、新CPK API内部では保持する。

### 9.2 Compact collector

`Unclaimed` / `Included`のrecordだけを現行順でcompactへ渡し、`Excluded`は渡さない。
support payloadをcompact algorithmへ漏らさない。cold/warm cacheでcompact root、
owner dependency、scheme outputが一致しなければcutoverを止める。

### 9.3 Positive alias traversal

`Unclaimed` / `Included`のrecordだけを現行順でalias候補へ渡す。weight、endpoint、
allowed set、cycle guard、first-seen dedupを変更しない。support payloadをalias
recursion条件に使わない。

### 9.4 Generalized witness capture

`Unclaimed`は現行どおり`Bound(record)`、`Included`は

```text
all uncovered representative claims in coverage-root order
then
all exact independent carriers in carrier total order
```

をparentへ写す。formulaのwinning branchだけへ削らない。empty `Included`では
parentを追加せず、raw `Bound(record)`へfallbackしない。

`ProjectionProofCarrier::Incomplete`は他のindependent carrierと同じcanonical順で
parentへ写し、underlying replay-evidence detailの欠落には既存completeness規則を
使う。mandatory support identityが解決不能ならwitnessだけをskipせずattemptを
失敗させる。

## 10. Oracleと実装slice

### 10.1 Slice A: query core

次を一commitで追加する。

- §3のtype
- §6のfailure vocabulary
- §7のround
- §8の`project_lower`
- missing/dangling/canonical-order/cycle-cut unit fixture

production consumerはまだcutoverしない。

### 10.2 Slice B: 4-consumer shadow parity

同じfixtureについてlegacyとCPKを並走させ、少なくとも次をexact比較する。

- decision: `Unclaimed` / `Excluded` / `Included`
- owner内record列とbound order
- `ProjectionClaimSupport.representative_claim`とlegacy `uncovered_claims`
- coverage rootのcanonical order
- independent exact carrier集合とsequence
- compact root
- positive alias sequence
- generalized witness parent / incoming edge sequence
- tight-budget witness prefixとcompleteness
- cycle-cut有無とdecision
- no-claim allocation zero

fixture matrix:

1. no-ledger / empty-ledger `Unclaimed`
2. standalone-only `Included`
3. derived-unary-only `Included`
4. replay-conjunction `Included` / `Excluded`
5. claimed-only uncovered / covered
6. claimed + independent mixed support
7. five-lineage matrix
8. same-root representative replacement
9. root/carrier admission permutation
10. `Included(empty)`
11. typed `ProjectionProofCarrier::Incomplete`
12. fault injectionによる各`ProofFailure`

Slice Bがgreenになるまで4 consumerをproduction CPK authorityへ切り替えない。
bool parityだけをSlice BのPASS条件にしない。

### 10.3 CPK-6b cutover

Slice A/B完了後も、4 consumerを一commitへまとめない。CPK計画とlong-task policyに
従い、一consumer一commit、各commit後にtargeted testとfull scoped suiteを実行する。
legacy queryとshadow parityはCPK-8まで残す。

## 11. Existing invariantとのcross-check

### 11.1 RCPF 23 invariant

- **Exact carrier identity (1)**: independent payloadはexact carrierを保持し、
  claimed payloadはrootとrepresentative claimの両方を保持するため一致する。
- **First representative / event-time snapshot (4/5)**: query時にwinnerを再導出せず、
  writer-fixed representativeを読むため一致する。
- **Covered/uncovered equivalence (6)**: live coverageをquery時にcanonical rootから
  読む現行規則を維持する。
- **Consumer equivalence (11)**: valid complete stateではlegacyの全payloadとsequenceを
  exact比較する。minimal witness化は行わない。
- **Cycle safety (13)**: cycle cut後のmemo共有禁止を維持する。
- **Insertion-order invariance (15)**: canonical support orderをAPI契約にする。
- **No-claim passthrough (17)**: no support/formula entryを`Unclaimed`とし、heap allocationを
  要求しない。
- **No permanent evaluation memo (22)**: round終了時にmemoを破棄する。
- **Diagnostic order isolation (23)**: payload orderだけを明示し、explanation graphの
  category/edge/hyperedge order自体はGap 2まで変更しない。

### 11.2 CPK計画§15

- OR/ANDをsupport集合へ潰さず、decisionはformula evaluatorだけが決める。
- mandatory routing/projection dataをbudgetでdropしない。
- `ProjectionProofCarrier::Incomplete`は通常のindependent supportとしてformulaへ
  含め、underlying provenance detailだけをincompleteとして扱う。
- before/afterを同じroundへ混ぜない。
- projectabilityを永続memoしない。
- proof layerはsemantic queue/mapをmutateしない。
- failure attemptからoutputを返さない。

### 11.3 CPK-0追補

- claimed-first、root昇順、independent carrier total orderをそのまま再利用する。
- representative更新でcanonical positionを変えない。
- unordered HashMap iterationをconsumer-visible sequenceへ流さない。
- user-visible provenance/truncation prefixをcanonical orderで固定する。

### 11.4 既存文書とのtension

二つのtensionがあるが、解消不能な矛盾ではない。

1. **旧metadata fail-open**:
   RCPF main文書、MPC、URR-v3の古い記述と現行legacy codeには、欠損metadataを
   projectable / `Unclaimed`側へ倒す規則がある。一方、後発のRCPF quarantine追補と
   CPK計画§12はmandatory failureのwhole-attempt discardを決定した。本書は後発規律を
   CPK production queryへ適用し、局所fail-openをsupersedeする。valid complete stateの
   consumer semanticsは変えない。
2. **empty selected witness assertion**:
   現行generalized witnessにはempty selected parentsを拒むdebug assertionがあるが、
   現行`Qualified`型とformula evaluatorはpayload non-emptyをsigned invariantとして
   保証していない。本書は`Included(empty)`を有効にし、CPK-6b前にfixtureで挙動を固定する。
   raw bound parentへのfallbackは、qualified provenanceをunclaimed provenanceへ変えるため
   採らない。

これ以外に、RCPF 23 invariant、CPK計画§15、CPK-0追補との矛盾は見つからない。

## 12. 本書固有のcorrectness invariants

1. `project_lower`はactive lower recordだけをdomainとする。
2. valid no-ledger / empty-ledgerだけを`Unclaimed`とする。
3. metadata failureを`Unclaimed` / `Included`へ変換しない。
4. `Excluded`はwell-formed graphを評価したfalseだけを表す。
5. `Included`はwell-formed graphを評価したtrueだけを表す。
6. `Included(empty)`を`Unclaimed`または`Excluded`へ再分類しない。
7. payloadは全qualifying supportであり、minimal/first winning witnessではない。
8. claimed payloadはcoverage rootとexact representative claimの両方を保持する。
9. same-root representativeをquery時に再選択しない。
10. independent payloadはexact carrier identityを失わない。
11. claimedを先、independentを後に返す。
12. claimedはcoverage root昇順、independentはfull carrier total orderで返す。
13. query時のHashMap iterationまたはadmission ordinalを返却順に使わない。
14. noncanonical storeをread-time sortでrepairしない。
15. `ProjectionProofCarrier::Incomplete`をmandatory missing-data failureと混同しない。
16. mandatory missing dataを`Incomplete` carrierへ変換しない。
17. support/formula/premise/carrierを同じsnapshotでpreflightする。
18. cycle cutはそのcircular routeだけをfalseにする。
19. cycle cut後のmemoを後続top-level queryへ共有しない。
20. cycle cutまたはshort-circuitでpayloadを削らない。
21. before/after viewを同じroundへ混ぜない。
22. round-local memoをmachine/cacheへ永続化しない。
23. failure後のroundまたはmachineからpartial outputを返さない。
24. owner内semantic lower record orderをsupport canonical orderで並べ替えない。
25. compact / aliasへproof payloadをsolver conditionとして漏らさない。
26. generalized witness parent orderはpayload orderと一致する。
27. `ProjectionProofCarrier::Incomplete`を通常のindependent supportとして
    projectability formulaへ含め、特別に除外またはinert化しない。欠落した
    underlying replay-evidence detailだけを後続provenance completenessへ反映する。
28. retryはattempt単位であり、record/query単位でauthorityを混在させない。
29. organic CPK failureをlegacy retry成功によってparity PASSにしない。
30. 本queryはsemantic queue、SCC、generalization coreを変更しない。

## 13. Stop conditions

実装またはshadow parityで次を観測した場合、consumer cutoverへ進まず本書へ戻る。

1. 4 consumerのいずれかが、§3のpayloadにないproof identityを必要とする。
2. generalized witnessがall-supportではなくwinning-clause-only payloadを必要とする。
3. valid complete stateでlegacyとCPKのclaim/carrier集合またはsequenceが異なる。
4. same-root representative claimをcanonical storeから一意に得られない。
5. `coverage_root`だけではcanonical orderが定まらないvalid stateが見つかる。
6. `carrier_cmp`が異なるexact carrierをequalと判定する。
7. `Included(empty)`がraw `Bound(record)` parentなしでは既存observable outputを
   再現できない。
8. empty `Included`の扱いがgeneralized witness completenessを未定義にする。
9. optional `Incomplete` carrierとmandatory missing carrierを識別できない。
10. complete stateでsupportに対応するformulaが存在しないvalid caseが見つかる。
11. formulaがsupportなしで存在するvalid caseが見つかる。
12. row/reduction opaque handleを解決するためsemantic coreへproof内容を漏らす必要がある。
13. cycle cut後のfresh evaluationとshared roundでdecisionまたはpayloadが異なる。
14. project_lowerのfallible collectがpartial outputをconsumerへ公開する。
15. ProofFailureを既存attempt failure channelへ接続できず、局所fallbackが必要になる。
16. clean retryがsame machineのpartial CPK memo/outputを再利用する。
17. outer record order、compact root、alias sequence、witness parent sequenceが変わる。
18. no-claim pathにheap allocationまたはproof graph traversalが増える。
19. std loweringでqueryごとのclone/sortが新しいhot spotになる。
20. Gap 1実装がGap 2/3の未決定を暗黙に固定し始める。

stop conditionに該当した場合、fixture期待値、failure mapping、canonical orderを
実装出力へ合わせて変更してはならない。原因を特定し、必要なら本書を改訂して
再承認する。

## 14. Gap 2 / Gap 3への境界

### 14.1 Gap 2: explanation / portable provenance

Gap 2は本書の次を再利用してよい。

- `ProjectionClaimSupport`のroot / representative identity
- exact `ProjectionProofCarrier`
- canonical support order
- `ProofFactRef` / `ProofFailure`
- mandatoryとoptional incompleteの区別
- attempt-level failure

ただし次はGap 2で別途決定する。

- explanation node / edge / hyperedgeのquery result shape
- 5 lineage attributionのexport shape
- portable session/generation ID mapping
- budget truncationとstable prefix
- source-location resolution failure
- diagnostic category order

### 14.2 Gap 3: invalidation query

Gap 3は本書の次を再利用してよい。

- same-snapshot projection decision
- separate before/after rounds
- `ProofFailure`とattempt terminal policy
- canonical owner identity vocabulary

ただし次はGap 3で別途決定する。

- before/after projection planのexact type
- affected owner dedup/order
- metadata-only / inclusion-flip / no-op class
- epoch/publication intentとcommit boundary
- failure時のpending publication破棄

本書はGap 2/3のproduction cutoverを認可しない。

## 15. 波及する文書

本書がClaude査読とユーザ承認を経て正本になった後、必要に応じて次へ参照を
追加する。

- `notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md`
  - §10.2から本書を参照する。
  - CPK-6のGap 1 prerequisiteが解決したことを記録する。
- `notes/design/2026-08-05-cpk-0-projection-admission-addendum.md`
  - §7のcanonical support orderがread-side payloadにも適用されることを記録する。
- `notes/design/2026-08-02-rcpf-quarantine-retry-authority-addendum.md`
  - 変更不要。本書§6がattempt-level failure precedentとして参照する。
- `notes/architecture/claim-propagation-architecture.md`
  - legacy `SchemeProjectableLowerReason`の将来置換先として本書を参照する。

これらの文書更新は本書本文のdraftとは別変更として扱う。

---

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定

状態: **ユーザ承認済み（2026-08-06）**

Claudeは、§4.4のempty `Included`、§5のformula/support closure、§6のfailure
variantと既存attempt channelの接続、§7のround lifetimeを再検証し、Codex
gpt-5.6-terraによる独立fact-checkで発見された`ProjectionProofCarrier::Incomplete`
分類の矛盾を修正した上で、ユーザの承認を得た。本書はGap 1のAPI・oracle・
failure contractの正本であり、CPK-6b consumer cutover自体は別途Slice A/B完了後に
判断する。
