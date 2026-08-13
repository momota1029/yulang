# CPK-SV-C 追補: dynamic dependency の単一 owner 化と late-bound validation obligation

日付: 2026-08-13

状態: **ユーザ承認済み（2026-08-13、rev.2）**

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定

**署名についての注記**: 上記は本リポジトリの Fable 5 不在時の起案手続を示す。
Codex Sol による起案後、fresh independent adversarial review はcore architectureを
`SOUND WITH GAPS`と判定し、(1) semantic publication用reverse mapの保存範囲、(2) support-ledger
closure、(3) frozen/current divergenceとcanonical fallbackの非対称性、の3点を指摘した。rev.2は
その全てを反映し、Claude (Sonnet 5) が全文を独立に読み直して最終査読・確定した。この領域は
CPK-SV-C初版から数えて実装レビュー3回・設計レビュー1回・本rev.2確認の計5回の吟味を経ている。
2026-08-13、ユーザが本書の内容（single-owner化 + late-binding設計、3 gapの修正内容、
implementation slices R0〜R3の構成を含む）を確認し、承認した。本書はここに正本文書として確定し、
CPK-SV-C-R0以降の実装に着手してよい。

本書は、ユーザ承認済みの
`notes/design/2026-08-12-cpk-preflight-structural-validity-addendum.md`
（以下 CPK-SV 追補）のうち、§3.4、§5.2、§8.2、§9 CPK-SV-C、およびそれらに
依存する stop condition を精密化・一部置換する addendum-to-the-addendum である。

CPK-SV-A の admission-time structural certificate と、CPK-SV-B の order-error authority
cutover は維持する。本書が変更するのは、CPK-SV-C が formula bucket へ materialize して
いた **current claim location / current coverage-root location / current live-row state** の
ownership と同期方式だけである。

本書は、CPK 計画
`notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md`
§9.2 の fallible prepare / infallible commit、one-event atomicity、failed attempt から output を
返さない規則を継承する。

## 0. 決定の要約

1. 現行 CPK-SV-C の「formula admission が claim/live-row を snapshot し、claim/live-row
   lifecycle が dependent formula records を snapshot する」双方向 materialization を廃止する。
2. Formula bucket は、可変な `BoundRecordId` や live row-state ID のコピーを永続 adjacency
   に持たない。代わりに、formula incidence だけから決まる安定した
   `ClaimBinding(representative, expected_root)` と `CoverageRootState(expected_root)`を持つ。
   さらに既存のrecord単位support-ledger preflight stageへ`SupportLedgerClosure(record)`検査を
   組み込み、formulaとの双方向closureを必須にする。
3. Claim location と live-row state は、それぞれ既存の claim store と
   `live_states_by_coverage_root` だけを正本とする。preflight は stable obligation を実行する
   時点で current state を正本から読む。
4. Claim move と live-row activation/deactivation は formula adjacency を一切更新しない。
   従ってCPK-SV-C validation-adjacency専用dependent-record reverse map、cross-owner prepared
   snapshot、remove/rekey fanoutは不要になる。
5. `ProofStructuralSnapshotId` は CPK-SV-D の successful-validation cache invalidation に用いる。
   adjacency writer 間の同期・競合解消には用いない。
6. Formula prepare/commit の stale base は、typed commit result と terminal failure/whole-attempt
   discard で明示的に伝播する。`commit_projection_clause_admission` が silent `return ()` する
   契約を禁止する。
7. Caller は prepared intent ではなく、**成功した commit が返す receipt** の accepted clauses
   だけから premise/dependency secondary index を publish する。
8. 本設計は fresh consequence、formula clause、claim、live row state を減らさない。削減する
   のは cross-owner duplicate state と、CPK-SV-C validation-adjacency保守のためだけに行う
   lifecycle時のdependent-record fanoutだけである。semantic projectability/publication用の
   `projection_lower_records_by_root`は削減・retireしない。

## 1. 本追補が必要になった経緯

### 1.1 三回の独立レビューが示した同一根因

CPK-SV-C は当初、formula incidence から得る static action と、claim/live-row の current state
から得る dynamic leaf action を同じ `ProjectionDependencyAdjacency` へ materialize した。
その後の三回の独立 adversarial review は、順に次を発見した。

1. **意味 identity の不足**
   - carrier existence と recursive closure が同じ constraint action に畳まれていた。
   - claimed support が読む current bound と live row reduction が action 集合に存在しなかった。
   - replay lower/upper side が identity から落ちていた。
2. **Formula 側から dynamic authority を snapshot する race と writer bound 違反**
   - formula prepare 後、commit 前に claim move / row liveness が変わると、stale leaf action を
     publish できた。
   - live states ごとの `Vec::contains` により O(N²) work が生じた。
   - claim move が全 dependent records を走査した。
3. **Dynamic authority 側から formula dependents を snapshot する反対向きの race と silent loss**
   - claim/live-row prepare 後、commit 前に formula dependency が追加されると、新しい formula
     record が lifecycle delta から漏れた。
   - formula commit が staleness を検出したとき silent `return ()` し、caller はその後も
     `prepared.accepted()` を処理した。formula clause が未 commit のまま premise/dependency
     secondary index だけが publish され得た。

各 finding は局所的には異なるが、すべて「同じ論理 dependency を二つの transaction owner
が current-value leaf として複製している」ことから生じた。

### 1.2 最も重大な現行 failure

current HEAD `520c332b` の
`ProofOccurrenceStore::commit_projection_clause_admission` は、次の二つを検出すると mutation
前に `return` する。

- prepared formula structural base と current bucket base の相違。
- prepare 時の claim/live-row snapshot と commit 時の current state の相違。

しかし戻り値は `()` であり、commit の成否を表さない。
`ConstraintMachine::commit_record_proof_clause_link_batch_mutation`
（`crates/infer/src/constraints/machine/bounds.rs`）は commit 呼出し後、無条件に
`prepared.accepted()` から inserted clauses を集め、premise dependency と projection index を
更新する。

従って現行契約では、次が同時に起き得る。

```text
formula bucket       : clause は未 commit
prepared intent      : accepted のまま
secondary dependency : accepted を根拠に publish
caller               : failure を観測できない
```

これは cache miss や shadow mismatch ではなく、mandatory proof relation の silent data loss と
secondary-index divergence である。本書では最優先で禁止する。

## 2. 現行 transaction / authority census

### 2.1 Adjacency membership を変え得る transaction family

current code で adjacency の persistent membership を直接または間接に変え得る family は次の
四つである。

| transaction family | 正本 mutation | 現行 adjacency への作用 | 本来の owner |
|---|---|---|---|
| formula clause/link admission | formula entry/support/exact link/canonical run | static action追加、claim/root snapshot、reverse dependency登録 | formula bucket |
| upper-claim admission/publication | claim occurrence生成、coverage root/producer/current record固定 | formula prepare と claim commit の間に初回dynamic leafを出現させる | upper-claim store |
| upper-claim move | `UpperClaimOccurrence::current_record` と record index更新 | 全 dependent formula record の `ValidateBound` rekey | upper-claim store |
| live-coverage activation/deactivation | `(root,state)` と `live_states_by_coverage_root`更新 | 全 dependent formula record の `ValidateRowReduction` insert/remove | live-coverage store |

補足:

- production で claim の `coverage_root`、producer、lineage を claim admission 後に書き換える
  writer は見つからない。`coverage_root` の直接変更は test corruption hook に限られる。
- row reduction record の内容、bound/constraint の存在・tombstone、carrier occurrence 等も
  validation result を変えるが、adjacency **membership shape** を変えない。これらは
  CPK-SV-D の `ProofStructuralSnapshotId` invalidation 対象であり、本書の cross-writer
  adjacency synchronization 対象ではない。
- production formula relation は append-only である。将来 removal/rekey を導入する場合は、
  source refcount/exact-source relation が別途必要になる。

### 2.2 実行モデル

これらは複数 thread が同時に同じ store を mutate する並列 transaction ではない。
すべて一つの constraint-solving loop から、exclusive `&mut ProofOccurrenceStore` を通して同期的に
呼ばれる。

ただし「真の並列でない」ことは prepared snapshot が安全であることを意味しない。
prepared object は borrow を保持せず、prepare と commit の間に別の同期 commit を挟める。
実際、upper-claim admission path には次の正規順序がある。

```text
prepare formula clause
prepare claim
commit claim
commit prepared formula clause
```

また test/non-standard path は、二つの formula transaction を同じ revision から prepare した後に
順番に commit できる。従って本システムの concurrency は thread parallelism ではなく、
**明示的に露出した prepare/commit の間へ別 family の commit を挟める logical interleaving**
である。

このモデルでは mutex/atomic CPU primitive は不要だが、prepared delta が何を観測し、何を
commit 時まで不変と要求するかを API で閉じなければならない。

### 2.3 現行の二方向 snapshot

現行実装は両方向に derived state を複製する。

```text
formula prepare
    -> claim occurrence/current_record/live states を snapshot
    -> current Bound/Row leaf actions を formula adjacency に書く

claim move / live-row prepare
    -> reverse map から dependent formula records を snapshot
    -> 各 formula adjacency の leaf actions を remove/rekey/insert
```

一方向の stale check を追加すると、反対方向の window が残る。

```text
F.prepare -- M.commit -- F.commit    // formula snapshot が stale
M.prepare -- F.commit -- M.commit    // dependent-record snapshot が stale
```

両方へ generation check を付けても、stale を検出した後に必要な capacity と reconciliation を
どう再prepareするか、既に commit した sibling mutation をどう扱うか、caller がどう failure を
伝播するかは解決しない。

## 3. 根因診断

### 3.1 Snapshot-and-check 自体が不可能なのではない

serializable transaction として、全関係する version を読み、全 write set の capacity を
preflightし、commit 時に全 version を検査し、conflict を caller へ返して whole transaction を
retry/discardすれば、snapshot-and-check でも理論上は成立する。

しかし現行 adjacency では write set が次のように相手側の future state に依存する。

- formula admission の write setは、claim locationとその時点の全live statesに依存する。
- claim move/live transition の write setは、その時点の全dependent formula recordsに依存する。

従って正しい serializable transaction を作るには、formula、claim、live coverage、reverse map、
各record adjacencyを一つの transaction coordinator で同時にlock/version/preflightする必要がある。
これは単一-thread環境に対して過大であり、O(validation-adjacency dependents) lifecycle fanoutも
温存する。

### 3.2 三回失敗した本質

本質は **ownership が一つの関係に対して分裂していること** である。

`ValidateBound(current_record)` と `ValidateRowReduction(current_state)` は formula incidence の
不変事実ではない。claim/live-row authority の current view から導出される値である。それを
formula-owned persistent indexへコピーしたため、次の二つが同時に必要になった。

1. formula writer が dynamic authority の current value を知ること。
2. dynamic authority writer が formula dependents を知り、全コピーを更新すること。

どちらか片側だけを強化すると、もう片側の prepared window が漏れる。これは「checkをもう一つ
足せばよい」問題ではなく、derived current value を二つの owner が永続化する設計の問題である。

### 3.3 単純な sequencing fix だけでは足りない理由

Formula prepare と commit を連続呼出しにして interleave を禁止すれば、formula側の stale window
は閉じる。しかし claim move/live transition は依然として全dependent formula adjacencyを更新
するため、lifecycle prepare と新formula commitの順序問題が残る。

逆に lifecycle commit を連続化しても、formulaがprepare時のdynamic stateをmaterializeする限り、
claim admissionをformula prepareとcommitの間に挟む既存の正規transactionを扱えない。

従って必要なのは sequencing の局所修正ではなく、**current dynamic leafを一方のownerへコピー
しない表現** である。

## 4. 選択する設計: stable obligation + authoritative late binding

### 4.1 Formula-owned adjacency の責務

Formula bucket が永続化するのは、formula incidence だけから決まり、その incidence が存在する
間は変化しない validation obligation に限定する。

概念型は次のとおりである。実装時の名称は変更してよい。

```rust
enum ProjectionValidationAction {
    // 既存のformula-owned static actions。
    ValidateRecord { /* exact role/side/carrier identity */ },
    ValidateConstraint { /* existence/recursive role */ },
    ValidateIndependentSupport { /* exact carrier */ },
    ValidateRowDerivation(RowDerivationId),
    ValidateOrigin(OriginId),
    ValidateGeneralizedWitness(GeneralizedSchemeWitnessId),
    ValidateCarrierOccurrence(ProjectionProofCarrier),

    // current leafではなくstable dynamic obligation。
    ValidateClaimBinding {
        representative: UpperReplayClaimId,
        expected_root: UpperReplayClaimId,
    },
    ValidateCoverageRootState {
        expected_root: UpperReplayClaimId,
    },
}
```

`expected_root` は commit 時の mutable claim lookup から取らない。exact incidence の
`ClaimedProjectionProofSource` / `ProjectionIncidenceMetadata` が凍結した event-time root を使う。

Claimed support `representative -> expected_root` は、少なくとも次の二obligationを生成する。

```text
ValidateClaimBinding(representative, expected_root)
ValidateCoverageRootState(expected_root)
```

`ProofPremise::RootCoverage(root)` は次を生成する。

```text
ValidateClaimBinding(root, root)
ValidateCoverageRootState(root)
```

同じrootを複数representative/clauseが参照する場合、claim bindingはrepresentativeごとに残し、
root-state obligationだけをroot単位でdedupする。これにより代表claim identityを粗化せず、
root current bound/live statesの重複走査を除ける。

現行actionとの置換境界は明示する。

- claimed supportの`ResolveSupport(Claimed(..))`と`ValidateRoot(..)`は、上記二obligationへ
  置換する。fast executorが旧`resolve_support(Claimed)`を追加で呼び、dynamic readを二重実行して
  はならない。
- independent supportだけが`ValidateIndependentSupport(exact_carrier)`相当のstatic actionを持つ。
- `ClaimRepresentative` / `CoverageRoot` roleのcurrent `ValidateBound`と、live state由来の
  `ValidateRowReduction`はpersistent actionからretireする。
- replay carrierがformula内に固定しているlower/upper bound、row derivation等のstatic identityは
  dynamic claim stateではないため従来どおり残す。
- `ValidateSupportLedgerClosure(record)`はpersistent actionを一件追加する型ではなく、既存の
  record単位support-ledger preflight stageを精密化する概念名とする。Formulaのfrozen normalized
  support keysとcurrent support ledgerの双方向closureをexactly once検証し、個々のclaimed
  supportを`ResolveSupport(Claimed(..))`で二重検証しない。これによりno-claim workloadへ新しい
  persistent allocationを加えない。

### 4.2 Late-bound execution semantics

`ValidateClaimBinding { representative, expected_root }` はquery snapshotで次を行う。

1. representative claimが存在することを検証する。
2. representativeのcurrent `coverage_root == expected_root`を検証する。
3. representativeのcurrent `BoundRecordId`をclaim authorityから読み、そのbound referenceを
   検証する。

`ValidateCoverageRootState { expected_root }` はquery snapshotで次を行う。

1. root claimが存在し、`claim == coverage_root == expected_root`であることを検証する。
2. root claimのcurrent `BoundRecordId`をclaim authorityから読み、bound referenceを検証する。
3. `live_states_by_coverage_root[expected_root]`の**現在存在するstateだけ**を明示cursorで列挙する。
4. 各indexed stateについてflat `live_coverage` occurrenceとの整合とrow-reduction factの存在を
   検証する。indexにあるstateがflat setに無い場合はpanic/assertせず、
   `ProofFailure::IncompleteMandatoryData { owner: ProofFactRef::LiveCoverage(expected_root),
   field: MandatoryProofField::LiveCoverage }`相当のtyped canonical failureを返す。

永続adjacencyにはcurrent bound IDもcurrent row-state IDも入らない。従ってclaim moveや
activation/deactivation後もobligation identityは変化しない。

### 4.3 Support-ledger closure

現行canonical preflightはformulaだけを検証しない。先にcurrent
`projection_supports[record]`をresolveし、その後formula incidenceのsupportを同じresolved identityへ
写して、次の双方向closureを検証する。Current HEAD `520c332b`では
`crates/infer/src/constraints/proof/mod.rs:10412-10429`がこのformula→ledger matchと最終unmatched
ledger checkを行う。

```text
formula resolved key ∉ resolved support ledger
    -> ProjectionInvariantViolation::OrphanFormula

resolved support-ledger keyがformula走査後もunmatched
    -> MissingProofFact(ProjectionFormula(record))
```

Stable-obligation pathもこのstageを残す。`ValidateSupportLedgerClosure(record)`と呼ぶrecord-local
stageはpersistent adjacency entryではなく、次を行う。

1. current support ledgerを現行と同じcanonical順でresolveし、duplicate claimed root、duplicate
   independent carrier、dangling support、support order failureを従来どおり検証する。
2. Formula bucketのfrozen `normalized_support_keys`とcurrent resolved ledger keysを双方向比較する。
3. success pathではset equalityだけを答える。mismatch時はerrorを直接作らず、§4.4のcanonical
   pathを実行してformula cursor順の`OrphanFormula`、またはledger順の`MissingProofFact`を返す。

比較はquery-localなinfallible `collect`を新設しない。既存preflightがfallibleに確保するresolved
support bufferとmatched bufferを再利用するか、二つのcanonical cursorを用いる。Formula bucketが
structurally validでも、このclosure成功なしにrecordをstructurally validとしてcacheしてはならない。

`normalized_support_keys`はclosureの高速membership sourceであり、formula/exact link authorityを
置き換えない。missing/dirty certificateやcorruption時のcanonical pathはformula cursorから
実際のfirst errorを再構成する。

### 4.4 Frozen/current divergence と canonical fallback

現行legacy `resolve_claim`はrepresentativeの**current** `coverage_root`を辿るだけで、incidenceが
凍結した`expected_root`と比較しない。従って単純に「fast failureを捨て、旧legacy resultだけを
返す」と、representativeがAから別のvalid root Bへcorruptされた場合にfast pathだけが見つけた
real invariant violationを消せる。

本書はcanonical validation自体を精密化する案を採る。Canonical formula cursorは各exact incidenceの
`ProjectionIncidenceMetadata`からfrozen `expected_root`を取得し、claimed formula supportをresolveする
ときに次を同じ順序で検証する。

1. representative claimの存在。
2. `representative.coverage_root == expected_root`。
3. current representative/root boundとlive-row relation。
4. resolved support-ledger closure。
5. clause/premise validation。

2が失敗した場合は既存typed
`ProofFailure::ProjectionInvariantViolation { record, kind:
ProjectionInvariantViolation::RepresentativeRootMismatch }`を返す。これはnormal writerが到達させない
corruption invariantの明示化であり、正常系の意味やfresh consequenceを変更しない。

Fast stable-obligation failureは常に、この**精密化済みcanonical path**へfallbackする。
Canonical pathは`ValidateClaimBinding`、`ValidateCoverageRootState`、record-local
`ValidateSupportLedgerClosure` stageが検査する全semantic invariantを同じsnapshotで検査しなければ
ならない。
従ってfrozen/current divergenceはcanonicalでも必ずfailureとなり、fast-only failureとして捨てられ
ない。

Error precedenceは次を維持する。

1. certificateがmissing/dirtyなら`NonCanonicalProjectionOrder`のorder-only passが最初。
2. current support ledgerのresolve/order/existence failure。
3. canonical formula cursor上のfrozen/current mismatch、closure mismatch、clause validation failure。
4. cursor終了後のunmatched ledgerによる`MissingProofFact`。

Indexed live stateがflat setに無いケースも同じcanonical `resolve_claim`/root-state helperでassertから
§4.2のtyped `IncompleteMandatoryData`へ変換する。Fast pathだけがpanicを回避し、fallback側がpanic
する非対称を残さない。Current HEADの該当assertは
`crates/infer/src/constraints/proof/mod.rs:10505-10508`にある。

精密化済みcanonical pathがfast failure後に成功した場合、そのfailureはunderlying proof stateでは
なくderived adjacencyのextra/corruptionである。productionはcanonical successをsemantic resultとし、
そのquery/snapshotでfast adjacency/cache publicationを無効化する。test/shadow/full-workload oracleは
これをmismatchとして必ず報告し、SV-D authority cutover前のstop conditionとする。

### 4.5 Exact identity と invariant 26/27 の精密化

CPK-SV 追補 invariant 26の「legacy validation action集合とのexact parity」は、dynamic leaf ID
のpersistent集合が常時同じであることではなく、**一つの固定snapshotでobligation cursorを
展開して得るdistinct typed validation obligation集合が、§4.4で精密化したcanonical preflight
traceを同じtyped identityへ正規化・重複除去した集合と一致すること** と精密化する。raw call
回数の一致は要求しない。raw clauseが同じobligationを繰り返すことを除くのがadjacencyの目的
だからである。

次を粗化してはならない。

- representative claim。
- expected coverage root。
- constraint existence / recursive closure role。
- replay lower / upper sideとcarrier。
- structural/reduction lineage、row derivation、origin、witness、carrier occurrence。

同一rootを参照する異なるrepresentativeは別の`ValidateClaimBinding`である。一方、同じrootの
current bound/live-state検証は同じvalidation ruleなので、一つの
`ValidateCoverageRootState`へdedupしてよい。

Fast adjacency executionでfailure候補が見つかった場合は、§4.4の精密化済みcanonical validationを
再実行し、そのerror/ownerだけを返す。従ってdedupによりfast pathのowner表現を保存する必要は
ないが、failureをfast actionから直接返すことは禁止する。

### 4.6 Single-owner rule

各persistent stateのwriterを次の一つに固定する。

| persistent state | 唯一の writer |
|---|---|
| formula entries/supports/exact links/runs | formula admission |
| static validation actions/stable dynamic obligations | formula admission |
| claim occurrence/current record/claim indices | claim admission/move transaction |
| live coverage/root→state index | live-coverage transaction |
| structural-validity cache generation | 各relevant transactionがcommit末尾で共通snapshotをbump |

禁止するもの:

- claim moveがformula bucketをremove/rekeyすること。
- live-row transitionがformula bucketへactionをinsert/removeすること。
- formula admissionがclaim/live-row current valuesをpersistent actionとしてcopyすること。
- reverse map `claim/root -> dependent formula records`をdynamic leaf maintenanceのために持つこと。

このruleにより、二つのtransaction familyが同じpersistent adjacency entryを書かない。
「bidirectional synchronization」は、shared mutable copyを同期する機構ではなく、shared copyを
除去し、query snapshotで各single authorityをjoinする形になる。

### 4.7 `ProofStructuralSnapshotId` の役割

Claim admission/move、live coverage change、formula admission、その他CPK-SV追補 §5.4のrelevant
mutationは、CPK-SV-Dで`ProofStructuralSnapshotId`が導入された後、atomic commitの最後に同IDを
一回進める。

これは次を保証するためのgenerationである。

- CPK-SV-Dの`Valid(snapshot)`がclaim move/live-row change後に再利用されない。
- queryが同じcompleted snapshot内でだけ成功を共有する。

これは次には使わない。

- adjacency write setのreconciliation。
- claim moveとformula admissionのlock代替。
- stale prepared formulaをsilentに受理する根拠。

Late-bound obligationは常にcurrent authorityを読むため、adjacency membership同期にshared
generationは不要である。

CPK-SV-C-R0〜R3はproduction validation cacheを導入しない。SV-Cではsnapshot invalidation writer
censusとtest-only bump oracleだけを準備してよいが、`Valid(snapshot)`の保存・参照はSV-Dまで開始
しない。このslice境界は元のCPK-SV追補を維持する。

## 5. Formula transaction API の改訂

### 5.1 Prepared intent と committed fact を型で分離する

現行の`PreparedProjectionClauseAdmission::accepted()`をcommit前後でcallerが読める契約を
廃止する。

```rust
struct PreparedProjectionClauseAdmission {
    // private: intended delta, reserved storage, observed formula base
}

struct CommittedProjectionClauseBatch {
    accepted: Vec<AcceptedProjectionClauseAdmission>,
}

enum ProjectionClauseCommitConflict {
    FormulaBaseChanged,
    CertificateBaseChanged,
}

fn commit_projection_clause_admission(
    &mut self,
    prepared: PreparedProjectionClauseAdmission,
) -> Result<CommittedProjectionClauseBatch, ProjectionClauseCommitConflict>;
```

具体的なerror enum名は実装時に既存`ProofFailure`へ統合してよい。ただし次は必須である。

- commitはpreparedをconsumeする。
- callerがaccepted clausesを取得できるのは`Ok(Committed...)`だけ。
- committed receiptのaccepted storageはpreparedからownership moveし、commit中にclone/allocate
  しない。
- stale/dirty/base mismatchはtyped failureとしてcallerへ届く。
- `Err`時はformula、adjacency、certificate、legacy/test oracle stateのどれも変えない。
- certificateをdirtyにすること自体も、failed commitのpartial mutationとして行わない。
  current bucketが既にdirtyならそのまま、currentならそのまま維持する。

### 5.2 Caller contract

`commit_record_proof_clause_link_batch_mutation`は次の順序にする。

```text
prepared = try_prepare_projection_clause_admission(links)?
committed = commit_projection_clause_admission(prepared)?
for accepted in committed.accepted:
    publish premise/dependency secondary indices
return snapshot derived from committed
```

`prepared.accepted`からsecondary stateを作ることを禁止する。

Formula-only transactionでbase conflictが起き、まだ他のsemantic mutationをcommitしていない場合は、
元のinput linksからclean reprepareを行ってよい。retry回数はboundedにし、通常のsingle-thread
production pathでは0回であることをgateにする。

Claim admissionのようにsibling core/proof mutationを既にcommitした後でformula conflictが発生した
場合、局所retryで誤魔化さない。CPK計画 §9.2/§12どおりwhole-attempt terminal failureとして
出力を破棄する。production coordinatorがprepare後に別formula commitを挟まない限り、この
conflictは到達不能である。到達した場合はprogramming/invariant failureとして可視化する。

### 5.3 Prepare / commit atomicity

Formula prepareは次のcapacityだけをfallibleに確保する。

- canonical formula/static index delta。
- static action delta。
- stable claim/root obligation delta。
- exact membership mapとflat nonempty action storage。
- structural certificate delta。

Claim current record数、live-state数、dependent formula record数に応じたcapacityは確保しない。
それらをpersistent formula deltaへmaterializeしないためである。

Commitはformula baseを再確認した後、予約済みdeltaだけをallocation-freeでpublishする。
certificate/revisionは最後にpublishし、その後に`CommittedProjectionClauseBatch`を返す。

## 6. Claim / live-row lifecycle transaction の改訂

### 6.1 Claim admission / move

Claim admissionとmoveは既存claim occurrenceおよびclaim indicesだけを更新する。

- `projection_validation_records_by_claim`を読まない。
- CPK-SV-C validation-adjacency dependent record listをsnapshotしない。
- formula adjacencyをremove/rekeyしない。
- CPK-SV-D landing後は、`current_record`変更をcommitした最後にstructural snapshotを一回bump
  する。SV-Cではそのwriter census/test hookまでに留め、cacheを導入しない。

Formulaがclaim publication前にpreparedされ、claim commit後にformula commitされる既存順序でも、
formula deltaはstable `(representative, expected_root)`しか持たないためstaleにならない。

### 6.2 Live coverage activation / deactivation

`ProofOccurrenceStore`内のlive-row authority transactionは`live_coverage`と
`live_states_by_coverage_root`だけをtransactionally更新する。その後にmachine-level
`record_scheme_projection_liveness_mutation`が行うsemantic projectability/publicationは別責務として
維持する。

- CPK-SV-C validation-adjacency更新のためにdependent formula recordsを列挙しない。
- per-record `ValidateRowReduction`をinsert/removeしない。
- activationのhash storageをprepareでfallibleにreserveする。
- commitはallocation-freeでauthoritative setを更新する。CPK-SV-D landing後は最後にsnapshotを
  一回bumpするが、SV-Cではそのwriter census/test hookまでに留める。

Query時の`ValidateCoverageRootState`がcurrent setを列挙するため、formulaがactivationの前後どちらに
commitされても同じcompleted snapshotを観測する。

### 6.3 Reverse maps の扱い

次のcurrent CPK-SV-C専用構造はretire対象である。

- `projection_validation_records_by_claim`。
- `projection_validation_claim_memberships`。
- claim moveの`PreparedProjectionValidationActionRekey`。
- live coverageのper-record `validation_action_mutations`。
- formula prepareの`ProjectionClaimDependencySnapshot`とcommit-time dynamic refresh。

他のproduction consumerが同じmapを必要とすることがcensusで判明した場合は、目的とidentityを
別名のauthorityとして設計し直す。CPK-SV-C dynamic leaf maintenanceのためだけに温存しては
ならない。

一方、次は**retire対象ではなく、本書のscope外として現行semanticsを維持する**。

- `projection_lower_records_by_root`。
- そのexact membership companionである`projection_lower_record_memberships`。
- `record_scheme_projection_liveness_mutation`がこれらとroot-coverage premise dependencyから集める
  semantic projectability/publication dependents。

`projection_lower_records_by_root`はsupport ledgerがclaimed rootへ属するlower recordsを表し、live
coverage transition後のsemantic projectability/publicationを再評価するためのproduction-essential
reverse mapである。CPK-SV-C adjacencyのcurrent bound/row leaf copyを同期する
`projection_validation_records_by_claim`とはownerも目的も異なる。本書の「dependent-record visit
zero」は、常に**CPK-SV-C validation-adjacency bookkeeping由来のvisitだけ**を指し、このsemantic
publication fanoutをゼロにする主張ではない。

## 7. Correctness argument

### 7.1 Completed-state observation

全production mutationはexclusive `&mut ProofOccurrenceStore`で同期的にcommitされる。
Preflight queryはmutation commitの途中に同じstoreを読むことができない。従ってqueryは必ず
次のどちらかを観測する。

- mutation前のcompleted snapshot。
- mutation後のcompleted snapshot。

Late-bound obligationはquery開始後に別threadから変更されない。真のparallel read/writeを将来
導入する場合、本書のargumentは成立しないため、immutable snapshot/lock/MVCCの新設計が必要に
なる。

### 7.2 Interleaving case analysis

#### Formula prepare → claim move → formula commit

Prepared formulaはrepresentative/root IDだけを持ち、old current recordを持たない。
Formula commit後のqueryはclaim authorityからnew current recordを読む。stale leafは存在しない。

#### Claim-move prepare → formula commit → claim-move commit

Claim-move prepared deltaはCPK-SV-C validation-adjacency dependent formula recordsを持たない。
move commitはclaim authorityだけを更新する。新formulaも旧formulaもquery時にnew current recordを
読む。missing adjacency dependentは生じない。

#### Formula prepare → live transition → formula commit

Prepared formulaはlive statesを持たない。queryはtransition後のcurrent root setを読む。

#### Live-transition prepare → formula commit → live-transition commit

Live-transition deltaはCPK-SV-C validation-adjacency dependent formula recordsを持たない。
transition commit後、すべてのformula bucketのroot obligationが同じcurrent setを読む。
`projection_lower_records_by_root`を用いるsemantic publication fanoutは従来どおり別段で実行する。

#### Formula A/Bを同じbaseからprepare → A commit → B commit

これはdynamic dependency raceではなくformula base conflictである。B commitはtyped `Err`を返し、
Bのcommitted receiptを生成しない。callerはB intentからsecondary stateをpublishできない。
clean retryまたはwhole-attempt failureだけが許される。

#### Claim/root corruption hook

Formula certificateはbucket-internal frozen relationだけを証明する。queryのstable obligationが
representative/current root mismatchを検出し、fast failureからcanonical fallbackへ移る。
corruptionをcertificate-validityだけで隠さない。

### 7.3 No-missed-dependency proof

あるformula incidenceがclaimed supportを持つとする。admission constructorはexact sourceから
`(representative, expected_root)`を必ず得る。Formula commitはそのpairとroot obligationを同じ
atomic deltaでpublishする。

Claim moveはpairのどちらのIDも変えない。Live transitionもroot IDを変えない。従ってincidenceが
存続する限り、obligationは存続する。

Queryはobligationからcurrent claim/root/live state authoritiesを辿るため、そのsnapshotで存在する
すべてのmandatory dynamic factを読む。逆に過去snapshotにしか存在しないold bound/row stateは
adjacencyに保存されないため読まない。

Dynamic readの完全性だけではformula/support-ledger closureの完全性を証明しないため、recordごとに
`ValidateSupportLedgerClosure`を必須とする。Current support ledgerをresolveしたkey集合を`L`、
formula bucketのfrozen normalized support key集合を`F`とする。

- `F - L != ∅`なら、canonical formula cursorで最初の該当incidenceを選び`OrphanFormula`を返す。
- `L - F != ∅`なら、formula cursorを完走してもunmatchedな最初のledger supportを根拠に
  `MissingProofFact(ProjectionFormula(record))`を返す。
- `F == L`でも、各claimed incidenceの`representative.coverage_root == expected_root`を別途検証する。
  Root keyが偶然同じ、または別のvalid rootへ移ったことをset equalityで隠さない。

従って、(a) formula incidence由来のstatic dependency、(b) late-bound claim/root/live dependency、
(c) formulaとcurrent support ledgerの双方向closure、の三者が揃ったときにだけrecord validationを
successとする。Formula/lifecycleのcommit順にかかわらず、current snapshotの精密化済みcanonical
validationが読むmandatory relationとstable-obligation executionは一致し、wrong/unrelated claimの
formulaをstructurally validとして受理しない。

### 7.4 CPK-SV-A certificate との関係

`ProjectionStructuralCertificate::support_relation_valid`が証明する対象を明確にbucket-localへ限定する。

- exact incidence metadataのfrozen `expected_root`。
- support groupの`match_key == Claimed(expected_root)`。
- exact link/support group/entryの内部整合。

current claim occurrenceの`coverage_root`がexpected rootと一致することはexternal semantic factであり、
certificateの対象ではない。これは`ValidateClaimBinding`がquery snapshotで検証する。

従ってclaim move/live transitionはformula revision/certificateをdirtyにしない。direct formula
corruptionやinternal support relation corruptionは従来どおりdirty/fallback対象である。

### 7.5 CPK-SV-B order authority との関係

Canonical orderはformula bucket内部だけで決まるため、本書はSV-Bのcertified order-pass skipを
変更しない。

- certificate current: order-only passをskip。
- certificate missing/dirty/mismatch: legacy order-only passを先に実行。
- stable obligationまたはsupport-ledger closure failure: §4.4の精密化済みcanonical validation
  fallbackを実行し、そこで確定したerror/ownerを返す。

`NonCanonicalProjectionOrder`の優先順位は本書でも最優先gateである。

## 8. Complexity / allocation bound

### 8.1 Formula admission

一つのnew exact incidenceが追加するpersistent workは、定数個のstatic actionとstable obligationに
限定する。各insertはexact membership finite mapのamortized O(1) lookupとflat appendである。

```text
writer work = O(new exact incidences × bounded actions per incidence)
```

既存record-wide action列のshift/resort、claimのlive-state数、claimのdependent-record数に比例する
workを禁止する。Formula relationがappend-onlyである間、remove/refcountは不要である。

### 8.2 Claim move / live transition

CPK-SV-C validation-adjacency関連のwriter workはどちらもO(1)である。

```text
claim move CPK-SV-C validation-adjacency work
    = 0 validation-adjacency dependent-record visits
live transition CPK-SV-C validation-adjacency work
    = 0 validation-adjacency dependent-record visits
```

Claim自身のrecord index更新とlive set自身のhash insertion/removalは残るが、これは正本mutationの
必要workである。Live transition全体には、scope外の`projection_lower_records_by_root`等からsemantic
projectability/publication dependentsを列挙する既存workが残る。このworkを上記0件gateへ含めない。

### 8.3 Query

```text
query work = O(real static actions
             + distinct claim bindings
             + distinct coverage roots
             + current live states of those roots
             + distinct resolved support/formula keys)
```

`ValidateCoverageRootState` cursorは存在するroot entryとlive statesだけを訪れ、
category×support×root×rowのempty Cartesian productを作らない。query-local collect/sortを禁止する。

### 8.4 Allocation fallibility

- Persistent action/obligation storageはformula prepareで`try_reserve`する。
- Claim/live authoritative containersは各lifecycle prepareで`try_reserve`する。
- Query cursorは既存slice/hash-set iteratorをborrowし、dynamic expansionのためのheap allocationを
  行わない。
- ID conversion (`usize -> u32`) はprepareで検査する。
- commit中の`.entry().or_default()`、unreserved `push/extend/collect`を禁止する。

## 9. 更新後の implementation slices

本書が承認された場合、current CPK-SV-Cを次の小sliceで閉じる。各sliceは独立commit/revert可能に
する。

### CPK-SV-C-R0: commit receipt / silent-loss barrier

目的: representation変更より先に、silent data loss経路を閉じる。

- `PreparedProjectionClauseAdmission`をconsumeするtyped commit resultを導入する。
- accepted dataを`CommittedProjectionClauseBatch`だけから公開する。
- bounds batch caller、claim admission caller、test helperを全censusし、prepared intentをcommit後の
  factとして使う経路をゼロにする。
- stale formula-base fixtureでcommit `Err`、formula mutationゼロ、secondary publicationゼロを
  確認する。
- sibling mutation後のconflictはwhole-attempt terminal failureとなり、部分outputを返さない。

Gate:

- silent `return ()` zero。
- failed commit receipt zero。
- failed commit後のpremise/projection secondary insertion zero。
- allocation/error precedence parity。

### CPK-SV-C-R1: stable obligation shadow

目的: formula-owned shadow adjacencyをcurrent leafからstable obligationへ置換する。

- claimed support/root coverageからexact `(representative, expected_root)`とroot obligationを構築。
- 既存record単位support-ledger preflightへ`ValidateSupportLedgerClosure` stageを組み込み、current
  resolved support ledgerとformula frozen normalized support keysの双方向closureをshadow検証する。
  Persistent adjacency entry/storageは追加しない。
- claimed `ResolveSupport` / dynamic `ValidateRoot` / current claim-bound/live-row leaf actionをstable
  obligationへ置換し、fast pathで二重実行しない。
- canonical formula validationへfrozen `expected_root`照合とtyped live-index/flat-set consistency
  failureを追加し、fast failure fallbackが全stable invariantを検査するようにする。
- structural certificateのsupport relationをfrozen incidence metadataとsupport match keyの
  bucket-local関係としてshadow再検証する。current claim stateをcertificateへ取り込まない。
- current `ValidateBound` / `ValidateRowReduction`をpersistent adjacencyへ追加しない。
- static action identity（constraint role、replay side/carrier等）を維持する。
- production preflightは§4.4で精密化したcanonical validationをauthorityとする。Stable adjacency
  read authorityへのcutoverはSV-Dまで行わない。

Gate:

- full fixtureでfixed-snapshot late-bound expansionとreal refined-canonical traceのmismatch zero。
- support-ledger closureのsuccess/`OrphanFormula`/`MissingProofFact` parity zero mismatch。
- representative A→別のvalid root B corruptionがcanonical `RepresentativeRootMismatch`になり、
  indexed-live-state/flat-set divergenceがpanicせずtyped failureになる。
- no-claim persistent allocation zero。
- 1,800 descending singleton/rekey fixtureでbounded append work。

### CPK-SV-C-R2: cross-writer retirement

目的: bidirectional synchronization stateを物理的に削除する。

- CPK-SV-C validation-adjacency専用claim/root→formula reverse mapsをretire。
- formula-side dynamic snapshots/commit refreshをretire。
- claim-move adjacency rekeyとlive-row per-record action mutationをretire。
- semantic projectability/publication用`projection_lower_records_by_root`と
  `projection_lower_record_memberships`は明示的に保存する。
- lifecycle commitは各authority更新だけにする。SV-D向けsnapshot invalidation writer censusを
  固定するが、production snapshot bump/cacheはSV-Dまで開始しない。

Gate:

- claim moveあたりCPK-SV-C validation-adjacency dependent-record visit 0。
- live transitionあたりCPK-SV-C validation-adjacency dependent-record visit 0。
- live transitionのscope外semantic projectability/publication fanoutはbaseline parity。
- many-formulas × repeated-moves と one-root × many-live-states のwriter scalingがlinear/constant bound。
- capacity-inclusive footprintが旧cross-index以下。

### CPK-SV-C-R3: exhaustive closure gate

目的: CPK-SV-Dがadjacencyをtrustする前に、全order/interleavingを反証可能な形で固定する。

- full-std env-gated exhaustive oracleを実行。
- prepare/commit interleaving matrixを実行。
- dynamic failure/error-owner parityを実行。
- RSS、writer counters、query action distributionを記録。
- 旧materialized leaf oracleやself-comparison helperを削除する。

Gate:

- exhaustive mismatch 0。
- silent-loss fixture 0 secondary writes。
- 18 GiB RSS hard limitから十分離れる。
- independent adversarial review完了。

### CPK-SV-D への接続

CPK-SV-DはR3完了後にだけ開始する。Dのexecutorはstatic actionsとstable obligationsを明示cursorで
実行する。successful validation cacheはcompleted `ProofStructuralSnapshotId`にだけpublishし、
claim/live mutation後は必ずmissする。projectability/cycle resultを保存しない既存規則は不変である。

## 10. Required oracle / fixtures

### 10.1 Independent fixed-snapshot trace oracle

Expected sideはadjacency translation helperを呼ばない。§4.4で精密化した実際のcanonical
`ProjectionPreflight::{resolve_support, resolve_claim, validate_carrier, validate_clause,
validate_record, validate_constraint}`のcall/read siteへtest-only trace sinkを置き、completed snapshotで
実行されたtyped readを収集する。traceはcall-siteのrole/side/representative/current rootを保持し、
stable obligation identityへ正規化した後にexact dedupする。

Actual sideはstable adjacency cursorを実行し、claim/live authoritiesをlate-bound展開したtyped readを
収集し、同じidentityへexact dedupする。

両者をset membershipで比較し、raw yield/call countは性能counterとして別に報告する。writerと
oracleが同じtranslation functionを共有すること、
adjacency自身からexpectedを作ること、carrierの手翻訳matchをvalidation本体の直前へ置くことを
禁止する。

Read-set比較とは別に、support-ledger closure oracleを必須とする。

- Expectedはreal canonical preflightがresolveしたsupport ledger、formula cursor上のresolved
  support、matched flags、最終error/ownerをtraceする。
- Actualはrecord-local`ValidateSupportLedgerClosure` stageが使うcurrent resolved ledger keysとformula frozen
  normalized keysをtraceする。
- exact success、formula-only key (`OrphanFormula`)、ledger-only key
  (`MissingProofFact(ProjectionFormula(record))`)、duplicate/order failureを比較する。
- claimed incidenceごとの`(representative, expected_root, current_root)`も比較し、set-level root
  equalityがrepresentative/root divergenceを隠していないことを確認する。
- indexed live stateがflat setに無いfixtureでは、fast/canonical双方が同じtyped
  `IncompleteMandatoryData`を返し、panicしないことを確認する。

### 10.2 Interleaving matrix

少なくとも次をfixture化する。

1. formula prepare → claim initial publication → formula commit。
2. formula prepare → representative move A→B → formula commit。
3. move prepare → new dependent formula commit → move commit。
4. formula prepare → root move A→B → formula commit。
5. formula prepare → row activate → formula commit。
6. row-deactivate prepare → new dependent formula commit → row-deactivate commit。
7. formula A/B same base prepare → A commit → B conflict。
8. conflict後、Bのpremise/dependency secondary indexがゼロ。
9. representativeがfrozen root Aから別のvalid root Bへcorruptされ、fast/canonical双方が
   `RepresentativeRootMismatch`を返す。
10. missing representative、missing root、dangling current bound、dangling live row、indexed
    live state missing from flat set。
11. formula-only support (`OrphanFormula`)とledger-only support (`MissingProofFact`)。
12. 上記failureとnoncanonical orderの共存時に`NonCanonicalProjectionOrder`が先行。

### 10.3 Writer-bound stress

- 1 rootに0/1/128/1,800/大規模live statesを持たせる。activation/deactivationのCPK-SV-C
  validation-adjacency workは全sizeで0 dependent-record visitsでなければならない。
- 1 claimを参照する0/1/128/1,800 formula recordsを作り、1,800回moveする。moveのCPK-SV-C
  validation-adjacency dependent-record visitsは全sizeで0でなければならない。
- 同じlive transitionについてscope外の`projection_lower_records_by_root`由来semantic
  publication dependentsがbaselineどおり列挙されることを別counterで確認する。全transactionの
  dependent workを0と主張しない。
- formula側は1recordへの1,800 descending singleton admission、comparator-equal prefix、late earlier
  insertion、mixed structural/reduction/replayを通す。
- query workはcurrent real states/actionsに比例することをcounterで確認する。

### 10.4 Full-workload gate

env-gated `std::text::parse` workloadで次を出す。

- refined-canonical trace action/read count。
- stable adjacency expansion count。
- missing/extra/mismatched identity count。
- distinct claim binding/root/live-state distribution p50/p95/max。
- formula writer membership probes/movement。
- claim move/live transitionのCPK-SV-C validation-adjacency dependent visits（必ず0）。
- `projection_lower_records_by_root`由来semantic projectability/publication dependent visits
  （baseline parity。0を要求しない）。
- capacity-inclusive adjacency/reverse-map bytes。
- peak RSS（18 GiB hard kill）。

## 11. 採らない案

### 11.1 Shared global generationだけで両writerを同期する

採らない。generationはstalenessを検出するが、次を解決しない。

- commit時に増えたdynamic leafのcapacityをどうfallibleに確保するか。
- 既にcommitしたclaim/core mutationをどうrollback/retryするか。
- 全dependent recordsへのfanoutをどうboundedにするか。
- callerがprepared intentをpublishしないことをどう型で保証するか。

Global generationは無関係なroot/formula間のfalse conflictも増やす。snapshot generationはSV-D cache
invalidationに限定する。

### 11.2 Claim/live lifecycleをformula reverse mapへfanoutし続ける

採らない。正しくversion化してもO(dependents) workとopposite snapshot raceを温存する。現在値の
copyを全formula bucketへ配る必要自体がない。

### 11.3 Formula commitでcurrent dynamic setを全rebuildする

採らない。formula側のstale windowは一時的に閉じても、claim/live側のprepared dependent set raceを
解決しない。さらにlive-state数×actionsのcommit workとallocationを再導入する。

### 11.4 Stale commitをsilent no-op / dirty certificateで吸収する

禁止する。Formula relationはmandatory dataであり、dropできない。Dirty certificateはread fallbackを
選ぶための状態であって、failed formula commitの代替ではない。

### 11.5 Dynamic leafをoptional shadowとして残す

採らない。shadowでも二重ownerの同期コード、reverse map、capacity、review surfaceを残す。
independent oracleはquery時にlate-bound expansionを比較すれば足りる。

### 11.6 Query時にraw formulaを再走査する

採らない。CPK-SV-Cの目的であるdistinct adjacencyを失う。Queryはpersistent stable obligationsを
読み、そのdynamic leafだけをauthorityから解決する。

## 12. 更新後の invariants

CPK計画とCPK-SV追補の既存invariantを継承し、§5.2に関する意味を次で補強する。

37. **Single-owner dynamic state**
    - current claim locationとcurrent live-row setは各authorityに一つだけ存在する。
    - formula adjacencyへcurrent leafをcopyしない。
38. **Stable obligation completeness**
    - claimed incidenceはexact representative/expected-root pairとroot-state obligationを持つ。
39. **Completed-snapshot expansion parity**
    - stable obligationのfixed-snapshot expansionは精密化済みcanonical validation traceと一致する。
40. **No cross-writer adjacency mutation**
    - claim/live lifecycle transactionはCPK-SV-C formula validation adjacencyを変更しない。
41. **Committed receipt authority**
    - secondary publicationはsuccessful commit receiptだけを根拠にする。
42. **No silent commit conflict**
    - stale prepared deltaはtyped error/terminal failureとなり、`()`/bool/no-opで隠さない。
43. **Bounded lifecycle work**
    - claim move/live transitionのCPK-SV-C validation-adjacency workはdependent countに依存しない。
    - scope外のsemantic projectability/publication fanoutは維持する。
44. **Fallible prepare / allocation-free commit**
    - persistent capacityとID boundはprepareで検査し、commitはallocationしない。
45. **Certificate locality**
    - structural certificateはbucket-internal frozen relationだけを証明し、current dynamic claim/live
      stateを証明したことにしない。
46. **Cache invalidation separation**
    - snapshot generationはsuccessful-validation reuseをinvalidateするが、adjacency同期の代替にしない。
47. **Support-ledger closure**
    - current resolved support ledgerとformula frozen normalized support keysを双方向に検証する。
    - formula-onlyは`OrphanFormula`、ledger-onlyは`MissingProofFact`のcanonical semanticsを保つ。
48. **Frozen/current canonical parity**
    - canonical formula validation自身がincidenceのfrozen `expected_root`とrepresentativeのcurrent
      rootを比較する。stable fast pathだけがこのinvariantを知る状態を禁止する。
49. **Typed live-index corruption**
    - indexed live stateとflat live occurrenceの不一致をpanic/assertで処理せず、canonical typed
      `ProofFailure`として返す。
50. **Semantic reverse-map preservation**
    - `projection_lower_records_by_root`と`projection_lower_record_memberships`はCPK-SV-C専用reverse
      mapではなく、retireしない。

## 13. Stop conditions

次の一つでも発生した時点で実装を止め、本書の再設計・再査読へ戻る。

1. formula commitが成否をcallerへ返さず終了する経路が残る。
2. failed/conflicted commitのprepared intentからsecondary index、snapshot、queue、diagnostic outputが
   publishされる。
3. claim move/live transitionがCPK-SV-C validation-adjacency更新のためにformula record listを
   snapshot/scanする。
4. formula admissionがcurrent claim bound/live row stateをpersistent adjacencyへmaterializeする。
5. 同じpersistent adjacency entryを二つ以上のtransaction familyがwriteする。
6. formula admissionとclaim/live lifecycleのvalidation adjacencyを同期するためだけのreverse mapが
   残る、またはscope外の`projection_lower_records_by_root`を誤ってretireする。
7. shared generation conflictを検出しても、retry/terminal propagationがcallerまで届かない。
8. claim move/live transitionのCPK-SV-C validation-adjacency workがdependent formula countに比例する。
   `projection_lower_records_by_root`由来のsemantic publication workはこのconditionの対象外であり、
   baseline parityを別gateで要求する。
9. formula writerのsmall deltaがrecord-wide shift/resort/rebuildを要求する。
10. commit中にallocation、unbounded `collect/extend`、unchecked ID conversionが残る。
11. fixed-snapshot late-bound expansion/support-ledger closureと精密化済みcanonical traceに一件でも
    mismatchが出る。
12. representative、expected root、constraint role、replay side/carrier等のexact identityが粗化される。
13. dynamic fast failureを精密化済みcanonical fallbackなしで外部へ返す、またはcanonical pathが
    frozen/current divergenceやlive-index/flat-set divergenceを検査しない。
14. `NonCanonicalProjectionOrder`、failure owner、first-error precedenceが変わる。
15. CPK-SV-A certificateがcurrent claim/live stateを永続的にcertifyする。
16. CPK-SV-D cacheがsnapshot bump後もhitする、またはprojectability/cycle resultを保存する。
17. query cursorがnested empty combinationを訪れる、またはlive statesをcollect/sortする。
18. no-claim workloadにdynamic-obligation/reverse-map persistent allocationが生じる。
19. full-std oracle mismatchが非zero、またはpeak RSSが18 GiB thresholdへ近づく。
20. true parallel mutationを導入したのに、本書のsingle-thread completed-snapshot argumentをそのまま
    使用する。
21. support-ledger/formula closureを検証せず`Valid(snapshot)`をpublishする。
22. formula-only/ledger-only support failureの`OrphanFormula`/`MissingProofFact` semanticsまたは
    `NonCanonicalProjectionOrder` precedenceが変わる。

stop conditionをdirty certificate、fail-open、test期待値変更、organic mismatch除外、retry loopの
無制限化で回避してはならない。

## 14. Rollback / migration

- CPK-SV-A/Bはrollbackしない。本書のR0〜R3はcertificate/order authorityから独立している。
- R0はtyped commit receiptだけを単独revert可能だが、silent-loss fixなのでR1以降の前提とする。
- R1はstable obligation shadowだけをrevert可能。production validation authorityは§4.4の
  refined canonical pathのまま。
- R2で旧dynamic leafとCPK-SV-C専用reverse mapsだけを削除する。
  `projection_lower_records_by_root` / `projection_lower_record_memberships`は削除しない。R2だけを
  revertする場合も、旧cross-writer pathをproduction defaultへ戻さず、R1 shadowとrefined
  canonical validationへ戻す。
- R3完了前にSV-D adjacency read authorityを開始しない。

current `520c332b` にあるdynamic snapshots/rekeysを段階的に削除するとき、一時的に旧leafと
stable obligationを同時writeする期間はtest/env-gated shadowに限定する。release defaultで恒久的な
dual writeを残さない。

## 15. Claude独立査読 checklist

1. current productionでadjacency membershipを変え得るtransaction familyを全てcensusしたか。
2. upper-claim initial publicationをformula prepare/commit間に挟む既存順序でもargumentが成立するか。
3. `expected_root`がmutable lookupではなくexact event/incidence metadataから得られるか。
4. `ValidateClaimBinding`と`ValidateCoverageRootState`の分解がcanonical `resolve_claim`の全readを
   覆い、indexed-live-state/flat-set divergenceをtyped failureにするか。
5. representative==rootの重複除去がfailure semanticsを変えず、canonical fallbackがownerを保存するか。
6. root current record moveとrepresentative current record moveを両方late-bindしているか。
7. live-row activation/deactivation以外にroot→state membershipを変えるwriterがないか。
8. CPK-SV-C専用reverse map削除後に別production consumerが失われず、特に
   `projection_lower_records_by_root`とsemantic publication fanoutが保存されるか。
9. `support_relation_valid`のbucket-local再定義がSV-B order skipのsoundnessを変えないか。
10. all `commit_projection_clause_admission` callerがcommitted receiptだけを使用するか。
11. claim/core sibling commit後のformula conflictがwhole-attempt failureまで確実に伝播するか。
12. independent oracleがwriter translation/self-comparisonを共有せず、support-ledger closureと
    frozen/current root comparisonもtraceしているか。
13. query cursorがactual actions/current live statesだけを訪れるか。
14. lifecycle writerのCPK-SV-C validation-adjacency workがdependent records数にかかわらずconstant
    であり、scope外semantic publication workを誤って0件gateへ含めていないか。
15. formula removal/rekeyがproductionに存在しないという前提がcurrent code全体で成立するか。
16. CPK-SV-D landing後、structural snapshot bumpが全dynamic authority commit末尾で一回だけ
    起きるか。SV-Cがcacheを先行導入していないか。
17. R0〜R3が各々rollback可能で、read authority cutoverをSV-Dより前に混ぜていないか。
18. formula/support-ledger closureがformula-onlyを`OrphanFormula`、ledger-onlyを
    `MissingProofFact`としてcanonical順に返すか。
19. representative A→別のvalid root B divergenceをfast/canonical双方が
    `RepresentativeRootMismatch`として検出し、fallbackがsuccessへ変えていないか。

## 16. 完了条件

- persistent dynamic claim/live leaf actionがformula bucketから消えている。
- claim/live lifecycleからCPK-SV-C formula validation-adjacency writeとその専用dependent-record
  fanoutが消え、`projection_lower_records_by_root`由来semantic publication fanoutは保存されている。
- stale formula commitがtyped failureとなり、secondary publicationがゼロである。
- completed-snapshot late-bound expansion/support-ledger closureと精密化済みcanonical real traceの
  exhaustive mismatchがゼロである。
- frozen/current root divergenceとlive-index/flat-set divergenceがcanonical typed failureとなり、
  panicまたはfallback successにならない。
- formula writerとlifecycle writerのbounded-work stress gateが成立する。
- allocation failureがcommit前に返り、partial formula/claim/live/certificate publicationがない。
- CPK-SV-A/Bのorder/error parity、formula sequence、exact links、support summaryが不変である。
- no-claim allocation、capacity-inclusive footprint、full-std RSSが記録される。
- Claude (Sonnet 5)の独立査読・確定とユーザ承認が完了する。

---

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定

状態: **ユーザ承認済み（2026-08-13、rev.2）**。CPK-SV-C追補への正式な改訂として確定した。
CPK-SV-C-R0以降の実装に着手してよい。
