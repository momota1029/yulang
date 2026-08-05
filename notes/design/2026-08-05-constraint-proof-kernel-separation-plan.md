# Constraint Proof Kernel 分離・再実装計画

日付: 2026-08-05

状態: **ユーザ承認済み（2026-08-05）**

著者: Claude (Sonnet 5)、Codex `gpt-5.6-sol`（xhigh）の調査・設計提案に基づき統合・記述。

**署名についての注記**: このリポジトリの正本文書は通常 Claude (Fable 5) が起案する
慣習だが、[[2026-08-01-dpn-root-claim-and-cycle-safety-addendum]] 以降の一連の
追補と同様の理由（Fable 5 が一時的に利用できない状況）により、本書も Codex Sol
XHigh の調査・設計提案を Claude (Sonnet 5、本セッションの監督エージェント) が
検証・統合して文書化した。

**適用範囲についての注記**: 本書は「Yulang全体を作り直す」計画ではない。
`crates/infer` の型推論アルゴリズム本体（subtype 解決、worklist、row/effect
reduction、SCC、generalization）は一切変更しない。変更対象は
`crates/infer/src/constraints/` 配下にある「証明・provenance の追跡層」のみ
——RCPF/CDM/MPC/DPN の系譜が積み上げてきた claim-parent 追跡・replay 証明・
projectability 判定の実装を、単一の正本モデルへ作り直す。

## 0. 背景

2026-08-05 のセッションで RCPF-E の production cutover を完了させたあと、
RCPF-F（legacy flat ledger の物理撤去）に着手する過程で、以下が明らかになった。

- RCPF-E closure 検証の対象は §11 の4項目に限られており、`claim_parents_by_constraint`
  を無条件（authority 分岐なし）に読む本番 consumer が他に5箇所残っていた
  （upper claim materialization、dependency-chain propagation、lower projection
  初期化/bootstrap、bound-vs-carrier delta 分類）。
- その5箇所のうち1つ（bound-vs-carrier 分類）を実装しようとしたところ、
  **既に承認済みの `notes/design/2026-08-03-rcpf-d-materialization-projection-addendum.md`
  §3 の規則自体**が、legacy の実際の挙動とも、既存の pinned test
  （`cdm_a_9_4_independent_then_claimed_keeps_both_occurrences`）が固定する
  挙動とも食い違っていることが判明した。承認済み文書に見落としがあったという
  ことである。

これらは実装が下手だったのではなく、**現在のアーキテクチャ
（意味論データと証明データを同じ struct・同じ mutation に同居させ、legacy flat
representation の上に factored representation を後付けで安全移行する構造）が、
この種の見落としを構造的に発生させやすい**ことを示す実例として扱う。

ユーザーは、この負債と1ヶ月近く向き合い続けてきた末に、次の方針を明示的に
決定した（2026-08-05）。

- Yulang 全体（parser・module・poly・mono・cache・VM・CLI・LSP）は書き直さない。
- 型推論アルゴリズムの核（worklist、`step_subtype`、bound 挿入/subsumption/
  pruning、lower×upper replay 生成、row/effect reduction、SCC、generalization）
  も変更しない。
- 証明・provenance の追跡層（RCPF/CDM/MPC/DPN の実装範囲）だけを、別レイヤーとして
  作り直す。

本書はこの方針の実行可能性を検証したうえでの実装計画である。

## 1. Decision summary

`ConstraintMachine` から証明・provenance の追跡を分離し、単一の正本
`ProofOccurrenceStore` を持つ新しい **Constraint Proof Kernel** を導入する。

以下は既存の core solver にそのまま残す。

- `TypeArena`
- `SubtypeConstraintKey` の canonicalization
- `ConstraintWork` queue
- `step_subtype`
- 意味論的な constraint/bound ID
- active な lower/upper bound の列
- weight composition
- subsumption・pruning・promotion
- lower×upper replay のペアリング
- row/effect reduction の状態
- subtract の意味論
- SCC の readiness と quantification scheduling
- generalization・simplification・finalization のアルゴリズム

以下を新しい Proof Kernel へ移す。

- source origin・source boundary
- constraint/bound の derivation edge
- replay derivation の occurrence
- claim identity と coverage
- claim-parent 伝播
- RCPF の parent set・occurrence・summary・clause projection
- CDM/MPC/DPN の projectability 判定
- lower projection の proof ledger
- dependency edge
- provenance epoch
- explanation graph
- portable provenance
- generalized witness の provenance
- ordinary-cast eligibility の provenance
- diagnostic の順序に関する metadata

新しい Proof Kernel は受動的な observer ではない。core solver が読む同期的な
query は、次の2つに限定する。

1. replay routing query（この replay を実行すべきか）
2. scheme projection query（この lower は projectable か）

この2点以外から、core solver が証明層の内部表現を直接読むことを禁止する。

## 2. Problem statement

現在の `ConstraintMachine` と `TypeBounds` は、意味論的な状態と証明の状態を
同じ owner に持つ（`crates/infer/src/constraints/mod.rs`、
`crates/infer/src/constraints/machine/bounds.rs`）。

1つの bound/replay イベントが、次を同時に行う。

- 意味論的な canonicalization
- active bound の mutation
- replay work の計画
- proof occurrence の登録
- claim の materialization
- clause の構築
- projection の評価
- dependency の伝播
- epoch の publication
- legacy/factored oracle の維持

この構造は、RCPF/CDM/MPC/DPN の各段階で局所的な順序契約と複数の ledger を
必要とし、**意味論そのものの変更を一切伴わないにもかかわらず**、高い実装
リスクと書き込みコストを生んできた。今日一日だけでも、RCPF-E の Gap 1
（claimed attribution の分類漏れ）、Gap 2（A1 preflight の順序問題）、
RCPF-F 着手時の5箇所の未 cutover consumer、D addendum §3 自体の規則不備、
という4つの独立した見落としが、同じ根本構造から発生している。

新しい設計では、「何が意味論的に起きたか」と「それを何が証明しているか」を、
型・owner・mutation vocabulary の3点で分離する。

## 3. Goals

1. 意味論的な solver の出力・queueing・termination を変更しない。
2. 証明関係の正本表現を1つだけにする。
3. canonical duplicate（意味論的には新規ワークを生まない重複）でも、
   proof occurrence を失わない。
4. Original／ReplayConstraint／ReplayEvidence／StructuralConstraint／
   ReductionRouteConstraint の5つの lineage 種別を、同じ型付きモデルで表す。
5. replay の exact lower/upper carrier と、event 時点の parent 共有関係を保存する。
6. projection の OR/AND 構造を直接表現する。
7. 証明の mutation を「1イベント単位」で atomic にする。
8. exact no-op では、永続的な allocation・evaluation・publication を一切行わない。
9. diagnostic 専用の provenance が budget 不足になっても、solver の意味論には
   一切影響しない。
10. session-local ID・generalization-generation ID・portable identity を、
    型で混同できないようにする。
11. 旧 RCPF/CDM/MPC/DPN の出力との parity を証明してから、consumer を切り替える。
12. 一時的な dual-write 期間を短くし、production のデフォルトでは shadow の
    コストを払わない。

## 4. Non-goals

- subtype 規則の変更
- bound の dominance・subsumption・weight composition の変更
- lower×upper replay の件数を意味論的に減らす最適化
  （Mechanism 2 の census で、926件中0件が global alpha 同値と実測済み——
  「もっと大胆に消せるはず」という前提には立たない）
- row/effect reduction の意味論の変更
- SCC アルゴリズムの変更
- co-occurrence・polarity elimination・generalization の意味論の変更
- export される scheme の期待値の変更
- provenance を粗い origin の集合へ潰すこと
- RCPF の exact carrier を捨てること
- 証明経路の全展開
- 新しい cache アーキテクチャ
- binder quantification policy 自体の再設計
- 既存の diagnostic policy の変更

## 5. なぜ「core algorithm はそのまま、証明層だけ分離」が成立するか

### 5.1 分離可能な箇所（core solving loop のトレース結果）

- **Worklist / subtype 伝播**: 意味論的なループは `entry.rs` の `drain()` と
  `propagate.rs` の `step_subtype()` にある。`step_subtype()` が判断するのは
  極性・weight・variable/bound 状態・row/effect 構造であり、claim や
  projection formula を直接読んでいない。child の enqueue 経路
  （`enqueue_derived_subtype()`、`enqueue_row_derived_subtype()`）は現在
  canonicalization と証明処理が同じ関数内に同居しているが、queueing の条件
  自体には証明内容が入っていないため分離できる。
- **`add_lower_bound` / `add_upper_bound`**: extrusion・weight/filter 処理・
  alias-cycle subsumption・canonical bound insertion・opposite frontier との
  replay は意味論的処理。`record_bound_provenance`・claim materialization・
  projection proof・dependency 伝播・epoch publication は証明処理で、これらは
  外部化できる。
- **Structural / reduction derivation**: 型そのものは `step_subtype()` が
  決める。証明層に必要なのは親 constraint ID・derivation rule・canonical
  child ID・admission disposition だけ。
- **Replay merge**: 意味論的 identity（lower/upper endpoint、composed weight、
  canonical key）と、証明側の exact identity（pivot、exact lower/upper
  `BoundRecordId`、replay rule、event 時点の parent snapshot）は分離できる。
- **SCC / generalization**: `SccMachine` の quantification readiness・SCC
  edge・selection settlement から claim/projection table への直接参照は
  見つからなかった。SCC アルゴリズム自体は温存できる。generalization が
  compact input を集める箇所だけが、新しい projection service を読む形になる。

### 5.2 分離できない箇所（core solving loop への read-back）

以下の4箇所は、証明層の状態が **solver の control flow そのもの** を
決めており、単純な「後から読まれるだけの受動ログ」にはできない。

1. **Replay routing**: `lower_bound_replay_actions()` / `upper_bound_replay_actions()`
   は、upper/lower record の claim coverage を読んで `should_replay` を決める。
   これは worklist に積まれるワーク量そのものを変えるため、証明層は
   単なる metadata ではなく、solver が呼び出す **同期的な semantic service**
   でなければならない。
2. **Scheme projection**: `scheme_projectable_lowers` が読む claim/projection
   の AND/OR 評価は、export される scheme（ユーザーに見える型推論結果）を
   直接左右する。診断専用ではない。
3. **Attempt termination**: `drain()` は `ReplayFactoredShadowStatus::Failed`
   で停止し、lowering は failed attempt を丸ごと破棄して legacy へ retry する。
   新しい証明層でも、この「部分的な証明状態を伴う attempt から出力しない」
   という規律は維持しなければならない。
4. **Invalidation**: projectability の flip が owner/global epoch と
   dirty scheduling を更新する。これは analysis/generalization の再計算を
   引き起こすため、証明層から core 側への通知経路が必要になる。

逆に、証明グラフの任意 traversal・claim-parent の列挙・diagnostic の
explanation が `step_subtype()` の構造分解そのものを決めている箇所は
見つからなかった。

### 5.3 結論

**分離可能（named exceptions つき）。** 「証明層を完全に外へ追い出す」ことは
できるが、「solver から一切呼ばれない受動的なログ」にすることはできない。
新しい証明層は、replay routing と scheme projection という2つの同期 query
だけを core solver に提供する、独立した kernel として設計する。

## 6. Ownership boundary

### 6.1 Semantic Kernel（変更しない）

Semantic Kernel は次を所有する。

```text
TypeArena
SemanticConstraintStore
SemanticBoundStore
ConstraintWorkQueue
SubtractState
RowReductionState
TypeLevels
VarAdjacency
SemanticEpoch
```

`ConstraintRecord` は原則として次だけを持つ。

```rust
struct SemanticConstraintRecord {
    key: SubtypeConstraintKey,
}
```

`BoundRecord` は次を持つ。

```rust
struct SemanticBoundRecord {
    direction: BoundDirection,
    owner: TypeVar,
    endpoint: BoundEndpoint,
    weights: ConstraintWeights,
    state: BoundRecordState,
}
```

derivation・origin・disposition の説明は Proof Kernel へ移す。

### 6.2 Proof Kernel（新規）

Proof Kernel は次を所有する。

```text
ProofOccurrenceStore
ProjectionFormulaStore
CoverageStore
ProofDependencyIndex
SourceBoundaryStore
ExplanationIndex
PortableProvenanceExporter
ProofPublicationState
```

Semantic Kernel の record を複製せず、安定 ID への型付き foreign key だけを
保存する。

```rust
enum SemanticFactRef {
    Constraint(ConstraintRecordId),
    Bound(BoundRecordId),
    Subtract(SubtractFactRecordId),
    RowReduction(RowReductionRecordId),
    LowerFilter(LowerFilterRecordId),
}
```

### 6.3 Read-only semantic view

Proof Kernel が endpoint や active/tombstone 状態を必要とするときは、
限定された read-only view を使う。

```rust
trait SemanticFactView {
    fn constraint(&self, id: ConstraintRecordId)
        -> Option<&SemanticConstraintRecord>;
    fn bound(&self, id: BoundRecordId)
        -> Option<&SemanticBoundRecord>;
    fn row_reduction(&self, id: RowReductionRecordId)
        -> Option<&SemanticRowReductionRecord>;
}
```

Proof Kernel が意味論側の map・queue・bound vector を直接 mutate することを
禁止する。

## 7. Canonical proof model

### 7.1 Proof occurrence

```rust
struct ProofOccurrence {
    result: ProofResult,
    cause: ProofCause,
    parents: ParentSetId,
    event: ProofEventId,
    completeness: ProvenanceCompleteness,
}

enum ProofResult {
    Semantic(SemanticFactRef),
    TrivialReplay(ReplayDropId),
    EvidenceBound(BoundRecordId),
}

enum ProofCause {
    Root(SourceBoundaryOrigin),
    Structural(StructuralDerivation),
    Row(RowDerivation),
    Replay(BinaryReplayDerivation),
    ReplayEvidence(BinaryReplayDerivation),
    ReductionRoute(RowDerivationId),
    SchemeInstantiation(SchemeInstantiationDerivation),
    SubsumedBy(BoundRecordId),
    PrunedBy(BoundRecordId),
    PromotedFromEvidence(BoundRecordId),
}
```

1つの意味論的 fact に複数の proof occurrence を結び付けられる。
semantic key と proof occurrence の identity を混同しない。

### 7.2 Lineage classes

projection の lineage は、次の5種類を型付きのまま保つ。

```rust
enum ProjectionLineage {
    Original,
    ReplayConstraint,
    ReplayEvidence,
    StructuralConstraint,
    ReductionRouteConstraint,
}
```

`notes/design/2026-08-05-rcpf-e-clause-link-attribution-and-ordering-addendum.md`
の writer-boundary 分類を継承するが、正本 store が1つになるため、
replay summary と flat-retained attribution の union を取る必要がなくなる。

### 7.3 Projection formula

projectability を expanded link の `Vec` から再構成せず、formula として
保存する。

```rust
enum ProjectionClause {
    Standalone {
        support: ProjectionSupport,
    },
    DerivedUnary {
        support: ProjectionSupport,
        premise: ProofPremise,
        rule: UnaryProjectionRule,
    },
    ReplayConjunction {
        support: ProjectionSupport,
        lower: BoundRecordId,
        upper: BoundRecordId,
        carrier: BinaryReplayDerivation,
    },
}
```

1つの record に属する clause 群は OR、`ReplayConjunction` 内部の lower/upper
は AND とする。exact carrier・parent side・representative claim・first
witness・insertion-order 契約は occurrence 自身に保存し、iterator の走査順
から再導出しない。

## 8. Typed lifecycle classes

```rust
struct SessionFactId<T> { ... }
struct ProofEventId { ... }
struct SchemeWitnessId {
    owner: DefId,
    generation: u32,
    index: u32,
}
struct PortableCauseId { ... }
```

規則:

- `SessionFactId` と `ProofOccurrenceId` は inference session の外へ出さない。
- `SchemeWitnessId` は owner/generation を跨いで再利用しない。
- cache/portable export は session ID を直接 serialize せず、`DefId`・
  source boundary・portable path へ変換する。
- `TypeVar`・quantifier・SCC の binder lifecycle 自体は今回変更しない。
- session ID から portable identity への変換は、1箇所の exporter だけが行う。

## 9. Stable event interface

### 9.1 Mutation vocabulary

core が発行できる event を固定する。

```rust
enum CoreProofEvent {
    ConstraintObserved(ConstraintObservation),
    BoundObserved(BoundObservation),
    ReplayObserved(ReplayObservation),
    RowReductionObserved(RowReductionObservation),
    CoverageChanged(CoverageChange),
    SubtractFactObserved(SubtractObservation),
    SchemeInstantiationObserved(SchemeInstantiationObservation),
}
```

各 observation は少なくとも次を含む。

- 安定した result ID
- 正確な意味論的 disposition
- 型付き cause
- exact parents/carrier
- pre-event の状態を識別する event ID
- 意味論的変化 / metadata のみ / exact no-op の区別

Replay の disposition:

```rust
enum ReplayOutcome {
    Enqueued(ConstraintRecordId),
    CanonicalDuplicate(ConstraintRecordId),
    Trivial(ReplayDropId),
    EvidenceOnly {
        lower: BoundRecordId,
        upper: BoundRecordId,
    },
}
```

### 9.2 Prepare / commit transaction

```rust
trait ProofKernel {
    fn prepare(
        &self,
        view: &impl SemanticFactView,
        draft: CoreProofEventDraft,
    ) -> Result<PreparedProofEvent, ProofFailure>;

    fn commit(
        &mut self,
        prepared: PreparedProofEvent,
        outcome: CoreAdmissionOutcome,
    ) -> ProofCommit;
}
```

順序:

1. core が意味論的な candidate と予定 ID を決める。
2. Proof Kernel が pre-event view 上で preflight する。
3. allocation/index insertion を prepare する。
4. core が意味論的な mutation を commit する。
5. Proof Kernel が prepared delta を infallible に commit する。
6. `ProofCommit` の invalidation を1回だけ publish する。
7. canonical duplicate なら意味論的 queue へは入れず、証明の commit だけ行う。
8. exact no-op なら両側とも何もしない。

prepare 後に core が commit できない場合は、prepared event を破棄する。
どうしても preflight できない allocation が残る場合は、現行と同じ
whole-attempt terminal failure + clean retry を使う。部分的な証明状態を
持つ attempt から出力を返さない。

## 10. Required synchronous queries

### 10.1 Replay routing

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

core は `routing` だけを見る。claim ID・coverage root・parent set の内部を
読まない。このクエリは、現在の以下を完全に置き換える。

- `upper_record_requires_generic_replay`
- `uncovered_upper_replay_claim_parents`
- `covered_claims`
- incremental route による claim 除外
- `lower_record_replay_claim_parents`

### 10.2 Scheme projection

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

generalization/compact はこの API だけを読む。raw な proof clause・claim・
link へ直接触れない。

### 10.3 Quiescent consumers

以下は solver loop の外側の query とする。

- explanation
- portable provenance
- OCAST eligibility
- generalized witness capture
- debug/census

これらは core の worklist を変更してはならない。

## 11. Publication and invalidation

`ProofCommit` は次を返す。

```rust
struct ProofCommit {
    logical_changed: bool,
    affected_projection_owners: SmallVec<[TypeVar; 2]>,
    completeness_changed: bool,
}
```

規則:

- logical に no-op なら epoch/publication を発行しない。
- metadata のみの変化なら provenance generation だけを進める。
- projectability の flip があれば、affected owner を dedup してから1回だけ
  publish する。
- 意味論的 epoch を、証明 storage の compaction によって進めない。
- before/after の評価を同じ round に混ぜない。
- core は証明の dependency graph を直接歩かない。

## 12. Failure and completeness policy

routing と projection に必要な事実は **mandatory な semantic-support data**
とする。budget によって drop してはならない。

optional にできるのは次だけ。

- diagnostic 表示用の attachment
- bounded explanation の補助 index
- portable export の追加詳細
- census/debug metadata

mandatory な write/read が失敗した場合:

1. attempt を terminal failed にする。
2. 以後の意味論的 queue を処理しない。
3. 出力を破棄する。
4. clean attempt で再実行する。
5. confirmed path を `projectable = true` へ吸収しない。

optional な detail の budget exhaustion は `Incomplete` として残し、
routing/projectability を変えない。

## 13. Migration plan

### CPK-0: Contract inventory and baseline

リスク: medium。コード挙動: 変更なし。

- 全ての証明 writer/read consumer を列挙する。
- 意味論的 queue・bound 順序・replay 件数・row 状態・SCC event・scheme 出力の
  baseline を固定する。
- RCPF/CDM/MPC/DPN の logical output を normalized snapshot 化する。
- **D addendum の Bound/Carrier 規則と現行 legacy 挙動の不一致を解決する**
  （2026-08-05 に発見済みの未解決事項）。
- **consumer #1（upper claim materialization）・#3（target-late lower
  初期化）・#4（lower bootstrap）・#5（bound-vs-carrier 分類）の未確定な
  意味論を、この場で source of truth として確定する**（RCPF-F 着手時に
  発見済みの未解決事項）。

Exit 条件:

- legacy の内部矛盾を、新 kernel の oracle としてそのまま使わない状態になっている。
- event vocabulary が全ての production writer をカバーしている。
- 原因不明の writer/read consumer がゼロ。

### CPK-1: Module seam and semantic record split

リスク: high。Authority: legacy。

- `constraints/proof/` module を作る。
- 意味論的な `ConstraintRecord` / `BoundRecord` から証明 payload への
  access adapter を定義する。
- `SemanticFactView` と Null/Legacy proof backend を導入する。
- queue・canonical map・active bound の順序は一切変更しない。

Exit 条件:

- 意味論的な件数・queue・event・epoch・出力が byte-identical。
- 新しい proof store への write はまだ行われていない。

### CPK-2: Canonical ProofOccurrence shadow store

リスク: very high。Authority: legacy。Production default: shadow off。

- root・structural・row・bound・subtract・scheme-instantiation の event を
  shadow store へ送る。
- replay occurrence は後続スライスまで未接続でも、coverage の gap を
  明示する。
- test/debug または明示的な env でのみ shadow を有効にする。
- production release で常時 dual-write しない。

Exit 条件:

- non-replay の証明グラフが parity。
- canonical duplicate の metadata-only な挙動が parity。
- 意味論的な性能の regression がない。

### CPK-3: Replay and row-reduction coverage

リスク: critical。Authority: legacy。

- exact lower/upper の replay carrier。
- event 時点の parent snapshot。
- canonical duplicate・trivial・evidence-only の区別。
- 5つの lineage kind。
- reduction root と live coverage。
- row/reduction の opaque proof handle。

を新 store へ接続する。

Exit 条件:

- exact replay occurrence の finite map が parity。
- first representative / first witness が parity。
- insertion-order fixture が parity。
- 意味論的な replay 件数が byte-identical。

### CPK-4: Projection formula and invalidation shadow

リスク: critical。Authority: legacy。

- Standalone / DerivedUnary / ReplayConjunction の formula を構築する。
- 新 evaluator を shadow で走らせる。
- record の projectability・affected owner・epoch class を legacy と比較する。
- five-source attribution matrix を新モデルへ移植する。

Exit 条件:

- projectability が parity。
- affected-owner set が parity。
- metadata-only／inclusion-flip の publication が parity。
- cycle-cut が parity。
- no-claim passthrough が parity。

### CPK-5: Replay routing shadow

リスク: critical。Authority: legacy。

- 新しい `prepare_replay_route()` を呼ぶ。
- 意味論的 routing は legacy の結果を使い続ける。
- 新旧の Generic・IncrementalOnly・Skip 判定を、event ごとに比較する。
- lower/upper replay の input 件数と accepted 結果を照合する。

1件でも routing の mismatch があれば cutover しない。

Exit 条件:

- repository std・RMW・URR・insertion-order fixture で routing mismatch ゼロ。
- queue/work 件数が parity。
- canonical constraint 件数が parity。

### CPK-6: Projection consumer cutover

リスク: critical。Authority: この時点から projection は新 proof kernel。

切替対象:

- `scheme_projectable_lowers`
- scheme compact collector
- positive alias traversal
- generalized witness capture
- projectability invalidation
- explanation / portable provenance
- OCAST の shadow classifier

SCC scheduling・generalization の core・simplifier は変更しない。

Exit 条件:

- generalize された scheme の alpha/出力が parity。
- compact root が parity。
- cache の cold/warm が parity。
- portable provenance が parity。
- diagnostic の順序が parity。

### CPK-7: Replay routing authority cutover

リスク: critical。Authority: この時点から routing と projection は新 proof kernel。

- `lower_bound_replay_actions`
- `upper_bound_replay_actions`
- incremental reduction-route の除外

を新しい routing query へ切り替える。これは意味論的 queue を変え得る
唯一の authority cutover であるため、projection cutover と同じ commit へ
混ぜない。

Exit 条件:

- 意味論的 worklist の trace が parity。
- replay census が parity。
- row reduction 状態が parity。
- 最終的な型/scheme/出力が parity。
- termination が parity。

### CPK-8: Legacy proof machinery removal

リスク: very high。

削除対象:

- flat/factored replay の二重 store
- `claim_parents_by_constraint`
- expanded な replay clause/link の `Vec`/`HashSet`
- `replay_claim_parent_keys`
- RCPF の authority dispatch
- legacy な proof projection ledger
- 移行専用の parity adapter
- production rollback backend

保持対象:

- 意味論的な constraint/bound ID
- active bound
- 意味論的な row reduction 状態
- 意味論的な epoch
- 外部から必要な read-only public/debug surface

compatibility iterator が必要な場合は、新しい occurrence store の上にだけ
実装する。

Exit 条件:

- 本番の証明表現が1つだけになっている。
- authority enum と dual-write がなくなっている。
- 旧 proof writer/reader がゼロ。
- 移行専用コードがゼロ。

### CPK-9: Closeout and performance gate

- `std::text::parse` の wall time/RSS。
- 証明 write の self time。
- event 件数・occurrence 件数・formula 件数。
- exact no-op の allocation（ゼロであること）。
- cache の cold/warm。
- 代表的な application corpus。
- full な安全 infer test coverage。

を計測する。性能目標は baseline 比だけでなく、証明 write が lowering 全体に
占める割合で置く。旧 dual-write path が profile 上から消えていることを
確認する。

## 14. Oracle and test strategy

### 14.1 意味論的な parity

比較対象: canonical constraint key/件数/順序、queue admission の順序、
処理済み work 件数、active lower/upper vector とその順序、bound の状態・
promotion・subsumption・pruning、replay の input/generated/accepted/
duplicate/trivial/evidence の件数、row の residual/reduction 状態、
constraint event、SCC event、generalize された scheme、poly/check 出力の
hash、termination。

### 14.2 証明の parity

比較対象: exact occurrence、exact replay carrier、event 時点の parent 共有、
5つの lineage kind、representative claim／first witness、projection
formula、clause の AND/OR、projectability、affected owner set、provenance
の completeness、explanation の category/edge 順序、portable provenance。

### 14.3 再利用可能なテスト

主に次を再利用する。

- `constraints/tests/case_01.rs`: subtype・bound replay・row・weight
- `case_02.rs`: claim/projectability/CDM/MPC/DPN/RCPF
- `case_03.rs`: duplicate provenance・promotion・budget
- `claim_qualified_provenance.rs`: 5つの lineage
- `explain.rs`: bounded graph query
- `portable_explain.rs`: portable の parity/順序
- `ocast_eligibility.rs`: source-boundary の分類
- `characterization.rs`: std/replay の census
- `pusp_characterization.rs`: parameter/scheme の provenance
- `subtype_fallthrough_characterization.rs`: core subtype の意味論
- `generalize/tests.rs`: liveness/projectability/generalization
- `compact/tests/mod.rs`: raw/projection collector の parity
- RCPF の insertion-order・target-late・canonical duplicate の pinned fixture

既存のテスト期待値を新しい出力に合わせて変更しない。論理的な表現の差だけを
canonical normalization で比較する。

## 15. Correctness invariants

1. 証明 ID は意味論的な `Hash`/`Eq` へ入らない。
2. 証明専用の mutation は、意味論的 queue へワークを追加しない。
3. canonical duplicate は意味論的ワークを再実行しないが、proof occurrence を
   失わない。
4. replay carrier は exact な lower/upper/pivot/rule を保つ。
5. parent の共有関係は event 時点の snapshot で固定する。
6. replay の側を失わない。
7. 5つの lineage kind を、shape から逆推定しない。
8. projection の OR/AND を、粗い root の集合へ潰さない。
9. mandatory な routing/projection の事実を、budget で drop しない。
10. 不完全な diagnostic provenance を complete として扱わない。
11. no-claim な経路では、証明の allocation をゼロにする。
12. exact no-op では、evaluation/publication をゼロにする。
13. before/after の view を同一 round に混ぜない。
14. projectability の結果を永続的に memo しない。
15. core は、2つの同期 query 以外から証明 storage を読まない。
16. 証明層は、意味論的な map/queue を mutate しない。
17. session ID を portable/cache へ直接 export しない。
18. consumer から見て順序が意味を持たない relation は、unordered な
    finite map として比較する。
19. consumer から見て順序が意味を持つ diagnostic だけが、明示的な
    canonical order を持つ。
20. 失敗した attempt から出力を返さない。

## 16. Stop conditions

次のいずれかが起きたら、次のスライスへ進まない。

- 証明状態なしでは `step_subtype` の構造規則を選べない箇所が新たに見つかる。
- core が任意の証明グラフ traversal を必要とする。
- replay routing の parity mismatch。
- projectability の parity mismatch。
- generalize された scheme/出力の mismatch。
- queue/work 件数の mismatch。
- 証明 event が、必要な pre-event 情報を失った後にしか発行できない。
- mandatory な証明データに、silent な drop が必要になる。
- 安定 event を作るために、意味論的な key/順序を変える必要が出る。
- row の opaque handle が証明内容を core へ漏らし始める。
- session/generation/portable ID の lifecycle を、型で分けられなくなる。
- 一時的な dual-write が production のデフォルトとして常設される。
- legacy oracle 自身の意味が未解決なまま、parity を定義しようとしている。

## 17. Estimated scope

現時点の粗い見積り。

- 新しい production proof kernel: 約4k〜7k LOC
- 移行 adapter/oracle: 約2k〜4k LOC
- 集中的なテスト/fixture: 約3k〜6k LOC
- 一時的なピーク時追加: 約9k〜17k LOC
- 削除可能になる旧 proof/移行 machinery: 約8k〜15k LOC

全体の規模は XL。8〜10個の独立したスライスが必要になる。正確な工数は、
CPK-0 の writer/consumer inventory と、Bound/Carrier の legacy 不一致解決後に
再見積りする。

## 18. Completion criteria

- core の subtype/worklist/row/SCC/generalization アルゴリズムが、旧
  baseline と同一である。
- 本番の証明 store が1つだけになっている。
- replay routing と scheme projection が、型付き API だけを通っている。
- RCPF/CDM/MPC/DPN の legacy storage と authority dispatch が削除済み。
- 全ての parity oracle が green。
- 代表的な std の出力が byte/alpha parity。
- 原因不明な incomplete provenance がない。
- profile 上、旧 dual-write path が消滅している。
- 証明 write のコストと RSS が記録済み。
- 移行専用コードと env flag が削除済み。

## 19. Open risks / unknowns

- **Replay routing は証明由来の意味論的決定である**。ここを「metadata だから
  後で記録すればよい」と扱うと solver のワーク量が変わる。CPK-7 を独立した
  critical cutover として扱う必要がある。
- **D addendum の Bound/Carrier 規則の不一致**。現行 legacy の挙動と、
  承認済み文書の意味が食い違っている疑いがある。この状態では、legacy を
  無条件の oracle にできない。CPK-0 で先に解決すべき前提になる。
- **RCPF-F を阻んでいた未 cutover consumer #1/#3/#4/#5**。新 kernel は
  結果的にこれらを置き換えるが、各 consumer が要求する意味を inventory へ
  取り込む必要がある。特に upper materialization と lower projection
  bootstrap は「消す」のではなく、新しい canonical query として再表現
  しなければならない。
- **Row derivation handle の先行発行**。row solver は derivation ID を
  後続の意味論的ワークへ載せる。opaque handle で分離できるが、event の
  prepare/commit 順序を誤ると dangling ID になる。
- **Allocation failure の atomicity**。core の mutation の後に証明の
  commit だけが失敗する形は許容できない。prepared allocation か
  whole-attempt discard のどちらかが必要になる。
- **Mandatory な事実と diagnostic detail の budget 分離**。routing/
  projectability に必要な root・coverage・formula は絶対に drop できない。
  説明用の rich attachment だけを `Incomplete` にできる。
- **Dual-write の再発**。移行中の shadow は必要だが、release のデフォルトで
  常時二重書きすると、RCPF の問題をそのまま再生産する。shadow は
  test/debug/明示的 benchmark に限定し、cutover 後すぐに旧 store を消す
  必要がある。

## 20. 波及する文書（本書 landing 後に更新。本書では編集しない）

- `notes/todo/performance-localization.md`: `std::text::parse` の ≤15秒
  target gap の次の一手として、本書への参照を追記する。
- `notes/architecture/claim-propagation-architecture.md`: 現行アーキテクチャの
  説明として、本書へのリンクと「置き換え予定」の注記を追加する。
- `notes/design/2026-08-02-replay-claim-parent-factorization.md` §11 の
  RCPF-F 節: RCPF-F 自体は本書の CPK-8 に吸収されることを注記する。

---

著者: Claude (Sonnet 5)（Codex `gpt-5.6-sol` xhigh の調査・設計提案を統合）

ユーザ承認済み（2026-08-05）。本書は設計判断の正本として扱う。
CPK-0（contract inventory and baseline）から着手してよい。
