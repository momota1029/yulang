# CPK-0 追補: projection admission 契約・consumer 意味論・baseline 固定

日付: 2026-08-05

状態: **ユーザ承認済み（2026-08-05）**

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定

**署名についての注記**: Fable 5 が一時的に利用できないため、`CLAUDE.md`
「Fable 5 不在時の起案担当」に従い、本書は必要な調査・設計判断を実施した
Codex `gpt-5.6-sol`（xhigh）が本文を起案した。Claude (Sonnet 5) は
コード・既存正本文書との照合、書式・整合性の査読、確定および署名を担当する。
査読では、本文が引用する主要な関数名（`merge_structural_claim_parents`、
`bootstrap_clause_projection_parents`、`register_reduction_route_claim_parent`、
`projection_carrier_is_independent`、`try_project_replay_parents`、
`support_has_clause_link`、`register_constraint_upper_replay_claims`、
`register_premise_dependency_chain`、`register_lower_projection_derivation`、
`register_existing_constraint_lower_projection_delta`）が全て
`crates/infer/src/constraints/` 内に実在することを確認した
（`bootstrap_clause_projection_parents` は top-level 関数ではなく
`bounds.rs:4394` のローカル変数であり、本文の記述と一致する）。

本書は
`notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md`
（以下 CPK 計画）§13 の CPK-0
（Contract inventory and baseline）について、着手前に未解決だった次の事項を
確定する追補である。

- production proof writer / read consumer の完全inventory
- D materialization addendum §3 の Bound / Carrier divergence
- consumer #1 / #3 / #4 / #5 が要求する正確な意味
- semantic execution と logical proof を分離したbaseline capture契約

本書はproduction behaviorの変更を認可しない。次に着手してよい作業は、
本書§9で定義するCPK-0a / CPK-0b / CPK-0cのtest-only baseline整備だけである。
CPK-1以降のproduction実装は、本書のユーザ承認とCPK-0のexit
criteria達成後に、別スライスとして進める。

## 0. 本書が下す決定の要約

1. D materialization addendum §3 の
   `LowerProjectionDelta::Bound / Carrier`規則は、単純な誤りではなく
   **不完全なモデル**としてsupersedeする。同規則は
   「new claimed rootsが現れたか」を扱う一方、
   「producerのfirst qualified-parent batchでは、過去のbound derivationを
   広く再評価する必要がある」という別のsignalを表現できていない。
2. lower projection admissionは、少なくとも次の直交signalから計画する。
   - current eventで新しく現れたclaimed roots
   - producerがevent前にqualified parentを持っていたか
   - projection ledgerがevent前に存在したか
   - current eventのexact carrier
3. `LowerProjectionDelta::Bound / Carrier`を正解判定の中心に置かない。
   `ProjectionAdmissionPlan`を
   `ClaimedRootPlan`と`IndependentSupportPlan`へ分離する。
4. consumer #1のupper claim materializationは、unordered mapを直接mutationへ
   渡さず、same-root winnerを固定した後、`coverage_root`昇順のordered action
   vectorをcommitする。
5. consumer #3/#4のtarget-late lower initialization / lower bootstrapは、
   full bootstrapとincremental deltaを分離する。full bootstrapは
   all claimed rootsとall bound derivationsをpreflightし、既存のcanonical
   projection orderへ正規化したordered action vectorをcommitする。
6. consumer #5はBound / Carrier enumを返すclassifierではなく、
   安定したpre-event viewから`ProjectionAdmissionPlan`を構築するquery
   boundaryへ置き換える。
7. 既知5 consumer以外に6つのflat依存が存在する。そのうち4つは
   replay flat relationの物理撤去を直接阻害し、残る2つはRCPF-F固有の
   blockerではないがCPK cutover対象になる。
8. baselineは、順序を含む`SemanticExecutionSnapshot`と、集合・graphとして
   canonical化する`LogicalProofSnapshot`へ分離する。既知のlegacy内部不整合や
   HashMap iteration orderを新kernelのoracleにしない。

## 1. 背景

### 1.1 RCPF-F bold attemptで発見された未cutover consumer

RCPF-E完了後、legacy replay flat ledgerを物理撤去するRCPF-Fのexploratory
attemptを行ったところ、`claim_parents_by_constraint`のReplay variantを
productionで無条件に読むconsumerが5箇所残っていることが判明した。

1. `register_constraint_upper_replay_claims`
   — upper claim materialization
2. `register_premise_dependency_chain`
   — dependency-chain propagation
3. `register_lower_projection_derivation`
   — target-late lower initialization
4. `register_existing_constraint_lower_projection_delta`
   — lower projection bootstrap
5. `register_constraint_projection_carrier_delta_with_precommitted_clause_links`
   — bound-vs-carrier delta classification

このうち#2はcommit `2b810745`で
`ReplayReadAuthority::Factored / LegacyRollback` dispatchへcutover済みである。
#1/#3/#4/#5は未解決のままCPK計画へ引き継がれた。

### 1.2 Bound / Carrier divergence

consumer #5をfactored readへ切り替えようとした際、D materialization addendum
§3の規則と現行LegacyRollback挙動が一致しないことが判明した。

D addendum §3の規則:

```text
new roots nonempty && previously had no claimed roots
    -> LowerProjectionDelta::Bound(Constraint(producer))
otherwise
    -> LowerProjectionDelta::Carrier(carrier)
```

現行production codeは、次のflat parent length比較を使う。

```rust
!parents.is_empty()
    && claim_parents_by_constraint[producer].len() == parents.len()
```

この場合に`Bound(Constraint(producer))`、それ以外を`Carrier(carrier)`とする。

このlength比較はcommit `cc53f749`
（`perf(infer): delta-materialize lower claim proofs`、2026-07-31）で導入され、
D addendumのlandingより前から存在する。導入時の意図は、producerのbound
derivationがqualified-parent admissionより先に存在した場合、first batchだけ
constraint全体のderivationを再評価することだった。

したがって現行length比較は、偶然次の2つを同時に近似している。

1. producerにとって最初のqualified-parent batchか
2. current eventで新しいclaimed rootが現れたか

D addendum §3は後者だけを明文化し、前者を表すsignalを持たない。このため、
D addendumのliteral ruleへそのまま切り替えると
`cdm_a_9_4_independent_then_claimed_keeps_both_occurrences`が要求する
independent-support bootstrapを失う。

本書はこの2つを別々の契約へ分離する。

## 2. Production proof writer / consumer inventory

### 2.1 分類

本inventoryではcurrent stateを次の4区分で記録する。

- **Single-current**: 現行の単一proof storeだけが存在し、
  Factored / LegacyRollback dispatchを持たない。
- **Dual-write / Factored-read**: legacyとfactoredへ二重書きするが、
  Factored authorityのproduction readはfactored側を使う。
- **Dual-write / Flat-read**: 二重書きされているにもかかわらず、
  Factored authorityでもproduction readがflat側へ残る。
- **Oracle-only flat**: production authorityでは使わず、
  parity / rollback oracleとしてのみflat側を読む。

### 2.2 Production writer inventory

#### Source boundary / origin

Production writers:

- `ConstraintMachine::alloc_source_boundary`
- `ConstraintMachine::record_source_boundary_location`
- `ConstraintMachine::record_root_origin`
- `ConstraintMachine::attach_root_origin_to_existing_subtype`
- `ConstraintMachine::enqueue_canonical_subtype_with_origin`

Written state:

- `origins`
- `source_boundaries`
- `ConstraintRecord::root_origins`

Consumers:

- generalized witness capture
- `constraints/explain.rs`
- portable provenance export
- diagnostics
- provenance coverage/timing

状態: **Single-current**。

#### Constraint derivation / canonicalization provenance

Production writers:

- `enqueue_canonical_subtype_with_origin`
- `enqueue_replay_subtype`
- `merge_replay_derivation`
- `merge_structural_derivation`
- `merge_constraint_canonicalization_disposition`
- `merge_scheme_instantiation_routes`
- `enqueue_row_derived_subtype`

Written state:

- `ConstraintRecord::structural_derivations`
- `ConstraintRecord::row_derivations`
- `ConstraintRecord::replay_derivations`
- `ConstraintRecord::scheme_instantiation_derivations`
- `ConstraintRecord::scheme_instantiation_routes`
- `ConstraintRecord::canonicalization_dispositions`
- `ConstraintRecord::replay_provenance`
- replay drop / completeness state

Consumers:

- lower/upper replay planning
- row derivation traversal
- lower projection initialization
- generalized witness capture
- explanation / portable export

状態: **Single-current**。CPK event vocabularyへ移す対象である。

#### Bound provenance / disposition

Production writers:

- `TypeBounds::add_lower`
- `TypeBounds::add_upper`
- `record_bound_provenance`
- `record_bound_disposition`
- `record_pruned_bound_dispositions`
- `merge_scheme_instantiations_into_lower_bound`
- `merge_unweighted_row_reduction_derivation`

Written state:

- `BoundRecord::derivations`
- `BoundRecord::disposition`
- `bound_dispositions`
- promotion / pruning / equivalence provenance

Consumers:

- lower×upper replay planning
- projection bootstrap
- generalized witness capture
- explanation / portable export

状態: **Single-current**。active boundのsemantic fieldsはSemantic Kernelへ残し、
derivation/dispositionだけをProof Kernelへ移す。

#### Row / subtract / effect provenance

Production writers:

- `intern_row_derivation`
- `record_subtract_fact`
- `row_derivation_parents`
- `record_lower_filter_provenance`
- `register_unweighted_row_reduction`
- `merge_unweighted_row_reduction_derivation`

Written state:

- `row_derivations`
- subtract fact derivations/uses
- lower filter records
- row residual derivations
- unweighted reduction provenance
- reduction claim / coverage state

Consumers:

- row/effect solver
- replay routing
- projection formula construction
- explanation / portable export

状態: row residual/reductionの状態はsemantic、derivation edgeは
**Single-current proof state**。CPKではopaque row derivation handleを介して分離する。

#### Generalized scheme / instantiation provenance

Production writers:

- `alloc_generalized_scheme_record`
- `intern_scheme_instantiation`
- `record_scheme_instantiation_use`

Written state:

- `generalized_schemes`
- `generalized_witnesses`
- `scheme_instantiations`
- instantiation index / completeness

Consumers:

- cache/export
- portable provenance
- diagnostics
- later same-session instantiation

状態: **Single-current**。session ID lifecycleを保ったままCPK exporterへ移す。

#### Upper replay claims / coverage

Production writers:

- `original_upper_replay_claim`
- `derived_upper_replay_claim`
- `insert_upper_record_claim_canonical`
- `move_upper_replay_claim`
- `insert_scheme_projection_live_coverage_state`
- `remove_scheme_projection_live_coverage_state`

Written state:

- `upper_replay_claims`
- `claims_by_upper_record`
- original/derived/root indices
- `live_coverage_by_root`
- reduction claim ownership

Consumers:

- replay routing
- upper/lower projection
- projectability evaluator
- generalized witness / diagnostics

状態: **Single-current**。upper record内のclaim orderはD addendum §12により
`coverage_root`昇順へcanonical化済み。

#### Claim-parent relation

Legacy production writers:

- `commit_claim_qualified_parent_mutation`
  - `TypeBounds::push_claim_qualified_parent`
  - `qualified_carrier_index`
- `register_replay_claim_parents_with_factored_drafts`
  - `replay_claim_parent_keys`
- `merge_structural_claim_parents`
  - `structural_claim_parent_keys`
- `register_reduction_route_claim_parent`

Factored production writers:

- `ParentSetArena::preflight_extend / commit_extend`
- `ReplayOccurrenceStore::try_insert / update_parent_versions`
- `ReplayResultSummary::try_record_admission`
- `NonReplayClaimParentStore::try_admit`

状態: **Dual-write**。consumerごとのread authorityは§2.3および§2.4で固定する。

#### Projection support ledger

Production writers:

- `link_scheme_projection_claim_to_constraint_lower`
- `link_scheme_projection_claim`
- `update_scheme_projection_proofs`
- `register_lower_projection_derivation`
- `register_existing_constraint_lower_projection_delta`
- `register_lower_projection_delta`

Written state:

- `scheme_projection_claims_by_lower_record`
- `projection_proofs_by_lower_record`
- root-to-lower reverse indices
- claimed lower owners

Consumers:

- `scheme_projectable_lowers`
- `SchemeProjectionEvaluator`
- generalized projection readers
- generalized witness capture
- explanation / portable export

状態: 現行canonical flat ledgerがproduction authority。
CPKの`ProjectionFormulaStore`へcutoverする対象である。

#### Clause / link / attribution

Legacy production writers:

- `TypeBounds::register_record_proof_clause_link`
- `commit_record_proof_clause_link_batch_mutation`
- `register_original_claim_standalone_link`
- structural/reduction claimed-link writers
- `register_replay_evidence_clause_link`
- independent standalone-link writer

Factored replay writer:

- `ReplayClauseProjection::try_project_replay_parents`

Written state:

- `record_proof_clauses`
- clause key/index
- expanded clause-link Vec/HashSet
- all-source attributed claims
- flat-retained attributed claims
- replay-attributed claims
- occurrence-to-clause projection

状態:

- claimed replay attribution / exact replay link:
  **Dual-write / Factored-read**
- Original / structural / reduction / evidence attribution:
  Factored readはflat-retained union
- independent support link:
  **Flat-read**

#### Dependency index

Production writers:

- `insert_dependent_record_edge`
- `register_claim_parent_dependency_chain`
- `register_new_constraint_premise_route_edges`
- clause-link batch publication

Written state:

- `dependent_records_by_premise`

Consumers:

- projection invalidation
- recursive projectability evaluation
- publication impact traversal

状態: consumer #2のreplay traversalは
**Factored / LegacyRollback dispatch済み**。dependency index自体は現行単一store。

### 2.3 既知5 consumerの現在地

#### #1 `register_constraint_upper_replay_claims`

要求する情報:

- producerに属する全qualified roots
- rootごとのexact representative parent
- same-root cross-kind first winner
- derived lineage
- deterministic mutation order

現在地: **Dual-write / Flat-read**。

`try_authoritative_upper_materialization_full`等のfactored adapterは存在するが、
production writerは`claim_parents_by_constraint`をhistorical orderで直接走査する。
adapterの`UpperMaterializationLineages`はunordered mapであり、mutation planを
losslessに表現しない。

#### #2 `register_premise_dependency_chain`

要求する情報:

- replay occurrenceの`lower` / `upper`
- structural/reduction non-replay parent
- root coverage premise

現在地: **Factored / LegacyRollback dispatch済み**（commit `2b810745`）。

#### #3 `register_lower_projection_derivation`

要求する情報:

- target-late時の全claimed roots
- lower recordのbound derivation
- independent carrier
- clause/link bootstrap

現在地: **Dual-write / Flat-read**。

#### #4 `register_existing_constraint_lower_projection_delta`

要求する情報:

- ledgerなしの場合のfull exact-parent view
- ledgerありの場合のcurrent-event delta
- rootごとのexact representative claim

現在地: **Dual-write / Flat-read**。

#### #5 bound-vs-carrier classification

要求する情報:

- producerがevent前にqualified parentを持っていたか
- current eventのnew claimed roots
- projection ledgerのpre-event状態
- current exact carrier

現在地: **Dual-write / Flat-read**。flat parent Vec lengthを複数signalのproxyに
している。

### 2.4 新たに見つかった6つのflat依存

#### A. Structural parent propagation

場所:

- `crates/infer/src/constraints/machine/entry.rs`
- `merge_structural_claim_parents`（現在およそ1458行）

挙動:

親constraintの`claim_parents_by_constraint`を全件cloneし、structural childへ
`StructuralConstraint` parentとして伝播する。

分類: **RCPF-F blocker**。

Replay variantを物理撤去すると、replay由来rootのstructural childへの伝播が
消える。CPKでは親semantic factに結び付いたcanonical occurrence/root queryを
使う必要がある。

#### B. Target-late clause-projection bootstrap

場所:

- `crates/infer/src/constraints/machine/bounds.rs`
- `register_replay_claim_parents_with_factored_drafts`
  （現在およそ4345行）
- local `bootstrap_clause_projection_parents`

挙動:

target lower recordが存在しprojection ledgerがまだない場合、Factored admission中
でも`claim_parents_by_constraint[result]`の全parentをcloneし、
clause projection bootstrapへ渡す。

分類: **RCPF-F blocker**。

CPKでは#3/#4のfull bootstrap planがclause/formula actionも同時に供給する。

#### C. Reduction-route exact dedup

場所:

- `crates/infer/src/constraints/machine/bounds.rs`
- `register_reduction_route_claim_parent`
  （現在およそ4719行）

挙動:

新しい`ReductionRouteConstraint` parentのexact duplicate判定を
flat parent Vecの`contains`で行う。

分類: **RCPF-F blocker**。

CPKではcanonical occurrence keyまたはnon-replay parent keyのmembership queryへ
置き換える。

#### D. Independent / qualified carrier classification

場所:

- `crates/infer/src/constraints/machine/bounds.rs`
- `projection_carrier_is_independent`
  （現在およそ4079行）

挙動:

Replay / Structural / ReductionRoute carrierがqualifiedかを
`qualified_carrier_index`から無条件に読む。

分類: **RCPF-F blocker**。

#5のlength classifierとは別のread siteだが、同じ
`ProjectionAdmissionPlan`構築時にcanonical qualification queryへ統合する。

#### E. Factored replay clause projectionのflat clause-ID参照

場所:

- `crates/infer/src/constraints/replay_factored.rs`
- `ReplayClauseProjection::try_project_replay_parents`
  （現在およそ1205行）

挙動:

factored occurrence/rootをprojectする際、flat
`record_proof_clause_by_key`および`record_proof_clause_link_keys`を読み、
factored occurrence-to-clause mappingを作る。

分類: **CPK-only cutover target**。

これはclaim-parent Replay variant撤去だけなら直接のRCPF-F blockerではない。
ただし単一`ProjectionFormulaStore`へ移るCPKでは、formula/clause identityを
canonical store自身が所有しなければならない。

#### F. Independent supportのflat expanded-link read

場所:

- `crates/infer/src/constraints/mod.rs`
- `SchemeProjectionEvaluator::support_has_clause_link`
  （現在およそ1448行）
- `SchemeProjectionProofSupport::Independent` branch

挙動:

Factored authorityでも
`record_proof_clause_links_by_lower_record`をlinear scanする。

分類: **CPK-only cutover target**。

RCPF-Eの対象はclaimed replay linkだったため、これはE closureの漏れではない。
CPKではindependent supportを含む全formula queryを単一storeへ移す。

### 2.5 Inventory completeness boundary

本inventoryは次をproduction proof mutation boundaryとして扱う。

- origin/source-boundary registration
- constraint/bound/row/subtract/scheme derivation registration
- replay occurrence/parent registration
- claim/root/coverage registration
- projection support/formula/link/dependency registration
- generalization witness/portable provenance registration

`machine/propagate.rs`はproof storeを直接mutateしない。
`enqueue_derived_subtype`、`merge_structural_derivation`、
`enqueue_row_derived_subtype`を通じて上記boundaryへ到達する。

今後CPK-0cで、このinventory外から旧proof fieldへ書くproduction writerまたは
読むproduction consumerが見つかった場合、本書のcompleteness failureとして
扱う。

## 3. Bound / Carrier divergenceの解消

### 3.1 Supersedeする範囲

本書はD materialization addendum §3の次の部分だけをsupersedeする。

```text
new roots nonempty && previously had no claimed roots
    -> LowerProjectionDelta::Bound(Constraint(producer))
otherwise
    -> LowerProjectionDelta::Carrier(carrier)
```

D addendumの他の決定、特に次は変更しない。

- Phase A / B / C ordering
- complete pre-event view
- same-root first winner
- canonical lower projection order
- canonical upper claim order
- diagnostic order isolation
- attempt-level Factored / LegacyRollback authority
- failure時のwhole-attempt discard

### 3.2 Projection admission input

Projection admissionの判断材料を次のtyped inputへ分離する。

```rust
struct ProjectionAdmissionInput {
    producer: ConstraintRecordId,
    lower_record: Option<BoundRecordId>,

    qualified_parent_batch_inserted: bool,
    had_qualified_parent_before: bool,
    projection_ledger_existed_before: bool,

    all_claimed_roots_after_event: Vec<ClaimedRootEntry>,
    new_claimed_roots: Vec<ClaimedRootEntry>,

    event_carrier: Option<ProjectionProofCarrier>,
}

struct ClaimedRootEntry {
    root: UpperReplayClaimId,
    representative_claim: UpperReplayClaimId,
}
```

規則:

- `had_qualified_parent_before`はcurrent batchをcommitする前のproducer単位
  canonical relationから取得する。
- lower recordのclaimed-root有無で代用しない。
- `qualified_parent_batch_inserted`はexact parentが1件以上新規commitされた場合だけ
  trueとする。duplicate batchをfirst batchとして扱わない。
- Replayの`new_claimed_roots`は`ReplayResultSummaryDelta.entries`に相当する。
- non-replayの`new_claimed_roots`はincoming parentのcanonical rootと
  pre-event root setとの差分から得る。
- `all_claimed_roots_after_event`はfull bootstrap時だけ使い、result-localな
  canonical root queryから得る。
- `event_carrier`は現在のexact derivation/carrierであり、rootやparent listから
  再推測しない。

### 3.3 Projection admission plan

```rust
struct ProjectionAdmissionPlan {
    claimed_roots: ClaimedRootPlan,
    independent_supports: IndependentSupportPlan,
}

enum ClaimedRootPlan {
    None,
    Delta(Vec<ClaimedRootEntry>),
    FullBootstrap(Vec<ClaimedRootEntry>),
}

enum IndependentSupportPlan {
    None,
    EventCarrier(ProjectionProofCarrier),
    ProducerFullScan(ConstraintRecordId),
    RecordFullBootstrap(BoundRecordId),
}
```

意味:

- `ClaimedRootPlan::Delta`:
  current eventで新しく現れたrootだけをlinkする。
- `ClaimedRootPlan::FullBootstrap`:
  target-late / ledger-late initializationのため、event後に存在する全rootをlinkする。
- `EventCarrier`:
  current exact carrierだけをindependent support候補として評価する。
- `ProducerFullScan`:
  `BoundDerivation::Constraint(producer)`が保持するroot origin、structural、
  replay、row、scheme-instantiation derivationを再評価する。
- `RecordFullBootstrap`:
  lower recordの全`BoundDerivation`を再評価する。

`ProducerFullScan`と`RecordFullBootstrap`はproof graph全体のglobal scanではない。
前者は単一producer、後者は単一lower recordにscopeされた局所bootstrapである。

### 3.4 Plan construction rule

次の順序でplanを構築する。

1. `lower_record == None`なら両planを`None`とする。
2. exact no-opで、新parent・new root・event carrierのいずれも存在しない場合、
   両planを`None`とする。
3. projection ledgerがevent前に存在せず、
   `all_claimed_roots_after_event`も空なら、projection ledgerを新設しない。
4. projection ledgerがevent前に存在せず、
   event後にclaimed rootが存在する場合:
   - `ClaimedRootPlan::FullBootstrap(all_claimed_roots_after_event)`
   - `IndependentSupportPlan::RecordFullBootstrap(lower_record)`
5. projection ledgerが既に存在し、
   `qualified_parent_batch_inserted == true`かつ
   `had_qualified_parent_before == false`の場合:
   - claimed sideは`new_claimed_roots`が空なら`None`、非空なら`Delta`
   - independent sideは`ProducerFullScan(producer)`
6. 上記以外でledgerが存在する場合:
   - claimed sideは`new_claimed_roots`だけの`Delta`または`None`
   - independent sideは`event_carrier`があれば`EventCarrier`、なければ`None`
7. `RecordFullBootstrap`と`ProducerFullScan`が同時に成立する場合、
   record full bootstrapがproducer scanを包含するため
   `RecordFullBootstrap`だけを実行する。
8. root entriesとsupport entriesはcommit前にcanonicalize / exact-dedupする。
9. 全fallible lookup / allocationをpreflightしたあと、
   prepared planを部分失敗のない形でcommitする。

### 3.5 Claim workとindependent workの独立性

次の組み合わせを正当なplanとして許容する。

- new rootsあり、independent workなし
- new rootsなし、producer full scanあり
- full root bootstrap + full record bootstrap
- new rootsなし、event carrierのみ
- 両方なしのexact no-op

特に「new rootsなし、producer full scanあり」が必要である。
pre-existing direct claimとfirst replay arrivalのcounterexampleはこの形になる。

`Bound`という名前で両方を同時に表すことを禁止する。

## 4. Known fixtureによる規則検証

### 4.1 `cdm_a_9_4_independent_then_claimed_keeps_both_occurrences`

事前状態:

- lower recordにはindependent derivationがある。
- claimed rootがないためprojection ledgerはまだない。
- producerにqualified parentが初めて到着する。

Plan:

```text
ClaimedRootPlan::FullBootstrap(all roots)
IndependentSupportPlan::RecordFullBootstrap(lower record)
```

結果:

- incoming claimed supportが追加される。
- 先に存在していたindependent derivationも全record bootstrapで回収される。
- claimed occurrenceとindependent occurrenceの両方が残る。

### 4.2 Pre-existing direct claim + first replay arrival

事前状態:

- lower projectionにはOriginal/direct claimed rootが既にある。
- projection ledgerは存在する。
- flat replay-parent listは空。
- producerにはqualified parentがまだない。

Plan:

```text
ClaimedRootPlan::Delta(new roots) または None
IndependentSupportPlan::ProducerFullScan(producer)
```

incoming replayが既存direct rootと同じrootなら`new_claimed_roots`は空になる。
それでもfirst qualified-parent batchなのでproducer full scanは実行する。

結果:

- 既存rootを重複追加しない。
- producerの過去のbound derivationを必要どおり再評価する。
- legacy length proxyの`Bound`とD §3 literal ruleの`Carrier`という
  見かけ上の対立自体が消える。

### 4.3 Duplicate / exact no-op replay

事前状態:

- producerは既にqualified parentを持つ。
- rootもexact carrierも既に存在する。

Plan:

```text
ClaimedRootPlan::None
IndependentSupportPlan::None
```

または、呼び出しboundaryがevent carrierを渡す場合でも、
exact qualification queryが既存qualified carrierと判定して実効supportはゼロとなる。

結果:

- claimed proofを重複追加しない。
- producer full scanを再実行しない。
- allocation、epoch、publicationを発生させない。

### 4.4 Target-late lower creation

事前状態:

- producerのclaim-parent relationは既に存在する。
- lower recordが後から生成される。
- lower recordのprojection ledgerは存在しない。

Plan:

```text
ClaimedRootPlan::FullBootstrap(all roots)
IndependentSupportPlan::RecordFullBootstrap(lower record)
```

結果:

- 全claimed rootsをexact representative付きで初期化する。
- lower recordの全bound derivationを一度だけ分類する。
- replay / structural / reduction / independent formulaを同じpre-event
  snapshotから構築する。
- expanded legacy replay linkの存在をbootstrap入力にしない。

## 5. Consumer #1: upper claim materialization

### 5.1 現在のgap

`register_constraint_upper_replay_claims`はtarget-late materialization時に
flat parent Vecをhistorical orderで走査する。

既存factored adapterは
`FxHashMap<(BoundRecordId, UpperReplayClaimId), UpperReplayClaimLineage>`を返す。
このmapはrootとlineageの集合を比較するoracleには使えるが、次を保持しない。

- derived claimのallocation順
- mutation/publication順
- same-root representativeのexact action
- no-op/reuse/createの区別を含むlossless mutation plan

RCPF-D4の最初のattemptで多数のfixtureが失敗した原因は、logical mapの一致を
mutation sequenceの一致と誤認したことにある。

### 5.2 Ordered materialization action

```rust
struct UpperClaimMaterializationAction {
    record: BoundRecordId,
    root: UpperReplayClaimId,
    representative_parent: ClaimQualifiedParent,
    lineage: UpperReplayClaimLineage,
    disposition: UpperClaimActionDisposition,
}

enum UpperClaimActionDisposition {
    ReuseRootAtRecord,
    ReuseDerivedClaim,
    CreateDerivedClaim,
}
```

target-late full queryは、producerのcanonical root集合からrootごとに1 actionを作る。

規則:

1. same-root winnerはwriter boundaryで固定された
   `FirstQualifiedParentSource`を読む。
2. winnerがReplayなら、first witnessが指すexact occurrence / side /
   representative claimを使う。
3. winnerがStructural / ReductionRouteなら
   `NonReplayClaimParentStore`のexact parentを使う。
4. root claimの`current_record == record`なら`ReuseRootAtRecord`。
5. `(record, root)`のderived claimが既に存在すれば`ReuseDerivedClaim`。
6. それ以外を`CreateDerivedClaim`。
7. actionsを`coverage_root: UpperReplayClaimId`昇順へsortする。
8. sort済みvector全体をpreflightしてから順番にcommitする。
9. qualified rootがゼロの場合だけ、従来どおりOriginal/direct claimを作る。
10. `admission_ordinal`はsame-root first winnerの証拠にだけ使い、
    cross-root sort keyには使わない。

### 5.3 Delta path

same-event eager materializationはfull root setを再走査せず、
current `ReplayResultSummaryDelta` / non-replay root deltaからactionを作る。

delta内でもaction orderは`coverage_root`昇順とする。
既存canonical storageへのposition insertionが最終格納順を保証する場合でも、
allocation ID・lineage depth・publication sequenceをHashMap iterationへ
依存させない。

### 5.4 Single canonical storeによる単純化

旧RCPFでは、Replay first witnessとNonReplay parent storeが別々に存在し、
cross-kind winner mapで両者を再結合していた。CPKでは1つの
`ProofOccurrenceStore`が次を同時に保持する。

- canonical result/root membership
- exact occurrence/carrier
- parent side
- representative claim
- first winner source
- lineage class

これによりFactored / LegacyRollback間の再構成問題は消える。

ただし、次は単一storeでも自然には決まらない。

- cross-root mutation order
- derived ID allocation order
- diagnostic/truncation prefixへ流れる順序

したがって、single store化はordered action vectorを不要にはしない。
必要なcanonicalizationを1箇所で実行できるようにする。

## 6. Consumer #3/#4/#5

### 6.1 #3: target-late lower initialization

`register_lower_projection_derivation`がtarget-late lower recordを初期化する場合、
次のcomplete inputをmutation前にpreflightする。

- producerの全canonical claimed root
- rootごとのexact representative claim
- lower recordの全`BoundDerivation`
- 各derivationから得られるindependent carrier
- replay occurrenceごとのconjunction clause
- structural/reduction routeごとのunary clause
- standalone support clause
- dependency premises

出力はunordered集合ではなく、次のordered action vectorとする。

```rust
enum LowerProjectionAction {
    EnsureClaimedSupport(ClaimedRootEntry),
    EnsureIndependentSupport(ProjectionProofCarrier),
    EnsureClause(ProjectionClauseAction),
    EnsureDependency(ProjectionDependencyAction),
}
```

Primary support order:

1. Claimed support
2. Independent support

Claimed内:

- canonical root昇順

Independent内:

- 既存`canonical_projection_key::carrier_cmp`のtotal order

同じsupportに属するformula action:

1. `Standalone`
2. `DerivedUnary`
3. `ReplayConjunction`

同一category内はtyped carrier / premise / record keyのtotal orderを使う。
生のHashMap iteration、flat parent admission history、expanded link Vec順を
mutation orderにしない。

clauseとdependency edgeは、そのsupport/formula actionに結び付いた形でcommitする。
全lookupとallocationを先にpreflightし、supportだけが存在してformulaが欠ける
中間状態をconsumerへ公開しない。

### 6.2 #4: lower bootstrap

`register_existing_constraint_lower_projection_delta`は次の2経路へ分ける。

```text
projection ledgerなし
    -> FullBootstrap
projection ledgerあり
    -> Delta
```

`FullBootstrap`:

- `all_claimed_roots_after_event`
- lower recordの全bound derivations
- 全formula / dependency action

を使う。

`Delta`:

- `new_claimed_roots`
- `IndependentSupportPlan`
- current eventが新しく作るformula / dependency action

だけを使う。

root entryは`(canonical root, exact representative claim)`を保持する。
同じrootへより新しいrepresentative claim IDが必要になった場合、
現在の`update_scheme_projection_proofs`と同様、canonical positionを変えず
representativeだけを更新する。

### 6.3 #5: classifierの廃止

consumer #5は、今後`LowerProjectionDelta::Bound / Carrier`を返さない。

代わりに次の責務を持つpre-event query boundaryとする。

```rust
fn prepare_projection_admission(
    view: &impl SemanticFactView,
    proof: &impl ProofFactView,
    event: &PreparedProofEvent,
) -> Result<ProjectionAdmissionPlan, ProofFailure>;
```

このboundaryが次を明示的に読む。

- producerのpre-event qualified membership
- lower recordのpre-event projection ledger
- accepted event delta
- canonical root membership
- exact event carrier

「first qualified batch」「new claimed root」「ledger bootstrap」
「event carrier classification」を別々に計算し、最後に
`ProjectionAdmissionPlan`へ合成する。

## 7. Canonical action orderの共通契約

consumer #1/#3/#4は次の共通規則に従う。

1. unordered relationはquery結果として許容するが、
   mutation inputとして直接反復しない。
2. same-root winnerはwriter boundaryで一度だけ固定し、iterator順から再計算しない。
3. cross-root orderはhistorical admission orderではなくcanonical root orderとする。
4. claimed / independent support orderはD addendumで承認済みの
   canonical projection comparatorへ従う。
5. exact carrier identityはdedupしても失わない。
6. canonicalization後のordered action vector全体をpreflightする。
7. commit中に新しいfallible lookupやallocationを行わない。
8. actionの論理集合だけでなく、ID allocation、epoch、publication、
   generalized witness、portable provenance、diagnostic prefixまでparity対象にする。
9. canonical relationに順序が不要な場合でも、user-visible diagnosticへ届く
   mutation sequenceは明示的なorderを持つ。
10. admission ordinalをcross-root canonical orderの代用品にしない。

## 8. Baseline capture design

### 8.1 二層に分ける理由

CPK移行では次の2種類を区別する必要がある。

- solverのcontrol flowや出力を変え得る、順序込みのsemantic execution
- relation / graphとして同値ならよいproof state

両者を1つのsnapshotへ混ぜると、次のどちらかが起こる。

- HashMap / internal ID順まで固定して新kernelの自由度を失う
- normalizationがsemantic queue orderの変化を隠す

したがってbaselineを`SemanticExecutionSnapshot`と
`LogicalProofSnapshot`へ分離する。

### 8.2 `SemanticExecutionSnapshot`

```rust
struct SemanticExecutionSnapshot {
    queue_events: Vec<SemanticQueueEvent>,
    constraints: Vec<SemanticConstraintSnapshot>,
    bounds: Vec<SemanticBoundSnapshot>,
    replay: ReplayExecutionSnapshot,
    row: RowExecutionSnapshot,
    publication: PublicationSnapshot,
    scc: SccExecutionSnapshot,
    output: SemanticOutputSnapshot,
}
```

#### Queue

記録対象:

- enqueue ordinal
- dequeue ordinal
- `ConstraintWork` kind
- canonical semantic key
- producer semantic ID
- admission outcome

outcome:

- enqueued
- canonical duplicate
- trivial
- evidence-only
- rejected/pruned/subsumed

raw pointer/hash iteration順ではなく、semantic factのfirst-seen ordinalへ正規化する。
enqueue/dequeueのsequence自体は正規化せず、そのまま比較する。

#### Constraints

記録対象:

- canonical subtype key
- canonical record creation order
- semantic disposition
- queue admissionの有無
- canonical constraint count

proof derivation listはここへ含めない。

#### Bounds

記録対象:

- TypeVarごとのlower/upper record order
- direction
- endpoint
- weights
- active/tombstoned state
- promotion/subsumptionによるsemantic survivor

`BoundRecord::derivations`とdiagnostic dispositionは
`LogicalProofSnapshot`へ置く。

#### Replay counts / dispositions

記録対象:

- input/generated
- accepted
- canonical duplicate
- trivial
- evidence-only
- prefiltered
- prefilter duplicate/trivial
- queue admission count
- stored semantic constraint count

既存`ConstraintTiming`のreplay countersを基礎にする。

#### Row state

記録対象:

- row residual keyとfresh tail
- residual creation/reuse
- original/remaining/consumed items
- current reduced upper
- unweighted reduction ownership
- subtract facts
- lower filters
- row semantic events

row derivation graphそのものは`LogicalProofSnapshot`へ置く。

#### Publication / epoch

記録対象:

- exact `ConstraintEvent` sequence
- semantic `ConstraintEpoch`
- provenance/publication epoch sequence
- owner invalidation key sequence
- projectability inclusion transition

proof-only eventがsemantic queueを増やしていないこともここで確認する。

#### SCC

記録対象:

- `SccStats`
- exact `SccEvent` sequence
- merge/component-edge/quantify/instantiate/open-use order
- generalization restart census

#### Output

記録対象:

- DefId順のfinalized schemes
- public formatted scheme
- raw scheme dump
- alpha-equivalence view
- role predicates
- unresolved selections
- lowering errors
- diagnostics/check report
- poly arena dump
- compiled namespace/lowering/runtime surface

### 8.3 `LogicalProofSnapshot`

```rust
struct LogicalProofSnapshot {
    occurrences: Vec<CanonicalProofOccurrence>,
    claim_relation: Vec<CanonicalClaimRelationEntry>,
    projection: Vec<CanonicalProjectionEntry>,
    dependencies: Vec<CanonicalDependencyEntry>,
    generalized: CanonicalGeneralizedProvenance,
    portable: CanonicalPortableProvenance,
}
```

#### Proof occurrences

記録対象:

- semantic result key
- typed cause
- exact carrier
- parent roots
- parent side
- completeness
- proof event class

session-local numeric IDはcanonical first-seen mappingへ変換する。

#### Claim relation

記録対象:

- result
- canonical root
- exact representative claim
- side
- exact replay/structural/reduction carrier
- same-root first winner
- lineage class

relation全体はcanonical keyでsortする。historical parent Vec長は記録しない。

#### Projection

記録対象:

- lower record
- claimed root support
- independent carrier support
- formula clause
- exact clause/support link
- root/lower reverse membership
- projectability logical result

support orderはcanonical projection comparatorを使う。
formulaは§6.1のtyped orderを使う。

#### Dependency

記録対象:

- `ProofPremise`
- dependent lower record
- transitive invalidation result

HashSet iteration順は比較しない。

#### Generalized / portable provenance

記録対象:

- generalized witness role/path
- exact incoming parents
- completeness
- portable nodes/edges/source sites
- root anchors
- truncation prefix
- diagnostic cause order
- duplicate-span survivor / primary span

### 8.4 Baselineに含めてはならないもの

次を新kernelのoracleにしない。

- `claim_parents_by_constraint`の生Vec長
- `LowerProjectionDelta::Bound / Carrier` tag
- HashMap / HashSetのiteration order
- duplicate shadow storageのcapacity
- legacy/factoredで既知不一致の内部state
- test helperが作る不完全な片側fixture
- allocation address
- sessionを跨いで意味を持たないraw ID

既知のlegacy不整合を「現行だから正しい」として固定することを禁止する。

### 8.5 Reuseする既存fixture

#### `constraints/tests/case_01.rs`

既に近いもの:

- exact `ConstraintEvent`
- basic subtype/bound replay
- row/weight admission
- bound record assertions

主に`SemanticExecutionSnapshot`のqueue/bound/publication面へ使う。

#### `constraints/tests/case_02.rs`

既に近いもの:

- CDM/MPC/DPN observer snapshots
- row residual/reduction state
- mixed claimed/independent projection
- one-sided row cases
- projection inclusion

semantic row snapshotとlogical projection snapshotの両方へ使う。

#### `constraints/tests/characterization.rs`

既に近いもの:

- canonical constraint count
- duplicate/trivial counts
- lower/upper replay counters
- row residual counters
- provenance coverage
- poly/check fingerprints

`SemanticExecutionSnapshot`のreplay/count/output面へ使う。

#### `constraints/machine/bounds.rs`のCDM/DPN/RCPF fixtures

既に近いもの:

- `CdmLowerOracleSnapshot`
- `CdmOracleLedgerSnapshot`
- carrier-order snapshot
- target-late consumer/publication snapshot
- canonical projection permutations
- first-winner oracle
- clause/dependency census
- portable consumer snapshot

`LogicalProofSnapshot`の主要fixtureとして再利用する。

#### `lowering/body/generalize_snapshot_characterization_tests.rs`

既に近いもの:

- finalized schemes
- residual role predicates
- unresolved selections
- generalization restart census
- SCC stats/events
- diagnostics
- poly/runtime surface

`SemanticExecutionSnapshot`のSCC/generalization/output面へ使う。

#### `pusp_characterization.rs` / portable explanation tests

既に近いもの:

- parameter/scheme provenance lifecycle
- generalized witness
- portable identity
- export budget/truncation
- explanation cause order

`LogicalProofSnapshot`のlifecycle/portable面へ使う。

## 9. CPK-0の残りスライス

### CPK-0a: `SemanticExecutionSnapshot`

目的:

- semantic queue order
- canonical constraint order
- bound order
- replay counts/dispositions
- row state
- publication/epoch sequence
- SCC stats/events
- final scheme/output

をtest-only snapshotとして固定する。

制約:

- production behaviorを変更しない。
- proof-only instrumentationがqueueへworkを追加しない。
- raw IDを比較する場合、そのID order自体がsemantic contractであることを
  明示する。
- normalizationでqueue/order mismatchを隠さない。

### CPK-0b: `LogicalProofSnapshot`

目的:

- current RCPF/CDM/MPC/DPNのlogical proof outputをcanonical keyで固定する。
- legacy flat relationとfactored relationのstorage shapeではなく、
  consumer-visibleなproof graphを比較する。
- §3〜§7で決めたprojection admissionとcanonical action契約を
  characterization fixtureとして表現する。

制約:

- D §3の旧Bound / Carrier tagをoracleにしない。
- 生HashMap orderをsnapshotへ露出しない。
- source boundary、exact carrier、parent side、representative、lineage、
  completenessを落とさない。

### CPK-0c: Inventory completeness assertion + fixture matrix

目的:

- §2の全writer/consumerがtest matrixへ対応していることを確認する。
- 新しいproduction writer/read consumerがinventory外へ増えた場合、
  testまたはcompile-time inventory checkで検出する。
- root/structural/row/replay/evidence/reduction/scheme-instantiationの全sourceを
  fixture matrixで覆う。
- full bootstrap / producer scan / event delta / exact no-opをそれぞれ固定する。

CPK-0cのexit条件:

- inventory外のproduction proof writerがゼロ
- inventory外のproduction proof consumerがゼロ
- semantic baselineが固定済み
- logical proof baselineが固定済み
- known counterexampleが§3のplanで一意に説明できる
- legacy内部不整合をoracleとして残していない

## 10. Correctness invariants

1. 本書自身はproduction behaviorを変更しない。
2. proof-only mutationはsemantic queueへworkを追加しない。
3. semantic constraint/bound admission順をproof storage都合で変更しない。
4. projection admissionはcomplete pre-event viewから計画する。
5. `had_qualified_parent_before`はproducer単位のpre-event relationから取得する。
6. lower recordのclaimed-root有無をfirst qualified-parent判定の代用品にしない。
7. `new_claimed_roots`とfirst qualified-parent batchを同じboolean/enumへ畳まない。
8. first qualified-parent batchはnew rootがゼロでもproducer full scanを要求できる。
9. exact no-opはroot link、independent scan、allocation、epoch、publicationを
   発生させない。
10. ledger-late/target-late initializationはfull rootsとfull bound derivationsを
    同じsnapshotから構築する。
11. same-root representativeはfirst-winsであり、iterator順から再導出しない。
12. exact carrier、parent side、lineage classをcanonicalizationで失わない。
13. cross-root action orderはcanonical root orderとし、admission ordinalを使わない。
14. claimed supportはindependent supportより前に格納する。
15. independent carrier orderは既存canonical total comparatorと一致させる。
16. formulaのORおよびReplayConjunction内部のAND semanticsを変更しない。
17. structural/reduction sourceをreplay-only storeへ混入させない。
18. structural childへのreplay-root propagationをflat ledger撤去時に失わない。
19. full bootstrap以外のeager eventでresult-global/graph-global scanを行わない。
20. unordered relationをmutation inputとして直接反復しない。
21. prepared actionのcommit中に新しいfallible allocationを行わない。
22. proof commit失敗後のpartial attemptからscheme/outputを返さない。
23. semantic baselineの順序差をlogical normalizationで隠さない。
24. logical proof baselineはraw storage shapeではなくconsumer-visible graphを比較する。
25. portable provenanceとdiagnostic truncation prefixはcanonical action orderに従う。
26. session-local IDをportable identityとしてserializeしない。
27. row derivation handleはsemantic coreからopaqueであり、dangling handleを作らない。
28. legacy/factoredの既知不一致を新kernelの正解oracleにしない。
29. Original / ReplayConstraint / ReplayEvidence / StructuralConstraint /
    ReductionRouteConstraintの5 lineageを維持する。
30. `Any` / `Never` / `Unknown`の型意味およびcore subtype semanticsは
    本書の対象外であり、一切変更しない。

## 11. Stop conditions

CPK-0a〜CPK-0cまたは後続CPK実装で次を観測した場合、現在のsliceを停止し、
本書へ戻って設計を再検討する。

1. inventory外のproduction proof writer/read consumerが見つかった。
2. consumer #1のordered action vectorだけではlegacy-visible
   ID/epoch/publication sequenceを再現できない。
3. same-root winnerをcanonical storeから一意に取得できない。
4. target-late bootstrapがhistorical flat parent orderを意味論として必要とする。
5. formula actionのtyped orderがportable provenanceまたはdiagnostic cause集合を
   変更する。
6. `ProducerFullScan`が単一producerを超えるglobal scanを必要とする。
7. `RecordFullBootstrap`が単一lower recordを超えるglobal scanを必要とする。
8. exact no-opでallocation、epoch、publicationのいずれかが増える。
9. `cdm_a_9_4_independent_then_claimed_keeps_both_occurrences`の
   independent occurrenceが失われる。
10. pre-existing direct claim + first replayで、既存rootの重複claimed proofが増える。
11. duplicate/no-op replayがproducer full scanを再実行する。
12. structural propagationでreplay-rootまたはexact lineageが失われる。
13. semantic queue enqueue/dequeue sequenceが変わる。
14. per-variable lower/upper bound orderが変わる。
15. replay accepted/duplicate/trivial/evidence dispositionが変わる。
16. row residual/reduction stateが変わる。
17. SCC event sequenceまたはgeneralization restart countが変わる。
18. finalized scheme、poly/check output、diagnosticsが変わる。
19. snapshot normalizationが実際のsemantic mismatchを吸収している。
20. CPK event vocabularyだけでは既存writerの意味をlosslessに表現できない。
21. allocation failure atomicityをprepare/commitまたはwhole-attempt discardで
    保証できない。
22. mandatory routing/projectability factをdiagnostic completeness budgetへ
    混入させる必要が生じる。
23. implementationが本書の範囲を超えてcore worklist/subtyping/row/SCC/
    generalization algorithmを変更し始める。

stop conditionに該当した場合、fixture期待値を新実装へ合わせて変更してはならない。
原因と不足したcontractを特定し、必要なら別の署名付き追補を作る。

## 12. Non-goals

本書は次を行わない。

- production codeの変更
- RCPF-Fの再開
- legacy flat ledgerの削除
- Factored / LegacyRollback authorityの削除
- subtype worklist algorithmの変更
- bound combination algorithmの変更
- row/effect reduction semanticsの変更
- SCC algorithmの変更
- generalization/finalization semanticsの変更
- diagnostics期待値の変更
- performance optimizationの実装
- CPK-1以降のproduction slice開始の認可

本書はCPK-0のcontractを確定する設計文書であり、実装artifactではない。

## 13. 波及する文書

本書がユーザ承認を経て正本になった後、必要に応じて次へ参照を追加する。

- `notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md`
  - CPK-0節から本書を参照する。
  - D §3 divergence、consumer #1/#3/#4/#5、追加6依存が解決済みであることを
    記録する。
- `notes/design/2026-08-03-rcpf-d-materialization-projection-addendum.md`
  - §3のBound / Carrier classifierが本書§3によりsupersedeされたことを注記する。
  - 他のD invariant/order契約は引き続き有効と明記する。
- `notes/design/2026-08-02-replay-claim-parent-factorization.md`
  - RCPF-Fを阻害した既知5 consumerと追加4 blockerを本書へリンクする。
- `notes/architecture/claim-propagation-architecture.md`
  - 現行flat/factored consumer inventoryの置換先として本書を参照する。

これらの文書更新は本書本文のlandingとは別変更として扱う。

---

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定

状態: **ユーザ承認済み（2026-08-05）**

Claudeによる査読（主要関数名の実在確認を含む）とユーザ承認を経て、
本書は設計判断の正本として扱う。§9のCPK-0a / CPK-0b / CPK-0cから
着手してよい。production behaviorを変更する実装（CPK-1以降）は、
CPK-0のexit criteria達成後に別スライスとして進める。
