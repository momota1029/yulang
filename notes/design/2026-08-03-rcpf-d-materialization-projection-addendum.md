# RCPF-D 追補: upper claim materialization / lower projection の factored 化設計

日付: 2026-08-03

状態: **ユーザ包括的事前承認済み（2026-08-03）**

著者: Claude (Sonnet 5)、Codex `gpt-5.6-sol`（xhigh）の調査・設計提案に基づき統合・記述。

**署名についての注記**: このリポジトリの正本文書は通常、個別の内容をユーザに提示して
具体的な承認を得る形を取る。本書はその通常手順とは異なる——2026-08-03 10:28 JST、
ユーザは「進めます．私はこれから外出します．全ての権限を許しますので，メンテナンス
作業を17:00まで続けてください．きちんと時間は計ってください」という包括的事前承認を
与えて外出した。本書はこの承認の範囲内で、RCPF-D実装再開前に必要だった設計判断
（RCPF-Dが単純な read-side swap では成立しないと判明した点）を埋めるために起案した。
[[2026-08-02-dpn-root-claim-and-cycle-safety-addendum]]・[[2026-08-01-urr-v3-causal-qualification]]
と同様、Codex Sol XHighの調査・設計提案をClaude (Sonnet 5)が検証・統合する形を取ったが、
今回はさらに「ユーザが個別内容を未読のまま包括的に許可した」という点で例外性が重なる
——通常より慎重な自己レビュー（既存23 invariantとの照合、独立検証、スコープの小ささ）を
徹底することでこの差分を埋める。ユーザが後で本書を確認した際、内容に異論があれば
訂正・撤回できるよう、状態欄には「包括的事前承認済み」と明記し、通常の「ユーザ承認済み」
とは区別する。

本書は `notes/design/2026-08-02-replay-claim-parent-factorization.md`（RCPF文書）
§11 の RCPF-D 節（「`first_parent_by_root`を使うupper claim materializationと
lower projection」）が、実装するには具体化が不足していたために生じた追補である。
RCPF-C3d（production cutover、commit `a52dfd44`）着地後にRCPF-D実装を試みたところ、
単純な read-side swap（C1〜C3dが踏襲してきたパターン）では成立せず、3点の追加設計が
必要と判明した。この追補はRCPF文書の中核決定を改廃せず、この3点だけを補う。

## 0. 本書が下す決定の要約

1. **result-local index の追加**: `ReplayResultSummary::first_parent_by_root`
   （既存、`(ConstraintRecordId, UpperReplayClaimId) -> FirstReplayParentWitness`の
   flat map）はそのまま維持し、`first_parent_roots_by_result:
   FxHashMap<ConstraintRecordId, FxHashSet<UpperReplayClaimId>>`という
   順序を持たないsibling indexを追加する。これによりresult単位での列挙が
   global scanなしでO(そのresultのroot数)で可能になる。
2. **commit順序の修正**: 既存のper-event flowを、同一admission event内で
   「factored summary commitをmaterializationより前」へローカルに並べ替える。
   新しいbatch/pass概念は導入しない。
3. **legacy mutation / factored commit+health / factored依存publication の
   3段階分離**: quarantine/retry追補の§3.3と同じ規律で、
   Phase A（legacy data mutation、常に無条件）→
   Phase B（factored commit + health check、これ以降だけをgate）→
   Phase C（factored依存のderived mutation、health成功時のみ）
   という順序契約を導入する。C3d後のevaluatorがFactored sourceを読むため、
   Phase A中にafter-evaluation/publicationを走らせると不完全なfactored stateを
   観測してしまう——これがC3bの単純な「順序入れ替え」だけでは足りない理由。
4. RCPF-C3a の whole-attempt discard と `LegacyRollback` をそのまま使う。
   event-level rollbackは追加しない。

## 1. 背景

RCPF-C3d着地後、RCPF-D（「`first_parent_by_root`を使うupper claim
materializationとlower projection」）の実装を試みた。当初の想定は
C1〜C3dと同じ「read consumerをlegacyからfactoredへ切り替えるだけ」という
単純なswapだったが、実装途中（282行のprototype、テスト追加前）で
以下の3点が絡み合っていることが判明し、scope-creep stop conditionにより
安全に撤退した。

1. `first_parent_by_root`にはresult単位で効率よく列挙するindexが無く、
   materialization/projection consumerが「このresultのroot全部」を
   問い合わせるにはglobal scan（性能制約違反）が必要になってしまう。
2. 現在のfactored summary commit（`try_record_admission`）は、
   admission event内でupper/lower materializationより後に実行されている。
   D consumerがこのevent由来のsummaryを読むには順序変更が必要。
3. その順序変更を素直に行うと、C3bで確定した大原則
   （legacy mutationは絶対にfactored healthにゲートされない）に
   抵触するリスクがある。さらにC3d後は、evaluatorがFactored sourceを
   読むため、Phase A（legacy mutation）中に不用意にafter-evaluation/
   publicationを走らせると、まだfactored commitが済んでいない
   不完全な状態を観測してしまう、という新しい危険が生じる。

## 2. Design 1: result-local index

### 現状

```rust
ReplayResultSummary {
    first_parent_by_root:
        FxHashMap<(ConstraintRecordId, UpperReplayClaimId), FirstReplayParentWitness>,
    projected_parent_versions: FxHashSet<...>,
}
```

`FirstReplayParentWitness`は`occurrence`・`parent_side`・`parent_claim`・
`admission_ordinal`を持つ。`try_record_admission`はlegacy admission順で
`inserted_parents`を処理し、`(result, root)`ごとに最初のwitnessだけを
記録する（既存entryは上書きしない）。現時点でproduction consumerは無く、
B1のwriter・debug oracle・census・testだけがこれを触っている。
既に出荷済みのこの状態を再構成する利点は無く、むしろrollbackリスクを
増やすだけなので、既存構造の変更ではなくsibling追加を選ぶ。

### 決定

```rust
first_parent_roots_by_result: FxHashMap<ConstraintRecordId, FxHashSet<UpperReplayClaimId>>
```

（名前自体に意味はなく、構造だけが重要）。既存のflat mapが唯一の
witness authorityであり続け、siblingはそのresultに属するroot集合だけを
保持し、`FirstReplayParentWitness`を複製しない。

クエリ形は:

```text
roots = first_parent_roots_by_result[result]
for root in roots:
    witness = first_parent_by_root[(result, root)]
```

コストはO(そのresultのroot数)、witness lookupは期待O(1)。global scanは
一切発生しない。

### commit契約

`try_record_admission`は引き続きlegacy順の`inserted_parents`から勝者を
決定する。意味論的なmutationの前に、pending witness storage・
pending-root dedup storage・outer result-index容量・result-local root
set・`first_parent_by_root`・`projected_parent_versions`の全てを
preflightで予約する。preflightに成功したpending rootだけが両indexへ
入る。片方のindexにだけ存在するrootはcorruptionであり、`panic`ではなく
`ReplayFactoredResult`として返す。no-claim・exact no-op admissionは
outer result entryもroot setも作らない（no-claim passthrough、
invariant 17を維持）。

### クエリ面

`first_parent_by_root`と`first_parent_roots_by_result`の両方を
個別に露出するのではなく、小さな追加APIにまとめる:

```text
roots_for_result(result)
first_parent_witness(result, root) -> ReplayFactoredResult<Option<Witness>>
preflight_witnesses_for_result(result) -> ReplayFactoredResult<一時collection>
```

full/bootstrap consumerは、derived claimやprojection proofを
mutateする前に、indexされた全rootとwitnessを一時的なresult-local
collectionへ検証してから使う。これにより、途中で見つかったcorrupt
rootが、部分的にmaterializeされたPhase Cを残すことを防ぐ。

### 同一event delta

`try_record_admission`は、すでに構築済みのaccepted summary deltaを
返すべきである:

```rust
struct ReplayResultSummaryDelta {
    entries: Vec<(UpperReplayClaimId, FirstReplayParentWitness)>,
}
```

これは永続的なRCPF identityではなく一時的なevent state。current
eventの勝者列を、result indexの再スキャンやroot listの再割り当てなしに
保持する。late-root eager materializationはこのdeltaを消費し、
target-late/bootstrap materializationはresult-local indexを消費する。

### Invariant 23（診断順序分離）との整合

first-admission順で保持する永続`Vec<(root, witness)>`は、たとえ
「単なるindex」と説明されても却下する——historical root orderを
永続化し、診断・provenanceコードから参照可能にしてしまうため。
`FxHashSet`は集合意味論を与える: membershipは永続的、historical
insertion orderはidentityではなく、hash iteration orderは契約では
ない。`admission_ordinal`はwitness evidenceのまま残り、診断順序を
再構成するライセンスにはしない。

D oracleはこれらをunordered mapとして比較する:
`(result, root) -> first witness`、`(record, root) -> derived
lineage`、`(lower_record, root) -> claimed support`。同一event
deltaに限っては、永続化しないため現在のevent順を一時的に保持しても
構わない。

target-late bootstrapは明示的なdiagnostic-order gateが必要。root
enumerationの変更がportable provenance・explanation edge order・
その他user-visibleな順序を変えるなら、実装を停止する。admission順の
永続化や`admission_ordinal`ソートで穴埋めしてはならない
（§4.7とinvariant 23への違反になる）。真にuser-visibleな順序依存が
見つかった場合は、別途diagnostic層の正規化設計が必要になる。

## 3. Design 2: commit順序の修正

### 現状の欠陥

`register_replay_claim_parents_with_factored_drafts`は現在:

```text
legacy exact/flat parent admission
eager upper/lower materialization
factored occurrence + ReplayResultSummary commit
factored clause projection
debug event oracle
```

の順で実行している。つまりfactored materialization consumerは、
自分のevent由来のsummary deltaをまだ見ることができない。

### 決定

既存のper-event flowを維持し、ローカルに並べ替える。post-batch pass
は導入しない。目標のevent flowは:

```text
0. complete pre-event inclusion/publication stateを取得
1. legacy exact/flat/carrier/link/edge dataを無条件でcommit
2. factored occurrence/parent versions/result summary/local indexをcommit
3. factored clause projectionをcommitし、pre-consumer health checkを走らせる
4. D consumerが必要とする全factored witnessをpreflight
5. そのdeltaからupper claimとlower claimed-root projectionをmaterialize
6. post-consumer equivalence oracleを走らせる
7. complete post-event stateを評価し、deferred net mutationをpublish
```

`LegacyRollback`ではstep 2を無効化し、step 5はlegacy adapterを読む。
authorityはattempt全体で固定されたまま。

### 具体的な関数への影響

`register_replay_claim_parents_with_factored_drafts`がevent
orchestratorになる: legacy admissionは引き続き最初かつ無条件、
`observe_factored_replay_parent_admission`はeager materializationより
前へ移動し、accepted `ReplayResultSummaryDelta`を受け取る。eager
materializationはhealth成功後にのみそのdeltaを消費する。

`try_observe_factored_replay_parent_admission`は
`ReplayFactoredResult<ReplayResultSummaryDelta>`を返すよう変更し、
occurrence・parent sets・summary・result-local indexをcommitし、
factored clause projectionを行い、derived-lineage event oracleの
内部実行は止める。

`materialize_existing_claim_parents_delta`は、生のreplay
`ClaimQualifiedParent`行ではなく、選択されたsource/deltaを受け取る
よう変更する。

`register_constraint_upper_replay_claims`はtarget-late full consumer
になる: replay parentsはresult-local summary indexから、
structural/reduction parentsは既存のnon-replay flat facadeから。
legacy clause-link mutationは、ここでの隠れたside effectとしては
もう発生しない。

`register_constraint_upper_replay_claims_delta`は、replay rootに
対してaccepted summary deltaを消費しつつ、小さなnon-replay delta
経路は維持する。

`register_lower_projection_derivation`と
`register_existing_constraint_lower_projection_delta`は同じmerged
facadeを使う: replay claimed rootsはsummaryから、
structural/reduction rootsはnon-replay flat storeから。

`register_constraint_projection_carrier_delta`は、full flat Vecの
長さをfirst-admission classifierとして使うのを止める必要がある。
代わりにPhase C以前にlower recordが既にclaimed rootsを持っていたか
どうかを捕捉する:

```text
new roots nonempty && previously had no claimed roots
    -> LowerProjectionDelta::Bound(Constraint(producer))
otherwise
    -> LowerProjectionDelta::Carrier(carrier)
```

result/root summaryに新規entryが無いoccurrenceは、別のclaimed proof
を追加してはならない。

`register_claim_parent_clause_links`はlegacy-onlyになるべきである。
現在の`observe_factored_replay_clause_projection`呼び出しは、
occurrence/summary commit後の明示的なPhase B配線へ移動する。これは
順序分離だけであり、RCPF-Eのlink cutoverそのものではない。

`observe_factored_replay_event_boundary`はPhase Cの後へ移動する
——derived-lineage比較が完了したmaterializationを必要とするため。
storage/index整合性チェックはPhase Cより前のまま。

### なぜ別passが不要か

`try_record_admission`は既に、その`(result, root) -> witness`の
新規entryを正確に計算している。この一時的なdeltaをeager
materializationへそのまま返せば、同一eventの入力として直接使える。

full result-local enumerationが必要なのはtarget-late bootstrapだけ。
どちらのケースも、単一のresultと単一の自然なadmission boundaryへ
scopeされたままである。

## 4. Design 3: legacy / factored commit / factored依存publicationの3段階分離

### C3d後の追加ハザード

単純な並べ替えだけでは、C3d後は安全ではない。

`admit_claim_qualified_parent`は現在:
`before evaluation → legacy flat mutation → route-edge mutation →
after evaluation → publication`
という順で実行される。`commit_record_proof_clause_link_batch`も
同様にbefore/after evaluationとpublicationを内部で行う。
`apply_scheme_projection_mutation`は即座に評価・publishする。

`SchemeProjectionEvaluator`がC3d後、`ReplayEvaluatorSource::Factored`
の下でfactored stateを読むようになったため、Phase A中に実行される
after evaluationは、新しいlegacy link/parentは見えるが、現在の
factored occurrence/summaryはまだ見えない、という不完全な混在状態を
観測してしまう。

### 順序契約

quarantine/retry追補§3.3と同じ規律を用いる:

```text
complete pre-event state
    ↓
before evaluation / publication snapshot
    ↓
A. legacy data mutation（無条件）
    exact keys
    flat claim-parent ledger
    qualified-carrier index
    legacy clause/link relation
    dependency edges
    ↓
B. factored commit
    parent sets
    occurrence
    result/root summary + result-local index
    factored clause projection
    storage/query health check
    ↓
C. factored依存のderived mutation
    upper derived claims
    lower claimed-root proofs
    reverse-index updates
    ↓
post-consumer oracle
    ↓
complete after evaluation
    ↓
deferred epoch/cache/provenance publication
```

### Phase Aの規則

Phase Aは、以下のいずれが起きても常にcommitする: factored
allocationが後で失敗する、summary検証が失敗する、D consumerの
queryが失敗する、post-consumer oracleが失敗する。特に、次のいずれも
factored status checkで囲んではならない: `replay_claim_parent_keys.insert`、
`push_claim_qualified_parent`、legacy clause/link登録、
dependency-edge登録、qualified-carrier登録。

replay pathには、「publicationを伴わないcommit」形の
`admit_claim_qualified_parent`と`commit_record_proof_clause_link_batch`
の内部版が必要になる。既存のnon-replay callerは通常の即時publication
wrapperを維持してよい。

### Publication fence

event-localな`ReplayAdmissionPublicationFence`（または同等のもの）
を導入する。これは一時的な制御状態であり、永続化されるRCPF identity
ではない。ローカルに影響を受けるrecordだけについて、pre-event
inclusion stateを捕捉する: `ProofPremise::Constraint(result)`の
dependents、target lower record、そのlower recordのtransitive
dependents、acceptedされたdeltaによって影響を受けるresult-local
roots。upper/projection mutationが返す既存のmetadata/provenance
publication intentも記録する。この影響範囲はgraph-localであり、
bound/claim/constraintのglobal scanは一切許可しない。

Phase Cとpost-consumer oracleの後、fresh evaluation roundがこの
before stateとcomplete final stateを比較する。既存のpublication
policyを維持しなければならない: 中間的なflipをpublishしない、
active ownerは既存の自然な境界内でdedupする、owner/global epoch
挙動は現行のまま、現行のmetadata/provenance bump policyは変更しない、
異なるresult/lower-record/admission boundaryをmergeしない。

D は§9.5のmetadata-only discrepancyを黙って「クリーンアップ」しては
ならない。`LegacyRollback`特性テストで、deferred fenceが現行経路と
同じowner/global/provenance epoch列を生成することを証明する必要が
ある。証明できなければ、停止して別のepoch-policyスライスとして
設計する。

### 失敗時の挙動

Phase Bまたはそのpre-consumer queryが失敗した場合: terminal
`Failed`をmarkする、Phase Cを実行しない、after evaluationを走らせ
ない、fenceをpublishしない、Phase Aをundoしない、C3aにmachine全体を
discardさせてfixed `LegacyRollback`でretryさせる。

Phase C後のpost-consumer oracleが失敗した場合: terminal `Failed`を
markする、deferred publicationを抑制する、attempt全体をdiscardする、
event-level rollbackは追加しない。

これは修正済みC3bと同じ原則である: legacy mutationは既に起きており、
shadow healthに条件付けられることは決してない一方、factored依存の
read/publicationは、失敗したattemptから決して漏れ出さない。

`ConstraintMachine::drain`は既存のwork-item境界でのみ停止し続ける。
RCPF-Dは2つ目のdrain/failure機構を追加しない。

## 5. 実装スライスの分割

各スライスは概ね150〜200 net行以内を目標とする。超える場合は、
testを分けるか、1つのpublication primitiveをその自然な境界で
分割する——D をRCPF-Eやepoch-policy cleanupと混ぜてはならない。

### RCPF-D1 — Result-local summary index

対象: `ReplayResultSummary`、additive unordered per-result root
index、fallible consistency/query helper、single/multiple/no-root・
allocation-failureのテスト。production consumerの切替は無し。

### RCPF-D2a — Qualified-parent deferred publication primitive

対象: replay legacy parent/route mutationとinclusion publicationの
分離、event-local before snapshotの追加、既存non-replay wrapperは
不変のまま維持、`LegacyRollback`挙動とepoch列が不変であることの証明。
summaryの並べ替えはまだ行わない。production関数2〜4個が対象。

### RCPF-D2b — Clause-link mutation/publication separation

対象: `commit_record_proof_clause_link_batch`の分割、
`register_claim_parent_clause_links`をlegacy-onlyにする、factored
clause projectionを明示的なorchestrationへ移動、injectedされた
factored failure下でもlegacy linkとdependency edgeがcommitされる
ことの検証。RCPF-D の順序基盤であり、RCPF-Eのread cutoverではない。

### RCPF-D2c — Summary delta and same-event ordering

対象: `ReplayResultSummaryDelta`の追加、
`try_observe_factored_replay_parent_admission`経由でのreturn、
`register_replay_claim_parents_with_factored_drafts`の並べ替え、
complete event oracleをderived mutationの後へ移動、health failure後に
after/publicationが発生しないことの検証。必要ならこのスライスでは
production sourceをlegacyのまま維持し、rollbackを小さく保つ。

### RCPF-D3a — Upper materialization adapter and shadow oracle

対象: summary index/delta経由のreplay full/delta adapter、
non-replay flat facade経由のstructural/reduction merge、
`(record,root)->lineage`をlegacyと比較、single root・multiple
candidate claims・late root・no root・target-late bootstrapを
カバー。production authority cutoverはまだ行わない。

### RCPF-D3b — Lower projection adapter and shadow oracle

対象: summary由来のclaimed-root入力、`qualified_carrier_index`の
維持、flat-length classifierをpre-event claimed-root stateへ置換、
proof vector/logical support map・reverse index・epochの比較、
occurrence-new/root-old と独立-first→claimed-laterをカバー。
mixed replay/non-replay same-rootのfixtureを両方のadmission順で
含める。inter-kind historical orderingを要求するmismatchは
stop condition。

### RCPF-D4 — Authority cutover

対象: upper/lower D consumerがattempt-level `ReplayReadAuthority`
からsourceを導出する、`Factored`はD adapterを使う、
`LegacyRollback`はlegacy adapterを使う、factored依存の
Phase C/publicationに対するPhase B health gateを有効化する、
legacy writeは全て無条件のまま維持する。upperとlowerは両方の
shadow oracleが通ってから一緒にcutoverする——これによりrollbackが
小さなadapter選択の変更のままになる。

## 6. Invariant checklist（RCPF §10 の23項目との照合）

1. Exact carrier identity: exact keyとoccurrence identityは不変。
   result-local indexはrootだけを持ち、carrier identityには答えない。
2. Exact parent relation equivalence: Phase Aが全legacy exact行を
   無条件で維持。factored occurrence/parent-set equivalenceは既存の
   event oracleでカバーされ続ける。
3. Exact keyの無条件性: 既存のsummary rootが新しいcarrier key・
   flat row・occurrence・clauseを抑制しない。summary dedupは
   root由来の帰結にのみ影響する。
4. First representative: `try_record_admission`は引き続きlegacy順の
   parentを処理しfirst-winsを適用。index/attachment側の反復は
   勝者を再計算しない。
5. Event-time snapshot: rootとrepresentativeはadmission draftと
   committed parent versionsから来る。現在のendpoint liveness
   からは来ない。
6. Covered/uncovered equivalence: planningとdraft構築は不変。
   Dはその結果を消費するだけ。
7. Result/root canonicality: `derived_claim_by_record_and_root`が
   引き続きauthoritative。新rootは`(record, root)`ごとに一度だけ
   materializeされる。
8. Occurrence/clause correspondence: legacy linkはPhase Aでcommit、
   factored clause projectionはPhase Bでoccurrence単位にcommit。
   root追加のみでは重複clauseを作らない。
9. Logical link equivalence: D2bはlegacy exact link mutationと
   既存のfactored projection oracleを維持。RCPF-Eがproduction
   link-read cutoverの責任を負う。
10. Occurrence attribution: result-local summaryはroot-to-clause
    membershipの推測には使わない。`ReplayClauseProjection`と
    occurrence parent versionsが引き続きauthoritative。
11. Consumer equivalence: D3 oracleがD4より前に、upper lineage・
    lower claimed support・generalization/portable provenance・
    diagnostics・epochを比較する。
12. DPN premise semantics: Record/Constraint/RootCoverage規則は
    無変更。replay materialization/projectionの入力選択だけが
    変わる。
13. Cycle safety: before/afterは別のfresh roundを使う。round内で
    部分的なfactored queryをfallbackしない。
14. Admission時完全性: summary commitとderived materializationは
    同一event内に留まる。repair pass・flush pass・後段fixpointは
    導入しない。
15. Insertion-order invariance: 入力の順列それぞれが、自身のlegacy
    streamで直接選ばれた勝者を比較する。永続的なresult enumeration
    順は勝者選択に使わない。
16. Atomic net publication: publication fenceが中間のafter
    evaluation・publicationを全て抑制する。complete post-event
    stateだけがpublishされる。
17. No-claim passthrough: 空のadmissionはoccurrence・summary
    delta・outer result index entry・materialization・publication
    を一切作らない。
18. Append-only: witness mapとresult-local root setは共に
    append-only。liveness駆動の削除・再分類は現れない。
19. Summary separation: sibling indexは「このresultでどのrootが
    first witnessを持つか」にのみ答える。exact qualificationは
    occurrence storeに残る。
20. Reverse-index維持: 既存の
    `scheme_projection_lower_record_memberships`更新経路が引き続き
    authoritative。D3bがこれをlegacyと明示的に比較する。
21. No global scan: eager consumerはevent deltaを使い、bootstrap
    consumerは単一resultのroot setだけをscanし、invalidationは
    localなdependency edgeだけを辿る。
22. No permanent evaluation memo: 新indexはadmitted input
    membershipを保持し、projectabilityは保持しない。evaluator memo
    はround-localのまま。
23. Diagnostic order isolation: admission順に並んだ永続Vecは追加
    しない。representative lineageは同一のまま。explanation graph
    のsourceと順序は不変。unordered root enumerationへの診断/
    provenance依存が観測された場合はcutover stop conditionであり、
    永続化や再構成の根拠にはしない。

## 7. Rollback

各スライスは独立rollback可能: D1（index追加のみ、consumer切替なし）
→ D2a/D2b（publication primitiveの分離、production挙動は不変）
→ D2c（同一event順序の変更、production sourceは必要ならlegacyの
まま維持可能）→ D3a/D3b（shadow oracleの追加のみ、production
authority cutoverなし）→ D4（実際のcutover、adapter選択を
Legacyへ戻すだけでrollback可能、D1〜D3bとfactored ledgerは残せる）。

D4のcutoverには2つの明示的なstop gateがある: `LegacyRollback`下で
deferred publicationが現行のowner/global/provenance epoch列を
再現すること、target-late・mixed replay/non-replay fixtureが
historical root orderへのconsumer-visibleな依存を示さないこと。
どちらかが失敗した場合は、admission-order indexやlocal workaroundで
穴埋めせず、別の承認済み設計改訂が必要になる。

## 8. 波及する文書（本書 landing 後に更新。本書では編集しない）

- `notes/design/2026-08-02-replay-claim-parent-factorization.md`
  （RCPF文書）: §11のRCPF-D節に、本書への参照と具体的なスライス分割
  （D1〜D4）を追記する。

## 9. 追補（2026-08-03、D3a着手時に発見されたcross-kind representative選択gap）

D2cシリーズ（D1/D2a/D2b/D2c-1/D2c-2a/D2c-2b/D2c-2c-1/D2c-2c-2a/
D2c-2c-2b）着地後、D3a（upper materialization adapter + shadow
oracle）の実装に着手したところ、本書が想定していなかった構造的
ギャップが見つかった。

### 9.1 問題

legacyのfull path（`claim_parents_by_constraint[result]`）は、
replay・structural・reductionの全parent kindが混在した実際の
admission順を走査し、`(record, root)`ごとに最初に承認されたparentの
lineageを採用する。

しかしfactored representationは、このプロジェクトの初期段階から
kindごとに分離している——replay parentのfirst-witness追跡はD1の
`ReplayResultSummary`（`first_parent_roots_by_result`/
`first_parent_witness`、`try_record_admission`内部のadmission
ordinalで管理）に、structural/reduction parentはC1の
`NonReplayClaimParentStore`（result単位のinsertion順`Vec`）に、
それぞれ存在する。どちらも「自分のkind内でのfirst-wins」は正しく
維持しているが、「replay parentとstructural/reduction parentの
どちらが実際に先に承認されたか」という相互の順序情報は、どちらの
索引にも存在しない。

このため、ある`(record, root)`をreplay parentとstructural/reduction
parentの両方が取り合う場合、factored側には legacy が実際に選ぶ
lineageを再構成する手段がなかった。D3aで組んだadapterは暫定的に
「replay優先」で実装されていたが、これは実際のadmission順で
structural/reductionが先だったケースでは誤りになる。

### 9.2 決定: cross-kind first-winner map

`first_parent_by_root`と同じ情報隠蔽の形（historical admission
順ではなく、単一のwinnerだけを保持する）を踏襲した、kind横断の
first-winner mapを追加する。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FirstQualifiedParentSource {
    Replay,
    NonReplay(ClaimQualifiedParent),
}
```

（`NonReplay`は`StructuralConstraint`または
`ReductionRouteConstraint`のみを許可する。）

```rust
first_qualified_parent_source_by_root:
    FxHashMap<(ConstraintRecordId, UpperReplayClaimId), FirstQualifiedParentSource>
```

この形を選ぶ理由:

- replay-vs-replayのwinner選択はD1が引き続きauthorityであり続ける
  （このmapは触れない）。
- structural-vs-reductionのwinnerは、最初のnon-replay parent自体を
  保持することで、後から`NonReplayClaimParentStore`を再走査せずに
  O(1)で正確なparentを取得できる。
- replay-vs-non-replayの勝敗はenum discriminantが決める。
- `Replay`側の具体的なclaim/side/carrierは複製せず、D1の
  `FirstReplayParentWitness`から解決する（`(result, root)`から
  `first_parent_witness`を引けばよい）。

追加クエリAPI（生のmap iteratorはproduction/diagnosticへ公開しない）:

```rust
try_record_first_qualified_parent_source(result, parent, bounds)
    -> ReplayFactoredResult<bool>

first_qualified_parent_source(result, root)
    -> ReplayFactoredResult<Option<FirstQualifiedParentSource>>
```

### 9.3 Writer位置

`commit_claim_qualified_parent_mutation`（D2aで作られた共通choke
point）に単一のwriter hookを置く。legacy flat parentの唯一のwriter
（`push_claim_qualified_parent`）はこの関数内にあり、replay path
（`replay_claim_parent_keys.insert`が成功したparentだけがここへ届く）
とstructural/reduction path（既存の`admit_claim_qualified_parent`
wrapper経由）の両方が同じ関数を通るため、二重のwriter hookを置く
必要はない。

```text
inclusion-before snapshot
legacy flat parent push
既存のnon-replay shadow observation
legacy route/dependency-edge mutation
cross-kind first-winner observation   ← 新設
return publication snapshot
```

map更新規則: canonical rootをfallibleに検証し、keyが既に存在すれば
完全なno-op（winnerを上書きしない、first-wins）。keyが無ければ
`try_reserve(1)`を先に行い、成功後だけinsertする。allocation
failureはterminal shadow failureとしてmark_replay_factored_failure
経由で記録し、legacy flat mutation・route edge・後続のPhase A
mutationは一切undo・gateしない（quarantine/retry追補の大原則を継承）。
`LegacyRollback`ではこのwriterを無効化し、legacy pathだけを使う。

### 9.4 D3aアダプタでの利用

full adapter:

1. replay rootsをD1のresult-local indexから列挙する。
2. structural/reduction rootsをC1のnon-replay facadeから列挙する。
3. 一時的なunordered root集合へ統合する。
4. 各rootを新しいcross-kind mapへpoint lookupする。
5. `Replay`ならD1のwitnessから、`NonReplay(parent)`なら保存された
   parentからlineageを組み立てる。
6. 全rootをpreflightしてからmaterializationへ渡す。

delta adapter: replay delta rootごとに新mapを読み、`Replay`なら
同event deltaのwitnessを、`NonReplay(parent)`なら保存済みの先行
winnerを使う。result全体やlegacy ledgerの再走査は発生しない。

### 9.5 Invariant 23（診断順序分離）との整合

この新しいmapはunordered finite mapであり、admission順のVecではない。
ordinal・timestamp・loser・イベント列・root間の順序は一切保存しない。
各entryが答えるのは「この`(result, root)`の単一winner sourceは何か」
だけであり、全entryを反復してもroot間のhistorical sequenceは
復元できない。同一root内で「winnerがloserより先だった」ことは
分かるが、これはlegacyと一致させるべきrepresentative lineageその
ものであり、既存の`first_parent_by_root`が既に保持している情報と
同じ性質である。diagnostic/provenance層へ生のiteratorは公開せず、
explanation graphのcategory/edge/hyperedge順序にも一切触れない。
debug oracleだけが、unordered mapとしてlegacy winnerと比較する。

関連invariantとの整合: invariant 4（first-winsで一度だけinsertし、
後続kindで上書きしない）、invariant 15（各入力順でlegacyが直接
選んだwinnerをadmission時に保存し、後からiteratorで再導出しない）、
invariant 17（accepted parentがないeventではentryを作らない）、
invariant 18（append-onlyで削除・再分類しない）、invariant 19
（`Replay`からcarrier-specific情報を推測せずD1のoccurrence/witness
へ問い合わせる）、invariant 21（write/queryは期待O(1)、full列挙も
既存のresult-local sourceだけを読む）。

### 9.6 D1への影響

D1の`first_parent_by_root`・`first_parent_roots_by_result`・
`ReplayResultSummaryDelta`・`admission_ordinal`の意味・writerは
変更不要。D1は引き続きreplay-vs-replayのfirst witness authorityで
あり続ける。cross-kind winnerが`NonReplay`側になったケースでも、
D1はreplay witnessを通常どおり記録する（exact replay relationや
将来のconsumerに必要なため、抑制しない）。新mapは完全にadditiveな
siblingであり、D1既存stateの再構築・backfill・restructureは不要。
event oracleには「`Replay`勝者ならD1のwitnessが存在する」という
整合検査だけを追加する。

### 9.7 実装スライスの再分割

RCPF-D3aの前に、新しい必須prerequisiteとして以下を挿入する:

- **RCPF-D3a-0a — Cross-kind winner store**: enum・map・fallible
  insert・point query・fault injection hookの追加。first-wins・
  no-op・allocation failure・storage censusのテスト。約80〜130行。
- **RCPF-D3a-0b — Phase A writer wiring**: 共通
  `commit_claim_qualified_parent_mutation`へのhook配線。
  replay-first/non-replay-first双方、structural/reduction双方、
  `LegacyRollback`、legacy-never-gatedのテスト。unordered legacy
  oracleの追加。約80〜130行。
- **RCPF-D3a（再開）**: `e323929d`で着地済みのshadow-only adapter
  primitivesを新しいwinner queryへ接続する。stashしてある
  oracle wiring差分（`stash@{0}`）は選択的に戻す。replay-firstと
  non-replay-firstの両方のsame-root fixturesを追加し、既存の
  single root・multiple replay candidates・late root・no root・
  target-late bootstrapのカバレッジも維持する。
- **RCPF-D3b**: 同じcross-kind winner mapをlower projectionの
  kind横断選択へ再利用する。両方のadmission順fixtureが一致する
  ことを必須gateにする。
- **RCPF-D4**: D3a/D3bの両方のshadow oracleが通るまで、authority
  cutoverには着手しない。

---

著者: Claude (Sonnet 5)（Codex `gpt-5.6-sol` xhigh の調査・設計提案を統合）

ユーザ包括的事前承認済み（2026-08-03）。本書は設計判断の正本として扱う。
実装は本書§5のRCPF-D1〜D4スライス、および§9のRCPF-D3a-0a/D3a-0bを
含む再分割スライス順に従って着手してよい。
