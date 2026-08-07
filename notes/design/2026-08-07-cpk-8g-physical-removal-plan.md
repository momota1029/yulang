# CPK-8G: 物理store撤去の詳細計画

日付: 2026-08-07

状態: **ユーザ承認済み（2026-08-07）**

著者: Codex gpt-5.6-sol（xhigh）が調査・起案、Claude (Sonnet 5) が査読・確定

**署名についての注記**: Fable 5 が一時的に利用できないため、このリポジトリの
「Fable 5 不在時の起案担当」の慣例に従い、本書は Codex `gpt-5.6-sol`（xhigh）が
本文を起案した。Claude (Sonnet 5) は、現行 code・既存正本文書（特に
`2026-08-07-cpk-8-legacy-removal-plan.md`）・invariant・stop conditionと照合して
査読し、ユーザの明示承認を経て本書を正本として確定した。

本書は、既承認の`notes/design/2026-08-07-cpk-8-legacy-removal-plan.md`（以下
CPK-8計画）§5 CPK-8Gを、CPK-8F完了（commit `f561c8d9`）後の現行codeに基づいて
具体化する。CPK-8計画自体は編集しない。本書はCPK-8計画§13の枠組みの中で、
§5 CPK-8Gの「8Aのdependency graphからleaf順を決め...」という指示を、現時点の
正確なinventoryと段階分割へ翻訳したものである。

## 1. 前提（CPK-8F完了時点）

- `ProofReadAuthority`・`ReplayReadAuthority`とも、通常productionの非test経路では
  automatic dispatchがゼロ（CPK-8D・CPK-8F-3で封印、CPK-8F-1・8F-4でdispatch自体を
  非test経路から除去済み）。
- `LegacyRollback` variant・explicit test constructor・flat/RCPF store/writer/reader
  そのものは、CPK-8計画の意図通りまだ全て残っている。

## 2. 現在のinventory（CPK-8F後の再確認）

### 2.1 Flat `TypeBounds`の残存proof-only field（27個）

- Claim arena/identity/coverage系 8: `upper_replay_claims`、
  `claims_by_upper_record`、`original_claim_by_record_and_producer`、
  `derived_claim_by_record_and_root`、`reduction_claim_by_state`、
  `root_claim_by_producer_constraint`、`live_coverage_by_root`、
  `replay_claim_cycle_coalesces`
- Qualified-parent関係 4: `claim_parents_by_constraint`、
  `qualified_carrier_index`、`replay_claim_parent_keys`、
  `structural_claim_parent_keys`
- Projection target/support/formula 7: `scheme_projection_lower_record_by_constraint`、
  `scheme_projection_lower_record_by_replay`、
  `scheme_projection_claims_by_lower_record`、`projection_proofs_by_lower_record`、
  `scheme_projection_lower_records_by_root`、
  `scheme_projection_lower_record_memberships`、
  `scheme_projection_claimed_lower_owners`
- Clause/attribution/dependency 8: `record_proof_clauses`、
  `record_proof_clause_by_key`、`record_proof_clause_ids_by_lower_record`、
  `record_proof_clause_links_by_lower_record`、`record_proof_clause_link_keys`、
  `attributed_claim_supports`、`flat_retained_attributed_claim_supports`、
  `dependent_records_by_premise`

`scheme_projection_lower_record_by_*`と`dependent_records_by_premise`は単純な
dead mirrorではなく、target-late linkageやpublication対象のclosureに現役で
使われている。削除ではなくCPK indexへの移管対象として扱う。

semantic frontier/worklist、`vars`、`canonical`、`records`、row/reduction
semantic stateはCPK-8計画§1.2.Aの保持対象のまま。

### 2.2 RCPF factored store（5つ、`ConstraintMachine`常設）

`ParentSetArena`・`ReplayOccurrenceStore`・`ReplayResultSummary`・
`ReplayClauseProjection`・`NonReplayClaimParentStore`。定義は
`replay_factored.rs`。付随して`ReplayReadAuthority`・
`ReplayFactoredShadowStatus`・parent-set/occurrence/draft/version ID・
RCPF failure/error/oracle type・RCPF専用soak telemetryも最終削除対象。

### 2.3 Migration/legacy machinery

`ProofReadAuthority`・`cpk_proof_oracle_active`・
`legacy_scheme_projectable_lowers`・routing/projection observation構造体
（`ReplayRoutingShadowToken`、`ShadowReplayRouteObservation`、
`ShadowReplayEventObservation`、`ShadowProjectabilityObservation`、
`ShadowProjectionPublicationObservation`）・`compare_projection_*_shadow`・
`begin/compare/finish_replay_routing_shadow`・`legacy_prepared_replay_route`・
`ProofOccurrenceStore`内の4 observation vector。

`YULANG_REPLAY_FRONTIER_SHADOW`等の環境変数はproof migration oracleとは
別目的のperformance instrumentationであり、名前だけを根拠に8Gで削除しない。

### 2.4 Test census の訂正

CPK-8E-7時点の「48件」（3 holdout + 1 permanent + 3 replacement-backed +
41 defer-to-8G）は、shared CDM fixture callerのcensusとしては正しいが、
**physical-removal用のcensusとしては不完全**だった。現HEADで再監査した結果：

- explicit Legacy authorityを直接構築するtest: **51件**
  （旧45件の内訳に加えて、`lower_and_upper_replay_planning_capture_legacy_parent_drafts`、
  `rcpf_d2c_2c_2a_deferred_clause_intent_preserves_immediate_value`、
  `rcpf_c3b_terminal_failure_stops_drain_before_the_next_queued_work`、
  `replay_claim_parent_dedup_keeps_each_exact_replay_carrier`、
  `target_late_legacy_rollback_reproduces_epoch_publication_and_consumer_sequences`、
  `rcpf_d4_4_quarantine_discards_attempt_without_legacy_retry`の6件が新たに
  確認された）
- routing count-parity holdout 3件を合わせて、authority/oracle依存の合計は
  **54件**。
- これとは別に、authorityを直接構築しないRCPF構造体unit testが
  `replay_factored.rs`に10件、`machine/bounds.rs`の`rcpf_*`に32件、
  `lowering/body/mod.rs`の`rcpf_*`に5件存在する（54件と一部重複するため
  単純加算不可）。

8G-0でこのcensusをsource-reference単位のphysical-removal manifestへ拡張する。

## 3. Claim-ID allocationの決定

### 3.1 決定

**CPK-owned dense claim arena**を採用する。不変条件
`UpperReplayClaimId == ProofOccurrenceStore.upper_claims の append index`を、
flat `Vec`からCPKの`Vec`へそのまま移す。

### 3.2 検討した候補と却下理由

| 候補 | 判定 | 理由 |
|---|---|---|
| Sparse/indexed flat arena | 却下 | flat側をallocation authorityのまま延命させ、CPK-8Gの削除目標そのものと矛盾する |
| 独立shared allocator | 却下 | proof IDをsemantic machineへ漏らし、allocator/storeの二重ownerを作る |
| CPK reservation→後でcommit | 単独では却下 | 失敗時にhole・partial publication・二重allocationのリスクを生む |
| CPK dense arena + atomic admission | **採用** | 現行ID・順序を維持したまま、ownerを一箇所に統合できる |

CPK-8Fのdispatch撤去はruntime branchを削減しただけで、allocationのblast
radius自体は大きく変わっていない。original/derived/reduction・claim move・
routing・generalization・projection publicationに跨るため、最低3コミット
（original allocator、derived/reduction allocator、claim move/coverage）
に分ける。

### 3.3 前提として必要な作業

現在の`UpperClaimOccurrence`は粗い`ProjectionLineage`しか持たず、
ReplayEvidence carrier・parent side・lineage depth等を復元できない。
allocation移管前に、flat側の`UpperReplayClaimLineage`と同等の情報量を
CPK-owned typed payloadへ移す必要がある（8G-2a）。`source`・`endpoint`・
`weights`はsemantic `BoundRecord`から`current_record`経由で取得可能なため、
CPK proof recordへ複製はしない。

### 3.4 Atomicity契約

新規claimは単一transactionで扱う：(1) CPK indexからexisting/newを決定、
(2) 全Vec/Map capacityをpreflight、(3) `next_id == upper_claims.len()`を
検証、(4) claim・dedup index・record index・projection linkageをcommit、
(5) 移行期間中は同じCPK-issued IDをflat mirrorへcommit、(6) IDをcallerへ
返す。予約だけを先に公開するAPIは作らない（失敗時のhole/dangling ID防止）。

## 4. 新たに見つかった隠れたload-bearing依存

### 4.1 `SchemeProjectionEvaluator`

`project_lower`の最終decisionは既にCPKを読むが、semantic publication/epoch
判定（`SchemeProjectionEvaluator`、`constraints/mod.rs`）は今もflat
projection proofs/clauses/coverage、RCPF replay occurrences、RCPF non-replay
parents、RCPF clause attribution、flat `dependent_records_by_premise`を
読んでいる。claim allocatorだけをCPKへ移しても、この経路が残っている限り
flat/RCPF削除の準備は完了しない（8G-4bで対処）。

### 4.2 `dependent_records_by_premise`

semantic queueそのものではないが、semantic publicationの対象を決める
proof dependency indexとして機能している。単純削除ではなくCPK indexへの
移管対象として扱う（8G-4a）。

## 5. 削除の依存順序（トポロジカル順）

1. CPK claim payload/allocator/dedup/move ownership
2. CPK qualified-parent exact index
3. CPK projection target index
4. CPK premise dependency reverse index
5. Publication evaluatorをCPK evaluatorへ切替
6. Logical/output parity snapshotをCPK-only化
7. Legacy test/reader/authorityを退役
8. Flat replay-parent/exact-keyレイヤー削除
9. Flat projection/clause/dependencyレイヤー削除
10. RCPFを逆依存順に削除
11. Flat claim/coverage arenaを最後に削除
12. Dual-write hooks・RCPF telemetry・obsolete census整理

RCPF内部の削除順（leaf→root）: `ReplayClauseProjection` →
`NonReplayClaimParentStore` → `ReplayResultSummary` →
`ReplayOccurrenceStore` → `ParentSetArena` → shell
（`ReplayFactoredShadowStatus`/failure type/telemetry/module）。

## 6. Test退役マッピング（§6 test-retirement policyに準拠）

### 6.1 既存CPK counterpartでmechanical retirement可能

- routing holdout3件: CPK-7 direct `PreparedReplayRoute`・disposition
  matrix・canonical-parent testsが保持。Legacy generated/input/accepted
  equalityはmigration-only characterizationとして退役理由を記録。
- `cpk_7_shadow_oracle_rejects_claim_index_corruption`:
  `cpk_7_cpk_authority_preflight_rejects_claim_index_corruption`と
  attempt-terminal testsが保持。
- replacement-backed3件（CPK-8E-1で追加済みのCPK-only test群が
  既にcorrectness propertyを保持）。

### 6.2 41件の内訳

flat/CDM representation・delta・index census系18件はCPK claim/projection/
parent contract確認後にcategory Bとして退役。残る23件はRCPF store/
failure/publication characterizationで、対応するstore/fault target削除時に
category Bとして退役し、CPK hard-failure/attempt-discard/canonical-
first-witness counterpartを維持する（詳細リストはproof_inventory.rsの
既存census参照）。

### 6.3 新CPK-only test が先に必要な項目（8G-1で追加）

- claim allocation/dedup/move/reduction atomicity
- no-claimパスのzero-allocation
- claim/index maintenanceがglobal scanを伴わないこと
- `rcpf_f_consumer_2_factored_lookup_failure_commits_no_dependency_edges`
  相当のCPK dependency transaction failure test
- `rcpf_c3b_terminal_failure_stops_drain_before_the_next_queued_work`
  相当のCPK terminal-failure queue-stop test
- `rcpf_d2c_2c_2a_deferred_clause_intent_preserves_immediate_value`の
  CPK publication-fence direct版
- `replay_claim_parent_dedup_keeps_each_exact_replay_carrier`の
  CPK qualified-parent index direct版
- CPK-only logical proof snapshot parity

新規に見つかった6件のうち3件（`lower_and_upper_replay_planning_capture_
legacy_parent_drafts`、`target_late_legacy_rollback_reproduces_epoch_
publication_and_consumer_sequences`、`rcpf_d4_4_quarantine_discards_
attempt_without_legacy_retry`）はLegacy internal draft/adjacent CPK
coverageによりcategory B。残り3件は上記の新規CPK-only testが先に必要。

## 7. 段階分割（17スライス）

### Reversible ownership-transfer phase

1. **8G-0**: physical-removal census拡張（54件+全direct store test）、
   rollback readiness確認（last-known-good artifact再現手順、cache/
   mixed-version方針）。
2. **8G-1**: §6.3の欠けているCPK-only test群を追加。
3. **8G-2a**: CPK claim payload completeness（full lineage/kindをCPKへ）。
4. **8G-2b**: original claim allocator（ID・original dedup・producer root
   のCPK owner化、flatはCPK-issued IDを受けるmirrorへ降格）。
5. **8G-2c**: derived/reduction allocator（root canonicalization・cycle
   coalesce・reduction state indexのCPK化）。
6. **8G-2d**: claim move/coverage（current-record mutation・claims-by-
   record・live coverageのCPK authority化）。
7. **8G-3**: qualified-parent authority（result別exact parent index追加、
   replay/structural/reduction exact dedupと canonical orderのCPK所有、
   RCPFへはevent-local prepared payloadのみ渡す）。
8. **8G-4a**: projection target/dependency index（constraint/replay→
   lower record、premise→dependent records、target-late propagationの
   CPK化）。
9. **8G-4b**: publication evaluator cutover（before/after/root override
   をCPK evaluatorへ、affected-owner・epoch・publication intentをCPKのみ
   から決定）。
10. **8G-5**: final dual-write parity freeze（logical snapshotをCPK-only
    へ、canonical order・worklist・row/replay census・portable outputを
    固定。全旧storeはまだ書かれる。**このcommitからlast-known-good
    binaryを生成・保存**）。
11. **8G-6**: Legacy test retirement and reader removal（54件のmigrate/
    retire、`ProofReadAuthority`・Legacy reader・observation構造体の削除、
    `ReplayReadAuthority::LegacyRollback`とtest constructorの削除。
    production storeはまだdual-writtenのまま）。

### Physical deletion phase

12. **8G-7a/b**: flat parent relations削除（writer hookをfieldごとの
    commitで）。
13. **8G-8a/b/c**: flat projection relations削除（support/root
    membership、clause/link/attribution、dependency/target indexを
    sub-layerごとに別commit）。
14. **8G-9a〜e**: RCPF逆トポロジカル順削除。
15. **8G-10**: RCPF shell削除。
16. **8G-11a/b**: flat claim mirror削除（live coverage/reduction/root
    index、claim Vec本体、`replay_claim_cycle_coalesces`）。
17. **8G-12**: 最終cleanup/gate（dual-write hook、obsolete inventory、
    zero-reference lexical gate、CPK hard-failure telemetryへの整理、
    fresh multi-round final CPK-only soak）。

各meaningfulコミット後の最低確認: `cargo check -p infer`、該当targeted
test、`cpk_`、scoped `constraints::` suite、`generalize::`/`compact::`、
claim-move/target-late/five-lineage/insertion-order、portable/canonical
diagnostic test、bounded contract corpus/cache smoke、semantic execution/
worklist/replay/row census、`free -h`とgross RSS/wall-time確認。常に
`--test-threads=4`。

## 8. 不可逆境界

境界は二段階ある。

1. **Code-level boundary**（§8.2の意味での境界）: 8G-5の最終dual-write
   green commit後、8G-6でLegacy authority/readerを物理削除する瞬間。
   automatic fallbackは既にCPK-8D/8F-3で封印済みだが、同一binary内で
   explicit Legacy representationを選ぶ能力そのものがここで消える。
2. **Deployed-state boundary**: 8G-7で最初のproduction flat writerを
   止める瞬間。以後、新processのstateには旧representationが存在せず、
   source revertだけでは同一process rollbackにならない。

last-known-good artifact・cache互換性・cold-restart/mixed-version手順は、
より早い**8G-6着手直前まで**に確認する。最後の可逆点は8G-5の最終green
commitである。

## 9. 先行文書との整合性

本書はCPK-8計画§5 CPK-8G・§8・§9・§10・§1.2.B・§2.3を具体化するのみで、
変更しない。CPK-8計画の23 invariant・30 stop condition・15
completion criteriaは全てそのまま継承する。矛盾が見つかった場合、実装で
平滑化せずCPK-8計画または本書の追補として再承認する。

---

著者: Codex gpt-5.6-sol（xhigh）が調査・起案、Claude (Sonnet 5) が査読・確定
