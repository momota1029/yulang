# CPK-8: legacy proof machinery 段階的撤去計画

日付: 2026-08-07

状態: **ユーザ承認済み（2026-08-07）。§5 CPK-8G（物理撤去）も事前承認済み（2026-08-07追記）**

§11 open question 12 は当初、8F green後・8G着手前に本書とは別のユーザ再確認を
必須としていた。ユーザは同日中に「8Gはもうこの時点で一旦承認しておきます」と
明示し、この再確認を前倒しで与えた。したがって8A〜8G全体が本書の承認範囲に
含まれる。ただし8G自体の物理削除は§8.2が定める不可逆境界（同一process内での
representation rollback不可）を伴うため、実装時も§9 stop conditionと§10
completion criteriaを厳格に適用し、8F greenの確認を経てから着手する。

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定

**署名についての注記**: Fable 5 が一時的に利用できないため、このリポジトリの
「Fable 5 不在時の起案担当」の慣例に従い、本書は Codex `gpt-5.6-sol`（xhigh）が
本文を起案した。Claude (Sonnet 5) は、現行 code・既存正本文書・invariant・
stop condition を査読し、独立した Codex `gpt-5.6-terra` セッションによる
fact-check（§1.1〜§1.5 の技術的主張7件中6件TRUE・1件PARTIALLY TRUE、
核心主張である §1.1 の organic LegacyRollback 到達可能性は確認済み）を経て、
ユーザの明示承認により本書を正本として確定した。

本書は、既承認の
`notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md`
（以下 CPK 計画）§13 CPK-8を具体化する草案である。CPK-6b（projection authority
cutover）と CPK-7（replay routing authority cutover、commit `7fad5fc3`）により、
通常の production machine は `ProofReadAuthority::Cpk` を選び、二つの同期 decision
を `ProofOccurrenceStore::project_lower` / `prepare_replay_route` から読む。

一方、pre-CPK の flat proof ledger、RCPF の factored representation、両者の
authority dispatch、LegacyRollback retry、migration parity oracle はまだ残っている。
CPK-8は、これらを一度に削除せず、観測・fallback封印・依存閉包・物理撤去を
独立にrevert可能なstageへ分ける。

本書はCPK-8だけを扱う。CPK-9の最終wall time/RSS/profile、application corpus、
closeoutは対象外とする。

## 0. 本書が提案する決定の要約

1. legacy proof machineryの撤去を、単一の大規模commitではなく、
   **soak instrumentation → dependency closure → final parity freeze → production fallback
   seal → no-fallback soak → migration adapter退役 → store/writer物理撤去**の順で行う。
2. `ProofReadAuthority::LegacyRollback`をproduction call siteから外す前に、最後の
   proof writer/consumer変更以後のapproved soak manifestで、次を要求する。

   ```text
   organic CPK ProofFailure terminal occurrence == 0
   organic CPK LegacyRollback retry entry       == 0
   organic RCPF Failed occurrence                == 0
   organic RCPF LegacyRollback retry entry       == 0
   unexplained parity mismatch                   == 0
   ```

   retry後の出力が正しくても、そのrunをPASSとして数えない。
3. 現行codeにはRCPF failure用soak telemetryはあるが、CPK `ProofFailure` / CPK
   `LegacyRollback` entry専用のorganic counterがない。CPK-8最初のcommitでこれを
   追加し、fault injectionをorganic countから分離する。
4. CPK exact shadow comparisonは現状`#[cfg(test)]`であり、release productionの
   query-time double-computation costではない。したがって「oracleを先に消せば
   productionが軽くなる」とはみなさない。oracleは最後のlegacy writerが消える直前
   までtest gateとして保持し、production costを持つdual store / dual writerを
   別stageで撤去する。
5. `ProofReadAuthority`とRCPFの`ReplayReadAuthority`は別のauthorityである。
   CPK-8は両方を対象にするが、CPK authorityが既にsoleであるという理由だけで、
   RCPF factored storeを即時削除しない。現行writer/materializationがRCPF summaryや
   flat claim relationからCPK eventを組み立てる依存を先に閉じる。
6. `TypeBounds`のfieldを名前だけで一括削除しない。semantic bound frontier、
   constraint/bound ID、row reduction state、semantic epochは保持する。
   proof-only ledgerは、CPK側へID allocationとwriter ownershipを移した後にだけ削除する。
7. Legacy-only testは一律に期待値をCPKへ書き換えない。各testを
   **CPK contractへ移植 / historical characterizationとして明示退役 / semantic-only
   fixtureとして維持**のどれかへ分類し、分類をcommitに記録する。
8. physical removal後のruntime fallbackは存在しない。CPK write/read failureは
   hard attempt failureとなる。運用上のrollbackは、互換性を確認した直前releaseへ
   binary/source commit単位で戻すことで行い、同一binary内のLegacy backendへは戻さない。
9. 各stageでcanonical order、five-lineage identity、worklist trace、replay census、
   row/reduction state、final type/scheme/output、terminationのgateを再確認する。
10. 一件でもorganic failure、ordering drift、semantic mismatch、fixtureの未分類、
    または削除対象からのproduction readが見つかったら次stageへ進まない。

## 1. 現在地（commit `7fad5fc3`）

### 1.1 Production authority topology

通常の`ConstraintMachine::new()`は次を選ぶ。

```text
ReplayReadAuthority::Factored
ProofReadAuthority::Cpk
```

二つは同じ意味ではない。

- `ProofReadAuthority::Cpk`は、scheme projectionとreplay routingの同期decisionを
  `ProofOccurrenceStore`へ一本化する。
- `ReplayReadAuthority::Factored`は、pre-CPK RCPFのparent-set / occurrence /
  result-summary / clause-projection系reader・writerを選ぶ。
- CPK proof queryが失敗すると、machine-local `proof_terminal_failure`が最初の
  `ProofFailure`をstickyに保持する。
- RCPF factored read/write/oracleが失敗すると、
  `replay_factored_shadow_status`が`Failed`へstickyに遷移する。

`lowering/body/mod.rs::run_replay_compilation_attempt`は、最初のattemptを
`(ReplayReadAuthority::Factored, ProofReadAuthority::Cpk)`で実行する。どちらかが
terminal failureを返すとfirst outputをdropし、fresh machineを次のように選んで
source/session inputから再実行する。

```text
RCPF failure only -> ReplayReadAuthority::LegacyRollback(failure)
CPK failure only  -> ProofReadAuthority::LegacyRollback(failure)
both              -> 両方をLegacyRollbackへ固定
```

したがって`ProofReadAuthority::LegacyRollback`はtest fixture専用ではない。
`project_lower`、lower-event routing batch preflight、upper-event routing batch preflightの
organic `ProofFailure`からproductionで到達可能である。

### 1.2 Legacy / migration surface inventory

#### A. semantic substrate（保持対象）

次はproof store撤去の対象ではない。

- `BoundRecordId` / `ConstraintRecordId`とそのsemantic record
- active lower/upper frontier、bound state、canonical semantic key
- semantic queue/worklist、canonical constraint map
- row derivation / row reductionのsemantic stateとopaque ID
- semantic/provenance epochのうち、外部publication契約に必要なもの
- source boundary、origin、generalized scheme等のsemantic/public provenance surface

proof metadataと同じstructに同居しているfieldがあっても、この層を消してはならない。

#### B. `TypeBounds`のflat proof ledger（撤去候補）

現行`TypeBounds`には、少なくとも次のpre-CPK relation/indexが残る。

- `upper_replay_claims`とclaim-by-record / producer / root / reduction系index
- `claim_parents_by_constraint`
- `qualified_carrier_index`
- `replay_claim_parent_keys` / `structural_claim_parent_keys`
- `live_coverage_by_root`
- `scheme_projection_claims_by_lower_record`
- `projection_proofs_by_lower_record`
- projection lower/root membership index群
- `record_proof_clauses`とclause key / lower-record index
- `record_proof_clause_links_by_lower_record`とlink key
- `attributed_claim_supports` / `flat_retained_attributed_claim_supports`
- `dependent_records_by_premise`

この一覧は「全部を同時に消してよい」という意味ではない。例えば現在のclaim IDは
flat claim allocationとCPK `upper_claims` mirrorで共有され、複数writerがflat claimを
作った直後に`proof_store.record_upper_claim`を呼ぶ。ID allocation・claim move・
representative選択をCPK-owned transactionへ移す前にflat arenaを消すと、dangling IDか
二重allocationになる。

#### C. RCPF factored representation（撤去候補）

`ConstraintMachine`は現在も次を常設する。

- `ParentSetArena`
- `ReplayOccurrenceStore`
- `ReplayResultSummary`
- `ReplayClauseProjection`
- `NonReplayClaimParentStore`
- `ReplayReadAuthority`
- `ReplayFactoredShadowStatus`

これらはflat relationの単なるtest oracleではない。Factored authority下で、replay
occurrence admission、first-parent summary、upper materialization、lower projection、
clause projection等のproduction writer/read preparationに関与する。CPKが二つの最終
decision authorityになった後も、CPK storeへ渡すeventの組立元にRCPF/flat stateが
残っているため、writer dependency closureが物理撤去より先でなければならない。

#### D. CPK migration oracle / adapter（撤去候補）

`constraints/proof/mod.rs`には次が残る。

- CPK-2系のthread-local capture storeと`record_*_shadow` writer
- legacy stateからCPK expected occurrenceを再構成するadapter
- RCPF occurrence/parent/summaryとCPK finite mapを比較するexact oracle
- projection publication/projectabilityのlegacy comparison
- replay routingの`legacy_prepared_replay_route` normalizerとevent census comparison
- matrix fixture専用observation / corruption hook

CPK replay-routing comparisonはexact parent claim/root/side/lineage/sequenceと
input/generated/accepted/dispositionを検査する。これらはmigration gateであり、最終
production APIではない。

#### E. Legacy read / rollback code（撤去候補）

- `legacy_scheme_projectable_lowers`
- test-only `legacy_scheme_projectable_lowers_for_test`
- `legacy_lower_bound_replay_actions`
- `legacy_upper_bound_replay_actions`
- Legacy incremental-route generic-exclusion branch
- `ProofReadAuthority::LegacyRollback(ProofFailure)` dispatch
- `ReplayReadAuthority::LegacyRollback(ReplayFactoredShadowFailure)` dispatch
- `run_replay_compilation_attempt`のfresh legacy retry orchestration
- legacy retry専用error/telemetry/test helper

### 1.3 Shadow-oracle costの事実

CPKのprojection/routing exact compareとthread-local shadow captureは`#[cfg(test)]`である。
通常release binaryはこの比較とobservation vectorを持たない。RCPFの比較も主に
`#[cfg(test)]`または`#[cfg(any(test, debug_assertions))]`で、event/evaluator oracleの
enableはtest fixtureに限定される。

一方、通常production machineはflat ledger、RCPF factored store、CPK storeを保持し、
既存writer境界で複数表現へ記録する。この常設store・index・writerがCPK-8のproduction
cost削減対象である。`YULANG_REPLAY_*_SHADOW`系のopt-in telemetryは別目的を含むため、
CPK migration-onlyか継続運用surfaceかをfieldごとに分類するまで一括削除しない。

### 1.4 Failure telemetryの不足

`constraints/replay_soak.rs`はRCPFについて、organic / intentional injectionを分けて
terminal write/read/oracle failure、factored read error、legacy rollback entryを数える。
しかしCPK `ProofFailure`と`ProofReadAuthority::LegacyRollback` entryには同等の
production soak counter/sinkがない。

よって、現時点で「organic CPK failureがゼロだった」はsuite greenだけからは証明
できない。retryが成功すれば最終compileは成功し得るため、CPK-8は最初に観測可能性を
閉じなければならない。

### 1.5 Dependent test / fixture surface

現行sourceには、意図的なLegacy characterizationが残る。

- `mpc_a_9_5_legacy_unattributed_claim_link_fails_open`
- `legacy_scheme_projectable_lowers_for_test`を使うSlice B oracle群
- explicit `legacy_rollback_proof_authority()`を使うparent-draft / RCPF failure fixture
- `ProofReadAuthority::LegacyRollback`下でCPK shadowのhard failureを検査するfixture
- RCPF Factored / LegacyRollbackのepoch、lineage、canonical ordering、allocation
  failure、whole-attempt discardを比較するfixture群

また、2026-08-07時点の限定lexical censusでは、`constraints/tests/`、
`machine/bounds.rs` test module、`proof/mod.rs`に、raw `.bounds.add_lower(` 10件、
`.bounds.add_upper(` 4件、`.bounds.original_upper_replay_claim(` 13件、
`.bounds.derived_upper_replay_claim(` 6件、direct `row_derivations.push` 1件、
`scheme_projection_claims_by_lower_record` direct insert/entry 1件がある。

これらの件数は「未修正gap数」ではない。semantic-only unit fixture、CPK mirrorを別途
正しく書くfixture、明示Legacy-only fixtureが混在する。CPK-8Aで各siteを一意に分類し、
未分類ゼロを物理撤去前gateにする。`proof_inventory.rs`のlexical censusは、この作業の
出発点として維持する。

## 2. Removal boundary

### 2.1 消すもの

CPK-8完了時、productionのproof representationは`ProofOccurrenceStore`だけとする。
削除対象は次である。

1. flat / RCPF factoredへのproof-only dual write
2. flat proof relationを読むproduction adapter
3. RCPF factored proof relationを読むproduction adapter
4. 二つのlegacy authority variantとdispatch
5. automatic runtime LegacyRollback retry backend
6. migration parity adapter / observation / env flag
7. migrationだけを目的とするfixture/helper
8. CPK storeと論理的に重複するflat/factored proof field/index

### 2.2 残すもの

1. semantic solverのbound/constraint/queue/row/SCC/generalization algorithm
2. semantic IDとstable opaque proof referenceを接続する最小event boundary
3. CPK `ProofOccurrenceStore`、typed query、`ProofFailure`
4. failure時のwhole-attempt discard（fallback backendがなくても必要）
5. external diagnostic / portable provenance / debug surface
6. CPK store上だけで実装される必要最小限のcompatibility iterator
7. fault injectionとcorruption hard-failure test

### 2.3 Ownership transferを先に行う

削除対象fieldが現在ID allocation、first-seen representative、event snapshot、または
CPK writer inputを所有している場合、その責務を「削除」してはならない。先に
`ProofOccurrenceStore`またはevent-local prepared valueへ移す。

各fieldの撤去PR/commitは、次の4分類を示さなければならない。

```text
semantic owner       -> 維持
CPK-owned proof fact -> CPK storeへownership transfer済み
migration mirror     -> consumerゼロ確認後に削除
test-only legacy     -> 移植または明示退役
```

## 3. CPK-8 invariants

CPK計画§15、RCPF§10の23 invariant、projection/routing追補を継承し、撤去中は特に
次を固定する。

1. 通常production decision authorityは全stageでCPKのままとする。
2. 同一attempt内でCPK/Legacyをrecord単位に混在させない。
3. failed attemptからscheme、diagnostic、cache、epoch publicationを返さない。
4. fallbackを外した後も`ProofFailure`をfail-openへ変換しない。
5. semantic queue/worklistのidentity、順序、件数を変えない。
6. bound/constraint canonical keyへproof IDを入れない。
7. upper claim ID、coverage root、representative claimを同一視しない。
8. claim move後もwriter-fixed representativeを保持する。
9. replay parentのlower/upper sideを失わない。
10. five-lineage kindをshapeから逆推定しない。
11. replay carrierのpivot/lower/upper/ruleを粗化しない。
12. corrected endpoint-decoupling（semantic `upper`とownership `upper_record`）を保つ。
13. projection formulaのStandalone / DerivedUnary / ReplayConjunction意味を変えない。
14. record routeのORとReplayConjunctionのANDを変えない。
15. parent/event snapshotはadmission時点で固定する。
16. canonical orderをlegacy containerの偶然のiteration orderへ戻さない。
17. diagnostic/provenance orderは既承認のcanonical orderを保つ。
18. mandatory routing/projection factをbudgetでdropしない。
19. diagnostic-only incompleteとmandatory missingを混同しない。
20. exact no-opがsemantic work、epoch、publicationを増やさない。
21. proof writer failureはpartial CPK commitを公開しない。
22. compatibility iteratorはCPK storeを再度flat全量物理化しない。
23. no-claim pathへ新しいallocationを入れない。
24. store撤去をSCC/generalization/simplifierの変更と同じcommitへ混ぜない。
25. legacy testの期待値を現CPK出力へ合わせて書き換えない。
26. 各stageを直前stageだけ戻せるcommit boundaryにする。
27. physical removal前の最後のparity snapshotを保存する。
28. organic failureを伴うretryをPASSに数えない。

## 4. Soak gate

### 4.1 観測単位

CPK-8AでCPK用soak telemetryを追加する。最低限、次をprocess-safeなcounter/eventとして
記録する。

```text
proof_terminal_failure(origin, ProofOperation, ProofFailure)
proof_legacy_rollback_entry(origin, first ProofFailure)
proof_retry_failure(origin)
```

`origin`は少なくとも`Organic`と`IntentionalTestInjection`を区別する。first failure
だけをterminal occurrenceとして数え、同じsticky failureの後続queryを重複計上しない。
sinkが開けないことをcompile successへ黙って吸収し、soakをPASS扱いしてはならない。
telemetry artifactにはcommit、build profile、workload、cache mode、process IDを含める。

### 4.2 Concrete zero-organic gate

production fallback封印前のcandidate commitを固定し、最後のwriter/consumer変更後に
次のmanifestを**3 round連続**で実行する。各roundはfresh process、fresh telemetry
artifactを使う。

1. CPK targeted suiteとCPK-7 18-item matrix
2. scoped `constraints::` suite（既知failureを明示分離）
3. `generalize::` / `compact::`
4. cache cold / warmの代表compile
5. insertion-order、target-late、claim-move、five-lineage、fault-injection fixture
6. repository representative corpus
7. memory-safeなstd characterization
8. portable provenance / diagnostic ordering characterization

3 roundを通算して次が全てゼロでなければならない。

```text
organic CPK terminal failure
organic CPK LegacyRollback entry
organic CPK retry failure
organic RCPF Failed
organic RCPF LegacyRollback entry
unexplained oracle mismatch
```

fault injectionはintentional countに現れることを別assertionで確認するが、organic zeroの
分母や成功件数へ混ぜない。一件でもorganic eventが出たら原因修正後の新commitから
3 roundを取り直す。

この3-round manifestに加えて、calendar-day / CI attempt数などdeploy環境の追加soakを
要求するかは§11のopen questionとする。少なくとも上記gateを短縮してよいとはしない。

### 4.3 No-fallback soak

production `LegacyRollback` entryを外したstageでも、同じmanifestを再度3 round実行する。
このstageのfailureはlegacyへretryせずhard attempt failureになる。legacy code自体は
まだcompiled/testableに残し、問題があれば当該authority-seal commitだけをrevertする。

## 5. Staged removal plan

### CPK-8A: census freezeとsoak instrumentation

変更:

- CPK `ProofFailure` / rollback entryのorganic telemetryを追加する。
- `proof_inventory.rs`を、flat / RCPF / CPK / semantic / test-onlyの分類付きcensusへ拡張する。
- raw test writer siteを§1.5の分類へ確定する。
- production read/write graphをfield単位で記録する。

Gate:

- instrumentation fault injectionがintentionalとしてのみ数えられる。
- organic zeroをartifactから機械判定できる。
- 未分類siteがゼロ。
- semantic fieldをproof-onlyと誤分類していない。

Rollback: instrumentation/censusだけのcommitとして戻せる。

### CPK-8B: writer dependency closure

変更:

- CPK writerがflat/RCPF containerを再走査してeventを再構成する依存を、一つずつ
  event-local prepared payloadまたはCPK indexへ置換する。
- claim allocation/move、coverage、projection support/formula、replay parent snapshot、
  first witness、row/reduction routeのownershipを明示する。
- compatibility readが必要ならCPK store上にのみ実装する。

このstageではlegacy store、authority、oracleを削除しない。各dependency familyを
独立commitにし、exact oracle green後にのみ次へ進む。

Gate:

- production CPK writer inputがlegacy proof fieldを読まない。
- new index maintenanceがglobal scan/re-sortを導入しない。
- claim move / same-root representative / endpoint-decoupling fixtureがgreen。
- CPK/legacy exact parityとsemantic trace parityがgreen。

Rollback: family単位のownership transferだけを戻せる。

### CPK-8C: final parity freezeとfallback前soak

変更:

- full shadow matrixの最後のbaseline artifactを保存する。
- canonical ordering、portable output、worklist/replay/row censusを固定する。
- §4.2の3-round soakを実行する。

このstageではtest-only exact oracleを保持する。release costがないため、早期削除で
safety marginを失わない。

Gate: §4.2の全項目がゼロかつ全parity green。

Rollback: code変更がなければ不要。baseline更新が必要なsemantic変更はCPK-8と分離する。

### CPK-8D: production fallback seal

変更:

- normal production constructorをCPK-only authorityへ固定する。
- `run_replay_compilation_attempt`からproof failure時のautomatic
  `ProofReadAuthority::LegacyRollback` retryを外す。
- `ProofFailure`時はwhole-attempt discard後にhard compilation errorを返す。
- legacy adapterとexplicit test constructorはcompiledのまま残す。
- RCPF `ReplayReadAuthority`の扱いは、8Bで依存が閉じた範囲だけ別commitで封印する。

Gate:

- failure後にpartial output/publicationがない。
- CPK corruption/fault injectionがexpected hard failureになる。
- §4.3 no-fallback soakがgreen。
- deploy rollback artifactが再現可能。

Rollback: authority-seal commitだけをrevertし、fresh LegacyRollback retryを復元できる。

### CPK-8E: migration oracle / Legacy-only test retirement

変更:

- Legacy expected adapterを読むparity testを、CPK typed contractのdirect fixtureと
  frozen semantic/output characterizationへ移す。
- historical Legacy fail-open / container-order / internal-draft testは、目的を記録して
  deliberate retirementする。
- corruption、failure、canonical order、five-lineage、endpoint-decoupling、attempt discard
  testはCPK-only版を保持する。
- CPK-2 thread-local shadow、legacy normalizer、observation-only structを削除する。

Gate:

- 削除したassertionと同じcorrectness propertyをCPK-only testが覆うか、歴史的挙動を
  意図的に退役した理由がcommitにある。
- diagnostic/provenance ordering coverageが減っていない。
- fixtureがexplicit Legacy authorityを暗黙に要求しない。

Rollback: oracle/test-retirementだけのcommitにする。production store削除と混ぜない。

### CPK-8F: legacy reader / authority type removal

変更:

- `legacy_scheme_projectable_lowers`とrouting legacy action plannerを削除する。
- `ProofReadAuthority` dispatchを削除し、CPK queryを直接呼ぶ。
- dormant `ReplayReadAuthority` reader/adapterを依存順に削除する。
- legacy retry専用error/helper/telemetryを削除またはCPK hard-failure telemetryへ統合する。

Gate:

- production sourceでlegacy reader referenceがゼロ。
- `ProofReadAuthority::LegacyRollback` / `ReplayReadAuthority::LegacyRollback`がゼロ。
- targeted/scoped/integration/characterizationがgreen。
- final output parityとtermination parity。

Rollback: reader/authority removalとstore removalを分ける。問題時にはdormant codeを戻せる。

### CPK-8G: physical store / writer removal

8Aのdependency graphからleaf順を決め、最低でも次を別commit群にする。

1. expanded flat replay parent / exact key / retained link mirror
2. flat projection support / formula / dependency mirror
3. RCPF parent arena / occurrence / result summary / clause projection / non-replay store
4. flat claim / coverage arenaとindex（CPK ownership transfer完了後）
5. dual-write hooks、migration env flag、obsolete inventory entries

一つのcommitで複数layerを消さない。各commit後に、compile、targeted test、scoped suite、
broader integration、representative characterizationを行う。

Gate:

- production proof storeが`ProofOccurrenceStore`一つだけ。
- old proof writer/read referenceがゼロ。
- compatibility iteratorがflat materializationを復活させていない。
- semantic state/epoch/worklist/outputに差がない。
- memory/RSSが悪化していない。

Rollback: physical deletionはsource上はcommit revert可能とする。deploy済みbinaryの
runtime fallbackは存在しないため、運用rollbackはlast-known-good artifactへの切替となる。

## 6. Test retirement policy

各Legacy依存testを次のいずれかへ分類する。

### A. Correctness contract test

Legacyとの比較ではなく、CPKのtyped result、canonical order、failure、semantic traceを
直接assertする。testは維持する。

### B. Historical Legacy characterization

旧fail-open、旧container assembly order、legacy internal draftだけを記述し、CPK完成後の
product contractではないtest。CPK counterpartが存在することを確認し、test名と退役理由を
commit messageへ残して削除する。期待値をCPK出力へ書き換えて延命しない。

### C. Semantic fixture

raw `TypeBounds` APIを使っていても、proof authorityを全く通らないsemantic unit testは
維持できる。ただしproof fieldへのdirect writeを含むならA/B/Dへ再分類する。

### D. Fixture-construction debt

oracle-active pathを通るのにlegacy proof fieldだけを書くfixture。production-mirrored CPK
admission APIへ移す。移せない場合はwriter ownership gapとしてstopし、新APIの設計を
別途承認する。

## 7. Correctness / regression gates by stage

各meaningful commit後に最低限次を確認する。

1. CPK targeted suite
2. projection 12-item × applicable consumer matrix
3. replay routing 18-item matrix
4. scoped `constraints::` suite（既知failureを明示）
5. `generalize::` / `compact::`
6. claim move / target-late / arrival permutation / five-lineage
7. fault injection / whole-attempt discard / no-fail-open
8. canonical constraint count/order
9. replay input/generated/accepted/disposition census
10. row/reduction mergeとsemantic worklist trace
11. final type/scheme/diagnostic/portable output
12. termination

CPK-9の最終performance gateを前倒しして完了扱いにはしないが、各CPK-8 commitでgross
wall-time/RSS regressionとglobal scanがないことはlocal gateとして確認する。

## 8. Rollback model and irreversible boundary

### 8.1 Stage rollback

8A〜8Fは、直前stageだけをrevertできるようにする。authority sealとphysical store removalを
同じcommitへ入れない。test retirementとproduction writer deletionも混ぜない。

### 8.2 Physical removal後

legacy codeを物理削除した後、同一process内のrepresentation rollbackは不可能になる。
これは意図した最終状態である。CPK failureはhard errorとなり、fail-openやpartial retryへ
逃がさない。

source code自体はgit revert可能だが、次が絡む場合は単純revertを運用rollbackと同一視
できない。

- cache / portable proof schemaのversion
- mixed-version process/artifact
- persisted diagnostic/provenance payload
- deploymentが旧binaryを再現できるか

したがって8G着手前にlast-known-good binary、cache compatibility、rollback procedureを
確認する。これを満たせない環境では8Gへ進まない。

## 9. Stop conditions

次のいずれかが起きたら、そのstageを止め、最後のgreen commitへ戻して設計レビューする。

1. organic CPK `ProofFailure`が一件でも発生する。
2. organic CPK LegacyRollback entryが一件でも発生する。
3. organic RCPF `Failed` / LegacyRollbackが一件でも発生する。
4. telemetry sink/counterがsoak runを完全に記録できない。
5. fault injectionがorganic countへ混入する、またはorganic eventがinjected扱いになる。
6. CPK writerが削除予定legacy proof fieldをproductionで読む。
7. legacy fieldがsemantic key/order/stateを所有していることが後から判明する。
8. claim ID allocation/moveをCPK側でatomicに表せない。
9. exact replay carrierまたはevent-time parent snapshotを再構成できない。
10. same-root representativeが変わる。
11. five-lineage identityが欠落・統合される。
12. endpoint-decoupled residual routeが失われる。
13. projection OR/AND/cycle resultが変わる。
14. routing decision/payloadが変わる。
15. canonical parent/diagnostic/portable orderが変わる。
16. worklist event、canonical constraint count/order、replay censusが変わる。
17. row/reduction mergeまたはstateが変わる。
18. final type/scheme/output/diagnosticが変わる。
19. terminationが変わる。
20. failure時にpartial output/publicationが外へ出る。
21. fallback removalのためにfail-openが必要になる。
22. compatibility iteratorが全flat relationを常設再物理化する。
23. writer index maintenanceがglobal scan/re-sortを導入する。
24. no-claim/exact-no-op pathへallocationまたはworkが増える。
25. Legacy-only testの目的を分類できない。
26. test期待値変更なしではgreenにできない。
27. physical deletionが独立revertできない。
28. SCC scheduling、generalization core、simplifierの変更が必要になる。
29. cache/portable schemaのrollback compatibilityが不明なまま8Gへ進もうとする。
30. CPK-9 scopeの性能改善をCPK-8 cleanupへ混ぜ始める。

## 10. Completion criteria

CPK-8をcompleteと呼ぶには、次を全て満たす。

1. projection/routingがCPK typed queryだけを読む。
2. productionのproof representationが`ProofOccurrenceStore`一つだけである。
3. flat/RCPFへのproof-only dual writeがゼロ。
4. legacy proof reader/writer referenceがゼロ。
5. `ProofReadAuthority` / `ReplayReadAuthority`のmigration dispatchがゼロ。
6. automatic LegacyRollback backendがゼロ。
7. migration parity adapter/oracle/observation/env flagがゼロ。
8. legacy-only fixture/helperがゼロ、または非proof semantic testとして分類済み。
9. whole-attempt hard failureとpartial-output discardがtest済み。
10. CPK-only corruption/fault-injection testがgreen。
11. canonical ordering / five-lineage / endpoint-decoupling regressionがgreen。
12. semantic worklist/replay/row/final-output/termination gateがgreen。
13. §4.2と§4.3のsoak artifactが保存され、organic countがゼロ。
14. gross wall-time/RSS regressionとtotal-store scanがない。
15. last-known-good artifactへのoperational rollback procedureが確認済み。

CPK-9の最終profileとcloseoutを完了したとは、この条件だけでは主張しない。

## 11. Open questions / review decisions

次は本草案で黙って確定しない。Claudeとユーザの承認時に明示判断が必要である。

1. **Soakの外部期間**: 本書は最低3 roundのdeterministic manifestを提案する。
   これに加えて7 calendar days、一定CI attempt数、実利用corpus数などを必須にするか。
2. **CPK telemetryの公開先**: 既存RCPF sinkへversion 2として統合するか、CPK専用sinkに
   分けるか。監視不能時をhard gateにする実装境界をどこへ置くか。
3. **RCPF authorityの撤去順**: upper materialization / lower projection / clause projectionの
   どのfactored readerが、現在もCPK writer inputのownershipを持つか。8A censusで確定後、
   field-level topological orderを承認する必要がある。
4. **Legacy-only testの保存価値**: old fail-openやcontainer orderをsource testとして残すか、
   design note/commit historyへ退役させるか。production compileされるexplicit Legacy backendを
   test保存だけのために残すことは、CPK-8 completion条件と両立しない。
5. **Shadow oracleの退役時点**: test-onlyでrelease costはないため、本草案は最後のwriter
   parityまで保持する。test/debug build time削減を優先して8C直後に凍結・削除するか。
6. **Ordering baseline**: legacy adapterが偶然提供していた順序を、diagnostic/portable consumerが
   まだ暗黙に読むsiteがないか。RCPF-D3b precedentどおり、container撤去前にconsumer-visible
   sequenceを独立fixtureで固定する範囲を再確認する。
7. **Proof claim ID ownership**: `upper_replay_claims`削除前に、ID allocationをCPK storeが直接
   所有するか、semantic event allocatorを別に置くか。proof IDをsemantic identityへ漏らさない
   条件を満たす必要がある。
8. **Dependency indexの所属**: `dependent_records_by_premise`のうち、semantic retriggerに必要な
   indexとproof-only explanation indexの境界をどこに引くか。誤って消すとsolver workが変わる。
9. **Operational rollback**: physical removal後、旧binaryと新cache/portable artifactの互換性を
   保証するか、cache version bumpとcold restartを要求するか。
10. **RCPF soak telemetryの寿命**: RCPF machinery削除後もgeneric proof health telemetryとして
    名前を変えて残すか、CPK hard-failure telemetryへ統合して旧counterを削除するか。
11. **Debug/public surface**: external read-only debug consumerがflat shapeを期待する場合、
    CPK-backed compatibility iteratorを残すか、public surfaceをversioned変更として別承認するか。
12. **Final physical deletionの承認点**（決定済み、2026-08-07。同日中に前倒し確認済み）:
    当初は8F green後、8G着手前に本書とは別のユーザ明示的再確認を必須としていた。
    ユーザは同日中に「8Gはもうこの時点で一旦承認しておきます」と明示し、この
    再確認を前倒しで与えた。runtime fallback消滅という実質的な不可逆点である
    ことに変わりはないため、実装は8F greenの確認を経てから着手し、§9 stop
    conditionと§10 completion criteriaを厳格に適用する。

## 12. 先行文書との整合性

- CPK計画§13 CPK-8の削除対象/保持対象/exit条件を具体化し、変更しない。
- CPK計画§15の20 invariantと§16 stop conditionを全て継承する。
- RCPF quarantine追補§3.2のwhole-attempt discardを維持し、fallback撤去後も
  fail-openへ戻さない。
- RCPF quarantine追補§3.6のzero-organic-Failed gateを、CPK `ProofFailure`へ拡張する。
- RCPF-Fの独立rollback規律を、8A〜8Gのcommit boundaryへ引き継ぐ。
- RCPF-D3bのcanonical orderingをcontainer撤去後も維持する。
- projection decision追補の`ProofFailure` / mandatory fact / attempt-terminal契約を維持する。
- replay routing追補とendpoint-decoupling追補のbatch preflight、parent identity、residual route
  契約を維持する。
- MPC/DPNのOR/AND、DerivedUnary、root reachability、tri-color cycle規則を変更しない。

矛盾が見つかった場合、実装で平滑化せず、本書または先行正本の追補として再承認する。

## 13. CPK-9との境界

CPK-8はold store/writer/authorityをゼロにし、gross regressionがないことまで確認する。
次はCPK-9へ残す。

- final `std::text::parse` wall time/RSS/profile
- proof write self timeと全lowering比率
- cold/warm cacheとapplication corpus
- old dual-write pathがprofileから消えたことの最終数値
- closeout document / inventory guardの最終整理

CPK-8中に性能bugが見つかった場合、そのstageを止めて原因を直す。ただし新しい
solver optimizationやCPK-9目標達成のための広いrefactorをCPK-8 removal commitへ混ぜない。

## 14. 波及する文書（本書では編集しない）

本書がClaude査読とユーザ承認を経て正本になった後、必要に応じて次へ参照を追加する。

- `notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md` CPK-8
- `notes/design/2026-08-02-replay-claim-parent-factorization.md` RCPF-F
- `notes/design/2026-08-02-rcpf-quarantine-retry-authority-addendum.md` §3.6
- `notes/design/2026-08-06-cpk-projection-decision-addendum.md`
- `notes/design/2026-08-06-cpk-replay-routing-decision-addendum.md` §15.1
- architecture/progress inventory documents that still describe LegacyRollback as active recovery

これらの更新は本書draftと別変更にする。

---

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定

状態: **PENDING REVIEW（Claude 査読・ユーザ承認待ち）**

本書は草案であり、ユーザ承認前にCPK-8 source implementationへ着手してはならない。
