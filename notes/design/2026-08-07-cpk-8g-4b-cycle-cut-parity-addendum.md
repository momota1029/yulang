# CPK-8G-4b 追補: cycle-cut parity と canonical clause evaluation order

日付: 2026-08-07

状態: **ユーザ承認済み**

本書は、`notes/design/2026-08-07-cpk-8g-physical-removal-plan.md` の
CPK-8G-4b（publication evaluator cutover）を二度停止した ordering gap のうち、
二度目に判明した **cycle-cut occurrence parity** の契約衝突を解決する追補である。

対象となる先行契約は次のとおり。

- `notes/design/2026-08-01-dpn-root-claim-and-cycle-safety-addendum.md`
  の active-path cycle cutting。
- `notes/design/2026-08-02-mpc-dpn-projection-evaluation-round.md`
  の A3 round-local evaluator sharing。
- `notes/design/2026-08-03-rcpf-d-materialization-projection-addendum.md`
  の canonical diagnostic order と invariant 23。
- `notes/design/2026-08-05-cpk-0-projection-admission-addendum.md`
  の typed canonical projection action order。
- `notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md`
  の CPK-4 shadow gate。
- `notes/design/2026-08-06-cpk-projection-decision-addendum.md`
  の `ProjectionEvaluationRound`、cycle safety、payload contract。

本書は cycle guard の意味論や evaluator の OR / AND algorithm を変更しない。
決めるのは、異なる clause 列挙順を持つ旧 flat evaluator と CPK evaluator の間で、
**cycle cut が起きたという事実そのものを parity 対象にするか**という一点である。

## 0. 決定の要約

本書は候補 c2 を採る。

1. **CPK の typed canonical formula order を、CPK-8G-4b cutover 後の唯一の
   clause evaluation order authority とする。** flat の historical insertion order は
   migration oracle であり、CPK へ保存・再構成しない。
2. **cross-authority / cross-permutation の cycle-cut occurrence・回数 parity を
   correctness contract から外す。** parity 対象は、同一 semantic snapshot / view に対する
   最終 `ProjectionDecision`、support payload、affected owner、epoch class、publication intent、
   および fresh/shared evaluator の最終 decision 同値である。
3. cycle guard 自体は緩めない。実際に `Visiting` node へ再入した route は false になり、
   一度でも cut が起きた round は memo sharing を停止し、残りの top-level query を
   fresh evaluator で評価する。
4. 必ず循環 branch を訪れる focused fixture は、cycle cut の発火と sharing disable を
   引き続き直接 pin する。外すのは「別の正しい short-circuit order でも同じ branch を
   必ず訪れる」という誤った要求だけである。
5. diagnostics、provenance、portable export、publication は cycle-cut counter を読まない。
   これらの observable contract は canonical support/action order と最終 decision により
   引き続き固定する。
6. この決定は CPK-8G-2（claim lifecycle）、CPK-8G-3（qualified parent）、
   CPK-8G-4a（target/dependency index）の identity、dedup、canonical order、atomicity を
   変更しない。

要するに、cycle cut は **評価器内部の safety event** であり、semantic proof result の
一部ではない。発火したなら共有を止める義務を持つが、OR short-circuit により循環 branch を
訪れなかった正しい評価へ「同じ cut を発火させる」義務は課さない。

## 1. 確定した finding

### 1.1 旧 flat evaluator の順序

`TypeBounds::register_record_proof_clause_link`
（`crates/infer/src/constraints/mod.rs:2965` 付近）は、exact clause key が新規なら
`RecordProofClauseId` を作り、
`record_proof_clause_ids_by_lower_record[lower_record]` の末尾へ追加する。

`SchemeProjectionEvaluator::eval_record_uncached`
（同 `mod.rs:1331` 付近）は、この lower-record-local `Vec` を先頭から読み、
最初に true になった clause で OR を short-circuit する。

したがって flat の順序は、全 record 共通の global order ではない。各 lower record について、
replay / structural / reduction / standalone の clause source を横断した
**unique clause の first-admission order** である。同じ clause に別 support link が後着しても、
clause 自身の位置は動かない。

### 1.2 CPK evaluator の順序

`ProjectionClause::category_rank`
（`crates/infer/src/constraints/proof/mod.rs:897` 付近）は次の順序を与える。

```text
Standalone < DerivedUnary < ReplayConjunction
```

`ProofOccurrenceStore::record_projection_clause`
（同 `proof/mod.rs:1797` 付近）は、この rank に従って
`projection_formulas[lower_record]` へ position insertion する。
`ProjectionPreflight`（同 `proof/mod.rs:2646` 付近）は category rank が逆行する列を
`ProofFailure::NonCanonicalProjectionOrder` として hard-fail する。

`category_rank` は claim lifecycle、qualified-parent comparator、target/dependency index の
共通 comparator ではない。現 HEAD での利用は projection formula の格納と preflight に限られ、
CPK-8G-2/3/4a の既着地 authority を直接駆動していない。

### 1.3 再現 case

`dpn_b_cycle_guard_cyclic_route_plus_independent_source_stays_projectable`
（`crates/infer/src/constraints/machine/bounds.rs:10561` 付近）は、一つの source record に
次の二 clause を持つ。

```text
source = cycle-arm OR independent-standalone-arm
dependent = source
cycle-arm = dependent
```

cycle clause を先に flat ledger へ入れる場合、flat evaluator は cycle-arm で一度 cut し、
その後 independent arm により `true` を返す。cycle cut count は 1。

同じ semantic graph を CPK が読む場合、`Standalone` が `DerivedUnary` より先なので、
independent arm が先に `true` となり、cycle-arm は評価されない。cycle cut count は 0。

両者の最終 projectability は `true` であり、support set も同一である。異なるのは
「短絡されなかった評価 branch 内で cycle guard が発火したか」だけである。

### 1.4 二度目の CPK-8G-4b attempt が停止した理由

CPK-8G-4b の最初の attempt は、CPK commit 後に before view を取ったため
before == after となる sequencing bug で停止した。その問題は、CPK の before view を
CPK commit 前に取る設計で独立に解決済みであり、本書の論点ではない。

二度目の attempt は、その sequencing を正した後に §1.3 の count 差を観測した。
最終 decision は同じだったが、既存 shadow oracle が cut occurrence equality を要求したため、
「observable behavior を変えない」という当時の gate に従って正しく停止した。
本書は、その equality 要求が semantic contract か accidental over-specification かを決める。

## 2. 契約衝突の解消

### 2.1 A3 の正本契約

MPC/DPN projection evaluation round 文書 §5 は、同一 snapshot / view について
各 root を fresh evaluator で評価した結果を oracle とし、root query order や
clause insertion orderに関係なく projectable result が一致することを要求する。
同時に、次を明記している。

> `cycle_cuts` の回数自体は short-circuit 順によって異なり得るが、
> projectable 結果は異なってはならない。

したがって A3 が固定した semantic contract は、cut count parity ではない。

- circular route を実際に訪れたら false にする。
- cut を観測した evaluator の context-dependent `Done` を後続 root へ共有しない。
- fresh evaluator 列と shared round の最終 bool 列が一致する。
- clause / link / root query permutation で最終 projectability が変わらない。

### 2.2 stricter shadow/test contract の位置づけ

CPK separation plan の CPK-4 exit condition は `cycle-cut が parity` と記載し、
`compare_projection_record_shadow`
（`crates/infer/src/constraints/proof/mod.rs:3318` 付近）は現在、legacy / CPK の
`cycle_cuts != 0` を exact 比較する。CPK projection decision addendum の Slice B も
`cycle-cut 有無と decision` を exact comparison matrix に含める。

これらは CPK の shadow 構築が旧 evaluator と同じ clause order を持つ間には有効な
migration guard だった。しかし、CPK-0 が historical order ではなく typed canonical order を
新 authority に選んだ後は、異なる traversal を同じ semantic resultへ収束させる二 evaluatorに
同じ safety event の発火まで要求している。

本書は、上記二文書のうち **cross-authority cycle-cut occurrence parity だけ**を置き換える。
projectability、payload、affected owner、publication class の parity、および cycle safety の
単体 contract は一切置き換えない。

### 2.3 cycle cut は observable semantic output ではない

現 HEAD の `cycle_cuts` / `cycle_cut` reference census では、counter の用途は次に限られる。

1. flat `SchemeProjectionEvaluationRound` が cut 後の共有を停止する。
2. CPK `ProjectionEvaluationRound` が cut 後の共有を停止する。
3. test/debug snapshot と migration shadow observation が発火を観測する。

次の consumer は counter を読まない。

- generalization/provenance の witness edge order。
- `explain.rs` の insertion order と truncation prefix。
- `portable_explain.rs` の portable traversal / budget prefix。
- `source/mod.rs` の `lower_sites` duplicate-span first-cause selection。
- affected-owner、semantic/provenance epoch、publication intent の決定。

これらが読むのは、最終 inclusion/decision、canonical support/action payload、parent/edge列、
または publication mutation である。CPK projection decision addendum §7.3 のとおり、support payloadは
evaluation trace から集めず、preflight 済み canonical support view から作る。そのため cycle cut、
short-circuit、query order は payload を削らない。

cycle cut は memo sharing の可否へ間接的に影響するが、これは性能・評価器安全性の内部制御である。
その安全性は raw count equality ではなく fresh/shared decision equivalence により検証できる。

### 2.4 「cut しなかったのに共有してよい」理由

問題の CPK 順序では independent `Standalone` が true を返した時点で OR が終了し、
cycle-arm の node は evaluator state に入らない。したがって、その branch の再帰から生じる
root-dependent `Done(false)` も作られない。

```text
cut が起きた
  -> Visiting re-entry があり、context-dependent Done の危険がある
  -> sharing を停止する

cut が起きなかった（cycle branch 自体が short-circuit された）
  -> その branch 由来の Visiting / Done は存在しない
  -> acyclic に実際に訪れた state だけを共有してよい
```

この含意が成立しない case、すなわち cut を観測せずに context-dependent memo が残る case が
見つかれば、本書の前提は反証される。§10 の stop condition とする。

## 3. 決定

### D1: CPK typed canonical formula order を authority とする

CPK-8G-4b の cutover 後、`SchemeProjectionEvaluator` 相当の publication evaluator は
CPK `ProofOccurrenceStore` の canonical formula view だけを読む。

評価列は CPK-0 projection admission addendum §6.1 と CPK projection decision addendum の
canonical-order contract に従う。少なくとも formula category は次の順序である。

```text
Standalone < DerivedUnary < ReplayConjunction
```

同一 category 内も、CPK-0 が要求する typed carrier / premise / record key の total order を使う。
historical flat clause admission order、raw `HashMap` iteration、arena ID、admission ordinal は使わない。

現実装の `record_projection_clause` が category rank だけを整列し、同一 category 内の
full typed total order をまだ検証していないなら、それは本書が admission order を許す根拠には
ならない。CPK-8G-4b cutover 前に、次のどちらかを機械的に固定する。

1. 現 writer が CPK-0 の full typed order をすでに別の upstream action order から受けており、
   同一 category 内の列も契約どおりであることを test で示す。
2. CPK store 自身で full typed comparator を適用・preflight する。

どちらも成立しない場合は cutover を止める。flat admission orderへ戻して埋めない。

### D2: parity の意味を semantic parity へ限定する

同一 snapshot / view に対し、旧 flat path と CPK path の間で一致を要求するのは次である。

1. `Unclaimed` / `Excluded` / `Included` の最終 decision。
2. `Included` の全 qualifying support payloadと canonical sequence。
3. before/after inclusion。
4. affected-owner set。
5. metadata-only / inclusion-flip / no-op の publication class。
6. semantic / provenance epoch delta。
7. generalized witness、explanation、portable explanation、related diagnostic の
   consumer-visible sequence / truncation prefix。
8. 同じ authority/order 内での fresh evaluator 列と shared round の最終 decision列。

一致を要求しないもの:

1. legacy insertion-order evaluator と CPK canonical-order evaluator の cycle-cut count。
2. 上記二 evaluatorの `cycle_cuts != 0` の真偽。
3. cut が起きるまでに訪れた内部 node 数、memo hit 数、branch trace。

これら内部観測値は instrumentation として残してよいが、parity pass/fail を決めてはならない。

### D3: cycle safety は維持する

CPK evaluator は引き続き次を満たす。

1. `Visiting` re-entry はその circular route だけを false にする。
2. OR の他 clause/source は継続して評価する。
3. top-level return時に `Visiting` を残さない。
4. cut が一度でも起きた round は即座に shared memo を破棄する。
5. 同 round の残り query は一件ごとに fresh evaluator を使う。
6. SCC、fixpoint、恒久 memo、proactive cycle enumeration を導入しない。
7. cycle cut や short-circuit で support payload を削らない。

したがって本書は「cycle cut を数えなくてよい」とは決めない。
「異なる正しい evaluation order に同じ cut の発火を強制しない」と決める。

### D4: historical insertion order を第二の identity にしない

CPK に evaluator 専用の historical clause-order `Vec` / ordinal を追加しない。

RCPF-D3b invariant 23 は、diagnostic/provenance のために admission 順の永続 `Vec` を
追加せず、consumer-visible order を canonical keyへ隔離することを要求した。本件の evaluator
専用 ordinal は字義上 diagnostic index ではないものの、削除予定の flat history を
第二の恒久 ordering identity として CPK に複製する点で、その設計方向と衝突する。

より直接には CPK-0 が、flat parent admission historyや expanded link `Vec` 順を mutation orderに
使わず、formula actionを typed total orderへ canonicalizeすると決めている。本書はこの文言を
そのまま採用し、RCPF-D3b invariant 23 や CPK-0 を改訂しない。

## 4. assertion / oracle の機械的な変更表

将来の CPK-8G-4b implementation slice は、次の区別に従う。

### 4.1 緩和・削除する assertion

#### `compare_projection_record_shadow`

場所: `crates/infer/src/constraints/proof/mod.rs:3318` 付近。

- 維持: `shadow_result == legacy_result`。
- 削除: `shadow_cycle_cut == legacy_cycle_cut` を parity failure にする assertion。
- `ShadowProjectabilityObservation::{legacy_cycle_cut, shadow_cycle_cut}` は移行中の
  debug data として一時保持してよいが、PASS/FAIL 判定に使わない。CPK-8G の oracle removal
  slice で observation struct と共に削除する。

#### `dpn_b_cycle_guard_cyclic_route_plus_independent_source_stays_projectable`

場所: `crates/infer/src/constraints/machine/bounds.rs:10561` 付近。

現行の次の insertion-order-specific assertionを semantic gate から外す。

```text
standalone_first == true  -> cycle_cuts == 0
standalone_first == false -> cycle_cuts == 1
```

置換後は次を固定する。

1. 両 admission permutationで source / dependent の最終 projectability が true。
2. CPK canonical store / decision / payload / publication が両 permutationで同一。
3. source→dependent、dependent→sourceの両 root query orderで fresh/shared decision列が同一。
4. 実際に cut を報告した round だけが sharing-disabled になり、その後の query が
   fresh oracleと一致する。

flat evaluator が物理削除前の characterization として 0/1 を観測し続けてもよいが、
その値を CPK parity gate や user-visible output contract にしない。

#### CPK-4 shadow gate 文言

- `notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md` の
  CPK-4 exit condition `cycle-cut が parity` は、本書により
  「cycle safety と fresh/shared decision parity」へ置き換わる。
- `notes/design/2026-08-06-cpk-projection-decision-addendum.md` Slice B の
  `cycle-cut 有無と decision` exact comparison は、
  「unavoidable-cycle unit fixtureでの cut 発火」+
  「cross-authority final decision/payload parity」へ分割して読む。

先行文書自体は本書で編集しない。本書を後継の裁定として参照する。

### 4.2 維持する cycle assertion

次は循環 branch が唯一または必須の評価経路であり、cycle guard 自体を検査する。
本書による緩和対象ではない。

1. `cpk_gap_1_project_lower_cycle_cuts_only_the_circular_route`
   （`proof/mod.rs:5850` 付近）
   - `Excluded`
   - `round.cycle_cuts() == 1`
   - `memo_sharing_disabled == true`
2. `cpk_gap_1_replay_conjunction_matches_all_four_cpk_consumers`
   （`proof/mod.rs:6191` 付近）の circular-only excluded half
   - `Excluded`
   - `round.cycle_cuts() == 1`
3. `cpk_4_derived_unary_only_cycle_flips_inclusion_and_owner`
   （`proof/mod.rs:9140` 付近）
   - owner/dependent owner publication
   - `Excluded`
   - unavoidable cycleで `round.cycle_cuts() > 0`
4. DPN の self-cycle / two-node-cycle / mixed record-constraint-cycle fixtures
   - circular-only proofが false
   - active-path cycle guardが有限停止すること

これらを消すと、occurrence parity の緩和ではなく cycle guard 自体の coverage 縮小になるため、
削除してはならない。

### 4.3 追加する regression gate

category-crossing mixed fixtureを CPK canonical storeから評価し、次を一つの testで固定する。

1. `Standalone` が `DerivedUnary` より先に評価される。
2. independent armにより最終 decisionは `Included`。
3. cycle branchをshort-circuitした場合、cut count 0 と sharing継続は許される。
4. 同じ root列をfresh evaluatorで評価した decision列と一致する。
5. admission permutationで canonical formula snapshot、decision、payload、publicationが同一。

この test は「0 cuts が常に正しい」と固定するものではない。typed canonical comparatorが将来
精密化されても、fresh/shared同値とsemantic outputが保たれることを固定する。

## 5. 他候補を採らない理由

### 5.1 候補 a: CPK に historical arrival-order view を追加する

採らない。

実現には、全 clause sourceを横断する lower-record-local unique clause identity、first-admission
sequence、dedup時に位置を維持する writer、CPK/flat atomicity、snapshot parityが必要になる。
既存 `ProofOccurrence.event` はprojection clauseと一対一ではなく、RCPFの
`admission_ordinal`はreplay occurrenceだけを覆うため再利用できない。

また、同じ clauseに異なるsupportが付く場合、formula entryのarrival順ではなくclause identityの
first arrivalを別に保持する必要がある。これは削除予定のflat orderingをCPKへ恒久複製する設計であり、
CPK-0 typed orderとRCPF-D3b invariant 23の方向に反する。

### 5.2 候補 b: `category_rank` ordering を外して insertion order に戻す

採らない。

rank自体はarrival sequenceを表せないため、単に削除すればcanonical orderが無くなるだけである。
`NonCanonicalProjectionOrder` preflight、CPK-0 formula action order、CPK projection decision
addendumのcanonical store contractを破る。diagnostic/provenanceのcanonical prefixを再び
historical timingへ結び付ける方向でもある。

### 5.3 候補 c1: flat evaluatorを先にCPK canonical orderへ変更する

採らない。

architectureとしては一つのorderへ収束できるが、削除直前のflat production writer/evaluatorの
挙動を先に変え、cycle-cut / memo-sharing sequenceを変更する別のsemantic migrationになる。
CPK-8G-4bのreader-only cutoverを越え、flat canonical-position insertion、同一category comparator、
旧fixture期待の全面更新が必要になる。消す側を新 authorityへ作り替えるコストに対し、
得られるのは不要な一時 parityだけである。

### 5.4 候補 c2: CPK canonical order + A3 semantic parity

採用する。

既存の署名済み二契約を同時に守る唯一の局所解である。

- CPK-0のtyped canonical orderを守る。
- A3が明記した「cut countはshort-circuit順で異なり得る」を守る。
- cycle guard、cut後sharing disable、fresh/shared equivalenceを守る。
- historical order indexを追加しない。
- evaluator algorithmを変えない。
- user/diagnostic-visible outputを変えない。

必要な変更は、reader cutoverと、誤ってsemantic parityへ昇格したshadow/test assertionの局所的な
修正に限定できる。

### 5.5 候補 c3: OR armをshort-circuitせず全件評価する

採らない。

cycle detectionをorder-independentにできても、decision algorithmを変える。
従来訪れなかったdangling/fallible branchを評価し、不要なhard failureや追加workを発生させ得る。
DPNが明示的に避けたSCC/fixpoint/proactive graph evaluationの方向へ近づき、hot pathの
O(reachable short-circuit prefix)を全reachable armへ広げる。cycle-cut telemetryを揃えるために
semantic evaluatorを変えるのは責務が逆である。

## 6. CPK-8G-4b の resulting design

### 6.1 before / commit / after sequence

前回attemptで確定したsequencing fixをそのまま使う。

```text
1. CPK authoritative stateからbefore viewを取得
2. CPK qualified-parent / projection index transactionをcommit
3. flat / RCPF mirrorへone-way feedをcommit
4. CPK authoritative stateからafter viewを取得
5. before/afterを既存algorithmで比較
6. affected owner / epoch class / publication intentを決定
```

before viewはCPK commit前、after viewはCPK commit後に取る。flat mirrorの書込み順を
before/after semanticsの根拠にしない。

### 6.2 evaluator read source

publication evaluatorは CPK authoritative structureだけを読む。

- claim lifecycle: CPK-8G-2。
- qualified parent exact/canonical index: CPK-8G-3。
- target/dependency/target-late index: CPK-8G-4a。
- projection support/formula: CPK `ProofOccurrenceStore` canonical view。

flat/RCPF writerはCPK-8G-5まで維持するが、publication decisionのreader authorityには戻さない。

### 6.3 A3 / A4 の維持

- same snapshot / view内だけ evaluator memoを共有する。
- before / afterは別roundにする。
- cycle cut後は同roundの共有を永久に停止する。
- clause-link mutation batchはcomplete post-event stateだけをpublishする。
- cycle-cut count差はbatch publicationを変えない。
- cycle-cut countをepoch、affected owner、publication intentへ入力しない。

### 6.4 8G-2/3/4aを再開しない

本書は次を変更しない。

- claim ID、original/derived dedup、root canonicalization、cycle coalesce。
- claim move、claims-by-record、live coverage。
- exact qualified-parent identity、per-result index、canonical parent order。
- target/dependency exact key、premise reverse edge、target-late propagation。
- 各CPK transactionのcapacity preflight / no-partial-commit contract。
- RCPF内部のreserve/commit logic。

formula evaluation orderの裁定を理由に、これらのstorage identityやmutation orderを変更しない。

## 7. 必須 invariant

1. **Final-decision invariance**: 同じsemantic graphのclause admission permutationで
   `ProjectionDecision`が変わらない。
2. **Typed canonical authority**: evaluatorはCPK canonical formula viewを読み、flat historical
   orderやadmission ordinalを読まない。
3. **Cycle-path rejection**: 実際に訪れたcircular routeはfalseになる。
4. **Alternative preservation**: circular route以外の独立なOR armは評価を継続できる。
5. **Conditional sharing disable**: cutを観測したroundだけがshared memoを破棄する。
6. **Fresh/shared equivalence**: 同一snapshot/view/orderのtop-level decision列はfresh evaluator列と
   shared roundで一致する。
7. **No escaped Visiting**: top-level return時に`Visiting` stateを残さない。
8. **Payload independence**: support payloadはcanonical preflight viewから作り、winning branch、
   cut、short-circuitで削らない。
9. **Publication independence**: affected owner、epoch、publication intentはbefore/after semantic
   stateから決め、cycle-cut counterを入力にしない。
10. **Diagnostic isolation**: witness/explain/portable/source diagnostic sequenceはcanonical
    support/action orderに従い、cycle-cut traceを読まない。
11. **No historical-order mirror**: CPKにflat clause arrival historyを保持する第二indexを追加しない。
12. **Focused cycle coverage**: unavoidable-cycle fixtureはcut発火とsharing disableをpinし続ける。
13. **No algorithm change**: record clause OR、ReplayConjunction AND、tri-color guard、fail-open / hard
    failure境界を変更しない。
14. **No prior-slice drift**: CPK-8G-2/3/4aのidentity、dedup、canonical order、atomicityを変更しない。

## 8. implementation / verification gate

CPK-8G-4bの再実装は次を一つのreviewable sliceとして行う。

1. CPK before viewをCPK qualified-parent commit前に取る。
2. evaluatorのbefore/after readをCPK stateへ切り替える。
3. `compare_projection_record_shadow`のcut-occurrence equalityだけを外す。
4. §4.1のmixed fixtureをsemantic/fresh-shared gateへ更新する。
5. §4.2のfocused cycle assertionsを期待値無変更で保つ。
6. category-crossing canonical-order regressionを追加する。
7. CPK formulaの同一category内orderがCPK-0契約を満たすことを確認する。

最低限のverification matrix:

- `dpn_b_cycle_guard_cyclic_route_plus_independent_source_stays_projectable`
- `dpn_b_9_5_late_constraint_route_retriggers_dependent_record`
- DPN self/two-node/mixed cycle fixtures
- `cpk_gap_1_project_lower_cycle_cuts_only_the_circular_route`
- `cpk_gap_1_replay_conjunction_matches_all_four_cpk_consumers`
- `cpk_4_derived_unary_only_cycle_flips_inclusion_and_owner`
- CPK / RCPF / DPN / MPC targeted suites
- constraints scoped suite
- generalize / compact / explain / portable_explain suites
- canonical portable / diagnostic / generalized witness characterization

期待する結果:

- final decision、payload、owner、epoch、publicationはcutover前と同一。
- category-crossing mixed fixtureのraw cut count差だけは許容。
- focused cycle fixtureは引き続きcutを観測。
- fresh/shared decision列は全view/query orderで同一。
- four canonical-order-sensitive consumerのoutput / prefixは不変。

## 9. blast radius と rollback

### 9.1 触る範囲

- `crates/infer/src/constraints/machine/bounds.rs`
  - pre-CPK-commit before view capture。
  - mixed cycle fixtureのcontract更新。
- `crates/infer/src/constraints/proof/mod.rs`
  - CPK-sourced before/after evaluation。
  - shadow cut-occurrence equalityの除去。
  - canonical category-crossing regression。
  - 必要なら同一category typed-order preflightの補完。
- `crates/infer/src/constraints/mod.rs`
  - SchemeProjectionEvaluator publication read adapterのCPK切替。
  - flat writerは維持。

実際のcall-site censusでこれを超える場合は§10に従う。

### 9.2 触らない範囲

- CPK-8G-2/3/4aのwriter authority。
- RCPF internal stores / reserve / commit。
- flat/RCPF dual writeの停止（CPK-8G-5）。
- claim/replay routing semantics。
- diagnostic/provenance comparator。
- SCC、fixpoint、worklist、generalization core。

### 9.3 rollback unit

CPK-sourced publication reader、pre-commit before capture、shadow/test contract更新を
CPK-8G-4bの一つのauthority-cutover commitとしてrevert可能にする。

rollback時に historical-order CPK index、flat canonicalization、exhaustive evaluationを追加しない。
reader authorityを直前のflat pathへ戻し、本書とregression fixtureはfindingの記録として残す。

## 10. stop / falsification conditions

次のいずれかが判明した時点でCPK-8G-4bを止め、本書の決定へ戻る。

1. cycle-cut count / occurrenceを入力にするproduction consumerが見つかる。
2. 同じfinal decision / payloadでもcut occurrence差だけでaffected owner、epoch、publication intent、
   diagnostic、provenance、portable outputのいずれかが変わる。
3. CPK canonical orderでcutを観測しなかったshared roundが、同じorderのfresh evaluator列と
   異なるdecisionを返す。
4. cutを観測せずにcontext-dependent `Done`またはescaped `Visiting`が残る。
5. clause admission permutationでfinal decision、payload、owner、epoch、publicationが変わる。
6. circular-only fixtureがcycleをcutせずtrueになる、無限再帰する、またはsharingを継続する。
7. same-category typed total orderを、historical admission ordinalなしでは実現できない。
8. CPK-0 typed canonical orderを守るためにCPK-8G-2/3/4aのidentityやmutation semanticsを
   変更する必要が出る。
9. evaluator read sourceとbefore/after decision algorithmを分離できず、algorithm変更が必要になる。
10. RCPF internal reserve/commit logicの変更が必要になる。
11. full suiteでraw cut count以外のobservable shiftが出る。
12. user-facing telemetry / compatibility contractがcycle-cut countを外部仕様として固定していた証拠が
    見つかる。

1、2、12のいずれかが見つかれば、本書の「cut occurrenceは内部event」という根拠が反証される。
その場合、test期待値を緩めて進まず、historical-order identityの必要性を含む新しい設計判断へ戻る。

3、4、6が見つかればA3のsharing safetyが成立していない。count parityを復活させて隠さず、
evaluator state machineの根因を調査する。

7、8が見つかれば本件とは別のCPK canonical-order implementation gapである。
flat insertion orderへfallbackせず、CPK-0追補の改訂または補完設計を先に承認する。

## 11. 先行文書との関係

### 11.1 DPN root-claim / cycle-safety 追補

active-path `Visiting` / `Done`、circular route=false、他OR arm継続、有限停止をすべて維持する。
cycle guardの発火回数をsemantic outputへ昇格しない点だけを明示する。

### 11.2 MPC/DPN projection evaluation round

A3 §5のliteral contract――cut countはshort-circuit順で異なり得るがprojectabilityは不変――を
正本として採る。cut後sharing disable、fresh/shared oracle、A4 atomic batchは変更しない。

### 11.3 RCPF-D3b

invariant 23を改訂しない。historical admission orderをCPKへ永続化せず、diagnostic/provenanceは
既着地canonical support orderへ隔離したまま保つ。

### 11.4 CPK-0 / CPK projection decision addendum

typed canonical support/formula order、`NonCanonicalProjectionOrder`、canonical payload、
cycle-cut後sharing disableを維持する。

置き換えるのは、旧flat insertion-order evaluatorとCPK canonical-order evaluatorの間で
cycle-cut occurrenceも一致させるというshadow-only requirementである。

### 11.5 CPK separation plan

CPK-4のhistorical exit condition `cycle-cut が parity` は、CPK-4当時のmigration gateとして
役割を果たした。本書以後のphysical reader cutoverでは、次へ精密化する。

```text
旧: legacyとCPKでcycle-cut occurrenceがparity
新: CPKのunavoidable cycleはcutされ、cut後sharingは停止し、
    legacy/CPKのfinal decision・payload・publicationがparityで、
    CPK fresh/shared decision列がparity
```

## 12. 完了条件

本書の決定を反映したCPK-8G-4bは、次をすべて満たしたときだけ完了とする。

1. publication evaluatorのbefore/after read authorityがCPKだけになる。
2. before viewがCPK commit前、after viewがCPK commit後に取得される。
3. flat/RCPF writerはCPK-8G-5まで維持されるがdecision authorityではない。
4. cross-authority cut-occurrence equalityがparity gateから外れる。
5. unavoidable-cycle unit testsはcutとsharing disableを引き続きpinする。
6. fresh/shared、permutation、cache/viewのfinal decisionとpayloadが一致する。
7. affected-owner、epoch、publication intentに差がない。
8. generalize / explain / portable / source diagnosticのcanonical outputに差がない。
9. CPK-8G-2/3/4aの全contractが期待値無変更でgreen。
10. §10のstop conditionが一件も発火しない。

---

著者: Codex gpt-5.6-sol（xhigh）が調査・起案、Claude (Sonnet 5) が査読・確定
