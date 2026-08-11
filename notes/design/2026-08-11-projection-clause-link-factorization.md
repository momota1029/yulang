# projection clause-link relation の factorization（PCLF rev.2）

日付: 2026-08-11（Claude 査読・確定: 2026-08-11、ユーザ承認: 2026-08-11）

状態: **ユーザ承認済み（正本）。PCLF-A 以降の実装に着手可**

基準 commit: `0e208ab4`。行番号はこの commit 付近を指し、実装時には関数名と型名を正本として再確認する。

本書は、Fable 5 が一時的に利用できない場合の代替起案手続きに基づく設計ドラフトである。
Codex `gpt-5.6-sol`（xhigh）が本文を起案し、Claude (Sonnet 5) がコード整合性と先行設計との
非矛盾を査読・確定した後、ユーザ承認を受ける。現時点では設計優先順位上の正本ではなく、
実装着手を許可する文書でもない。

略称として、本設計を **PCLF（Projection Clause-Link Factorization）** と呼ぶ。

rev.2 は、rev.1 の adversarial code review で判明した source-template uniformity の反例を反映する。
rev.1 は claimed source template を clause entry ごとに一つと仮定したが、current writer は
`ReplayConstraint { result }` と `ReplayEvidence`、または異なる `result` を、異なる outer raw support から
同じ `(record, RecordProofClause)` へ合法に到達させうる。rev.2 は source metadata を clause entry ではなく
exact incidence ごとに保持する。rev.1 の workload census 値は変更せず、その zero-conflict 観測を
一般不変条件として扱わない。

## 0. 決定要約

`ProofOccurrenceStore` の projection formula は、意味上は次の二部関係である。

```text
record-local exact clause body × exact raw support occurrence
```

現行実装は、この二部関係を一件の link ごとに展開し、同じ exact clause body を
`projection_formulas` と raw link ledger の双方へ繰り返し格納する。
`std::text::parse` workload の fresh census では、logical exact link は `28,526,006` 件だが、
distinct `(record, RecordProofClause)` は `847,858` 件にすぎない。一 clause あたりの link は
平均 `33.644791934` 件である。

PCLF は意味上の exact link を削除・併合しない。物理表現だけを次へ正規化する。

1. record ごとに `ProjectionFormulaBucket` を一つ持つ。
2. exact `RecordProofClause` body は `ProjectionFormulaEntry` として一度だけ格納する。
3. raw `SchemeProjectionProofSupport` は record-local support group として一度だけ格納する。
4. logical exact link は compact な
   `(ProjectionSupportGroupId, ProjectionFormulaEntryId) -> ProjectionIncidenceMetadata`
   incidence として保持する。claimed source template はこの exact incidence の小さい value であり、
   clause entry 全体の属性にはしない。
5. `projection_clause_keys` は、record-local な
   `RecordProofClause -> ProjectionFormulaEntryId` hash index に置き換える。
6. exact link membership は compact incidence index で expected O(1) とする。
   raw-link `Vec` の binary search は採らない。
7. canonical formula は hash iteration から作らず、category、raw support、clause suffix の
   現行 `ProjectionClause::canonical_cmp` と同じ順序を返す typed iterator として提供する。
8. claimed link の event-local source metadata は、coverage root を support group 側に、source kind と
   producer/result を exact incidence 側の `ClaimedProjectionSourceTemplate` に保持する。同じ clause の
   異なる incidence が異なる template を持てることを必須とする。
9. evaluator、GWCB decisive-arm capture、audit、portable/logical consumer は query API を介し、
   production hot pathで expanded 28.5M-link formulaを再構築しない。

この形は、RCPF と同じく logical exact relation を保ったまま物理的な共通部分を factored representation
へ移す設計である。CDM と同じく admission は full snapshot rebuild ではなく delta prepare/commit にする。
ただし RCPF の replay parent-set snapshot と本設計の projection clause-link incidence は別の relation であり、
ID や snapshot を安易に共用しない。

## 1. 問題

### 1.1 現行 storage と identity

`crates/infer/src/constraints/proof/mod.rs` の `ProofOccurrenceStore` は、projection clause/link について
次の六つの概念的 storage 面を持つ。最後の attribution 面は二つの `FxHashSet` からなるが、同じ
`(record, root)` summary family として一面に数える。

| storage | identity / value | 現行の役割 |
|---|---|---|
| `projection_formulas` | `record -> Vec<ProjectionClause>` | evaluator の canonical OR-arm 列。link ごとに full clause を保持 |
| `projection_claimed_link_audit` | `(record, raw support, RecordProofClause) -> ClaimedProjectionProofSource` | claimed exact membership、GWCB certificate source |
| `independent_projection_clause_link_keys` | `(record, raw support, RecordProofClause)` | independent exact membership |
| `projection_clause_keys` | `(record, RecordProofClause)` | distinct clause 判定、dependency edge exactly-once |
| `projection_formula_support_keys` | `record -> set<ProjectionSupportMatchKey>` | evaluator の normalized support membership |
| attribution summaries | `(record, root)` | any-attributed と flat-retained-attributed の二 summary |

claimed と independent の raw exact link storage は disjoint union であり、同じ raw identity を二つへ
重複登録しない。一方、`projection_formulas` は両方を full `ProjectionClause` として再度保持するため、
logical link 一件につき clause/carrier/premise/support の大きい payload が複数面へ現れる。

`try_prepare_projection_clause_admission`（`proof/mod.rs:3067` 付近）は、各 admission について次を行う。

1. `projection_clause_link_is_registered` で claimed audit map または independent set を引く。
2. batch-local raw link set で同一 batch 内 duplicate を落とす。
3. `projection_clause_keys` で distinct clause かを判定する。
4. claimed source metadata と attribution summary delta を準備する。
5. accepted が非空なら既存 `projection_formulas[record]` 全体を clone し、delta clause を canonical insert する。
6. `projection_formula_support_keys[record]` も新しい set へ copy する。
7. 全 storage の capacity を preflight し、`commit_projection_clause_admission` で lockstep commit する。

caller 側にも exact membership と batch-local duplicate の preflight がある。この caller/writer 二重判定は
CDM-shaped な小さい重複であるが、単独除去実験では dominant cost を説明しなかった。PCLF の中心は
この二重判定ではなく、28.5M logical link に full identity/payload を物理展開する storage shape である。

production mutation は `try_prepare_projection_clause_admission` / `commit_projection_clause_admission` に集約され、
production remover は見つかっていない。一方、test-only には二つの bypass writer がある。

- `set_projection_formula_for_test`（`proof/mod.rs:3052` 付近）は `projection_formulas` と
  `projection_formula_support_keys` を直接置換する。
- `cpk_gap_1_five_lineages_project_through_the_real_formula_graph`（`proof/mod.rs:10233` 付近）は
  `projection_formulas.get_mut` から attribution を直接書き換える。

これらは production writer invariant の証拠に含めないが、legacy field 撤去前に放置もしない。
PCLF-A で admission/source metadata を明示する test fixture API へ移し、PCLF-E で direct legacy mutation zero を
再 census する。

### 1.2 Fresh PCLF-0 census

2026-08-11、`0e208ab4` の同一 cold `dump-poly-std` reproduction で temporary counter を入れ、
main `ProofOccurrenceStore` を終了時に全走査した。instrumentation は測定後に除去し、clean source で
release binary を再buildした。

#### Formula / link volume

| 項目 | 実測値 |
|---|---:|
| formula record 数 | 108,241 |
| logical exact link | 28,526,006 |
| claimed exact link | 28,516,968 |
| independent exact link | 9,038 |
| distinct `(record, RecordProofClause)` | 847,858 |
| exact links / distinct clause | 33.644791934 |
| distinct clauses / formula record | 7.833057714 |

`projection_formulas` の record-local expanded link 数分布は次である。

| 指標 | link 数 |
|---|---:|
| mean | 263.541596992 |
| p50 | 30 |
| p95 | 1,759 |
| max | 4,700 |

distinct clause 一件を超えて繰り返される link occurrence は `27,678,148` 件で、logical link の
`97.027771781%` に当たる。これは 97% の exact link が意味上 duplicate という意味ではない。
各 support occurrence は exact relation の別の一件であり不可侵である。重複している主 payload は、各 occurrence に
繰り返し埋め込まれた record prefix、exact clause body、carrier/premise である。source kind と producer/result は
rev.2 では incidence ごとに異なりうるため、compact value として残す。

#### Admission outcome

caller preflight と direct writer path を重複計上しない logical attempt は `70,610,294` 件だった。

| outcome | 回数 | 割合 |
|---|---:|---:|
| persistent existing duplicate | 21,133,034 | 29.929112036% |
| batch-local duplicate | 20,951,254 | 29.671670819% |
| real insertion | 28,526,006 | 40.399217145% |

no-state-change の duplicate/re-touch は合計 `42,084,288` 件、`59.600782855%` である。
caller は `28,513,660` 件を writer へ渡し、writer は同じ persistent membership をもう一度確認した。
writer-side duplicate hit はゼロだった。direct writer admission は `12,346` 件で、すべて real insertion だった。

これは小さい CDM-shaped component が実在することを示す。ただし prior isolated experiment と profiler では、
caller/writer recheck だけを消しても wall time は有意に動かなかった。PCLF はこの recheck を最終的に一 authority
query へ統合できるが、それを factorization の性能根拠として過大評価しない。

### 1.3 Source metadata factorability

claimed audit 全 `28,516,968` link を、`(record, exact RecordProofClause)` ごとに group 化した。
`coverage_root` を除く source metadata を次の template として比較した。

```text
Original { producer }
DerivedUnary { result }
ReplayConstraint { result }
ReplayEvidence
```

結果は次である。

| 項目 | 実測値 |
|---|---:|
| claimed clause group | 838,820 |
| claimed links / group mean | 33.996528457 |
| claimed links / group max | 97 |
| source template conflict | 0 |
| source root mismatch | 0 |
| missing claim root | 0 |

この workload では source conflict は観測されなかった。しかし rev.1 adversarial review は、これは reachable state の
不変条件ではないと確認した。`RecordProofClauseLinkAdmission::claimed` は clause/source の kind compatibility だけを
検証し、同じ `(record, RecordProofClause)` の全 incidence が同じ template を持つとは保証しない。
特に canonical replay writer の `ReplayConstraint { result }` と replay-evidence writer の `ReplayEvidence` は、
異なる outer raw support から同じ `ReplayConjunction` body へ到達できる。また `result` は
`ReplayConjunction` / `DerivedUnary` clause identity に含まれない。

従って zero-conflict は workload 特性の実測としてのみ保持する。rev.2 は uniformity を要求せず、claimed sourceを
exact `(support group, clause entry)` incidence の compact value にする。PCLF-A は全 writer constructor と
合成 conflict fixture で、この per-incidence model が raw audit finite map を lossless に表すことを確認する。

### 1.4 Membership feasibility probe

同じ終了時 store から claimed raw identity を 100,000 件抽出し、successful membership を比較した。

| lookup | 平均 |
|---|---:|
| flat raw-link hash | 16.168 ns/op |
| current canonical raw-link formula の binary search | 1,557.711 ns/op |

current raw-link `Vec` の binary search は flat hash の約 `96.345x` だった。
この probe は factorized distinct-clause `Vec` の直接測定ではないが、p95 1,759 / max 4,700 の
raw-link formula を admission authority にする案を棄却するには十分である。

一方、distinct clause は record あたり平均 7.833 件であり、`projection_clause_keys` 自体も 847,858 件しかない。
従って PCLF は binary search へ authority を移さず、現在の distinct-clause hash lookup を record-local
`RecordProofClause -> ProjectionFormulaEntryId` index へ精密化する。exact support occurrence membership も
full raw identity ではなく compact ID pair の hash index で答える。

### 1.5 問題の正確な形

record `r` の distinct exact clause body 集合を `C(r)`、raw support 集合を `S(r)`、logical incidence を

```text
L(r) ⊆ S(r) × C(r)
```

とする。現行 `projection_formulas[r]` と raw link ledger は `L(r)` を full tuple へ展開する。

```text
current physical payload
  ≈ Σr |L(r)| × (record + support + full clause + source/index overhead)
```

PCLF の target は次である。

```text
factored physical payload
  ≈ Σr (
        |C(r)| × clause
      + |S(r)| × raw-support/root
      + |L(r)| × (compact incidence/index reference + compact source metadata)
      )
```

logical `Σr |L(r)| = 28,526,006` は変えない。削減対象は exact semantics ではなく、
各 incidence に反復する大きい record/support/clause prefix/body である。claimed source template は
raw full keyとは分離するが、意味上必要な incidence-local payload として削除しない。

## 2. 先行設計との関係

### 2.1 RCPF

RCPF は replay claim-parent relation を exact occurrence と shared parent-set snapshot へ factor した。
PCLF はその closest precedent だが、共有単位が異なる。

- RCPF: 多数 carrier が共有する event-time parent-set snapshot。
- PCLF: 一 record 内で多数 raw support が共有する exact clause body。source template は共有を仮定せず、
  compact incidence metadata として保持する。

どちらも logical exact relation の full expansion を oracle/explicit export に限定し、normal consumer は
factored query を読む。PCLF は RCPF の `BinaryReplayDerivation` exact identity、parent side、representative claim、
event-time completeness を変更しない。ReplayConjunction entry は exact carrier と lower/upper premise を全て保持する。

RCPF の occurrence ID や parent-set version ID を PCLF の clause/support ID と共用しない。同じ replay carrier が
関係しても、claim-parent relation と clause-link relation は異なる identity と mutation boundary を持つ。

### 2.2 CDM

CDM の規律を次の二点で継承する。

1. full snapshot を clone/rebuild せず、accepted occurrence delta だけを prepare/commit する。
2. 現行の正しくて大きい展開表現を test-only linear reconstruction oracle として退役させる。

admission 時完全性、natural-event batch、before/commit/after publication、failed admission の logical atomicityを
変更しない。dirty mark、delayed flush、repair pass、不動点反復を導入しない。

### 2.3 MPC / DPN

PCLF は `RecordProofClause` の意味を変えない。

- `Standalone` は support 自身を評価する。
- `DerivedUnary` は typed `ProofPremise` 一件を評価する。
- `ReplayConjunction` は lower/upper premise の AND である。
- record formula 全体は OR である。

exact carrier、premise、occurrence attribution、dependency edge を粗化しない。
new clause 一件だけが既存規則どおり dependency edge を作り、同じ clause への新 support incidence は edge を増やさない。

### 2.4 GWCB

GWCB の semantic contract は不可侵である。

```text
ProjectionEvidence =
    DecisiveClaimedArm(ClaimedProjectionProof)
  | ExactWithoutClaimedArm
  | FailOpenIncomplete
```

PCLF は `ClaimedProjectionProof`、normalized `ClaimedProjectionProofKey`、raw audit identity、
single canonical-first decisive arm の意味を変更しない。変更するのは raw facts の物理配置だけである。

現行 decisive claimed read は、evaluator が短絡採用した `ProjectionClause` から

```text
(record, raw support, RecordProofClause)
    -> projection_claimed_link_audit
    -> ClaimedProjectionProofSource
    -> ClaimedProjectionProof
```

を O(1) で行う。PCLF 後は次になる。

```text
record bucket
    -> raw support -> ProjectionSupportGroupId
    -> RecordProofClause -> ProjectionFormulaEntryId
    -> compact exact incidence metadata
    -> incidence.claimed_source + support_group.coverage_root
    -> ClaimedProjectionProofSource
    -> ClaimedProjectionProof
```

全 lookup は record-local hash/index で expected O(1) とする。formula scan、全 incidence expansion、certificate cache、
true-arm collection は置かない。missing entry/template/incidence は別 producer へ近似せず、GWCB の corruption /
`FailOpenIncomplete` contract を維持する。

### 2.5 今回変更しないもの

- claim identity、coverage root、liveness、claim movement。
- semantic bound/constraint generation、solver replay、row reduction。
- include/exclude、record OR、ReplayConjunction AND、cycle cut、fail-open の向き。
- `ProjectionSupportSet` と generalization semantic payload。
- GWCB local/portable/logical topology と decisive-arm contract。
- RCPF claim-parent representation と qualified-parent ordering。
- diagnostic text、source location、portable shared-edge dedup。
- epoch/publication policy。
- exact clause/link の logical cardinality。

## 3. 提案する factorized representation

型名と配置は PCLF-A で現行命名との衝突を再確認する。以下は意味上の model である。

### 3.1 Stable record-local IDs

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ProjectionFormulaEntryId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ProjectionSupportGroupId(u32);
```

ID は一つの `ProjectionFormulaBucket` 内だけで有効とする。record を跨ぐ global ID として使わない。
entry/support arena は append-only とし、ID を再利用・renumber しない。内部 compaction が必要になっても、
consumer-visible な ID stability と canonical iterator を変えない方式だけを許す。

### 3.2 Clause entry

```rust
struct ProjectionFormulaEntry {
    clause: RecordProofClause,
}
```

`RecordProofClause` は exact のまま保存する。

- `Standalone.support` に埋め込まれた raw support を落とさない。
- `DerivedUnary.carrier/premise` を落とさない。
- `ReplayConjunction.carrier/lower_premise/upper_premise` を落とさない。

同じ entry に independent occurrence と claimed occurrence が共存でき、異なる claimed incidence が異なる
source kind/result を持てる。従って entry は source metadata を持たない。independent/claimed attribution と
claimed source template は §3.4 の exact incidence value から得る。clause entry の lifetime と source metadata の
lifetime を結合しないため、independent-first / claimed-later に entry promotion は発生しない。

### 3.3 Support group

```rust
struct ProjectionSupportGroup {
    raw_support: SchemeProjectionProofSupport,
    match_key: Option<ProjectionSupportMatchKey>,

    // raw_support が Claimed の場合だけ Some。admission-time に凍結する。
    coverage_root: Option<UpperReplayClaimId>,

    // 各 Vec は現行 ProjectionClause::canonical_cmp の category 内 suffix 順。
    standalone_entries: Vec<ProjectionFormulaEntryId>,
    derived_unary_entries: Vec<ProjectionFormulaEntryId>,
    replay_conjunction_entries: Vec<ProjectionFormulaEntryId>,
}
```

raw support identity と normalized support identity を混同しない。

- exact raw link membership は `raw_support` を使う。
- evaluator の qualifying-support summary は `match_key` を使う。
- claimed certificate normalization は `coverage_root` を使う。
- same-root representative replacement は raw occurrence を失わない一方、normalized summary/certificate key は一つへ畳める。

category 別 Vec は canonical output の adjacency index であり、authority は §3.4 の exact incidence relation である。
hash iteration orderを formula orderへ漏らさない。

### 3.4 Record-local bucket

```rust
struct ProjectionFormulaBucket {
    entries: Vec<ProjectionFormulaEntry>,
    entry_by_clause:
        FxHashMap<RecordProofClause, ProjectionFormulaEntryId>,

    support_groups: Vec<ProjectionSupportGroup>,
    support_group_by_raw:
        FxHashMap<SchemeProjectionProofSupport, ProjectionSupportGroupId>,

    // Logical exact relation L(r) と incidence-local source の compact authority。
    exact_links:
        FxHashMap<
            (ProjectionSupportGroupId, ProjectionFormulaEntryId),
            ProjectionIncidenceMetadata,
        >,

    // canonical support iteration。projection_support_cmp 順。
    canonical_support_groups: Vec<ProjectionSupportGroupId>,

    // Hot summaries。現行 query semantics を維持する。
    normalized_support_keys: FxHashSet<ProjectionSupportMatchKey>,
    attributed_roots: FxHashSet<UpperReplayClaimId>,
    flat_retained_attributed_roots: FxHashSet<UpperReplayClaimId>,
}

struct ProjectionFormulaStore {
    by_record: FxHashMap<BoundRecordId, ProjectionFormulaBucket>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ProjectionIncidenceMetadata {
    Independent,
    Claimed(ClaimedProjectionSourceTemplate),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ClaimedProjectionSourceTemplate {
    Original { producer: ConstraintRecordId },
    DerivedUnary { result: ConstraintRecordId },
    ReplayConstraint { result: ConstraintRecordId },
    ReplayEvidence,
}
```

`entry_by_clause` は `projection_clause_keys` を置き換える。global `(record, clause)` key の record prefixを
各 entryへ繰り返さず、bucket lookup 後は exact clause body だけで O(1) lookup する。

`exact_links` は logical incidence を一件ずつ保持する。key は二つの `u32` ID だけであり、value は
`Independent` または coverage root を除いた小さい claimed source template である。raw record/support/full clauseを
28.5M hash entryへ複製しない。source kind と producer/result は incidence 間で異なりうる意味情報なので、
claimed incidence の value から削除しない。

ここで「小さい」は full raw key / full clauseを含めないという設計上の比較であり、Rust layout、padding、hash table
capacityを含む実byte数を測定済みという意味ではない。`ProjectionIncidenceMetadata` の `size_of` と全capacity込みbytesは
§9.4どおりPCLF-Bで **要検証** とする。

lookup `(raw support, exact clause)` は `support_group_by_raw` と `entry_by_clause` から ID pair を作り、
`exact_links.get(&(support_id, entry_id))` でその exact link 固有の metadata を得る。同じ entry に
`ReplayConstraint { result }` と `ReplayEvidence` が別 support から到達しても、二つの pair は別 value を保持する。
`entry_by_clause` は引き続き clause bodyだけを authority とするため、dependency edge exactly-onceを変えない。

canonical adjacency には logical link 一件につき compact `ProjectionFormulaEntryId` が一つ現れる。
従って incidence は membership hash と canonical adjacency の二つの compact projectionを持つ。
これは full tuple の二重保存ではないが、実 byte footprint は PCLF-B で計測する。
backend がこの model より大きく、raw flat ledger と同程度の bytes を使う場合は authority cutover へ進まない。

### 3.5 Canonical formula iterator

`ProjectionFormulaBucket::canonical_clauses()` は次の順で `ProjectionClause` を値として遅延生成する。

```text
for category in [Standalone, DerivedUnary, ReplayConjunction]:
    for support_group in canonical_support_groups:
        for entry in support_group.entries_for(category):
            yield reconstruct(entry, support_group)
```

`canonical_support_groups` は `projection_support_cmp` 順に維持する。category 内 entry Vec は、
reconstructed `ProjectionClause` に対する `ProjectionClause::canonical_cmp` の support より後ろの keyで
昇順に維持する。equal な reconstructed clause が複数ある場合、出力 value が byte-identical であること、
raw exact identity と per-incidence claimed source template が別 oracle で一致することを要求する。hash/arena ID順を
tie-breakerとして diagnostics や decisive-arm semanticsへ露出しない。

reconstruct 時の attribution は entry-global stateから読まない。各 `(support_id, entry_id)` の
`ProjectionIncidenceMetadata` を読み、`Independent -> None`、claimed templateのvariant -> 現行
`ProjectionLineage`へ写す。従って source kindが異なる同一clause bodyも現行 `canonical_cmp` のattribution rankで
正しく並ぶ。

test-only oracle は iterator を `Vec<ProjectionClause>` へ展開し、legacy `projection_formulas[record]` と
sequence equalityで比較する。set equalityだけでは GWCB decisive armを保護できない。

新 support group の canonical support Vec への insertion は record-local support 数に、新 entry incidence の
category Vec insertion はその support/category の distinct entry 数に比例する。どちらも record の全 raw link 数
`|L(r)|` には比例させない。これらの分布は PCLF-B で追加 census し、累積 movement が新しい支配項になる場合は
ordered backend を再レビューする。

### 3.6 Exact membership

```rust
fn exact_link_is_registered(
    &self,
    record: BoundRecordId,
    support: SchemeProjectionProofSupport,
    clause: RecordProofClause,
) -> bool {
    let bucket = self.by_record.get(&record)?;
    let support_id = bucket.support_group_by_raw.get(&support)?;
    let entry_id = bucket.entry_by_clause.get(&clause)?;
    bucket.exact_links.contains_key(&(*support_id, *entry_id))
}
```

実 API は `Option` を boolean へ潰す前に corruption distinction を必要に応じて保持する。
重要なのは lookup が、record bucket、raw support index、distinct clause index、compact incidence index の
定数回 hash lookup だけで終わることである。raw-link `Vec` binary search、full formula scan、
source reconstruction scanを置かない。

### 3.7 Raw audit reconstruction

claimed exact link `(record, raw support, clause)` の source は次から lossless に再構成する。

```text
exact_links[(support_group_id, entry_id)].Claimed(source_template)
    + support_group.coverage_root
    -> ClaimedProjectionProofSource
```

mapping は次で固定する。

```text
Original { producer } + root
    -> Original { coverage_root: root, producer }
DerivedUnary { result } + root
    -> DerivedUnary { coverage_root: root, result }
ReplayConstraint { result } + root
    -> ReplayConstraint { coverage_root: root, result }
ReplayEvidence + root
    -> ReplayEvidence { coverage_root: root }
```

raw audit iterator は `canonical_support_groups` と category adjacency、または明示的な exact incidence iteratorから
`(record, raw support, RecordProofClause) -> source` finite mapを遅延生成する。normal lowering で全 mapを作らない。

independent link は source を持たず、同じ incidence relation から列挙する。claimed/independent を別の
28.5M-entry storeへ戻さない。

metadata/support kind mismatch は corruption である。

- claimed support group + `Independent` value。
- independent support group + `Claimed(_)` value。
- claimed incidenceでmissing coverage root/template。

これらを sourceなし、別 producer、または `ReplayEvidence` defaultへ近似しない。existing raw auditと同じく
fail-hard/debug assertionまたは既存 `FailOpenIncomplete` 境界へ送る。

### 3.8 Support / attribution summaries

`normalized_support_keys`、`attributed_roots`、`flat_retained_attributed_roots` は evaluator/fail-open の
hot summary として bucket に保持する。これらは evaluation result cache ではなく、append-only accepted inputの鏡である。

新 exact link admission 時に次を行う。

- support group が新規なら normalized match key を一回 insertする。
- claimed link なら coverage root を `attributed_roots` へ insertする。
- incidence source template が `ReplayConstraint` 以外なら current `FlatRetained` 規則どおり
  `flat_retained_attributed_roots` へ insertする。
- exact duplicate は summary capacity/lenを変えない。

既存 `projection_formula_support_keys` / `projection_attributions` /
`flat_retained_projection_attributions` を別 global setとして残すか、bucket summaryへauthority cutoverするかは
PCLF-D の adapter境界で決める。完成形では同じ logical summaryを二重保持しない。

## 4. Admission transaction

### 4.1 Natural-event boundary

PCLF は既存 `try_prepare_projection_clause_admission` / `commit_projection_clause_admission` の境界を維持する。
異なる lower record、異なる replay admission、before/after evaluation を storage sharing のために一 batchへ混ぜない。

```text
caller event
    -> collect RecordProofClauseLinkAdmission delta
    -> before inclusion view
    -> prepare PCLF delta
    -> commit PCLF delta
    -> dependency edges for new clauses only
    -> after inclusion view
    -> existing publication policy
```

### 4.2 Prepared delta

意味上の plan は次を含む。

```rust
struct PreparedProjectionFormulaAdmission {
    record: BoundRecordId,
    accepted: Vec<AcceptedProjectionClauseAdmission>,

    new_entries: Vec<PreparedProjectionFormulaEntry>,
    new_support_groups: Vec<PreparedProjectionSupportGroup>,
    new_links:
        Vec<(
            ProjectionSupportGroupId,
            ProjectionFormulaEntryId,
            ProjectionIncidenceMetadata,
        )>,

    normalized_support_delta: Vec<ProjectionSupportMatchKey>,
    attribution_delta: Vec<UpperReplayClaimId>,
    flat_attribution_delta: Vec<UpperReplayClaimId>,
}
```

provisional ID は current arena len と plan-local ordinal から決めてよいが、同じ `&mut` transactionの間に
別 mutationを挟まない。prepared plan は別 record/storeへ再利用できない。

### 4.3 Prepare order

prepare は次の順序にする。

1. admission constructor invariant と claimed source/root consistency を検証する。
2. immutable pre-transaction bucket に対して raw support、exact clause、exact incidence を lookupする。
3. batch-local `(raw support, exact clause)` duplicate を compact provisional ID で除く。
4. exact duplicate の per-incidence source template/root が既存 value と一致することを fail-hard assertする。
5. new clause、new support group、new exact incidence、summary deltaを計算する。
6. accepted が空なら persistent storageを作らず `None` を返す。
7. 全 fallible validation を終えた後、entry/support/incidence/adjacency/summaryの capacityを preflightする。
8. capacity preflightが全て成功した場合だけ prepared planを返す。

prepare 中に current bucket の logical len/contentを変更しない。capacity reserve が途中まで成功して後続 reserve が
失敗した場合も、logical formula/link/summary は変わらない。allocation capacityまで完全 rollbackすることは
Rust container APIの契約ではないため、failed reservation testは logical partial commit の不存在を主 gateとする。

### 4.4 Commit order

commit は allocation/fallible validationを行わない。次の順で deltaだけを適用する。

1. new clause entries と `entry_by_clause`。
2. new support groups と `support_group_by_raw` / canonical support order。
3. compact exact incidence metadata。
4. category adjacency。
5. normalized support / attribution summaries。

commit後、`accepted` の `clause_inserted` だけが既存 dependency edge registrationへ流れる。
新 support incidenceは既存 clauseのdependency edgeを再登録しない。

各 step は debug/test buildで「insert予定が既存だった」「IDが別entryを指した」場合に fail-hard する。
release の既存 terminal-failure contract を弱めない。

### 4.5 Exact duplicate / batch duplicate / no-op

- persistent existing duplicate: source/root parityを確認して no-op。
- batch-local duplicate: first accepted occurrenceとmetadataが一致することを確認して no-op。
- accepted delta zero: bucket、entry、support group、incidence、summary、epoch、evaluationを変更しない。
- no-claim workload: claimed incidence metadata/attribution storageを作らない。
- independent-only workload: `Claimed` incidence value/attribution storageを作らない。

`PerformanceIndexAllocationCensus` は bucket map、entry/support arena、index、adjacency、summaryの len/capacity を測り、
accepted zeroで persistent growthがゼロであることを固定する。

temporary batch plan allocationは persistent census の対象外である。empty input と singleton exact duplicate の
total heap allocation zeroを別 allocator counterで確認する。arbitrary-size batch-local duplicate除去に必要な
temporary scratchまで persistent censusだけで「heap zero」と主張しない。この区別はGWCB §9と同じである。

### 4.6 Retraction

現 census と current writer audit では projection clause/link relation は append-only である。
PCLF-0時点で remover/retraction は見つかっていない。

実装中に formula entry、raw support occurrence、incidence source metadata、attributionを remove/reclassifyする production pathが
一件でも見つかった場合、append-only modelを前提に進めない。全 removerとepoch/invalidationを設計へ追加するまで
PCLF-B以降を停止する。

## 5. Consumer API と cutover contract

consumer が bucket fieldsへ直接依存しないよう、少なくとも次を境界にする。

```rust
fn projection_formula(
    &self,
    record: BoundRecordId,
) -> impl Iterator<Item = ProjectionClause>;

fn projection_clause_link_is_registered(
    &self,
    record: BoundRecordId,
    support: SchemeProjectionProofSupport,
    clause: RecordProofClause,
) -> bool;

fn projection_clause_is_registered(
    &self,
    record: BoundRecordId,
    clause: RecordProofClause,
) -> bool;

fn projection_support_match_is_registered(
    &self,
    record: BoundRecordId,
    key: ProjectionSupportMatchKey,
) -> bool;

fn claimed_projection_source(
    &self,
    record: BoundRecordId,
    support: SchemeProjectionProofSupport,
    clause: RecordProofClause,
) -> Result<Option<ClaimedProjectionProofSource>, ProofFailure>;

fn exact_projection_clause_links(
    &self,
    record: BoundRecordId,
) -> impl Iterator<Item = RecordProofClauseLinkAdmission>;
```

`exact_projection_clause_links` は oracle、debug census、明示的 audit/exportだけに使う。normal evaluator、admission、
GWCB decisive lookupから呼ばない。

### 5.1 Evaluator

`CpkProjectionEvaluator::eval_record_uncached` は canonical iteratorを一度歩き、現行どおり最初の exact included armで
短絡する。normalized support qualification は bucket summaryの O(1) membershipを使う。

次を byte-for-byte 不変にする。

- clause sequence。
- include/exclude/fail-open result。
- recursive premise evaluation順。
- first `IncludedExact` clause。
- round memo stateとcycle cut。

factored storageを毎 queryでexpanded `Vec`へcollectしてはならない。

### 5.2 GWCB decisive arm

evaluatorが選んだ claimed clauseについて、同じ iterator itemが持つ raw support、entry ID、recordから sourceを引く。
`support_group_by_raw` と `entry_by_clause` が作る exact ID pairで `exact_links` を一回引き、その incidence の
`Claimed(source_template)` と support group coverage rootから、現行 helperと同じ
`ClaimedProjectionProofSource` / `ClaimedProjectionProof` を作る。entry-global source、formula scan、別 audit scanを使わない。

required parity:

```text
legacy projection_claimed_link_audit lookup result
== PCLF exact incidence metadata + support-root reconstruction

legacy ClaimedProjectionProof
== PCLF ClaimedProjectionProof

legacy ProjectionEvidence
== PCLF ProjectionEvidence
```

same-root representative replacement、Standalone embedded support normalization、incidence-local ReplayConstraint result、
ReplayEvidence attributionを全て維持する。同じ clause entry の別 incidence が異なる source templateを持つcaseでも、
decisive raw supportが選ぶ exact pair の sourceだけを返す。

### 5.3 Audit / portable / logical consumers

raw exact relationを必要とするconsumerは factored iteratorから遅延列挙する。

- raw identityを `(record, raw support, exact RecordProofClause)` のまま返す。
- claimed sourceを lossless に返す。
- independent/claimed の disjoint unionを保つ。
- unordered finite mapを比較するconsumerは set/map parityを使う。
- canonical formula sequenceを比較するconsumerは §3.5 の sequenceを使う。
- portable outputに順序が現れる場合は現行 canonical orderへnormalizeする。

production normal loweringで全28.5M linkを `Vec` / `HashMap`へ再展開しない。

## 6. 必須 invariants

1. **Exact link identity**
   - logical key `(record, raw SchemeProjectionProofSupport, exact RecordProofClause)` を変えない。
   - raw supportをcoverage rootへ正規化してexact dedupしない。

2. **Exact clause identity**
   - `Standalone` embedded support、DerivedUnary carrier/premise、ReplayConjunction carrier/lower/upperを落とさない。
   - exact carrierをsemantic premise pairへ粗化しない。

3. **Expanded relation equivalence**
   - 到達可能な任意のevent境界で、
     ```text
     expanded(PCLF bucket) == legacy exact raw link finite map
     ```
     が成立する。

4. **Formula sequence equivalence**
   - `canonical_clauses().collect::<Vec<_>>() == legacy projection_formulas[record]`。
   - set/countだけの比較で済ませない。

5. **Record OR / premise semantics**
   - record OR、Standalone support、DerivedUnary premise、ReplayConjunction ANDを変えない。

6. **GWCB decisive-arm equivalence**
   - canonical-first decisive clause、`ProjectionEvidence`、`ClaimedProjectionProof`がbyte-for-byte一致する。
   - non-decisive armを追加・削除・並べ替えしてdecision provenanceを変えない。

7. **Raw / normalized identity separation**
   - exact incidenceはraw supportで保持する。
   - qualifying summary/certificate semantic keyだけをcoverage rootへ正規化する。

8. **Source metadata exactness**
   - claimed source kind、producer/result、coverage rootを失わない。
   - lineage/endpoint shapeからsourceを推測しない。

9. **Per-incidence source exactness**
   - source-template uniformityをclause entryへ要求しない。
   - 各 claimed `(record, raw support, exact RecordProofClause)` incidence は、自身のsource kindとproducer/resultを保持する。
   - 同じ clause entry の別 incidence が `ReplayConstraint` / `ReplayEvidence` または異なる`result`を持てる。
   - exact duplicateだけは同じ source metadataを再提示しなければならず、不一致はfail-hardする。

10. **Claimed/independent coexistence**
    - 同じ exact clause entryへclaimed/independent incidenceが共存できる。
    - independent occurrenceをclaimedへreclassifyせず、両logical linkを保持する。

11. **Same-root representative preservation**
    - raw representative claimが異なるexact linkを失わない。
    - normalized support/certificate summaryは現行どおりcoverage rootでcollapseする。

12. **Attribution equivalence**
    - any-attributed / flat-retained-attributed root集合がlegacy二setと一致する。
    - ReplayConstraintとReplayEvidenceを混同しない。

13. **Distinct-clause exactly-once**
    -一 clause entryにつきdependency edgeを高々一回登録する。
    - support incidence追加でedgeを増やさない。

14. **Canonical order isolation**
    - HashMap/HashSet iteration、arena ID、allocation address、input permutationをformula orderへ漏らさない。

15. **Insertion-order equivalence**
    - 現行がcanonicalに同値とするadmission順序でformula、exact relation、GWCB evidence、scheme結果が一致する。
    - source-conflict linkはouter raw supportが異なる別incidenceとして両方を保持し、順序によるentry-global winnerを作らない。
    - 同じexact raw identityが異なるmetadataを再提示する入力は合法なpermutationではなく、全順序でfail-hardする。

16. **Admission-time completeness**
    - accepted linkは同じevent内でentry、incidence、summary、dependency consumerへ到達する。
    - repair/flush/fixpointへ依存しない。

17. **Transactional logical atomicity**
    - reservation/validation failureでformulaとindex/audit/summaryが片肺commitされない。

18. **Exact no-op**
    - accepted zeroならpersistent len/capacity、evaluation、dependency edge、epoch/publicationを増やさない。

19. **No-claim / independent-only isolation**
    - no-claimはclaimed incidence source/attribution storageを作らない。
    - independent-onlyは`Claimed` incidence valueを作らない。

20. **Append-only**
    - entry、support group、accepted incidence、そのincidence source metadataはappend-only/monotonicである。
    - retractionが見つかった時点で設計へ戻る。

21. **No full-bucket rebuild**
    - admission deltaのためにrecordの全exact link formula/support setをclone/re-sortしない。

22. **No production full expansion**
    - evaluator、admission、GWCB lookup、epoch publicationはexpanded exact link collectionを作らない。

23. **No permanent evaluation cache**
    - bucket/indexはappend-only proof inputの表現であり、include/projectability result cacheではない。

24. **Corruption / fail-hard preservation**
    - missing source/template/incidenceを別 producerやindependent reasonへ近似しない。
    - existing debug assertion / terminal failure / fail-open completenessを弱めない。

25. **Consumer boundary**
    - production consumerはbucket fieldsを直接走査せず、§5 APIを使う。

26. **Logical vs physical census separation**
    - logical exact link数、distinct clause/support数、compact incidence/index bytesを別々に報告する。
    - compact physical reference数をlogical link削減と誤記しない。

## 7. Oracle と regression specification

### 7.1 Linear reconstruction oracle

legacy storageをauthorityとして残すshadow期間中、event境界で次を比較する。

1. expanded `Vec<ProjectionClause>` sequence。
2. claimed raw finite map `identity -> source`。
3. independent raw exact set。
4. distinct clause set。
5. normalized formula support set。
6. any/flat attribution set。
7. `AcceptedProjectionClauseAdmission::clause_inserted` sequence。
8. dependency edge set。
9. evaluator include/exclude/fail-open とdecisive clause。
10. `ClaimedProjectionProof` / `ProjectionEvidence`。

fixture終了時のcount比較だけでなく、test/debug buildでは各natural admission event後に比較できるhelperを置く。
std workloadで毎event full expansionは行わず、targeted fixtureとsampled censusを分ける。

### 7.2 Required fixtures

- exact claimed duplicate。
- exact independent duplicate。
- batch-local duplicate。
- new support / existing clause。
- existing support / new clause。
- new support / new clause。
- independent-first / claimed-later。
- claimed-first / independent-later。
- same-root different representative claims。
- Standalone embedded claimed support normalization。
- DerivedUnary structural / reduction-route。
- ReplayConjunction ReplayConstraint / ReplayEvidence。
-同じ record / `ReplayConjunction` clauseへ、異なる claimed support incidenceから
  `ReplayConstraint { result }` と `ReplayEvidence` が到達するcase。
-同じ record / exact clauseへ、異なる claimed support incidenceから異なる `result` templateが到達するcase
  （ReplayConjunctionとDerivedUnaryの両variant）。
-上記source-conflict fixtureの全admission-order permutation。formula sequence、raw audit finite map、
  decisive sourceが各legacy順序と一致し、entry-global first-winsへcollapseしないこと。
- canonical duplicate / evidence-only / promotion。
- one exact clauseへの多数support（census max 97を超える合成caseも含む）。
-一supportへの複数category/clause。
- insertion-order permutation。
- failed reservation before/after各reserve point。
- exact no-op persistent allocation census。
- no-claim / independent-only allocation census。
- GWCB decisive arm、mixed-bound、dual-reach、portable/logical parity controls。
- DCP/MPC/DPN/URR/RCPF pinned controls。

### 7.3 Canonical-order oracle

local edge setやunordered audit mapと違い、formulaはsequence contractである。

- category境界。
- raw claimed/independent support order。
- carrier/premise order。
- attribution rank。
- byte-equal ProjectionClause multiplicity。

を含むfixtureを作る。PCLF iteratorとlegacy Vecのfirst mismatchを、record、index、raw support、entry ID、
reconstructed clauseまで表示する。

### 7.4 Allocation census

`PerformanceIndexAllocationCensus`へ次を追加する。

- bucket map len/capacity。
- entry arena len/capacity。
- distinct-clause index len/capacity。
- support-group arena/index len/capacity。
- compact exact incidence index len/capacity。
- compact exact incidence metadataのvariant別countとvalue `size_of`。
- category adjacency total len/capacity。
- normalized support / attribution summary len/capacity。

legacy dual-write期間はlegacy/factoredを別々に数える。authority cutover後は、raw flat storageがゼロであることを
明示する。temporary prepare allocationは別 allocator measurementにする。

## 8. 実装スライス

各sliceは独立commit・独立rollback単位にする。前sliceのgateを閉じるまで次へ進まない。

### PCLF-0: writer / volume / factorability census

状態: **実施済み（2026-08-11）**。

変更:

- read-only writer/storage census。
- temporary counterによるfresh volume/duplicate測定。
- exhaustive source-template factorability測定。
- membership feasibility probe。

結果:

- §1.2〜1.4 の数値を取得。
- RCPF-shaped factorizationを支持。
- std workloadでsource-template conflict zero。ただしrev.2 adversarial reviewでこれは一般不変条件でないと確定。
- raw-link formula binary searchを棄却。
- instrumentationを除去し、working treeをcleanへ戻した。

Gate:

- logical exact relation、writer、storage six facesを列挙できた。
- distinct clause factorizationがworkload上成立した。source templateはper-incidenceに保持する必要がある。
- compact distinct-clause hash indexを選ぶ根拠が得られた。

### PCLF-A: test-only oracle と型境界

変更:

- §3 のID/entry/support/bucket型を追加するがproduction authorityにしない。
- legacy six facesを一つのcanonical test read modelへ展開するhelperを追加する。
- §7.1〜7.3 fixtureを追加する。
- 全writer constructorについてper-incidence source mappingを静的/fixtureで確認する。
- `set_projection_formula_for_test` と `cpk_gap_1_five_lineages...` のdirect `get_mut`を、
  exact admission/source metadataを明示するtest-only fixture APIへ移す。
- retraction/remover censusを再確認する。

Gate:

- production behavior/epoch/allocation不変。
- legacy read modelが既存fixtureと自明に一致する。
- source-conflict fixtureを含め、各exact incidenceのsourceがlegacy raw auditと一致する。
- legacy formula/support-keyへのtest-only bypass writer zero。
- remover/retractionなし。

Stop:

-一exact incidenceのsourceをcompact metadataでlosslessに表せないcase、または未列挙removerが一件でもあれば
  PCLF-Bへ進まない。

### PCLF-B: shadow factored bucket

変更:

- clause admission prepare/commitからshadow `ProjectionFormulaStore`へdual-writeする。
- consumerはlegacyのみを読む。
- event-boundary linear oracleとallocation censusを接続する。
- support/category adjacencyとper-incidence metadataのsize/movement分布を測る。

Gate:

- §7.1の全face一致。
- formula sequenceとGWCB source reconstruction一致。
- no-claim/exact-no-op persistent growth zero。
- failed reservationでlegacy/factored logical stateが部分commitされない。
- shadow bytes、adjacency movement、peak RSSが安全範囲内。

Rollback:

- shadow field/writerだけを削除。legacy behaviorへ影響なし。

### PCLF-C: membership / clause authority cutover

変更:

- `projection_clause_link_is_registered` をbucketのsupport/clause/incidence indexへ切り替える。
- distinct-clause判定を `entry_by_clause` へ切り替える。
- `projection_clause_keys` はtest oracleへ退役する。
- caller/writer二重checkは同じauthority queryへ統合できる場合だけ別commitで除く。

Gate:

- legacy/factored membership全件一致。
- accepted/existing/batch-local outcome列一致。
- `clause_inserted` とdependency edge集合一致。
- 70.6M attempt相当の合成censusでraw-link binary search/full scan zero。
- caller/writer recheck除去の有無を別々にprofileし、非dominant変更をfactorization効果へ混ぜない。

Rollback:

- query adapterをlegacyへ戻せる。shadow bucketは残してよい。

### PCLF-D: canonical formula / evaluator / GWCB cutover

変更:

- evaluator formula sourceを`canonical_clauses()`へ切り替える。
- normalized support/attribution queryをbucket summaryへ切り替える。
- GWCB decisive claimed source lookupをexact incidence metadata + support rootへ切り替える。
- `logical_proof_snapshot.rs` の `projection_formula_for_record` readerを§5 iterator APIへ切り替え、
  canonical snapshot sequence/hash parityを確認する。
- legacy formula/auditはoracleとして残す。

Gate:

- formula sequence byte equality。
- evaluator result、short-circuit index、cycle/fail-open parity。
- `ProjectionEvidence` / `ClaimedProjectionProof` byte equality。
- GWCB motivating/control、MPC/DPN/RCPF tests green。
- production queryからfull expansion zero。
- cold std loweringでPCLF-C比のunexplained regressionなし。

Rollback:

- evaluator/GWCB adapterをlegacyへ戻す。membership cutoverとは独立にrevert可能にする。

### PCLF-E: expanded legacy storage retirement

変更:

- production `projection_formulas` expanded Vecを撤去する。
- production `projection_claimed_link_audit` raw full-key mapを撤去する。
- `independent_projection_clause_link_keys` を撤去する。
- `projection_clause_keys` を撤去する。
- support/attribution global mirrorをbucket summaryへ統合し、二重authorityをなくす。
- production/testを再 censusし、legacy fieldsへのdirect reader/writerがzeroであることを確認する。
- legacy expanded representationはtest-only reconstruction oracleに限定する。

Gate:

- production hot pathのexpanded full-link storage/collection zero。
- logical counts `28,526,006 / 847,858` と全oracle一致。
- §9のstructural/numeric performance gate。
- peak RSS安全閾値内、swap増加なし。
- portable/logical/diagnostic output zero-diff。

Rollback:

- PCLF-Dとは別commitにする。問題があればEだけを戻し、dual-write legacy authorityを復元できる形にする。

### PCLF-F: integration / closeout

変更:

- targeted CPK/RCPF/MPC/DPN/GWCB suite。
- safety-scoped infer suite（documented skip list、`--test-threads=4`、RSS 18 GiB hard kill）。
- cold/warm std reproduction、representative application corpus。
- logical/physical count、proof-write self time、RSS、no-op allocation測定。
- temporary trace/counter除去。

Gate:

- intentional known-red以外のnew failure zero。
- §9 gateを満たすか、残差を新profileの具体的functionへ帰属できる。
- source diffがPCLF cause boundaryだけに限定される。
- working tree/temporary artifact clean。

## 9. 性能・メモリ gate

### 9.1 Baseline discipline

現在の参考値は `0e208ab4` の cold reproduction で次である。

| 指標 | 参考値 |
|---|---:|
| `std::text::parse` | 77.9s |
| full command | 127.97s |
| peak RSS | 9.33 GiB |

PCLF-0 instrumentation runの `80.902s parse / 125.912s lower_loaded_files / 141.85s process wall` は、
終了時に28.5M audit全走査とmicrobenchmarkを実行した測定用runでありlanding baselineに使わない。

PCLF-B着手前にclean current HEADでcold runを最低二回行い、同じcache/build/RSS monitor条件のmedianを
正式baselineにする。上の単一run値から差がある場合、数値を都合よく選ばず両方を報告する。

### 9.2 Structural gate

PCLF-Eで次を全て満たす。

1. full `ProjectionClause` をlogical link一件ごとにpersistent Vec保存しない。
2. full `(record, raw support, RecordProofClause)` をclaimed link一件ごとのHashMap keyにしない。
3. claimed incidenceに必要なsource kind/producer/resultはcompact valueとして保持するが、full raw key、coverage root、
   clause bodyと一体化したparallel audit entryとして保存しない。
4. exact link membershipはcompact record-local ID indexでexpected O(1)。
5. distinct clause lookupは847,858-entry scaleに比例し、28.5M raw link scaleに比例しない。
6. admissionごとのfull formula/support-set clone/re-sortを行わない。
7. evaluator/GWCB/admissionのfull expansion countはzero。
8. logical incidenceとcanonical adjacencyはcompact ID/referenceを一件ごとに保持し、incidence valueは
   lossless source metadataの最小payloadに限定する。
9. no-claim/exact-no-opのpersistent allocation growthはzero。
10. per-incidence source-template/coverage-root reconstructionのglobal scanはzero。

### 9.3 Wall time target

直前profileではprojection-clause admission clusterがparse self-time sampleの約35%だった。sampling比率を
厳密なself-time秒数とは扱わない。全35%を消せたと仮定するAmdahl上限は

```text
77.9s × 0.65 ≈ 50.6s
```

だが、logical 28.5M incidence insertionとnecessary hash workは残るため、50.6sをlanding promiseにしない。

段階的目標:

- PCLF-B shadow:
  - correctness測定用。wall time改善を要求しない。
  - baseline比15%超の回帰またはRSS 18 GiB接近時はfull workload dual-writeを止め、targeted fixtureへ戻る。
- PCLF-C/D:
  - 各authority cutover後にfresh profileを取り、projection-clause clusterが減ることを確認する。
  - unrelated hot path改善をPCLF成果へ含めない。
- PCLF-E minimum success:
  - clean baseline median比でparse 10%以上改善。
  - full command 6%以上改善。
  - current参考値なら概ね `parse <= 70.1s`、`full <= 120.3s`。
  - exact output zero-diff、RSS非増加を同時に満たす。
- project target（推定）:
  - parse 60〜65s。
  - full command 105〜115s。
- stretch target（保証しない）:
  - session初期の約53.239s parse圏への接近。

minimum gateを満たさなくてもstructural bytes/operationsが大幅に減った場合、即revertとは限らない。
ただし「性能問題を閉じた」と主張せず、新profileで残るcostを帰属し、次の設計判断へ戻る。

### 9.4 Memory target

PCLF-0は新backendの実byte数を測っていない。従って「何GiB削減」とは現時点で断定しない。
rev.2 の per-incidence source valueと、未測定のdistinct support-group count / category `Vec` overheadを含む
完成形bytesは **要検証** である。この確認はimplementation shapeを必要とするため、設計承認前の既確認事項ではなく
PCLF-B shadow gateとする。

Gate:

- PCLF-Bでlegacy/factoredのmap/bucket/arena len/capacityと`size_of`を別々に測る。
- PCLF-Eでprojection clause/link persistent bytesをlegacy推定比50%未満にすることをproject targetとする（推定、要検証）。
- peak RSSは最低でも9.33 GiB baselineを超えない。
- project targetはpeak RSS 20%以上削減（約7.46 GiB以下、推定）。
- dual-write oracleをproduction peak RSS測定へ混ぜない。
- swapを増やさない。
- temporary full reconstructionはtest/debug/measurement後に破棄する。

50% physical-byte targetがtype layout/capacity overheadで不可能と判明した場合、数値だけを緩和せず、
incidence/index/adjacencyの二重compact projectionが妥当か設計レビューへ戻る。

### 9.5 Operation/count target

logical countは変えない。

```text
logical exact links = 28,526,006
distinct clauses    =    847,858
```

完成形のproduction storageは概ね次に比例する。

```text
full clause entries:        O(847,858)
raw support groups:         O(distinct record-local supports)  -- PCLF-Bで実測
compact incidence keys:     O(28,526,006)
compact source values:      O(claimed exact incidences)
compact canonical refs:     O(28,526,006)
```

full raw-link hash keyとfull ProjectionClause entryはproductionでzeroにする。claimed sourceの意味payload自体は
削除せず、coverage rootをsupport groupへfactorしたsmall incidence valueとして残す。
caller/writer二重membershipは可能なら一回へ減らすが、この約28.5M check削減をPCLFの主成果として扱わない。

## 10. 棄却案

### 10.1 Raw-link Vec の binary search

棄却する。

- measured 1,557.711 ns/op、flat hash 16.168 ns/op、約96.345x。
- p95 1,759 / max 4,700のraw-link bucketを70.6M attemptで検索する。
- storage factorizationをせず、full ProjectionClause payloadを残す。

distinct clauseの小さいVecをbackend内部で使うことまで禁じる結果ではないが、admission authorityは
record-local distinct-clause hash indexとcompact incidence indexに置く。

### 10.2 Caller/writer duplicate checkだけを除く

単独解として棄却する。

- writer recheck 28,513,660件は実在する。
- isolated experimentでdominant wall timeは動かなかった。
- 28.5M expanded formula/audit storageを一件も減らさない。

PCLF-Cのauthority整理として除去する余地はあるが、factorizationの代替ではない。

### 10.3 Exact clause/carrier identity の粗化

棄却する。

- RecordProofClause field、Replay carrier rule/pivot/lower/upper、Derived premiseを落とせない。
- CDM/RCPF/MPC/DPNのexact identityを破る。
- dependency edge、portable provenance、GWCB certificateを誤る。

### 10.4 Coverage rootだけへのlink dedup

棄却する。

- raw representative claimを含むexact audit identityを失う。
- same-root representative replacementのraw parityを壊す。
- normalized summaryとraw relationを混同する。

### 10.5 `projection_formula_support_keys` だけをauthorityにする

棄却する。

- supportがformulaに一件あることしか答えない。
-どのexact clause/carrier/premiseへ帰属するか答えられない。
- GWCB decisive sourceとdependency edge exactly-onceを再構成できない。

### 10.6 Per-query reconstruction / permanent evaluation cache

棄却する。

- per-query formula/audit scanはCPK-9/GWCBで実測済みの回帰を再導入する。
- permanent evaluation cacheはliveness/proof/epoch全mutationのinvalidationを必要とする。
- input relationのphysical factorizationを先に行うべきである。

### 10.7 Delayed flush / global repair

棄却する。

- admission時完全性を破る。
- stale read窓とflush順序を導入する。
- natural-event before/after publicationと両立しない。

### 10.8 Entry-global source default + sparse override

棄却する。

- rev.2 adversarial reviewでsource-template uniformityは一般不変条件でないと確定した。
- default/overrideは一部incidenceを暗黙にentry-global first-winsへ依存させ、raw audit parityを壊しやすい。
- override頻度zeroというstd workload観測を、reachable state全体のstorage contractへ昇格できない。
- source metadataを全exact incidenceで同じ明示的valueとして扱う方が、lookup、atomicity、oracleを単純に保てる。

### 10.9 Flat raw hashを残してformulaだけfactorizeする

移行sliceとしては許すが完成形として棄却する。

- `projection_claimed_link_audit`だけで28,516,968 full raw keys/source valuesが残る。
- GWCB lookupは速いが、storage amplificationの半分を温存する。
- exact sourceはcompact incidence template + support rootからlosslessに再構成できるrev.2 modelを使わない。

## 11. Stop / rollback conditions

### 11.1 Stop conditions

次のいずれかが判明した時点でimplementationを止め、Claude/userの設計レビューへ戻る。

1. 合法なwriter pathのsource kind/producer/resultを、exact incidenceのcompact value + support-group rootから
   losslessに再構成できない。
2. source coverage rootがraw support groupからadmission-timeに一意に凍結できない。
3. projection clause/linkのretraction、reclassification、removerがあり、全mutation pathを列挙できない。
4. expanded exact raw finite mapがlegacyと一致しない。
5. canonical formula sequenceがlegacy Vecと一致しない。
6. GWCB decisive `ProjectionClause` / `ClaimedProjectionProof` / `ProjectionEvidence`が一致しない。
7. canonical orderのためhash iteration、arena ID、allocation address、global sort/full reconstructionが必要になる。
8. exact link O(1) membershipのためfull raw identityを28.5M件そのまま再保存する必要がある。
9. incidence metadata index + canonical adjacencyがlegacy physical bytesの50%未満へ収まる見込みを
   PCLF-Bで示せない。
10. compact adjacency insertionの累積movementが新しいdominant O(record links) costになる。
11. failed reservationでlegacy/factoredまたはbucket内facesがlogical partial commitされる。
12. exact no-op/no-claimでpersistent capacity/lenが増える。
13. accepted linkを同event内で全consumerへ反映するためdelayed flush/repair/fixpointが必要になる。
14. dependency edge exactly-onceを保てない。
15. fail-open/corruptionを別source/producerへ近似しなければconfirmed pathが動かない。
16. DCP/MPC/DPN/RCPF/GWCB/URRのpinned contractにexact cause不明のshiftが出る。
17. semantic output、diagnostic text、portable/logical topologyの期待値変更が必要になる。
18. production normal loweringでexact full expansionが必要になる。
19. PCLF-E後のwall/RSSが§9 minimum gateを外れ、残差を具体的costへ帰属できない。
20. 各authority cutover/legacy retirementを独立rollbackできない。

### 11.2 Rollback units

- PCLF-Aのoracle/fixtureは、正しい観測である限り後続sliceを戻しても保持する。
- PCLF-B shadow storeは一sliceで削除可能にする。legacy authorityへ影響させない。
- PCLF-C membership cutoverとcaller/writer recheck整理を別commitにする。
- PCLF-D evaluator/GWCB cutoverはmembership cutoverから独立してlegacy adapterへ戻せるようにする。
- PCLF-E legacy retirementはD以前と別commitにし、performance/correctness問題時にexpanded authorityを復元できるようにする。
- rollbackでexact key、canonical order、GWCB decisive contractを旧buggy/coarser semanticsへ戻さない。

## 12. Claude 査読時の必須確認事項

Claude (Sonnet 5) は本書を確定する前に、少なくとも次をcurrent codeへ再照合する。

1. §1.1のsix-face writer/remover censusが全production pathを覆い、二つのtest-only bypass writerが
   PCLF-A migration対象になっているか。
2. `ProjectionClause::canonical_cmp` を§3.5のcategory/support/entry traversalでsequence-equivalentに再現できるか。
3. `RecordProofClause::Standalone` embedded supportとouter supportの関係に、entry factorizationを破る合法caseがないか。
4. 全writer constructorのsource kind/producer/resultがper-incidence metadataへtotalに写り、同じ clause の
   source-conflict fixtureでもraw audit finite mapをlosslessに再構成できるか。
5. support groupのadmission-time coverage rootがclaim movement/livenessと独立なimmutable factか。
6. **PCLF-B gate（設計承認前の既確認事項ではない）**: per-incidence source value、support-group count、
   `Vec`/hash capacityを含むcompact index + canonical adjacencyの実bytesがlegacyより十分小さいか。
7. GWCB decisive source reconstructionがexact incidence metadataを選び、現行raw audit lookupと
   O(1)/byte-equivalentか。
8. attribution summariesをbucketへ移したとき、direct consumer/reverse queryを見落としていないか。
9. capacity preflight/commit順が現行terminal failureとnatural-event atomicityを保つか。
10. PCLF-Eのlegacy field撤去前に、`logical_proof_snapshot.rs`を含む全direct readerとtest-only bypass writerが
    §5/test fixture APIへ移っているか。
11. §9のnumeric targetがfresh clean baselineに対して現実的か。
12. safety-scoped suiteと18 GiB RSS hard kill protocolがcloseout planに明記されているか。

項目1〜5、7〜9は設計確定前にcurrent codeへ照合する。項目6はshadow representationなしには実測できないため、
未測定であることを明示したうえでPCLF-Bのmandatory stop gateとする。項目10〜12は後続slice/closeout planの
完全性を査読し、該当gateを満たす前にlegacy retirementやcloseoutへ進まない。一つでもこの分類どおりに
確認・割当できなければ「査読・確定」とせず、該当sliceまたはrepresentationを改訂する。

---

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定

承認状態: **ユーザ承認済み**。本書は `CLAUDE.md` の設計優先順位における正本である。
PCLF-A 以降の実装は、本書の invariant・stop condition・スライス順序に従って着手できる。
