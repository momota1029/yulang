# qualified-parent replay occurrence relation の factorization（QORF rev.3）

日付: 2026-08-12（Claude 査読・確定: 2026-08-12、ユーザ承認: 2026-08-12）

状態: **ユーザ承認済み（正本）。QORF-A以降の実装に着手可**

基準 commit: `acdd4246`。行番号は固定せず、実装時には型名・関数名を正本として再確認する。

本書は、Fable 5 が一時的に利用できない場合の代替起案手続きに基づく設計文書である。
Codex `gpt-5.6-sol`（xhigh）が調査結果から本文を起案し、Claude (Sonnet 5) がcurrent codeとの整合性、
RCPF/PCLFとの非矛盾、transaction/error precedence、reader topologyを独立査読・確定した後、ユーザ承認を受けた。

略称として、本設計を **QORF（Qualified-parent Occurrence-Relation Factorization）** と呼ぶ。

draft rev.2は、最初の独立adversarial reviewで判明した二つのauthority不足を修正する。第一に、evaluator用の
一occurrence一armだけでは、`merge_structural_claim_parents`と`register_constraint_upper_replay_claims`が必要とする
「各`(result, root)`のfirst canonical parent」を表せず、clause-link bootstrapが必要とする全
`(root, exact carrier)` associationも列挙できない。rev.2はdistinct `(result, root)` scaleのcanonical root-winner
projectionと、exact-output consumer専用のstreaming root/carrier association cursorを分離する。第二に、parent accepted zeroでも
`record_replay_admission`が全dispositionのeventを記録し、accepted parent deltaはnew/late occurrenceを問わずgeneric
`ProofOccurrence`を追加する現行contractを設計へ含める。rev.3でeventはinner transaction外、generic occurrenceはinner側と
境界を精密化した。duplicate metadataはfail-hardではなくsilent first-winsである。

また、本書でいうcurrent replay authorityを、既に撤去済みの旧RCPF `ReplayOccurrenceStore` / attachment batchと区別する。
current codeに残るのは`ProofOccurrenceStore::replay_finite_map`、`replay_finite_map_index`、
`replay_indices_by_result`、`replay_admissions`から成る**CPK replay finite-map ledger**である。本書は以後この名称を使う。

draft rev.3は、第二回adversarial reviewで判明したfailure/event境界をcurrent codeどおりに修正する。
`register_cpk_replay_claim_parents`がqualified-parent preparation failureをterminal failureへ記録してreturnした後も、外側の
`apply_cpk_bound_replay_actions`は`record_replay_admission`を必ず呼ぶ。従ってreplay event appendはparent/side/arm/root-winnerの
all-or-nothing transactionには含めず、その成否に関係なく後で一件記録するouter action contractとする。
new occurrenceの`first_event`はappend前の`replay_admissions.len()`、すなわち直後にappendされるeventのzero-based indexである。
また、root-winner更新を全variant共通のqualified-parent admission planへ置き、structural/reduction-routeによるlater canonical
winner replacementをnon-replay pathでも同じatomicityで扱う。heapを使うexact/association cursorはfallible constructorで
全capacityを確保し、構築後のiterationをallocation-freeにする。

## 0. 決定要約

`std::text::parse` workloadのqualified-parent relationは、次の二つにほぼ完全に分かれる。

```text
replay qualified parents:              50,390,357
structural / reduction-route parents:      30,256
```

replay側50,390,357件は、current CPK replay finite-map ledgerがproductionで保持する865,571 replay occurrenceの
lower/upper parent relationと
**全件exact parity**を持つ。2026-08-12のQORF-0 censusでは、次のtupleを全件比較し、missing、extra、field mismatch、
duplicate occurrence entryはいずれもzeroだった。

```text
(result, exact replay derivation, side, coverage root,
 representative claim, lineage)
```

現行qualified-parent storageは、同じrelationをさらに次の二faceへ物理展開する。

1. global `qualified_parent_keys` hash set。`QualifiedParentKey`は28 bytes。
2. result-local canonical `ExactQualifiedParent` Vec。entryは28 bytes。

両faceとfirst-source summaryを合わせたcapacity込みproxyは3.32 GiBである。このうち、first-source summaryを
残したままreplay full-key/full-entry faceを退役させられる部分は3.266 GiBである。一方、current CPK replay finite-map ledgerの
capacity込みproxy 0.999 GiBは、exact replay provenance、first witness、logical snapshot、carrier validationに
既に必要なsunk costであり、QORFのためだけに新設するstorageではない。

QORFは次を完成形とする。

1. current CPK replay finite-map ledgerを、replay qualified-parentのexact identity/source authorityへ昇格する。
2. occurrenceのlower/upper parent payloadは、first-winsで確定した
   `(coverage_root -> representative claim, lineage)` をlosslessに保持する。
3. exact `(occurrence, side, root)` membershipは、side-localな最大128件のsorted chunk AVLで答える。
   global 50.39M-entry qualified-parent hashを別名で再作成しない。
4. evaluator向けにはresult-localな**canonical replay arm index**を置く。一occurrenceにつきcompact IDを一件だけ保持し、
   legacy canonical exact-parent列でそのoccurrenceが最初に現れるkey順に並べる。
5. materialization向けにはdistinct `(result, coverage root)`ごとに、existing comparatorで最小のexact parentを指す
   **canonical root-winner projection**を一件だけ持つ。historical first-source/first-witnessとは別winnerである。
6. clause-link bootstrapは全`(root, exact carrier)` associationを必要とするため、finite-map ledgerからside重複を除いて
   canonical順に流す専用streaming cursorを使う。このlower-bound traversalをpersistent/eager full expansionへ変えない。
7. canonical arm indexは非empty result bucketだけを持ち、chunked AVLと明示cursorで走査する。
   evaluatorは50.39M exact parentsを展開せず、occurrenceを一回ずつ評価する。
8. structural/reduction-route 30,256件は現行exact flat storeを小さいnon-replay storeとして残す。
   evaluatorはcanonical replay arm cursorとnon-replay canonical cursorを明示two-way mergeする。
9. exact 50.39M件のcanonical列挙が本当に必要なoracle/exportだけは、side-local sorted cursorを明示k-way mergeする。
   normal evaluator、admission、count、first-source queryからこのfull-value iteratorを呼ばない。
10. `qualified_parent_count`、first-source、first replay witnessなど、現在O(1)またはfirst-winsで確定済みのsummaryは
   relationからquery-time再導出せず維持する。
11. current finite-map ledgerのlogical occurrence identity、event-time snapshot、representative/first-witness first-wins、
   `replay_admissions` / `first_event` semanticsは変更しない。旧RCPF attachment batchの復活は行わない。
12. replay event appendはcurrent codeどおりinner admission成功/失敗の外に置き、必ず一件記録する。inner transactionは
    qualified-parent、occurrence parent delta、generic proof occurrence、canonical arm/root-winner update、summary、
    small non-replay deltaをpreflightし、commit中のfallible allocationとpartial publicationを禁止する。

この設計は、同じlogical relationを二つのproduction authorityへ展開している問題をRCPF-shapedに解消する。
ただし、gap A（exact membership）にはside-local chunked search tree、gap B（consumerごとに異なるcanonical order
projection）にはevaluator arm、distinct-root winner、exact-output association cursorを使い分ける。これらを一つのunordered hashや
一occurrence一armへ押し込めない。

## 1. 問題と実測根拠

### 1.1 現行qualified-parent storage

current `ProofOccurrenceStore`のqualified-parent側は、概念上次を持つ。

| face | logical role | physical shape |
|---|---|---|
| `qualified_parent_keys` | exact duplicate/membership | global `FxHashSet<QualifiedParentKey>` |
| `qualified_parents_by_result` | canonical result-local read | `result -> Vec<ExactQualifiedParent>` |
| first-source summary | result/rootの代表source | first-wins map |

`QualifiedParentKey`と`ExactQualifiedParent`はいずれも28 bytesである。replay parent一件は、result、exact
`BinaryReplayDerivation`、Lower/Upper side、coverage root、representative parent claim、lineageを意味上保持する。
global key faceはmembership localityを、result-local Vecはcanonical read orderを提供するため、同じ50.39M relationを
別々のfull entryとして保存する。

prepare/commitの主要な仕事は次である。

1. input keyのexact membership判定。
2. accepted keyのglobal hash insertion。
3. result-local accepted deltaのcanonical sort。
4. 既存canonical bucketとのmerge。
5. first-source first-wins summaryの更新。

qualified-parent canonical merge自体は既に、既存bucket全体の反復`sort_unstable_by`からsorted delta mergeへ改善済みである。
それでもaccepted volumeが50.42M件あるため、full key hash writeとfull exact-parent canonical payloadの維持が大きい。

### 1.2 Profiling / admission census

frame-pointer付きreleaseのcold `std::text::parse` profileでは、qualified-parent key insertion clusterがparse self-timeの
約25〜31%を占めた。sampling比率を厳密な秒数とは扱わないが、残存hot clusterとして十分に大きい。

| 項目 | 実測値 |
|---|---:|
| input qualified parents | 50,515,574 |
| accepted | 50,420,613 |
| duplicate / rejected | 94,961 |
| accepted ratio | 99.812% |

acceptedの99.812%はgenuine new factsである。従ってduplicate fast-path、hash algorithm差し替え、caller-side no-op skipだけで
このclusterを消せない。cost sourceは、主として次の二つだった。

- 50M scaleのscattered hash probe/write locality。
- result-local canonical Vecへfull 28-byte entryを維持するmerge/memory bandwidth。

under-reservationが主因ではない。first-source temporary structuresの過剰reserveは別のbounded fixとして既に分離され、
QORFの3.266 GiB duplicationを解消しない。

### 1.3 QORF-0 exact parity census

QORF-0は、全accepted replay qualified parentとcurrent CPK finite-map parentをexhaustiveに照合した。

| 項目 | 実測値 |
|---|---:|
| qualified replay entries | 50,390,357 |
| CPK finite-map parent entries | 50,390,357 |
| qualified側missing | 0 |
| occurrence側extra | 0 |
| exact field mismatch | 0 |
| lineage mismatch | 0 |
| side mismatch | 0 |
| duplicate occurrence entry | 0 |

比較identityは次である。

```text
result
+ exact BinaryReplayDerivation
+ ReplayClaimParentSide
+ coverage root
+ representative claim
+ lineage
```

`ClaimQualifiedParent::ReplayConstraint`から得るreplay relationだけでなく、ReplayEvidence由来のparent claim lineageも
この比較に含めた。zero mismatchは、current finite-map ledgerをauthority候補にできるgo/no-go根拠である。
実装sliceで一件でもparity divergenceが再現した場合、本書のpremiseが崩れるためstop conditionとする。

この一回目のinstrumentation自体は測定後に除去された。比較algorithm、invocation、raw resultはAppendix Aへ記録し、
QORF-Aで同じschemaのretained/reusable oracleとfull-workload harnessをrepositoryへ追加する。historical数値だけを
再現可能なgateの代用にしない。

### 1.4 Occurrence distribution と既存cost

| 項目 | 実測値 |
|---|---:|
| occurrence数 | 865,571 |
| parents / occurrence mean | 58.216318476 |
| parents / occurrence p50 | 29 |
| parents / occurrence p95 | 133 |
| parents / occurrence max | 161 |
| lower mean / p50 / p95 / max | 28.3154 / 14 / 69 / 97 |
| upper mean / p50 / p95 / max | 29.9009 / 17 / 64 / 96 |

capacity-inclusive payload proxyは次である。proxyはrepoの既存census規律に従い、container capacityとentry
`size_of`、hash control-byte相当をface別に数える。allocator metadataそのもののexact RSSではない。

| occurrence face | bytes |
|---|---:|
| occurrence arena | 83,886,080 |
| lower/upper parent payload | 855,657,552 |
| occurrence key index | 30,277,632 |
| result map | 3,784,704 |
| result occurrence refs | 9,500,800 |
| core subtotal | 983,106,768 |
| first witness | 60,555,264 |
| replay admission events | 29,360,128 |
| occurrence total | 1,073,022,160 bytes = 0.99933 GiB |

この0.99933 GiBはcurrent finite-map consumerのため既に支払われる。QORF後もexact occurrence、parent payload、first witness、
admission eventは消さない。

qualified-parent側は次である。

| qualified face | bytes |
|---|---:|
| full exact keys | 1,702,887,424 |
| result map | 3,784,704 |
| full canonical entries | 1,800,550,388 |
| first-source summary | 60,555,264 |
| total | 3,567,777,780 bytes = 3.322752 GiB |

first-source summaryを維持したままretire可能なfull-key/full-entry faceは3,507,222,516 bytes = 3.266356 GiBである。
occurrence + qualifiedのcombined proxy 4.322082 GiBに対するpotential removalは75.5737%である。
これはnew index overheadを差し引く前の上限であり、final savingの実測値ではない。

### 1.5 Reader volume / yield

QORF-0はproduction qualified-parent readerをcall site別に計測した。

| reader | calls | current parent yields / inspected | occurrence refs相当 | distribution |
|---|---:|---:|---:|---|
| direct evaluator slice | 1,964,985 | 29,462,911 | 3,030,123 | parent mean 14.994, p50 2, p95 36, max 2,109; occurrence mean 1.542, p50 1, p95 3, max 19 |
| values/materialization | 267,782 | 43,259,402 | 1,044,295 | parent mean 161.547, p50 8, p95 1,096, max 3,904; occurrence mean 3.900, p50 2, p95 15, max 35 |
| count | 781,149 | bucket width sum 601,961,067 | occurrence width sum 9,188,611 | current countはO(1)。bucket幅は実walkではない |
| carrier query | 834,088 | actual inspected 11,543,962 | occurrence refs 9,918,911 | inspected mean 13.84, p50 8, p95 44, max 1,265 |

evaluator hot readは、exact parents 29.46M件からoccurrence refs 3.03M件へ約89.7%減らせる可能性がある。
これは「全consumerで89.7%」という主張ではない。count queryは既にO(1)であり、values/carrier consumerはそれぞれ
必要なsummary/projectionへ個別に切り替える必要がある。current codeに直接GWCB qualified-parent readerは残っていない。

### 1.6 Replay snapshot writer baseline

`record_cpk_replay_parent_snapshot`のQORF-0 censusは次だった。

| 項目 | 実測値 |
|---|---:|
| calls | 865,571 |
| new occurrences | 865,571 |
| workload内late extension | 0 |
| input / inserted parents | 50,390,357 / 50,390,357 |
| linear duplicate comparisons | 1,363,997,696 |
| comparisons / inserted parent | 27.07 |
| elapsed run 1 / run 2 | 6.318s / 6.599s |
| per call | 7.30〜7.62 μs |
| per parent | 125〜131 ns |

このworkloadでは各occurrenceが一度に完成し、snapshot writerのlinear duplicate rescanは完全に冗長だった。
ただしcurrent finite-map contractはlate parent extensionを合法とするため、「常にnew occurrence」と仮定してbranchを消さない。
side-local exact membershipをtransactional writerへ統合し、new occurrenceはsorted unique deltaから一度だけbulk build、
late extensionは既存side indexへのdelta admissionとして扱う。

## 2. 先行設計との関係

### 2.1 RCPF とcurrent CPK replay finite-map ledger

RCPFが一度導入したfactorized `ReplayOccurrenceStore`、parent-set version、attachment batchは後続migrationで撤去済みであり、
`proof_inventory.rs`の`cpk_8g_9d_replay_occurrence_store_is_fully_removed`が再導入を禁止する。QORFはこのretired型を
復活させない。QORFがpromoteするcurrent structureは`ProofOccurrenceStore::replay_finite_map`とそのindex/event streamである。

current CPK replay finite-map ledgerは、RCPFで固定された次のsemantic contractを引き継いでいる。QORFもこれを維持する。

- exact occurrence keyは`(result, exact BinaryReplayDerivation)`。
- logical replay parent keyは`(occurrence, side, coverage root)`。
- representative claimはlegacy admission streamのfirst-wins。
- first replay witnessも`(result, root)`のfirst-wins。
- lower/upper sideをidentityから落とさない。
- parent集合はadmission-time snapshotであり、後からlive endpointを再読して作り直さない。
- exact carrier全field、lineage、replay admission event boundaryを粗化しない。
- no-claim passthrough、admission-time completeness、natural-event publicationを変えない。

QORFはcurrent finite-map occurrenceを別relationへ変換しない。qualified-parent consumerが、同じexact occurrence relationを
別の50.39M-entry full-key/full-value storeから読むのを止める。

ただしcurrent occurrence sideはadmission-order `Vec`であり、gap Aを解くexact membership authorityとしてはlinear scan、
gap Bを解くcanonical qualified-parent iteratorとしてはorder不一致である。このためQORFは、RCPFから継承した**意味**を変えず、
parent sideの物理containerをsorted chunk indexへ精密化し、result-local canonical arm projectionを追加する。
これはrepresentative/first-witnessの選択規則や`replay_admissions` / `first_event`を変更するものではない。current consumerがside Vecの
physical arrival orderへ依存していると判明した場合、その依存を列挙・移行するまでQORF-Bを止める。

### 2.2 PCLFから継承する規律

PCLF-Dは、意味上正しいfactored storageでもreader topologyが悪ければ14〜20%のwall regressionを起こし得ることを示した。
QORFは次を明示的に継承する。

1. hot readerは非empty physical projectionを明示cursorで一回だけ歩く。
2. `Map -> Fuse -> FlatMap`の多層adapter、empty category/product walk、query-time full materializationを置かない。
3. exact membershipとcanonical iterationは異なるlower boundを持つため、無理に一containerへ統合しない。
4. sorted chunkは最大128 entriesとし、singleton late insertionが既存side全体をscan/moveしない。
5. split node/bufferはprepareでfallible allocationし、commit中allocationを禁止する。
6. canonical outputはset/countではなくbyte-equal sequence oracleで検証する。
7. shadow authority、reader cutover、legacy retirementを別sliceにする。

QORFのcanonical mismatchはPCLF-Dのempty category×support topologyとは異なる。current finite-map ledgerはresultごとの
非empty finite-map entry ID列を自然に持ち、一index cursorで歩ける。問題は、物理arrival orderがqualified-parent comparatorの
`coverage root -> carrier -> side -> representative claim`順ではないことである。従ってQORFは50.39M incidenceを
canonical runへ再複製せず、evaluatorには一occurrence一arm、root materializationには一distinct-root一winner、
exact-output consumerには明示streaming cursorを与える。

### 2.3 今回変更しないもの

- `BinaryReplayDerivation`、claim/root identity、coverage/liveness。
- representative parent claimとfirst replay witnessのfirst-wins。
- current `replay_admissions` / `ReplayProofOccurrence::first_event`の意味とlogical exact cardinality。
- semantic subtype/replay planning、row route、solver、cycle cut。
- structural/reduction-route qualified-parent representationの意味。
- PCLF projection clause-link storage、GWCB decisive certificate、DPN/MPC semantics。
- portable/logical/diagnostic公開形式。
- epoch/publication boundary。
- permanent evaluation cache policy。

## 3. 提案するrepresentation

以下の型名はdraftであり、QORF-Aでcurrent namingとの衝突を再確認する。identityとquery contractを正本とする。

### 3.1 Stable IDs

current `replay_finite_map`のindexをtyped wrapperにする場合も、retired `ReplayOccurrenceId`名を復活させない。
qualified-parent replay authorityは同じfinite-map indexを使い、別のduplicate IDを作らない。

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayFiniteMapEntryId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayParentChunkId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayQualifiedArmChunkId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct CanonicalQualifiedParentRootChunkId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct NonReplayQualifiedParentId(u32);
```

IDはappend-only arena indexであり、allocation address、hash iteration、AVL shapeをcanonical outputへ露出しない。
`u32::MAX`等のreserved valueが既存memo/tagと衝突する場合、allocatorで`ResourceExhausted`として拒否する。

### 3.2 Exact occurrence authority

```rust
struct ReplayProofOccurrence {
    result: ConstraintRecordId,
    carrier: BinaryReplayDerivation,
    lower: ReplayParentSideIndex,
    upper: ReplayParentSideIndex,
    // current fieldと同じreplay_admissions stream boundary。
    first_event: usize,
}
```

`result`と`carrier`はcurrent finite-map occurrence identityである。lower/upperは同じcontainer型を使うが、sideはoccurrence fieldの
位置で固定され、parent payloadへ反復保存しない。

```rust
#[derive(Clone, Copy, PartialEq, Eq)]
struct ReplayProofParent {
    coverage_root: UpperReplayClaimId,
    representative_claim: UpperReplayClaimId,
    lineage: ProjectionLineage,
}
```

current `ReplayProofParent`の`side` fieldは、QORF完成形ではlower/upper side containerの位置で表す。actual field名/layoutと、
tag除去によるRust layoutはQORF-A/Bで再確認する。意味上、coverage rootはside内uniqueであり、representative claimと
lineageはそのexact keyのfirst accepted valueである。later persistent duplicateまたはbatch-local duplicateが異なる
representative/lineageを提示しても、current writerは比較・rejectせず、そのentry全体をsilentにdropしてfirst accepted valueを残す。
QORFもこのsilent first-winsを維持し、metadata mismatchを新しいerrorへ変えない。

### 3.3 Gap A: side-local sorted chunk AVL

current side `Vec<ReplayProofParent>`のlinear exact membershipを、次のnonempty chunk treeへ置き換える。

```rust
const REPLAY_PARENT_CHUNK_CAPACITY: usize = 128;

struct ReplayParentSideIndex {
    root: Option<ReplayParentChunkId>,
    len: u32,
}

struct ReplayParentChunkNode {
    // coverage_root、次にrepresentative_claim、lineageのstable tie rule。
    // coverage_rootはside内unique。
    entries: Box<[ReplayProofParent]>, // 1..=128
    left: Option<ReplayParentChunkId>,
    right: Option<ReplayParentChunkId>,
    height: u8,
}

struct ReplayParentChunkArena {
    nodes: Vec<ReplayParentChunkNode>,
}
```

global arenaはindex IDでnodeを参照するため、arena `Vec`自体がreallocateしてもlinkは壊れない。node entry bufferは
exact lengthのboxed sliceとし、current side Vecのspare capacityをそのまま残さない。128はPCLFで実装・fixture検証済みの
fixed boundを再利用する提案値であり、QORF workloadでのphysical最適値は**要検証**である。

操作は次になる。

```text
contains(root):
    AVL pivot binary search + chunk binary search
    O(log chunk_count + log 128)

iter():
    fixed-stack in-order chunk cursor + contiguous chunk entries
    O(parent_count)

new occurrence:
    event-local parent deltaをfirst-wins確定後にroot順sort/dedup
    最大128件ずつbulk packし、balanced treeをprepare中に構築

late extension:
    accepted deltaだけをsort
    affected chunkへroute
    existing最大128件 + local deltaをmerge
    overflow chunkをsplitし、prepare済みnodeをAVL insert/rebalance
```

これによりexact membershipはgap Aのlinear side scanを解消する。expected O(1) global hashではなくbounded logarithmic queryへ
変わるため、QORF-B/Cはcall-countとwall profileで回帰zeroをblocking gateにする。50.39M-entry compact hashを別に置く案は、
scattered writesとduplicate cardinalityを残すため完成形に採らない。

payload scan/moveはaffected chunkあたり128件以下に閉じる。一eventが複数chunkへdeltaを持つ場合は
`O(delta log chunks + affected_chunks * 128)`であり、side全長のclone/re-sortを行わない。tree rotationはID/node fieldの
入れ替えだけでallocationしない。

### 3.4 Small non-replay flat store

structural/reduction-route 30,256件は、current exact keyとcanonical valueを保つ小さいstoreへ分離する。

```rust
struct NonReplayQualifiedParentStore {
    keys: FxHashSet<QualifiedParentKey>,
    entries: Vec<ExactQualifiedParent>,
    by_result: FxHashMap<ConstraintRecordId, Vec<NonReplayQualifiedParentId>>,
}
```

型をreplay/non-replayへ静的に分けられる場合はnarrow key/valueを導入してよいが、QORFの必須条件にはしない。
30,256件をfactorizeするためにstructural/reduction semanticsを同時変更しない。

### 3.5 Gap B: result-local canonical replay arm index

legacy evaluatorはcanonical exact-parent列を歩き、同じexact replay carrierを何度も評価する必要はない。
QORF-0では29.46M exact parent inspectionを3.03M occurrence referencesへ縮められる可能性が観測された。

result `r`のoccurrence `o`について、qualified-parent comparator順で最小のexact replay parent keyを

```text
first_key(o) = min {
    (coverage_root, exact carrier, side, representative_claim)
    | parent ∈ o.lower ∪ o.upper
}
```

とする。coverage rootはside内uniqueであり、exact carrierはoccurrenceに固定される。実装はexisting
`qualified_parent_entry_cmp` / exact comparatorを正本とし、この略記から独自の順序を再発明しない。

```rust
struct ReplayQualifiedArmIndex {
    by_result: FxHashMap<ConstraintRecordId, ReplayQualifiedArmTree>,
    chunks: Vec<ReplayQualifiedArmChunkNode>,
}

struct ReplayQualifiedArmTree {
    root: Option<ReplayQualifiedArmChunkId>,
    len: u32,
}

struct ReplayQualifiedArmChunkNode {
    // first_key(finite-map entry)順。payloadはfinite-map entry IDだけ。
    entries: Box<[ReplayFiniteMapEntryId]>, // 1..=128
    left: Option<ReplayQualifiedArmChunkId>,
    right: Option<ReplayQualifiedArmChunkId>,
    height: u8,
}
```

一occurrenceにつきarm IDはexactly oneである。50.39M exact incidence IDをcanonical projectionへ複製しない。
tree comparatorはoccurrence arenaから`first_key`を読む。equal keyが合法に存在する場合は、existing exact comparatorの
remaining stable fieldを使い、arena ID/admission orderをobservable tie-breakへ使わない。current code上でtotal orderを
構成できないcaseが見つかった場合はstopする。

late extensionでnew parentがcurrent `first_key`より前へ入る場合、armを同じtransactionでrekeyする。

```text
prepare:
    old first_keyをimmutable snapshotから得る
    new accepted parentを含むnew first_keyを計算
    arm deletion/reinsertionに必要なreplacement chunks/split nodesを全preflight

commit (exclusive &mut publication boundary):
    old-key armをallocation-free remove
    occurrence side deltaをallocation-free commit
    new-key armをallocation-free insert
```

readerがtree invariantの中間状態を観測できないnatural-event boundaryを維持する。no min-key changeならarm treeを触らない。
removeでchunkがemptyになる場合のnode unlink/AVL rebalanceもallocation-freeにする。QORF-A/Bでinsert/remove/rekeyを
exhaustive model oracleと比較する。

このprojectionがlegacy evaluator順と等価であるためには、次を証明する必要がある。

```text
legacy canonical exact-parent sequenceから
同一replay occurrenceの2件目以降をstableに除いた列
== canonical replay arm cursor
```

さらに、同一occurrenceの別root/side/representativeがevaluatorのvalidation result、error precedence、provenanceを
変えないことをcurrent codeとfixtureで確認する。この性質を証明できない場合、89.7% reductionを前提にreader cutoverしない。

### 3.6 Result-local canonical root-winner projection

evaluator armはboolean carrier evaluationには十分だが、root単位のmaterializationには不十分である。
`merge_structural_claim_parents`と`register_constraint_upper_replay_claims`はcurrent canonical exact-parent列をroot順に読み、
各`(result, root)`で最初のexact parentの`parent_claim` / lineageを後続claimの代表にする。このwinnerはhistorical
first-source/first-witnessと一致するとは限らない。

QORFは次のcompact projectionを別authorityとして持つ。

```rust
#[derive(Clone, Copy, PartialEq, Eq)]
enum CanonicalQualifiedParentRef {
    Replay {
        finite_map_id: ReplayFiniteMapEntryId,
        side: ReplayClaimParentSide,
    },
    NonReplay {
        parent_id: NonReplayQualifiedParentId,
    },
}

struct CanonicalQualifiedParentRootEntry {
    coverage_root: UpperReplayClaimId,
    winner: CanonicalQualifiedParentRef,
}

struct CanonicalQualifiedParentRootIndex {
    // resultごとのcoverage_root順nonempty chunk AVL。
    by_result: FxHashMap<ConstraintRecordId, CanonicalQualifiedParentRootTree>,
    chunks: Vec<CanonicalQualifiedParentRootChunkNode>,
}

struct CanonicalQualifiedParentRootTree {
    root: Option<CanonicalQualifiedParentRootChunkId>,
    len: u32,
}

struct CanonicalQualifiedParentRootChunkNode {
    entries: Box<[CanonicalQualifiedParentRootEntry]>, // 1..=128, root順
    left: Option<CanonicalQualifiedParentRootChunkId>,
    right: Option<CanonicalQualifiedParentRootChunkId>,
    height: u8,
}
```

`Replay` refはmap keyのrootとoccurrence side indexからexact representative claim/lineageをO(log chunks)で得る。
`NonReplay` refは30,256-entry scaleのstable non-replay arenaを指す。full 28-byte parentをroot summaryへ複製しない。

cardinalityはexact parent数ではなくdistinct `(result, coverage_root)`数である。QORF-0 workloadでは、同じkey domainを持つ
existing `first_qualified_parent_source_by_root`が1,792,654 entriesだった。QORF-A retained censusとQORF-D0はroot indexの
logical countがこのdistinct-root
domainと一致することをfreshに測り、50.39M scaleへ膨らまないことをgateにする。このobserved cardinalityはreplay exact
50,390,357件の3.557534%であり、一root一compact refというshape自体はsecond full expansionにならない。entry/treeのactual
`size_of`、capacity、allocator overheadは未実装なので**要検証**であり、QORF-D0 gateでcapacity-inclusiveに測る。
historical first-sourceとcanonical winnerは
winner規則が違うためvalueを共用しない。物理的に同じroot-summary bucketへ二valueを置く最適化は、双方を独立oracleで
比較できる場合だけ許す。

root treeも最大128-entry nonempty chunkとprepared AVL nodeを使う。new root insertionはaffected chunkだけをmerge/splitし、
resultの全root winnerをclone/re-sortしない。existing rootのwinner replacementは同じchunk内のfixed-size value overwriteであり、
tree orderを変えない。全buffer/node capacityはparent/arm transactionと同時にpreflightする。

new accepted exact parent `p`について、root entryがなければinsertする。既存winnerがあればexisting
`qualified_parent_entry_cmp(p, winner)`が`Less`の時だけwinner refをreplaceする。exact duplicateはcurrent writerどおり
silent dropし、root winnerを更新しない。root tree keyはcoverage rootだけなのでwinner replacementはtree rekeyを必要としない。
全replacementはsame prepared transactionで行う。

writer authorityはreplay snapshot専用pathではなく、全`ClaimQualifiedParent` variantが通るgeneric
`try_prepare_qualified_parent_admission` / `commit_qualified_parent_admission` boundaryへ置く。replay callerはgeneric planをside/arm
inner transactionへ包み、structural/reduction-route callerは`begin_non_replay_claim_parent_admission`から同じroot deltaをcommitする。
structural carrierはreplay carrierよりcanonical comparatorで先行するため、later structural parentがexisting replay winnerを
置換し得る。このreplaceをnon-replay small-store commit、first-source/count update、publication fenceと同じpreflight/commitへ含める。

root cursorはcoverage root順に一entryずつ返す。このprojectionを次へ使う。

- `merge_structural_claim_parents`: rootごとのwinner parentから一件だけ新structural parentを作る。
- `register_constraint_upper_replay_claims`: rootごとのwinner lineageでderived claimをmaterializeする。
- root単位diagnostic/materializationのfirst canonical parent。

同じrootの全exact carrier associationを必要とするclause-link bootstrapにはwinner一件だけを使わない。§3.8の専用cursorを使う。

### 3.7 Hot canonical cursor

evaluator用cursorは次の二sourceだけを明示two-way mergeする。

1. replay arm treeのin-order `ReplayFiniteMapEntryId` cursor。
2. small non-replay result-local canonical Vec cursor。

```text
replay_head = next replay occurrence arm, key = first_key(occurrence)
non_replay_head = next non-replay exact parent, key = existing canonical key

while either head exists:
    yield smaller head under existing qualified_parent_entry_cmp
    advance only that source
```

cursorはfixed stackのAVL in-order walkと二つのheadだけを持つ。empty result、empty side、全occurrence×全sideのproductを
work itemにしない。`Map` / `Fuse` / `FlatMap` chainへ実装しない。replay armからevaluatorへ渡すのはborrowed
`result/carrier`と必要なfirst-source identityだけであり、50M exact parent valueを再構築しない。

count queryはpersistent `qualified_parent_count_by_result` summaryをO(1)で読む。countのためarm/exact iteratorを歩かない。
carrier query、values/materialization queryは§5のconsumer別projectionへ移し、hot pathでfull exact iteratorを共有しない。

### 3.8 Exact canonical / clause-association cursors

portable/audit/test oracle等が全exact qualified parentsをcanonical順で必要とする場合、次の明示k-way mergeを使う。

1. resultの各occurrenceについて、lower/upper side chunk cursorのheadを作る。
2. headをexisting qualified-parent comparator keyのsmall heapへ入れる。
3. minimumをyieldし、そのside cursorだけをadvanceする。
4. small non-replay canonical cursorも同じmerge frontierへ入れる。

これは`O(N exact * log active_sides)`であり、50.39M relationをpersistent canonical Vecへ戻さない。constructorはresult indexから
active side数とsmall non-replay source数を先に数え、frontier/cursor storageを`try_reserve`してからheadをseedする。
construction failureは`ProofFailure::ResourceExhausted`として返し、iterator本体は固定capacity frontierでpop/pushするため
`next()`中にallocationしない。portable/exportでこのcostが問題になる場合は、そのconsumerのexplicit workloadとして別設計へ戻る。
evaluator performanceを守るためexact cursorをarm cursorの実装へ流用しない。

`preflight_claim_parent_clause_links`のbootstrapは全`(root, exact carrier)` associationを必要とし、そのoutput自体が
exact association cardinalityを持つ。このconsumerには別の`try_replay_clause_link_associations(result)` streaming cursorを提供する。

```text
resultのoccurrence side cursorをroot/carrier/side順にk-way merge
    -> 同じ(occurrence, root)がLower/Upper双方にある場合は一件へdedup
    -> (coverage_root, exact carrier, projection source)をyield
    -> PCLF clause-link preflightへ直接stream
```

このcursorは必要な各associationを一回訪れるが、50.39M full `ExactQualifiedParent` Vec/HashMapを構築しない。
structural/reduction-route associationはsmall non-replay canonical cursorから供給し、existing comparatorでreplay streamとmergeする。
通常のsublinear-output materializationへ流用せず、clause-link bootstrapのcall/yieldと生成link数が一致することをcensusする。
association cursorも同じfallible-constructor disciplineを使う。active side/non-replay source数のfrontier capacityをmutation前に
確保し、constructed cursorのiteration中allocation zeroとする。clause-link preflightはconstructor errorをそのままpropagateし、
empty iteratorへ近似しない。
従ってinvariantは「全production consumerのexact traversal zero」ではなく、「exact-output consumer以外のexact traversal zero、
全consumerのeager full expansion zero」とする。

canonical exact sequenceはlegacy `qualified_parents_by_result[result]`とbyte-for-byte比較する。set/count parityだけでは、
first source、error precedence、diagnostic orderを保護できない。

### 3.9 First-wins summaries

次はrelationから後で再導出しない。

- qualified-parent first source。
- current finite-map first replay witness。
- representative parent claim / lineage。
- result-local logical qualified-parent count。

first-source summary 60,555,264 bytesはQORFの3.266 GiB removal estimateから除外済みである。first replay witnessとのさらなる
factorizationは、両summaryの全field parityを別censusで証明するまで行わない。

winnerはlegacy admission streamと同じ順序でprepare中に確定し、canonical tree/heap iterationから再計算しない。
canonical orderとhistorical first-wins orderを混同しない。

### 3.10 Completed store shape

完成形は概ね次になる。

```rust
struct ProofOccurrenceStore {
    replay_finite_map: Vec<ReplayProofOccurrence>,
    replay_finite_map_index:
        FxHashMap<(ConstraintRecordId, BinaryReplayDerivation), ReplayFiniteMapEntryId>,
    replay_indices_by_result:
        FxHashMap<ConstraintRecordId, Vec<ReplayFiniteMapEntryId>>,

    replay_parent_chunks: ReplayParentChunkArena,
    replay_qualified_arms: ReplayQualifiedArmIndex,
    canonical_qualified_parent_by_root: CanonicalQualifiedParentRootIndex,

    non_replay_qualified_parents: NonReplayQualifiedParentStore,
    qualified_parent_count_by_result: FxHashMap<ConstraintRecordId, u32>,
    first_qualified_parent_source_by_root: /* existing historical summary */,

    // PCLFの既存summary、replay admission event、first witness等。
}
```

完成形のproductionには、replay `QualifiedParentKey` 50.39M件とreplay `ExactQualifiedParent` 50.39M件を残さない。
test-only legacy reconstruction oracleは許すが、release binaryでpersistent allocation/growth zeroとする。

## 4. Outer replay event / inner admission transaction

### 4.1 Natural-event boundary

current codeのaction boundaryは、eventをparent admissionとall-or-nothingにはしていない。`apply_cpk_bound_replay_actions`は
`register_cpk_replay_claim_parents`を先に呼び、そこでqualified-parent preparationが失敗するとterminal failureを記録してreturnする。
その後もcallerは必ず`record_replay_admission`を呼ぶ。従ってQORFも、次の二層を明示的に分ける。

1. **outer replay action contract**: canonical duplicate、exact duplicate、incomplete、trivial、evidence-only、qualified-parent
   preparation failureを含む全outcomeについて、最後に`ReplayAdmissionEvent`を一件appendする。
2. **inner qualified-parent transaction**: accepted parent、finite-map side、arm、root-winner、first summaries、accepted delta由来の
   generic `ProofOccurrence`をall-or-nothingでprepare/commitする。new index reserve failureではinner logical mutation zeroだが、
   outer eventは失わない。

`record_replay_admission`のexisting append自体はfallible QORF admissionの一部へ変えない。allocator-level abortを新しい
`ResourceExhausted` semanticsへ変更するのも本書の範囲外である。QORF failure injectionはside/arm/root-winner等のrecoverable
reservation failure後にもeventが一件増えることを要求する。

```text
replay event inputs
    -> freeze (result: Option<_>, carrier, ReplayAdmissionDisposition)
    -> try inner qualified-parent prepare/commit
         new occurrence prepare: capture event_index = replay_admissions.len()
         success: commit parent/side/arm/root-winner/summary/generic occurrence
         failure: mark terminal failure; inner logical mutation zero
    -> record_replay_admission(...) exactly once in either case
    -> appended event index == captured event_index
    -> existing outer action continuation
```

new finite-map occurrenceはinner commit時に`first_event = event_index`を保存する。ここで`event_index`はappend**前**の
`replay_admissions.len()`であり、直後にappendされるeventのzero-based index `N`である。`len_after_append`で書くなら
`first_event = len_after_append - 1`であり、post-append length `N + 1`ではない。

parent accepted zeroはparent/index/summaryに対するno-opであって、outer replay event ledgerのno-opではない。
accepted parent delta以外から作られるevidence等の`ProofOccurrence`はcurrent outer action上の既存位置を維持し、QORFのために
inner transactionへ移動しない。accepted delta由来のgeneric replay `ProofOccurrence`だけはside/root projectionと同じinner planへ含める。

異なるresult/eventをstorage sharingのため一transactionへ混ぜない。planningのimmutable readとcommitの`&mut` boundaryを
跨いでprepared planを再利用しない。

### 4.2 Prepared delta

```rust
struct PreparedReplayAdmissionEventDescriptor {
    result: Option<ConstraintRecordId>,
    carrier: BinaryReplayDerivation,
    disposition: ReplayAdmissionDisposition,
}

struct PreparedQualifiedParentAdmission {
    // replay / structural / reduction-routeの全variant共通。
    accepted: Vec<ExactQualifiedParent>,
    root_winner_delta: Vec<PreparedCanonicalRootWinnerUpdate>,
    first_source_delta: Vec<PreparedFirstSource>,
    count_delta: u32,
    // legacy shadow / small non-replay delta等。
}

struct PreparedReplayQualifiedParentTransaction {
    qualified: PreparedQualifiedParentAdmission,

    // parent accepted zeroならNone。outer event descriptorはこのplanの外に必ず存在する。
    occurrence: Option<PreparedOccurrenceIdentity>,
    lower_delta: Option<PreparedReplayParentSideDelta>,
    upper_delta: Option<PreparedReplayParentSideDelta>,

    old_arm_key: Option<ReplayQualifiedParentCanonicalKey>,
    new_arm_key: Option<ReplayQualifiedParentCanonicalKey>,
    prepared_arm_edit: Option<PreparedReplayQualifiedArmEdit>,

    // accepted new-parent deltaが作るgeneric Replay cause。
    proof_occurrence_deltas: Vec<PreparedProofOccurrence>,

    // new finite-map occurrenceだけが使うappend前len = 後続eventのzero-based index。
    first_event_index_before_append: Option<usize>,

    accepted_exact_count: u32,
    first_witness_delta: Vec<PreparedFirstWitness>,
    consumer_summary_delta: PreparedReplayConsumerSummaryDelta,
}
```

planはaccepted exact rootsと既存duplicateを区別し、batch-local duplicateをfirst accepted valueへcollapseする。
existing/batch duplicateはcurrent writerと同じく後続representative/lineageを比較せずsilent dropする。ID overflow、constructor
invariant、canonical comparator failure、missing claim/sourceはcapacity reserveより前に検証する。

`PreparedQualifiedParentAdmission`がroot-winner updateの共通ownerである。replay pathはこれを
`PreparedReplayQualifiedParentTransaction`へ包み、side/arm/first-witness/generic occurrenceと一inner transactionにする。
`begin_non_replay_claim_parent_admission`は同じgeneric planを直接使うため、structural/reduction-route parentもroot winnerを
atomicにinsert/replaceする。structural carrierはreplay carrierよりcanonicalに先行するため、later structural admissionが
existing replay winnerを置換するcaseを明示的にprepareする。

これはQORF-D0まで到達した**完成inner transaction shape**である。QORF-Bはproof occurrence、finite-map side、legacy shadow、
summary部分を先に実装し、arm/root-winner fieldsはnon-authoritative placeholderまたはempty deltaにする。
QORF-D0は別commitでarm prepare/commitとgeneric root-winner deltaをplanへ追加する。QORF-Bの時点で未実装projectionをcommitしたことにせず、
各sliceのfailure-injection censusも、そのsliceでpersistentになったfaceだけを正確に列挙する。

### 4.3 Prepare order

outer actionとinner prepareは次の順序を固定する。

1. outer actionが`result: Option<_>`、carrier、dispositionを凍結する。
2. carrier/result/side/root/representative/lineage constructor invariantを検証する。
3. generic qualified-parent planで全variantのexact membershipを引き、accepted deltaとroot-winner updateを作る。
4. replay variantならimmutable occurrence key indexを引き、existing/new occurrenceを判定する。non-replay variantはside/arm deltaを持たない。
5. lower/upper side indexでpersistent exact membershipを引く。existing keyはmetadataを比較せずsilent first-winsでdropする。
6. batch-local `(side, root)` duplicateも最初のentryだけを残し、後続metadataを比較しない。
7. accepted deltaだけをroot canonical orderへsortする。
8. old/new occurrence `first_key`を計算し、arm no-op/insert/rekeyを決める。
9. accepted exact parentsをexisting root winnerとcanonical比較し、distinct-root scaleのwinner deltaをgeneric planへ置く。
10. count、first source、first witness、consumer summary deltaをlegacy admission stream順に確定する。
11. accepted replay parent deltaが非emptyならgeneric replay `ProofOccurrence`を一件準備する。
12. new finite-map occurrenceなら、そのoccurrence prepare時点の
    `first_event_index_before_append = replay_admissions.len()`を凍結する。
    existing occurrenceの`first_event`は変更しない。
13. semantic/error-precedence validationを全て終える。
14. generic proof occurrence arena/index/parent Vec、finite-map occurrence arena/key/result index、
    parent chunk arena/replacement buffers、arm/root-winner tree replacement/split nodes、non-replay store、summaryのcapacityを
    worst caseでfallible preflightする。
15. parent accepted zeroならinner parent/arm/root-winner/count/first summary deltaをemptyにする。
16. inner prepare/commitの成否にかかわらず、callerはdescriptorどおりouter eventを一件appendする。

inner capacity reservation failureはinner logical state mutation前に`ResourceExhausted`相当へ返す。途中reserveでcapacityだけが
増えることはRust container contract上あり得るが、parent/side/arm/root-winner/summary/proof-occurrenceのlogical
len/content/first-wins/epoch partial commitを禁止する。outer event appendはこのrollback setに含めない。

### 4.4 Commit order

inner commitはfallible validation/allocationを行わない。

1. existing arm rekeyならold armをallocation-free removeする。
2. new finite-map occurrence identityをappendし、`first_event`をprepared `first_event_index_before_append`へ設定する。
3. lower/upper prepared parent chunksをcommitする。
4. new/rekey armをallocation-free insertする。
5. generic qualified-parent deltaとcanonical root-winner updateをallocation-free commitする。
6. exact count、first source、first witness、consumer summaryをcommitする。
7. accepted new-parent deltaが要求するprepared generic replay `ProofOccurrence`をappendする。
8. existing inner publication/epoch policyへ進む。
9. inner functionがsuccessまたはfailureをcallerへ返した後、outer callerが`ReplayAdmissionEvent`をexactly once appendする。
10. inner successでnew occurrenceを作った場合、debug/test buildはappended event indexが保存済み`first_event`と一致するとassertする。

new occurrenceでは1〜8の間にconsumerが走らない。existing occurrence rekeyでは1〜6の中間stateを観測させない。
prepare済みowned buffers/nodes以外をcommit中に作らない。debug/test buildでは各step前後のID、len、tree invariantをassertする。

QORF shadow期間はlegacy qualified facesとoccurrence/arm facesを同じprepared planからdual-writeする。legacy prepare成功後に
new proof-occurrence/side/arm/root-winner reserveが失敗してもinner facesをlogical mutationしない。ただしouter eventはcurrent
behaviorどおり一件appendする。failure injectionは各inner persistent reserveの前後、複数side/chunk/arm/root runの間に置き、
failureごとにinner state不変とevent `+1`を同時にassertする。

### 4.5 New occurrence / late extension

new occurrenceはlower/upper deltaを一度だけsort/dedupし、chunkをbulk buildする。QORF-0 workloadの865,571 callは全てこのcaseだった。
linear duplicate rescan 1,363,997,696 comparisonsを実行しない。

late extensionはcurrent finite-map contract上合法である。

- existing root: later representative/lineageを比較せずsilent first-winsでexact parent no-op。replay admission eventは別途記録する。
- new root, min key不変: affected parent chunksとsummaryだけを更新。
- new root, min key変化: same transactionでarm remove + parent update + arm insert。
- accepted new rootが既存canonical root winnerより小さい: root winner refをsame transactionでreplaceする。
- accepted deltaが非empty: new occurrence/late extensionのどちらでもgeneric replay `ProofOccurrence`を一件appendする。
- empty occurrenceは作らない。last parent removalはappend-only modelでは存在しない。

side全長Vecのclone/re-sort、result全armのsort、global repair、delayed rekeyを行わない。

### 4.6 Retraction / remover

current finite-map/QORF censusはaccepted replay occurrence parentをappend-only factとして扱う。実装中にparent removal、root reclassification、
exact keyに保存済みのrepresentative claim/lineage replacement、occurrence carrier rewriteが一件でも見つかった場合、QORF-B以降を止める。
arm rekeyはnew smaller root追加に伴うordered projectionの物理更新であり、logical parent removalではない。
canonical root-winner refのreplacementも、新しいaccepted exact parentによって既存rootのcanonical minimumが変化した時の
derived projection更新であり、保存済みexact parent metadataのreplacementではない。

## 5. Consumer API とcutover

consumerがtree/arena fieldsへ直接依存しないよう、少なくとも次を境界にする。

```rust
fn exact_replay_qualified_parent_is_registered(
    &self,
    result: ConstraintRecordId,
    carrier: BinaryReplayDerivation,
    side: ReplayClaimParentSide,
    root: UpperReplayClaimId,
) -> bool;

fn replay_qualified_arms_for_result(
    &self,
    result: ConstraintRecordId,
) -> impl Iterator<Item = ReplayFiniteMapEntryId>;

fn qualified_parent_evaluation_items(
    &self,
    result: ConstraintRecordId,
) -> impl Iterator<Item = QualifiedParentEvaluationItem<'_>>;

fn canonical_qualified_parents_by_root(
    &self,
    result: ConstraintRecordId,
) -> impl Iterator<
    Item = (UpperReplayClaimId, CanonicalQualifiedParentRef),
>;

fn try_replay_clause_link_associations(
    &self,
    result: ConstraintRecordId,
) -> Result<ReplayClauseLinkAssociationCursor<'_>, ProofFailure>;

fn try_exact_qualified_parents(
    &self,
    result: ConstraintRecordId,
) -> Result<ExactQualifiedParentCursor<'_>, ProofFailure>;

fn qualified_parent_count(&self, result: ConstraintRecordId) -> usize;

fn first_qualified_parent_source(
    &self,
    result: ConstraintRecordId,
    root: UpperReplayClaimId,
) -> Option<QualifiedParentFirstSource>;
```

`try_exact_qualified_parents`はoracle、portable/audit、明示的export専用である。normal evaluator、count、admission、first-source、
carrier membershipから呼ばない。`try_replay_clause_link_associations`だけはexact-outputであるclause-link bootstrapから呼べるが、
full `ExactQualifiedParent` collectionを作らずPCLF preflightへstreamする。両constructorは全query-local capacityをfallibleに
確保し、成功後に返すnamed cursorの`Iterator::next`はinfallible/allocation-freeとする。consumerはconstructorの
`ProofFailure`を既存error channelへpropagateし、empty resultやpanicへ変換しない。

### 5.1 Evaluator

evaluatorは§3.7のreplay arm/non-replay merge cursorを歩く。replay itemはoccurrence carrierを一回だけ評価し、同じoccurrenceの
root/side multiplicityをboolean evaluationへ再展開しない。

次をlegacy pathと一致させる。

- evaluation item semantic sequence。
- include/exclude/fail-open。
- first successful parent/carrier。
- recursive premise evaluation順。
- cycle cut / memo state。
- first errorとerror precedence。
- first-source / evidence identity。

独立reviewはcurrent `eval_constraint_uncached`がreplay parentについてcarrierの`lower` / `upper`だけを読み、root、side、
representative claim、lineageをboolean evaluator inputに使わないことを確認した。従って一occurrence一armはevaluatorには十分である。
QORF-Aはこのcode factをretained fixture/oracleへ固定し、将来root/side固有validationが追加された場合にgateを再度開く。

### 5.2 Values / materialization / dependency consumers

consumerごとに必要なprojectionを使う。一occurrence一armをmaterializationの代用にしない。

- carrierの真偽だけが必要: finite-map entry ID/carrierを一回読む。
- `(result, root)` historical first witnessが必要: current first-witness summaryを読む。
- `merge_structural_claim_parents`: `canonical_qualified_parents_by_root`からrootごとのfirst canonical parentを読む。
- `register_constraint_upper_replay_claims`:同じroot-winner cursorからderived claim lineageを選ぶ。
- `preflight_claim_parent_clause_links`: `try_replay_clause_link_associations`で全replay `(root, exact carrier)`をstreamし、
  same occurrence/rootのLower/Upper重複だけを現行link keyどおり落とす。small non-replay exact cursorもcanonical mergeし、
  structural/reduction-route associationを落とさない。
- exact parent countが必要: result-local count summaryを読む。
- exact root/side membershipが必要: occurrence side indexを読む。
- exact lineage/exportが必要: exact compatibility cursorを明示的に使う。
- structural/reduction-routeが必要: small non-replay storeを読む。

root-winner projectionはdistinct `(result, root)` scale、clause association cursorは生成すべきexact clause-link scaleである。
後者のnecessary traversalを「full expansion zero」と偽らず、eager collection zeroとoutput一件あたりworkを測る。
43.26M yieldsのvalues pathや11.54M inspectedのcarrier pathを、同じ一つのgeneric iteratorへ無理に統合しない。
consumer別call/yield censusをauthority cutoverごとに再測定する。

root-winnerのwriterは§3.6/§4.2のgeneric qualified-parent planであり、consumer cutoverとは独立する。特に
`begin_non_replay_claim_parent_admission`をbypassするstructural/reduction-route direct writerをD0 censusでzeroにし、
later non-replay winner replacementがroot-winnerだけ先行/遅延publicationされないことを確認する。

### 5.3 Portable / logical / diagnostic

public outputのidentityとcanonical orderを変更しない。

- exact `(result, carrier, side, root)`をlosslessに列挙する。
- representative claimとlineageをfirst-wins値のまま出す。
- structural/reduction/replayのmixed orderをexisting comparatorどおりにする。
- shared-edge dedup、logical snapshot hash、diagnostic role/orderを変えない。
- hash/tree shape、chunk split、finite-map entry IDをoutputへ露出しない。

exact outputが必要なpathは§3.8のfallible constructorを使い、そのfailureをexisting error channelへpropagateし、call countとyieldを
censusする。full-value cursorはnormal std lowering中zero、clause-association cursorはbootstrap output数と一致し、
eager full collection zeroであることをQORF-D/E gateにする。

## 6. 必須invariants

1. **Exact replay identity**
   - `(result, exact BinaryReplayDerivation, side, coverage root)`を変えない。
   - carrierのpivot/lower/upper/ruleを粗化しない。

2. **Exact value preservation**
   - representative claimとlineageを各exact keyについてlosslessに保持する。
   - root/side/carrierからlineageを推測しない。

3. **Exhaustive relation parity**
   - 任意のnatural event境界で、expanded occurrence relationとlegacy replay qualified finite mapが全件一致する。

4. **Current finite-map occurrence semantics**
   - occurrence key、event-time snapshot、lower/upper side、admission-time completenessを変えない。
   - retired RCPF `ReplayOccurrenceStore` / attachment batchを再導入しない。

5. **Representative first-wins**
   - same exact keyのwinnerをcanonical orderやtree insertion orderから再導出しない。
   - persistent/batch duplicateのlater metadataを比較・rejectせず、current writerどおりsilent dropする。

6. **First witness / first source**
   - `(result, root)` first witnessとqualified first sourceのlegacy winnerを維持する。
   - 二summaryを未検証で一つへcollapseしない。

7. **Gap A exact membership**
   - occurrence+side固定後、root membershipはside-local chunk treeでbounded logarithmicに答える。
   - full global replay `QualifiedParentKey` hashを完成形へ残さない。

8. **Side-local canonical order**
   - chunk in-order列はcoverage rootを第一keyとするcurrent exact orderと一致する。
   - chunkは全てnonempty、1..=128 entries、root uniqueである。

9. **Full canonical sequence equivalence**
   - `try_exact_qualified_parents(result)?.collect::<Vec<_>>() == legacy[result]`をbyte-for-byte要求する。
   - set/countだけの比較で済ませない。

10. **Evaluator arm equivalence**
    - canonical replay arm列はlegacy exact列のfirst occurrence列とsemantic/error-precedenceを含めて一致する。
    - 一occurrenceにつきactive arm exactly one。

11. **Mixed replay/non-replay order**
    - structural/reduction/replayのrelative orderをexisting comparatorどおりにする。

12. **Canonical isolation**
    - hash iteration、arena ID、allocation address、AVL shape、chunk split、admission permutationをobservable orderへ漏らさない。

13. **Late extension / rekey**
    - new smaller rootで`first_key`が変わる場合、old armを同transactionでremoveしnew keyへinsertする。
    - stale arm、duplicate arm、delayed repairを許さない。

14. **Transactional logical atomicity**
    - inner transactionではgeneric proof occurrence、legacy shadow、occurrence side、arm/root-winner index、summaryの一部だけをcommitしない。
    - innerの全fallible capacityをmutation前にpreflightする。
    - outer replay eventは意図的にrollback set外であり、inner失敗後にもcurrent codeどおり一件appendする。

15. **Error precedence**
    - semantic corruption、canonical-order rejection、resource exhaustionのfirst returned errorをlegacyと一致させる。
    - allocationをvalidationより前へ動かしてerrorをmaskしない。

16. **Exact-parent no-op / event preservation**
    - persistent duplicate/batch duplicate/accepted zeroでparent/arm/root-winner/count/first-wins storageを増やさない。
    - 同じoutcomeでも`record_replay_admission`が要求するeventは必ずappendし、inner preparation failureでも落とさない。

17. **No full-side/bucket rebuild**
    - late deltaのためside全parent、result全exact parent、全armをclone/re-sortしない。
    - affected fixed-capacity chunksだけをreplace/splitする。

18. **No production full expansion**
    - evaluator、count、admission、membership、first-source、root-winner materializationで50.39M full-value iteratorを使わない。
    - clause-link bootstrapはΩ(output)のassociationをstreamできるが、full Vec/HashMapをmaterializeせず各associationを一回だけ訪れる。

19. **Explicit cursor topology**
    - hot arm walkはnonempty tree/chunkとsmall non-replay cursorだけを訪れる。
    - nested product/empty walk/generic deep adapterへ戻さない。

20. **Logical cardinality preservation**
    - replay 50,390,357、non-replay 30,256というQORF-0 logical relationを、同workloadのoracleで維持する。
    - physical arm ID削減をlogical parent削減と誤記しない。

21. **Count O(1)**
    - count queryをarm/exact traversalへ退行させない。

22. **Append-only logical relation**
    - exact parentのremoval/reclassification、保存済みrepresentative claim/lineage replacementを導入しない。
    - arm rekeyとcanonical root-winner ref replacementはordered projectionの更新でありlogical delete/value rewriteではない。

23. **Consumer boundary**
    - production consumerはarena/tree fieldsを直接走査せず§5 APIを使う。

24. **Corruption/fail-hard preservation**
    - missing occurrence/parent/lineageを別source、structural parent、fail-openへ近似しない。
    - exact duplicate metadata mismatchはcorruptionへ昇格せず、invariant 5のsilent first-winsを優先する。

25. **Current finite-map / RCPF-history independence**
    - QORF rollbackでcurrent finite-map occurrence、first witness、replay event stream、PCLF clause-link consumerを壊さない。
    - retired RCPF occurrence/attachment surfaceを復活させない。

26. **No permanent evaluation cache**
    - arm/root-winner indexはappend-only exact-parent inputから導くordered projectionであり、boolean evaluation result cacheではない。
    - late extension時のarm rekey/root-winner replacementを許すため、projection storage自体をappend-onlyとは仮定しない。

27. **Logical/physical census separation**
    - exact parents、occurrences、arm refs、root-winner refs、chunk nodes、event/proof-occurrence entries、capacity bytes、
      full-value/association query yieldsを別々に報告する。

28. **Atomic arm rekey**
    - readerはold key/old parentまたはnew key/new parentのどちらか一方だけを観測する。
    - commit-time allocationとtemporary stale keyを許さない。

29. **Canonical root-winner equivalence**
    - 各`(result, root)`のwinnerはlegacy full canonical sequenceで最初の`ExactQualifiedParent`とbyte-equivalentである。
    - historical first-source/first-witnessをcanonical winnerの代用にしない。
    - projection cardinalityはdistinct `(result, root)`でありexact parent cardinalityへ膨らまない。
    - replay、structural、reduction-routeの全accepted parentをgeneric qualified-parent transactionで比較し、later non-replay
      admissionによるcanonical winner replacementも同じatomicityでcommitする。

30. **Replay event / proof occurrence equivalence**
    - canonical duplicate、exact duplicate、incomplete、trivial、evidence-only、zero acceptedを含む全outcomeの
      `ReplayAdmissionEvent` sequenceをlegacyと一致させる。
    - qualified-parent/side/arm/root-winner preparation failureでもouter eventを一件記録する。
    - new occurrenceの`first_event`はappend前len `N`、すなわち後続eventのzero-based indexであり、post-append lengthではない。
    - accepted new-parent deltaはnew/late occurrenceを問わずlegacyと同じgeneric `ProofOccurrence`を一件作る。

31. **Clause-link association completeness**
    - bootstrapは全`(result, root, exact carrier)`associationをexactly onceでPCLF preflightへ渡す。
    - root winner一件またはevaluator arm一件で全carrierを代表させない。

32. **Fallible exact cursor construction**
    - exact/association k-way cursorはconstructorで全frontier capacityをfallibleに確保し、failureを`ProofFailure`で返す。
    - construction後のiteration中allocation zeroとし、failureをempty iterator、panic、partial preflightへ変えない。

## 7. Oracle とregression specification

### 7.1 Linear reconstruction oracle

shadow期間は各natural event後に次を比較できるhelperを置く。

1. replay exact finite map（result/carrier/side/root -> representative/lineage）。
2. full canonical exact-parent sequence。
3. result-local count。
4. exact membership answer。
5. representative first-wins。
6. first witness / first source。
7. replay arm sequenceとlegacy stable-first occurrence sequence。
8. `(result, root)` canonical winnerとlegacy sequenceのfirst parent。
9. mixed replay/non-replay evaluator item sequence。
10. evaluator include/exclude/fail-open、first success、first error。
11. inner success/failure双方のreplay admission event sequence、append前lenに基づく`first_event`、generic/evidence proof occurrence sequence。
12. clause-link `(root, exact carrier)` associationとdependency/materialization output。
13. portable/logical/diagnostic output。
14. finite-map occurrence/side/arm/root-winner tree invariant。

std workloadで毎event 50M full expansionを行わない。targeted fixtureではevent-boundary full oracle、stdではsampled record/resultと
終了時exhaustive censusを分ける。QORF-Aはこのhelperを一時instrumentationで終わらせず、後続sliceが再利用できる
`#[cfg(test)]` oracleとしてrepositoryへ残す。QORF-0の再実行手順とraw resultはAppendix Aを正本とする。

### 7.2 Required fixtures

- new occurrence with lower only / upper only / both sides。
- exact persistent duplicate。later representative/lineageが異なってもsilent dropし、new errorを返さない。
- batch-local duplicate。同じくfirst entryをsilentに保持する。
- same root、different representative claim/lineageのfirst-wins。各admission orderでlegacy winnerと一致するが、
  異なるorder間でwinner不変とは仮定しない。
- same carrier/root、different side。
- same result、different exact carrier。
- structural / reduction-route / replay mixed order。
- one occurrenceへp95/max以上のparents。
- side 128 / 129 / multiple chunks境界。
- descending/ascending/middle singleton late extensionを1,800 events反復し、side全長scan/moveがないcase。
- late extensionで`first_key`不変。
- late extensionでlower/upperのnew smaller rootが`first_key`を変え、armがrekeyされるcase。
- rekey前後に同resultの他occurrence/non-replay parentがあり、先頭・中間・末尾へ移るcase。
- 一occurrenceのglobal minimumとは別rootについて、別occurrenceとのcanonical競合があり、root winnerが正しく選ばれるcase。
- same rootへlater accepted carrierがcanonicalに先行し、root winnerだけがreplaceされhistorical first-source/first-witnessは不変なcase。
- existing replay root winnerの後にstructural parent、reduction-route parentを各々admitし、existing comparatorで先行する
  non-replay winnerがgeneric qualified-parent transaction内でatomicにreplaceされるcase。
- `merge_structural_claim_parents` / `register_constraint_upper_replay_claims`がroot winner lineageをlegacyどおり選ぶcase。
- clause-link bootstrapが同rootの複数exact carrierを全件保持し、同occurrence/rootのLower/Upperだけをdedupするcase。
- equal-prefix comparator、全tie field、input permutation。
- canonical exact sequenceとarm stable-first sequenceの全admission-order permutation。
- malformed lineage、dangling carrier/premise、canonical order violationが同時にあるerror-precedence fixture。
- canonical duplicate / exact duplicate / incomplete / trivial / evidence-onlyの各zero-parent eventが
  `replay_admissions`へ残り、parent facesは増えないcase。
- new side/arm/root-winner reservationを各点でfailure injectionし、inner stateは全face不変だがouter
  `ReplayAdmissionEvent`だけはexactly one appendされるcase。
- new occurrence準備前の`replay_admissions.len() == N`、inner commit後の`first_event == N`、outer append後の
  event index `N` / len `N + 1`を同時にassertするcase。
- late extension accepted deltaがgeneric replay `ProofOccurrence`を一件追加するcase。
- failed reservation before/after each inner proof-occurrence/occurrence/side/chunk/arm/root-winner/summary reserve。
- 一eventで複数side/chunk/arm/root editがあり、Nth reserve失敗でもlogical state不変なcase。
- exact/association cursor constructorのfrontier reserve failureが`ProofFailure::ResourceExhausted`を返し、iterationまたは
  clause-link mutationを開始しないcase。successful cursorはiteration-time allocation zero。
- exact-parent no-op persistent allocation census。event-required outcomeはeventだけが増えることをface別に確認する。
- no-claim / non-replay-only allocation census。
- count query walk count zero。
- evaluator full exact expansion count zero。clause-link association streamはcall/yield/output countを別計上する。
- portable/logical exact reconstruction parity。
- current first witness/replay event stream、MPC/DPN/PCLF/GWCB/RCPF-history pinned controls。

### 7.3 Model / canonical oracle

side chunk AVL、arm AVL、root-winner AVLのinsert/remove/rekey/replace/rotationは、小さいfinite domainで
reference `BTreeMap`/sorted Vec modelと
exhaustive比較する。

- tree flatten sequence。
- root/key uniqueness。
- height/balance/pivot invariant。
- nonempty chunkとcapacity bound。
- all insert positions。
- split、single-child/two-child remove、rotation。
- arm rekey old absence/new presence。
- root winner insert/replaceとhistorical first-source independence。
- arena reallocation後のID safety。

PCLF-D0のlessonに従い、descendingだけでなくfull chunk middle insertionとcomparator equal-prefixを含める。

### 7.4 Allocation / operation census

`PerformanceIndexAllocationCensus`または専用のtest censusへ次を追加する。

- occurrence arena/key/result index len/capacity。
- replay parent logical len、chunk/node len/capacity、entry boxed bytes。
- side count、side size/chunk count分布。
- arm result bucket/tree/chunk/ref len/capacity。
- canonical root-winner result bucket/tree/chunk/ref len/capacityとdistinct `(result, root)` count。
- non-replay key/entry bytes。
- count/first-source/first-witness summary bytes。
- legacy replay key/result-entry bytes（shadow期間のみ）。
- membership comparisons、chunk lookup、binary search、split/rotation。
- arm insert/remove/rekey comparison、scan/move/split/rotation。
- root-winner lookup/replace/insert comparison、scan/move/split/rotation。
- exact compatibility iterator calls/yields/heap capacity。
- clause-link association cursor calls/yields/dedup/output count、temporary heap capacity。
- exact/association cursor constructor reserve attempts/failures、reserved frontier capacity、iteration-time allocation count。
- evaluator arm cursor calls/yields。
- snapshot writer self-timeとduplicate comparisons。
- replay admission event / generic proof occurrence len/capacityとoutcome別count。inner-failure後eventも別countにする。

temporary prepare scratchはpersistent censusと分離する。parent-only no-op total allocation zeroを主張する場合はallocator counterで
別に測る。replay eventを要求するoutcomeはevent allocationをno-op censusへ混ぜず、parent faces zero-growthを別に報告する。

## 8. 実装slice

各sliceは独立commit・独立rollback単位にする。前sliceのgateを閉じるまで次へ進まない。

### QORF-0: parity / volume / reader census

状態: **実施済み（2026-08-12）**。

変更:

- qualified replayとcurrent CPK finite-map occurrenceのexhaustive parity census。
- occurrence/side distributionとcapacity-inclusive bytes。
- production reader call/yield census。
- snapshot writer comparison/time census。
- iteration topology feasibility review。

Gate result:

- 50,390,357対50,390,357、全field mismatch zero。
- occurrence authority premiseは成立。
- gap Aとgap Bを明示した。
- one-off instrumentation除去、working tree clean。再現手順/raw resultはAppendix Aへ記録した。

### QORF-A: test-only oracle / type boundary

変更:

- §3のside chunk/arm/root-winner ID・prepared delta型をtest-onlyまたはnon-authoritativeに追加する。
- legacy qualified replay finite mapとcurrent finite-map occurrence relationのlinear oracleを、後続sliceから再利用可能な
  `#[cfg(test)]` helperとしてrepositoryへ残す。
- Appendix Aのfull-workload censusを再実行できるretained harnessまたは明示的ignored census testを追加し、
  command/result schemaを固定する。
- §7.2/§7.3 fixtureを追加する。
- production reader/writer/remover censusをcurrent codeで再確認する。
- exact comparator、evaluator dedup位置、validation/error precedenceをcurrent codeへ照合する。
- root-winner、clause-link association、replay event/generic proof occurrence sequence oracleを追加する。
- `apply_cpk_bound_replay_actions`のfailure後event append順、append前lenによる`first_event` formula、
  `begin_non_replay_claim_parent_admission`のgeneric root-winner ownershipをfixtureへ固定する。
- fallible exact/association cursor constructorのAPI/error modelをnon-authoritative typeとして追加する。

Gate:

- production behavior/allocation/epoch zero change。
- QORF-0 exact parityをtargeted synthetic fixtureでも再現。
- arm stable-first equivalenceをsemantic/error precedence込みで証明。
- root-winnerがlegacy first canonical parentと一致し、clause associationが全root/carrierを保持する。
- replay inner failureでもevent `+1`、inner faces不変。`first_event == len_before_append`。
- later structural/reduction-route winner replacementとcursor-construction failure oracle green。
- full-workload parity censusがclean checkoutから再実行可能。
- unlisted remover、physical arrival-order consumer zero。

Stop:

- occurrence payloadがqualified exact valueの全fieldをlosslessに持たない。
- evaluatorが同一occurrenceの二件目以降にroot/side固有semanticを必要とし、compact armでlegacy behaviorを再現できない。

### QORF-B: shadow side-local exact index / inner unified prepare

変更:

- current occurrence lower/upper Vecと並行してside chunk AVLへdual-writeする。
- qualified replay admission、`record_cpk_replay_parent_snapshot`、accepted-delta generic replay proof occurrenceを
  一inner prepared transactionへ統合する。
- `record_replay_admission`はinner rollback set外のouter action appendとして維持し、inner success/failureの後にexactly once呼ぶ。
- new occurrenceの`first_event`はouter append前lenをcaptureして保存する。
- new occurrence bulk build、late extension、split、failure injectionを実装する。
- legacy qualified read/writeはauthorityのまま。
- operation/allocation censusを接続する。

Gate:

- side flatten/value/membershipがlegacy occurrence/qualified keyと全件一致。
- representative/lineage silent first-wins、first witness/first source parity。
- 全dispositionとinner preparation failureのreplay event sequence、new occurrence `first_event == len_before_append`、
  accepted-delta generic proof occurrence parity。
- failed reserveでinner proof occurrence/legacy/finite-map/side/summary partial commit zero、outer eventだけ`+1`。
- 1,800 late singleton fixtureでpayload workがfixed-chunk linear bound。
- std snapshot writerの1,363,997,696 redundant comparisonsがside authority pathでzeroまたはaccepted delta相当へ低下。
- shadow peak RSSが18 GiB safety thresholdへ接近しない。

Rollback:

- side shadowとunified adapterを外し、current finite-map Vec/qualified writerへ戻せる。

### QORF-C: occurrence side authority cutover

変更:

- exact replay qualified membershipをoccurrence key + side chunk indexへ切り替える。
- current finite-map consumersをside cursorへ切り替える。
- current occurrence side Vecはtest oracleへ退役する。
- replay snapshot writerのlinear duplicate rescanを撤去する。
- count/first summariesは既存authorityを維持する。

Gate:

- exact membership exhaustive parity。
- writer admission outcome列、first-wins、error precedence parity。
- RCPF-history/MPC/DPN/PCLF/GWCB pinned controls green。
- exact membership/snapshot writer wall profileにnew regression zero。
- no production linear side scan。

Rollback:

- query adapterをlegacy occurrence Vec/global qualified keyへ戻せる。arm indexはまだauthorityにしない。

### QORF-D0: shadow canonical arm / root-winner projections

変更:

- result-local arm chunk AVLをshadow dual-writeする。
- distinct `(result, root)` canonical winner chunk AVLをshadow dual-writeする。
- root-winner deltaを全variant共通`PreparedQualifiedParentAdmission`へ置き、replay inner transactionと
  `begin_non_replay_claim_parent_admission`の双方からatomic commitする。
- new occurrence insert、late extension no-op/rekey、remove/splitを実装する。
- legacy canonical exact parentからstable-first occurrence oracleを作る。
- fallible exact compatibility k-way cursorをtest/oracle向けに実装する。
- fallible clause-link association streaming cursorを実装するが、production bootstrapはまだlegacy readerを使う。
- evaluatorはlegacy qualified Vecを読み続ける。

Gate:

- arm sequence、root-winner、mixed non-replay sequence、full exact sequence、clause association byte parity。
- later structural/reduction-route admissionがexisting replay winnerよりcanonicalに先行するfixtureでreplacement parity。
- one active arm/occurrence、no stale key、all rekey fixtures green。
- arm refsはoccurrence scale、root winner refsはdistinct `(result, root)` scaleであり、どちらも50M exact-entry projectionを再現しない。
- insert/remove/rekeyがfull result bucket rebuildを行わない。
- replay failure injectionでside/arm/root-winner/legacy inner state不変とouter replay event `+1` parity。
  non-replay root-winner failureではgeneric inner state不変かつreplay event変化zero。

Rollback:

- arm/root-winner shadowだけを除去できる。QORF-C side authorityは不変。

### QORF-D1: evaluator / consumer cutover

変更:

- evaluatorを§3.7 explicit arm/non-replay merge cursorへ切り替える。
- `merge_structural_claim_parents`と`register_constraint_upper_replay_claims`をroot-winner cursorへ切り替える。
- `preflight_claim_parent_clause_links` bootstrapをfallible clause-association streaming cursorへ切り替え、
  constructor failureをexisting `ProofFailure` channelへpropagateする。
- values/carrier/その他materialization consumerを§5.2の最小projectionへ切り替える。
- countはO(1) summaryを維持する。
- portable/logical exact consumerだけを§3.8 fallible full-value cursorへ接続する。
- frame-pointer付きreleaseでcursor/profileを比較する。

Gate:

- evaluator result、first success、first error、cycle/memo、diagnostic order byte parity。
- direct evaluator parent yields 29.46Mからoccurrence-scaleへ低下する。3.03MはQORF-0 observationであり、
  implementation後fresh値を正本とする。
- production normal lowering full-value compatibility cursor call/yield zero。
- clause-association cursor yieldが生成link候補と一致し、root-winner consumerのexact traversalはzero。
- exact/association cursor constructor reserve failureのerror precedence parity、successful iteration-time allocation zero。
- nested adapter/empty product/full materialization frame zero。
- cold wall/RSSに説明不能な回帰zero。
- portable/logical/diagnostic output zero-diff。

Rollback:

- consumer adapterをlegacy qualified Vecへ戻せる。side/arm/root-winner shadowは維持できる。

### QORF-E: replay qualified legacy retirement

変更:

- production `qualified_parent_keys`からreplay entriesを撤去し、non-replay small storeへ縮小する。
- production `qualified_parents_by_result`からreplay full entriesを撤去する。
- replay legacy facesをtest-only reconstruction oracleへ移す。
- 全direct field reader/writerをAPIへ移行する。
- first-source/first-witness summaryは本書の範囲では維持する。

Gate:

- production replay full-key/full-entry cardinality zero。
- replay logical count50,390,357、non-replay30,256、全oracle一致。
- capacity-inclusive final bytesとRSSを§9 gateへ照合する。
- source diffとfield censusにbypass reader/writer zero。

Rollback:

- D1と別commitにし、E単独revertでlegacy dual-writeを復元できる。

### QORF-F: integration / closeout

変更:

- full targeted/pinned/safety-scoped infer suite。
- cold/warm std reproduction、representative corpus。
- final logical/physical count、reader yield、writer self-time、RSS、no-op allocation測定。
- temporary trace/counter除去。
- design docへ実測closeoutを記録する。

Gate:

- intentional known-red以外のnew failure zero。
- exact/portable/logical/diagnostic zero-diff。
- §9のminimum structural/numeric gate。
- working tree/temporary artifact clean。

## 9. 性能・memory gate

### 9.1 Baseline discipline

QORF implementation開始前にcurrent clean HEADでcold std reproductionを最低二回行い、同じrelease flags、cache、RSS monitor、
host load条件のmedianを正式baselineにする。profile buildとmeasurement buildを混同しない。

既測定の25〜31% self-time cluster、6.318〜6.599s snapshot writer、3.32 GiB qualified storageはQORF-0 evidenceであるが、
landing後改善を先取りしたpromiseではない。

### 9.2 Structural gate

QORF-E完成形で次を満たす。

1. replay full `QualifiedParentKey` persistent entry zero。
2. replay full `ExactQualifiedParent` canonical persistent entry zero。
3. logical replay parent50.39M件はcurrent finite-map side payloadからlosslessに列挙可能。
4. exact membershipはglobal50M hashではなくside-local bounded search。
5. evaluator canonical projectionは一occurrence一compact arm。
6. hot evaluator/count/admission/first-source/root-winner materializationのfull exact expansion zero。
7. clause-link bootstrapのnecessary exact associationはstreamingであり、eager full collection zero。
8. late extensionでside/result全体のclone/re-sort zero。
9. first-wins summaryをcanonical iterationから再計算しない。
10. root-winner projectionはdistinct `(result, root)` scaleで、exact-parent scaleへ膨らまない。
11. 全dispositionとinner preparation failureのreplay event、append前lenを指す`first_event`、accepted-delta generic proof occurrenceがlegacyと一致する。
12. structural/reduction-route30,256件のexact semantics不変。
13. explicit cursorにnested empty-product traversal zero。
14. exact/association cursorはfallible construction、successful iteration-time allocation zero。

### 9.3 Memory target

measured upper-bound opportunityは次である。

```text
retirable replay qualified faces = 3,507,222,516 bytes = 3.266356 GiB
already-required CPK finite map = 1,073,022,160 bytes = 0.999330 GiB
```

new side chunk nodes、arm index、root-winner index、small non-replay storeのcapacityは未実装のため**要検証**である。

段階gate:

- QORF-B/D0 shadowでlegacy/new faceを別々にcapacity-inclusive測定する。
- new persistent overheadはretirable3.266 GiBの25%未満をminimum design gateとする。これは**目標値**であり未測定。
- QORF-Eのnet retained reductionは2.0 GiB以上をminimum、2.5〜3.1 GiBをproject target（**推定**）とする。
- arm refは865,571件scaleであり、50,390,357件scaleへ増えた時点でstopする。
- root-winner refはdistinct `(result, root)` scaleである。QORF-0のexisting first-source key domainは1,792,654件だが、
  QORF-A retained censusとQORF-D0でfresh countを再確認し、exact-parent scaleへの増幅をstop conditionとする。
- peak RSSはclean pre-QORF baseline比で増やさず、shadow期間は18 GiB hard killを使う。

`ReplayFiniteMapEntryId` payloadだけなら865,571 × 4 bytes ≈ 3.30 MiBだが、tree node、boxed chunk、map capacity、allocator
overheadを含まない**推定下限**にすぎない。これをarm indexの実byte数として報告しない。

### 9.4 Wall target

25〜31% clusterを全て消せるという主張はしない。logical parent payload50.39M件は残り、side bulk build、first-wins、
summary、exact portable outputにはnecessary workがある。

段階target:

- QORF-B/C: snapshot writerの1.364B linear duplicate comparisonsを除き、6.3〜6.6s inclusive writer costを明確に減らす。
  全6.3〜6.6sが消えるとは仮定しない。
- QORF-D1: evaluator inspected/yield volumeをoccurrence-scaleへ下げ、QORF-0の約89.7% source reductionをfresh censusで再確認する。
- minimum project success: clean baseline比parse 8%以上、full command 5%以上、RSS非増加、output zero-diff。
- realistic target（**推定**）: parse 10〜18%改善。
- stretch target（保証しない）:25〜31% clusterの大半を除く20〜25%改善。

PCLFの三failed attemptと同様、correctness parityだけでwall gateを閉じない。authority cutoverごとにframe-pointer profileを取り、
new tree comparator、arm/root-winner cursor、clause-association/exact compatibility iterator、allocatorが新dominantになっていないことを確認する。

### 9.5 Operation/count target

logical countは変えない。

```text
replay exact parents = 50,390,357
non-replay parents   =     30,256
occurrences          =    865,571
```

完成形のpersistent projectionは概ね次に比例する。

```text
exact replay payload:          O(50,390,357)  // current finite-map side payload
occurrence identities:         O(865,571)
canonical replay arm refs:     O(865,571)
canonical root winner refs:    O(distinct (result, root))
non-replay exact flat entries: O(30,256)
first-source/witness summaries: existing measured cardinality
```

replay full hash keyとfull canonical entryの追加`O(50,390,357)` faceをzeroにする。

## 10. 棄却案

### 10.1 現行qualified storageを維持する

棄却する。

- exact parityでsame relationの二重authorityと確認した。
- 3.266 GiB removable faceを残す。
- 50M scattered hash writeとcanonical full-entry mergeを残す。

### 10.2 Hash algorithmだけを交換する

単独解として棄却する。

- accepted99.812%はgenuine insertionである。
- profile/censusはhash computationだけでなくscattered write localityとcanonical payload maintenanceを示す。
- full key/value cardinalityと3.32 GiBを減らさない。

### 10.3 Reserve tuningだけで閉じる

単独解として棄却する。

- first-source temporary over-reserveはbounded fixとして有効だが、persistent50.39M full-key/full-entryを減らさない。
- under-reservationはqualified clusterの主因ではなかった。

### 10.4 Compact global `(occurrence, side, root)` hashを置く

移行oracle候補としても慎重に扱い、完成形として棄却する。

- keyを28 bytesから縮めても50.39M hash entries/scattered writesを残す。
- current finite-map side payloadと同cardinalityのsecond authorityを作る。
- QORFの主要なlocality/footprint目的を半分失う。

side-local chunk membershipが実profileで不可能と判明した場合、compact global hashは別revisionのoptionとして再評価する。

### 10.5 Current side Vecのlinear scan

棄却する。

- measured maxはlower97/upper96だが、current finite-map contractにhard upper boundはない。
- late extensionやadversarial sourceでunbounded linear membershipになる。
- snapshot writerは既に1.364B comparisonsを実測した。

### 10.6 Sorted single Vec + binary search

完成形として棄却する。

- lookupは改善するが、repeated late singleton insertionがside lengthに比例してshift/mergeする。
- PCLF-D0で同じ形のquadratic worst caseが実証された。
- full-side rebuild禁止を構造的に満たさない。

### 10.7 50.39M canonical incidence ID projection

棄却する。

- full payloadより小さくてもlogical incidenceと同cardinalityのsecond ordered faceを作る。
- evaluatorについては一occurrence一armで十分とcurrent code reviewで確認したが、root materializationとclause-link bootstrapには
  §3.6/§3.8の別projectionが必要である。
- persistent footprintとwrite bandwidthを温存する。

### 10.8 Query-time full sort/materialization

棄却する。

- evaluator1,964,985 callsで50M relationを繰り返し展開する。
- PCLF-Dのnested/reconstruction regressionを別relationで再現する。
- error precedenceとallocation failure orderingを不安定にする。

### 10.9 Occurrence admission orderをcanonical orderとして使う

棄却する。

- measured/current physical layoutはfirst occurrence admission、次にLower/Upper arrival orderである。
- required qualified orderはcoverage root、carrier、side、representative claimで一致しない。
- output/evaluator orderを変更する。

### 10.10 Carrier-only arm order

棄却する。

- legacy canonical exact sequenceはroot-firstであり、same result内occurrenceのfirst appearanceもminimum rootに依存する。
- late smaller rootでrelative orderが変わる。
- error/first-success order parityを壊す。

### 10.11 Nested occurrence × side × parent adapter

hot evaluator案として棄却する。

- exact iteratorには使えてもevaluatorが50M parentsを再訪する。
- generic nested adaptersはPCLF-Dで実測済みのregression riskを持つ。
- hot pathはarm cursor、exact pathは明示heap cursorへ分離する。

### 10.12 Standard `BTreeMap`へ直接移行する

現時点の完成形として棄却する。

- ordered membership/iterationは得られるが、current Rust APIでは全node allocationをprepareでfallible preflightしにくい。
- commit-time allocation failureとtransaction atomicityを説明できない。
- custom fixed chunk arenaはreservation pointとmovement boundを明示できる。

### 10.13 First-source / first-witnessも同時に統合する

棄却する。

- exact parent parityは確認したが、二summary間の全field/winner parityは本censusのgo/no-go条件ではない。
- first-wins bugはportable/lineageへ直結する。
- 60.6 MiBを得るため3.266 GiB migrationのscopeを広げない。

### 10.14 Structural/reduction-routeも同時にfactorizeする

棄却する。

- 30,256件、全体の約0.06%にすぎない。
- replay occurrenceへ自然に写らない別identityである。
- benefitに比してrollback/correctness scopeが広がる。

### 10.15 Occurrence armを全materializationの代表にする

棄却する。

- armはoccurrence全体のglobal minimum parentしか表さない。
- 別rootのfirst canonical parentが別occurrenceとの比較でwinnerになるcaseを落とす。
- `merge_structural_claim_parents` / `register_constraint_upper_replay_claims`のlineageと、
  `preflight_claim_parent_clause_links`の全root/carrier associationを再現できない。

evaluator限定ではarmを採用し、root winnerとexact associationを別lower-bound projectionへ分ける。

### 10.16 Historical first-source / first-witnessをcanonical root winnerに使う

棄却する。

- historical first-winsはarrival streamの最初、canonical winnerはexisting comparatorのminimumである。
- 両者が一致する保証はなく、later accepted carrierがcanonicalに先行しうる。
- canonical winnerの更新でhistorical provenanceを上書きしてはならない。

## 11. Stop / rollback conditions

### 11.1 Stop conditions

次のいずれかが判明した時点でimplementationを止め、Claude/userの設計レビューへ戻る。

1. qualified replayとcurrent CPK finite-map occurrenceのexact finite mapに一件でもmissing/extra/field mismatchが出る。
2. representative claimまたはlineageをoccurrence side payloadからlosslessに得られない。
3. current production consumerがfinite-map side Vecのphysical arrival orderをsemantic identityとして必要とする。
4. exact parent removal/reclassification、または保存済みrepresentative claim/lineage replacement pathがあり、append-only planで扱えない。
5. side-local chunk membershipがcurrent exact duplicate/error precedenceを再現できない。
6. evaluatorが同一occurrenceの二件目以降にroot/side固有semanticを必要とし、一arm collapseがlegacy behaviorを再現できない。
7. existing comparatorからoccurrence armのstable total `first_key`を構成できない。
8. late smaller rootのarm rekeyを、same-event allocation-free/partial-publication-freeに行えない。
9. canonical exact sequence、canonical root winner、clause-link association、またはmixed replay/non-replay sequenceが
   legacyとbyte-equalにならない。
10. canonical orderのため50.39M-entry persistent ordered projection、eager query-time full sort/materialization、global repair、
    delayed rekeyが必要になる。exact-output consumerの明示streaming traversalはこのstopに含めない。
11. exact membershipのため50.39M-entry global hashを完成形へ残す必要がある。
12. side/chunk/arm/root-winner mutationがfull side/result bucket rebuildまたはadversarial quadratic movementを必要とする。
13. inner capacity failureでgeneric proof occurrence、finite-map occurrence、qualified legacy、arm/root-winner、
    first-wins summaryのlogical partial commitが起きる、またはouter replay eventが一件appendされない。
14. semantic validation/error precedenceを保つためresource allocationを先に行う必要がある。
15. exact-parent no-op/no-claimでparent facesが増える、またはrequired zero-parent replay eventが欠落する。
16. production normal loweringでfull-value exact compatibility iteratorが非zeroになる。clause-link association cursorは
    output-bound streaming用途に限定し、eager collectionまたは別consumerから呼ばれた時点でstopする。
17. arm/side cursorにnested empty-product adapterまたはper-query full materializationが現れる。
18. QORF-B/D0のnew overheadが§9.3 gateを超え、net savingが2.0 GiB未満になる。
19. QORF-C/D1のcold wall/RSSがclean baseline比で説明不能な回帰を示す。
20. snapshot writerのlinear duplicate comparisonsが残るか、別のtree comparator/rotationがnew dominantになる。
21. current first witness/replay event/first_event、RCPF-history guard、PCLF formula、MPC/DPN/GWCB/URR pinned invariantがshiftする。
22. portable/logical/diagnostic outputの期待値変更が必要になる。
23. production/test direct field reader/writerを全列挙できない。
24. authority cutoverとlegacy retirementを独立rollbackできない。
25. logical count削減とphysical projection削減を混同しなければ性能gateを説明できない。
26. structural/reduction-route admissionがgeneric root-winner transactionを通らず、later canonical winner replacementが
    replay pathとatomicにならない。
27. exact/association cursorがconstruction failureを`ProofFailure`で返せない、またはsuccessful `next()`中にallocationする。
28. portable/logical/clause-link consumerがcursor construction failureを既存error channelへpropagateできず、empty result、panic、
    output変更のいずれかを必要とする。

### 11.2 Rollback units

- QORF-A oracle/fixtureは正しい観測である限り保持する。
- QORF-B side shadow/unified prepareはauthority cutover前に単独削除できる。
- QORF-C side authority adapterはD0 arm/root-winner indexから独立にlegacyへ戻せる。
- QORF-D0 arm/root-winner shadowはside authorityを変えず単独削除できる。
- QORF-D1 consumer cutoverはarm/root-winner writerから独立にlegacy readerへ戻せる。
- QORF-E legacy replay retirementはD1と別commitにし、E単独revertでdual-writeを復元できる。
- rollbackでRCPF-history/PCLFの既修正を旧flat/coarser semanticsへ戻さず、retired RCPF occurrence surfaceを復活させない。

## 12. Claude 査読時の必須確認事項

Claude (Sonnet 5) は本書を確定する前に、少なくとも次をcurrent codeへadversarialに再照合する。

1. QORF-0の50,390,357対50,390,357 parity identityが全`ClaimQualifiedParent` replay constructor、ReplayEvidence lineage、
   lower/upper pathを覆うか。
2. `QualifiedParentKey` / `ExactQualifiedParent`のactual field、size、canonical comparatorが§1/§3の記述と一致するか。
3. `register_cpk_replay_claim_parents` / `record_cpk_replay_parent_snapshot`のinner transactionがsuccess/failureを返した後も、
   `apply_cpk_bound_replay_actions`が`record_replay_admission`をexactly once呼ぶcurrent順を維持するか。
4. canonical duplicate、exact duplicate、incomplete、trivial、evidence-only、zero accepted、inner preparation failureの各eventが残り、
   inner capacityだけがinner logical mutation前にpreflightされるか。eventをinner rollback setへ誤って含めていないか。
5. new occurrenceの`first_event`がappend前`replay_admissions.len() == N`、後続eventのzero-based index `N`であり、
   post-append length `N + 1`を保存していないか。
6. current finite-map side Vecのarrival orderを直接/間接に読むconsumer、test fixture、portable/logical snapshotを漏らしていないか。
7. coverage rootがoccurrence+side内でuniqueなmembership keyであり、later representative/lineage conflictを
   currentどおり比較せずsilent first-winsで扱うか。
8. side-local chunk AVLのtotal order、pivot、split/rotation、arena ID safety、128 bound、fallible allocationがPCLFの既検証patternと
   同じhard contractを満たすか。
9. standard/global compact hashを持たず、bounded logarithmic membershipへ変えることが実call volumeで性能回帰を起こさないか。
10. legacy canonical exact sequenceからstable-first occurrenceを取る操作が、actual evaluatorのlower/upper-only semanticsと
   byte-equivalentか。将来root/side固有validationが追加された場合にoracleが検出するか。
11. `first_key(occurrence)`がexisting comparatorの全fieldを含むtotal keyであり、equal key/admission-order tieを作らないか。
12. late extensionでnew smaller rootがlower/upperどちらへ入ってもarm rekeyが必要十分で、old/new tree invariantを同時に保てるか。
13. arm AVL deletion（empty chunk、single/two-child、rotation）とprepared reinsertionがcommit-time allocationなしで動くか。
14. root-winner projectionが`merge_structural_claim_parents` / `register_constraint_upper_replay_claims`のactual canonical winnerを
   各rootで再現し、historical first-source/witnessを代用していないか。全variant共通generic planが
   `begin_non_replay_claim_parent_admission`も覆い、later structural/reduction-route winnerをatomicにreplaceするか。
15. root-winner cardinalityがdistinct `(result, root)` scaleで、exact parent scaleへ膨らんでいないか。
16. clause-link association cursorが全`(root, exact carrier)`を保持し、winner一件やarm一件へcollapseしていないか。
17. replay arm/non-replay two-way cursorがmixed canonical order、first success、first errorを変えないか。
18. exact/association k-way cursorがfallible constructorでfrontier capacityを全確保し、failureを`ProofFailure`へ返し、
   successful iteration中allocationせず、full-value normal loweringから呼ばれないAPI境界か。
19. count、values、carrier、materialization各readerが必要最小projectionへ移り、count O(1)とfirst-wins summaryを維持するか。
20. all inner reserve/failure injection pointがproof occurrence、legacy shadow、finite-map side、arm/root-winner、summaryの
   partial commit zeroとouter event `+1`の双方を検出できるか。
21. side/arm/root-winner chunk/node/capacityを含むfresh physical bytesが§9.3 targetを満たし、3.266 GiBをgross savingのまま
   netとして報告していないか。
22. frame-pointer profileでqualified insertion cluster、snapshot writer、evaluator/root-winner/association cursorが実際に減り、
   新dominant tree/heap costがないか。
23. structural/reduction-route30,256件がsmall flat storeへ完全に残り、replay occurrenceへ誤投影されないか。
24. first-source summaryとcurrent first replay witnessを未検証で統合していないか。
25. PCLF/GWCB/MPC/DPN/RCPF-history/URR、portable/logical/diagnostic、proof inventoryのmigration manifestをslice gateへ含めたか。
26. Appendix Aのcensusをclean checkoutから再実行でき、QORF-A retained oracleが同じidentity/value schemaを使うか。
27. safety-scoped suiteの`--test-threads=4`、documented skip list、18 GiB RSS hard kill、wall timeoutをcloseoutへ明記したか。
28. production legacy retirement前に全direct reader/writer censusがzeroで、test oracleだけが`#[cfg(test)]`に残るか。

項目1〜17はdesign approval前にcurrent codeとmodelへ照合する。項目18〜22はAPI/algorithm contractをapproval前に査読し、
actual count/bytes/profileはQORF-B〜D1のmandatory gateとする。項目23〜28はmigration/closeout planを査読し、
該当slice gateを満たす前にlegacy retirementへ進まない。一件でも反例または未割当consumerがあれば本書を確定せず、
該当representation/sliceを改訂する。

## Appendix A. QORF-0 parity census の再現手順とraw result

### A.1 Workload / invocation

QORF-0は基準commit `acdd4246`付近のclean release buildへtemporary env-gated censusを入れ、sessionで共通に使った
`std::text::parse` cold lowering workloadを一回実行した。

```bash
timeout 1200s bash -lc \
  "printf '1 + 2\\n' | \
   YULANG_INFER_TIMING=files \
   YULANG_QORF_CENSUS=1 \
   target/release/yulang dump-poly-std /dev/stdin"
```

external cacheは同sessionのcold baselineと同じ手順で無効化し、process RSSを18 GiB hard-kill monitor下で観測した。
temporary `YULANG_QORF_CENSUS` branchは測定後に除去したため、このcommandだけではcurrent clean checkoutにcensusが現れない。
この再現性gapを閉じるため、QORF-Aは次節のalgorithmを実装するretained `#[cfg(test)]` helperと、full stdを明示的に走らせる
`#[ignore]`またはenv-gated harnessをcommitすることを必須deliverableとする。harness名、command、raw output schemaは
QORF-A commit messageと本Appendixへ追記する。

### A.2 Exact comparison procedure

qualified faceから次のfinite mapを作る。

1. `qualified_parents_by_result`の全result bucketを走査する。
2. `ExactQualifiedParent.parent`が`ClaimQualifiedParent::ReplayConstraint`のentryだけを選ぶ。
3. `coverage_root`は`ExactQualifiedParent.coverage_root`を使う。
4. `representative_claim`は`ReplayConstraint.parent_claim`を使う。
5. `lineage`は同じclaim IDをcurrent upper-claim arenaへ引き、`ProjectionLineage`へ写す。
6. key/valueを次で作る。

```text
key   = (result, exact BinaryReplayDerivation, parent_side, coverage_root)
value = (representative_claim, ProjectionLineage)
```

current CPK finite-map faceから同じfinite mapを作る。

1. `ProofOccurrenceStore::replay_finite_map`の全`ReplayProofOccurrence`を走査する。
2. `lower_parents`はexpected side Lower、`upper_parents`はexpected side Upperとして走査する。
3. 各`ReplayProofParent.side`がcontainer expected sideと一致することを別counterで確認する。
4. occurrenceの`result/carrier`とparentの`coverage_root/representative_claim/lineage`から同じkey/valueを作る。
5. 同一keyの二回目insertをduplicate occurrence entryとして数える。

比較はHashMap iteration順で行わず、次を独立に報告する。

- qualified replay entry count。
- finite-map replay parent count。
- qualified-only key countと最初のkey/value。
- finite-map-only key countと最初のkey/value。
- common key value mismatch countと最初の両value。
- side/container mismatch count。
- duplicate finite-map key count。
- lineage mismatch count。

QORF-A retained oracleは、targeted event境界では両mapの直接equality、full std harnessでは終了時全件equalityを行う。
deterministic checksumを追加する場合は、上のkey/valueを全stable fieldの辞書式順にsortしてから計算し、hash iterationや
debug addressを入力へ含めない。QORF-0 one-off runではchecksumを記録していないため、未測定値を本書へ捏造しない。

### A.3 Recorded raw result

```text
qualified replay entries       = 50,390,357
finite-map replay parents      = 50,390,357
qualified-only keys            = 0
finite-map-only keys           = 0
common-key value mismatches    = 0
lineage mismatches             = 0
side/container mismatches      = 0
duplicate finite-map entries   = 0
```

同じrunでoccurrence count `865,571`、parents/occurrence mean `58.216318476`、p50 `29`、p95 `133`、max `161`を記録した。
このraw resultは設計premiseのhistorical artifactであり、QORF-A retained oracleの代用ではない。future rerunが一件でも異なる
logical relationを示した場合、expected countを更新してgreenにせず、writer/corpus差を説明するまで§11 stop condition 1を適用する。

---

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定。

承認状態: **ユーザ承認済み**。本書は`CLAUDE.md`の設計優先順位における正本である。
QORF-A以降の実装は、本書のinvariant・stop condition・スライス順序に従って着手できる。
