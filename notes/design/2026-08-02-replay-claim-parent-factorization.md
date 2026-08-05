# replay claim-parent relation の factorization

日付: 2026-08-02

状態: **ユーザ承認済み**

本書は、replay由来のclaim-parent relationを、意味論を変えずにfactorized representationへ移行する設計判断である。

対象は`std::text::parse`のloweringで観測された約5,042万件のclaim-parentと約2,852万件のexact clause-linkである。exact carrierやproof clauseを意味的に併合する設計ではない。異なるcarrierへ同じendpoint parent集合が物理コピーされているrelationを正規化し、consumerが必要とするprojectionを別々に維持する。

調査基準は`56035b8d`。コード行番号はこの基準付近を指し、実装中にずれた場合は関数名を正本とする。

略称として、本設計をRCPF（Replay Claim-Parent Factorization）と呼ぶ。

## 1. 決定要約

### 1.1 採用する完成形

次の二つを一体として採用する。

1. **Exact occurrence + immutable parent-set snapshot**
   - exact `(result, replay carrier)`に`ReplayOccurrenceId`を与える。
   - occurrenceのLower/Upper各sideは、admission時に確定したimmutableな`ParentSetVersionId`を参照する。
   - parent-setの意味内容は、canonical root membershipをdomain、各rootについてlegacy admission streamが選んだfirst representative claimを値とする、次のunorderedな有限写像である。
     ```text
     coverage_root -> representative_claim
     ```
   - 同じroot membershipとrepresentative claim写像をcarrierごとにコピーしない。
   - entry permutationや、そのwinner選択に至ったadmission順序自体はpersistent parent-set identityへ含めない。
   - logicalな`(result, root, side, carrier)`relationと、各exact keyのrepresentative claimはlosslessに列挙・membership判定できる。

2. **Consumer別summary**
   - evaluatorは一つのreplay carrierをroot数に関係なく一回だけ評価する。
   - upper claim materializationは`(record, root)`単位で処理する。
   - projection proofはroot集合とexact carrier集合を別々に読む。
   - clause evaluatorはcarrierごとの`ReplayConjunction`を保持する。
   - flat fail-openは`(lower_record, root)`のattribution summaryを読む。
   - portable provenanceはfactored relationからexact occurrenceを遅延列挙する。

Bだけでは、consumerが毎回factored relationを展開した時点でコストが戻る。Cだけでは、losslessなexact provenanceを保持できない。従ってB+Cを同じ完成形として設計する。

### 1.2 変更しない意味論

次は不可侵とする。

- `BinaryReplayDerivation`の全field:
  - `pivot`
  - `lower`
  - `upper`
  - `rule`
- logical exact key:
  ```text
  (result, canonical coverage root, parent side, exact replay carrier)
  ```
- lower/upper parent sideの区別。
- admission時点で選ばれたcanonical root集合。
- 各exact keyについて、legacy admission streamのfirst-winsで選ばれたrepresentative claimの値。
- `(result, root)`について、legacy admission streamのfirst-winsで選ばれたfirst witnessの値。
- representative claimとfirst witnessの選択結果は不変とするが、その選択に至った入力順列や処理順序自体はpersistent identityの一部としない。
- covered/uncovered判定。
- incremental row routeがgeneric replay側から除外される規則。
- first accepted parent claimがderived claimの代表lineageになる可能性。
- MPCのoccurrence→clause帰属。
- `ReplayConjunction = eval(lower premise) AND eval(upper premise)`。
- DPNの`ProofPremise`三ソートとconstraint/root評価。
- DPN cycle追補のtri-color cycle cutting。
- A1 exact no-op、A3 round境界、A4 natural-event batch境界。
- admission時完全性。
- no-claim passthrough。
- `scheme_projection_lower_record_memberships`によるreverse-index membership。

### 1.3 精密化する既存決定

CDM D1は、当時のmigration範囲では`claim_parents_by_constraint`の最終内容をbyte単位で維持した。RCPFはCDMが§5.3で先送りしたexact-occurrence store/summary分離を正式に再開する。

RCPF最終cutover後は、CDM D1の物理的なflat Vec保存要件を次へ精密化する。

```text
expanded exact relationの集合
+ 各exact keyのfirst representative claim
+ admission時完全性
+ portable provenanceの決定的列挙
```

これらは不変とする。一方、5,000万件の`ClaimQualifiedParent`をflat Vecとして常設すること自体は契約から外す。

この精密化はexact carrier identityを粗化しない。CDMが修正したcarrier conflation bugを再導入しない。

### 1.4 今回は扱わないもの

- lower×upper carrier自体の意味的dedup。
- solver全体のpivot graph化。
- bound dominance規則の追加。
- structural/reduction-route parentのfactorization。
- claim identity、coverage、livenessの変更。
- evaluator結果の恒久cache。
- metadata-only provenance epoch監査の決着。
- portable provenanceの公開形式変更。

## 2. 実測による問題設定

### 2.1 最終ledger census

`std::text::parse` lowering完了時点の測定値は次のとおり。

| 項目 | 最終値 |
|---|---:|
| `constraint_records.len()` | 143,157 |
| `bounds.records.len()` | 231,703 |
| `upper_replay_claims.len()` | 1,716,791 |
| claim-parent総数 | 50,416,990 |
| replay claim-parent | 50,386,734 |
| structural claim-parent | 30,127 |
| reduction-route claim-parent | 129 |
| unique qualified carrier | 878,089 |
| projection proof総数 | 1,716,034 |
| exact clause総数 | 847,758 |
| Standalone clause | 21,342 |
| DerivedUnary clause | 8,761 |
| ReplayConjunction clause | 817,655 |
| exact clause-link | 28,524,776 |
| dependency edge | 1,658,682 |

claim-parent総数をunique qualified carrier数で割ると、

```text
50,416,990 / 878,089 = 57.4167...
```

となる。

この57.42は「一つのlower recordに57個のupper recordがある」という意味ではない。`BinaryReplayDerivation`は既に一つのlower recordと一つのupper recordを固定している。57.42は、一つのqualified carrierへ平均何個の`root/side`membershipが付与されたかを表す集約値である。

### 2.2 exact clauseとsemantic clause

semantic truth keyによる再集計結果は次のとおり。

| clause kind | exact | semantic unique |
|---|---:|---:|
| Standalone | 21,342 | 17,999 |
| DerivedUnary | 8,761 | 8,761 |
| ReplayConjunction | 817,655 | 817,655 |
| 合計 | 847,758 | 844,415 |

全体の圧縮率は、

```text
847,758 / 844,415 = 1.00396...
```

にすぎない。

全clauseの96.45%を占めるReplayConjunctionでは、exactとsemanticが完全一致した。従って、carrierの`pivot`や`rule`をkeyから外すだけのtruth-layer dedupには性能余地がない。

この測定が否定するのは「異なるexact carrierが同じpremise pairを大量に重複保持している」という仮説である。「異なるcarrierが同じendpoint parent集合を共有している」というrelation factorization仮説は否定しない。

### 2.3 admission census

clause-link admissionの測定値は次のとおり。

| 項目 | 回数 |
|---|---:|
| attempt | 98,425,569 |
| existing exact duplicate | 48,973,040 |
| batch内duplicate | 20,949,095 |
| 実insert | 28,503,434 |

割合は概算で次になる。

- existing duplicate: 49.76%
- batch内duplicate: 21.28%
- insert: 28.96%

A1/A4は不要なinsertとbefore/after評価を削減したが、logicalに新しいlinkだけで約2,850万件残った。

### 2.4 evaluator census

`flat_fail_open`の測定値は次のとおり。

| 項目 | 値 |
|---|---:|
| call数 | 7,907,822 |
| proof数P 平均 | 32.95 |
| P p50 / p95 / max | 22 / 69 / 97 |
| link数K 平均 | 412.73 |
| K p50 / p95 / max | 125 / 1,541 / 4,700 |
| 実比較回数 | 12,620,754,599 |

proofやclauseの数だけではなく、supportとexact linkのincidenceを繰り返し比較する構造が支配している。

### 2.5 問題の正確な形

carrier `c`について、admission時に捕捉されたlower-side root集合を`Rₗ(c)`、upper-side root集合を`Rᵤ(c)`とする。

現行のreplay claim-parent数は概ね、

```text
Nparent = Σc (|Rₗ(c)| + |Rᵤ(c)|)
```

となる。

同じrootが両sideに存在する場合、sideがidentityに含まれるため二件になる。

問題は、`Rₗ(c)`や`Rᵤ(c)`が多くのcarrier間で同じ、または大きく重なっていても、各tupleを独立したHashSet/Vec entryとして保持・処理している点にある。

### 2.6 RCPF-0 / RCPF-0b parent-set census

RCPF-0では、parent-set identityへ含める情報を変えた場合のphysical entry数を、同じ`std::text::parse` workloadで比較した。

| 構成 | 実測結果 | §12.3判定 |
|---|---:|---|
| root membershipのみ | logical replay parent比0.95% | PASS |
| `coverage_root -> representative_claim`のunorderedな有限写像 | unique entry 4,169,215件、logical replay parent比8.27% | PASS |
| root membership層と上記写像の合計 | 4,648,988件 | PASS（5,038,674件未満） |
| `ParentSetEntry { root, representative_claim }`とfirst-admission順序 | logical replay parent比15.52% | FAIL |

root membershipだけなら十分に小さいが、first representative lineageを保持できないため完成形にはならない。一方、representative claimのwinner値まで含めても、entry permutationをidentityから外せば§12.3の10%未満を満たす。

RCPF-0bでは、次の代替構成を測定した。

```text
global (result, root) representative default
+ carrier-specific override
```

override率は95.37%であり、overrideを疎に保てなかった。physical entryはlogical replay parent比12.05%となり、§12.3をFAILした。

従って、global default＋overrideは採用しない。RCPFのpersistent parent-set identityは、root membershipをdomain、legacy admission streamが選択したrepresentative claimを値とするunorderedな有限写像とする。admission順序はwinner確定までの処理上の入力であり、persistent identityには含めない。

このcensusはparent-set表現の採否だけを支持する。wall time、RSS、attachment数、consumer切替後のoperation countについては、引き続き§12の各gateで判定する。

## 3. 現行データフロー

### 3.1 データ構造

`crates/infer/src/constraints/mod.rs:1414`付近の`TypeBounds`は、現在次を別々に持つ。

```text
claim_parents_by_constraint
qualified_carrier_index
replay_claim_parent_keys
scheme_projection_claims_by_lower_record
projection_proofs_by_lower_record
record_proof_clauses
record_proof_clause_by_key
record_proof_clause_links_by_lower_record
record_proof_clause_link_keys
dependent_records_by_premise
```

replay parent一件は、

```rust
ClaimQualifiedParent::ReplayConstraint {
    parent_claim,
    parent_side,
    replay,
}
```

として`claim_parents_by_constraint[result]`へappendされる。

dedup keyは、

```rust
ReplayClaimParentKey {
    result,
    coverage_root,
    parent_side,
    replay,
}
```

である。

### 3.2 新規lowerのreplay

`add_lower_bound`（`machine/bounds.rs:424`付近）は、`bounds.add_lower`後に`semantic_changed`を確認する。意味的に新しくないlowerはreplay pairを生成しない。

意味的に新しいlowerは`lower_bound_replay_actions`（`:2064`付近）へ進む。

処理は次の形になる。

```text
new lower record
    ├─ lower_record_replay_claim_parents(lower)
    └─ for each existing projection upper:
           upper_record_replay_claim_parents(upper)
           combined = clone(lower parents) + upper parents
           carrier = (pivot, lower, upper, LowerBoundAdded)
           canonicalize consequence
```

`projection_upper_records`はordinary upperとevidence upperの両方を含む。

upper-side parent選択は、

- uncovered claims
- lower endpointが変数の場合のcovered claims
- incremental routeが既に扱うclaimの除外

を含む。

従ってsnapshotは単なる`claims_by_upper_record`のlive viewではない。イベント固有のfilter結果である。

### 3.3 新規upperのreplay

`add_upper_bound`（`:618`付近）は、upper alias-cycle subsumption、既存upperによるsubsumption、pruningを行う。

意味的に新しく、generic replayが必要なupperだけが`upper_bound_replay_actions`（`:2225`付近）へ進む。

```text
new upper record
    ├─ uncovered_upper_replay_claim_parents(upper)
    └─ for each existing projection lower:
           combined = lower parents + clone(upper parents)
           carrier = (pivot, lower, upper, UpperBoundAdded)
           canonicalize consequence
```

lower-side parent集合はlower recordごとに異なるが、new upperのparent集合は全carrierで共通する。

### 3.4 canonicalizationとprovenance retention

`push_replay_constraint_or_prefilter`（`:2276`付近）はpairを以下へ分類する。

- new semantic constraint
- canonical duplicate
- evidence-only
- trivial

canonical duplicateはsemantic queueへ再投入されないが、exact replay derivationとclaim-parentは保持される。

```text
apply_bound_replay_actions
    -> enqueue_replay_subtype
    -> register_replay_claim_parents

apply_prefiltered_replay_provenance
    -> merge_replay_derivation
    -> register_replay_claim_parents(materialize_existing_target = true)
```

trivial actionは`ReplayDropRecord`だけを保持し、claim-parentを登録しない。

### 3.5 claim-parent登録

`register_replay_claim_parents`（`:1729`付近）は、parentごとにcoverage rootを取得し、4成分exact keyをinsertする。

新規keyでは、

```text
admit_claim_qualified_parent
    ├─ claim_parents_by_constraintへappend
    ├─ qualified_carrier_indexへinsert
    ├─ dependency route edge登録
    └─ before/after inclusion publication
```

を行う。

queue-suppressed duplicateでは後続のconstraint admissionがないため、`materialize_existing_claim_parents_delta`（`:1779`付近）へ新規parent deltaを渡す。

### 3.6 projectionとclause-link

差分は次の二方向へ流れる。

```text
upper:
    register_constraint_upper_replay_claims_delta
    -> derived claimを(record, root)単位でmaterialize

lower:
    register_constraint_projection_carrier_delta
    -> update_scheme_projection_proofs
    -> register_claim_parent_clause_links
```

`register_claim_parent_clause_links`（`:875`付近）は、Replay parentを次へ変換する。

```text
support = Claimed(canonical root)

clause = ReplayConjunction {
    carrier,
    lower_premise: carrier.lower,
    upper_premise: carrier.upper,
}
```

A4後は同一lower record・同一admission eventのlink列を一batchでcommitする。

### 3.7 評価側

`SchemeProjectionEvaluator::eval_constraint_uncached`（`constraints/mod.rs:863`付近）は、現在`claim_parents_by_constraint[constraint]`を全走査する。

Replay parentでは`parent_claim`と`parent_side`を真偽判定に使わず、

```text
eval(replay.lower) && eval(replay.upper)
```

だけを評価する。

root/sideが異なる同一carrierを数十回評価しようとするが、round内memoが一部を吸収する。それでもparent列の走査とmatch自体は残る。

record評価では、ReplayConjunction clauseをcarrierごとに一回評価する。exact clauseとsemantic clauseが一致したため、このcarrier粒度は維持する。

## 4. 意味上必要なidentity

### 4.1 Exact replay carrier

```text
BinaryReplayDerivation {
    pivot,
    lower,
    upper,
    rule,
}
```

全fieldがidentityの一部である。

同じlower/upperでもruleやpivotが異なるcarrierを併合しない。

### 4.2 Exact replay claim-parent

logical identityは次である。

```text
ReplayParentIdentity =
    (result, canonical_root, parent_side, exact_carrier)
```

RCPF後も、この集合をlosslessにmembership判定・列挙できなければならない。

### 4.3 Representative parent claim

dedup keyはcoverage rootを使うが、`ClaimQualifiedParent`は`parent_claim`も保持する。

同じexact keyへ複数のclaim IDが到達した場合、現行実装は最初にinsertされたclaimを残す。このrepresentativeはderived claim lineageやportable provenanceへ影響し得る。

RCPFは各logical exact keyについてfirst accepted `parent_claim`を保持する。

### 4.4 Replay occurrence

RCPFでは次を一つのoccurrenceと定義する。

```text
ReplayOccurrenceKey = (result, exact_carrier)
```

一つのoccurrenceはLower/Upper各sideについてゼロ個以上のcanonical rootを持つ。

同じoccurrenceへ後から新しいrootが到達した場合、occurrenceを作り直さずparent-set versionをappend-onlyに拡張する。

### 4.5 Parent side

Lower/Upper sideはclaim-parent identityに残す。

一方、MPC clause-linkのsupport identityはcanonical rootであり、同じrootが同じclauseへ両sideから到達した場合、exact clause-linkとしては一件へdedupされる。

従って次の二つを混同しない。

```text
claim-parent:
    (occurrence, side, root)

clause-link:
    (lower_record, root, clause)
```

### 4.6 Event-time snapshot

parent集合は次の結果である。

- その時点のlower record claim集合
- その時点のupper record claim集合
- covered/uncovered liveness
- endpoint形状
- incremental routeの除外
- replay planningのcanonicalization disposition

後からendpointのlive集合を読むだけでは、この履歴的な選択を再現できない。

RCPFはplanning時に選ばれたclaim ID列をdraftとして捕捉し、admission時にcanonical rootへ正規化してimmutable snapshotへ変換する。

### 4.7 Admission order

legacy admission streamとは、現行のreplay action traversalと、各actionから`register_replay_claim_parents`相当へ届くparent claim traversalを合わせた処理列である。

RCPFは、このstreamを次の値が確定する地点までは変更しない。

- 各`(result, root, side, carrier)`のfirst representative claim。
- 各`(result, root)`のderived claimに使うfirst witness。

representative claimとfirst witnessは、legacy admission streamを処理しながらfirst-winsで直接確定する。後続claimでwinnerを上書きしない。

persistent parent-set identityが保存するのは、こうして確定した`coverage_root -> representative_claim`写像である。winner選択に至ったclaim順、action順、entry permutationはidentityへ含めない。attachment blockから選択履歴を再構成し、representativeまたはfirst witnessを再導出してはならない。

exact iteratorは、§6.6のblock total order、block内occurrence順、parent-setのcanonical entry orderで列挙する。この順序は決定的な列挙契約であり、legacy flat Vecのhistorical parent permutationを再現する契約ではない。

flat Vecのアドレス配置やHashMap iteration orderは契約にしない。

### 4.8 Summaryはidentityではない

次はconsumer向けprojectionであり、exact identityを代替しない。

- `result -> exact replay occurrence set`
- `(result, root) -> first witness`
- `(record, root) -> has attributed clause`
- `(record, occurrence) -> replay clause`

summaryだけからcarrier-specific qualificationを推測してはならない。exactな問いはoccurrence storeへ問い合わせる。

## 5. コストモデル

一つのpivotについてsemantic lower数を`L`、semantic upper数を`U`とする。

### 5.1 carrier生成

incremental replayのlogical carrier数はworst caseで、

```text
C = O(L · U)
```

になる。

これは`L <: pivot <: U`の全含意を処理するためのworst-case下限でもある。ただし全含意を一件ずつheap objectへ物理化する必要性までは意味しない。

現設計ではcarrier clauseを維持するため、RCPFの第一段階でも`O(C)`は残る。

### 5.2 現行parent量

carrier `c`のlower/upper parent集合を`Rₗ(c)`、`Rᵤ(c)`とすると、

```text
Nparent = Σc (|Rₗ(c)| + |Rᵤ(c)|)
```

である。

同じnew-lower eventで生成された多数のcarrierは`Rₗ(c)`を共有する。同じnew-upper eventでは`Rᵤ(c)`を共有する。

現行表現は共有を表さず、`O(C·R)`個のtupleへ展開する。

### 5.3 RCPF後の物理量

次を置く。

- `Cq`: qualified replay occurrence数
- `S`: internされたparent snapshot/versionのunique entry総数
- `A`: occurrenceとparent deltaを結ぶattachment block数
- `RR`: unique `(result, root)` summary数
- `BR`: unique `(lower_record, root)` attribution数

RCPFのtarget physical costは、

```text
O(Cq + S + A + RR + BR + clauses + dependency edges)
```

である。

logical exact parent数`Nparent`は変わらないが、通常のconsumerは展開しない。

### 5.4 evaluator cost

Replay source評価は、

```text
O(number of qualified replay occurrences reachable in the round)
```

とする。

root数を乗じない。

record clause評価は引き続きcarrierごとのReplayConjunctionを評価するため、`O(C)`を維持する。

### 5.5 worst case

各carrierが完全に異なるparent集合を持つworst caseでは、snapshot共有率が低くなる。RCPFはその場合でも意味論を保つが、メモリ削減率を保証できない。

従って実装前にsnapshot reuse censusを追加し、§12のgateを満たさなければflat ledger撤去へ進まない。

## 6. Factorized abstract model

### 6.1 IDとside

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayOccurrenceId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ParentSetVersionId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ParentSetChunkId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayParentAttachmentBatchId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ReplayParentSide {
    Lower,
    Upper,
}
```

既存の`ReplayClaimParentSide`をそのまま使用してもよい。新名を導入する場合は一対一変換にし、二重の意味型を作らない。

### 6.2 Plan-local draft

replay planningは現在`&self`で動き、その後にmachine mutationを行う。planning中にproduction ledgerを変更しないため、plan-local IDを使う。

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayParentDraftId(u32);

struct ReplayParentDraft {
    // representativeとfirst witnessを確定するまでのlegacy claim順。
    claims: Box<[UpperReplayClaimId]>,
}

struct BoundReplayPlan {
    parent_drafts: Vec<ReplayParentDraft>,
    actions: BoundReplayActions,
    evidence_actions: BoundReplayActions,
    duplicate_actions: BoundReplayActions,
    trivial_actions: BoundReplayActions,
    // 既存stats...
}

struct BoundReplayAction {
    constraint: SubtypeConstraintKey,
    derivation: BinaryReplayDerivation,
    lower_parents: ReplayParentDraftId,
    upper_parents: ReplayParentDraftId,
    canonicalization_disposition:
        Option<ConstraintCanonicalizationDisposition>,
}
```

draftのclaim ID列とplan内のaction traversalは、legacy admission streamに従ってrepresentative claimとfirst witnessを確定するためのplan-local情報である。

admissionではこの順序のままfirst-wins選択を行い、winnerを確定した後にroot単位の有限写像へcanonicalizeする。draft順序、選択途中のloser、entry permutationはpersistent snapshot identityへ含めない。

empty draftには共通のsentinel IDを使い、no-claim workloadでheap allocationしない。

new lower eventでは一つのlower draftを全actionが共有する。new upper eventでは一つのupper draftを全actionが共有する。

### 6.3 Parent-set entry

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ParentSetEntry {
    coverage_root: UpperReplayClaimId,
    representative_claim: UpperReplayClaimId,
}
```

parent-setの意味上のmodelは、次のunorderedな有限写像である。

```text
ParentSet =
    { coverage_root -> representative_claim }
```

写像のdomainがcanonical root membershipを表す。各rootの値は、§4.7のlegacy admission streamでfirst-wins選択されたrepresentative claimである。

同じrootへ複数claimが到達した場合、既存versionのwinnerを置き換えない。同じadmission draft内で競合する場合も、legacy admission streamで最初のclaimをwinnerとし、そのwinner値だけをpersistent entryへ保存する。

entry permutationはparent-set identity、equality、fingerprint、hash-cons keyのいずれにも含めない。同じ`coverage_root -> representative_claim`写像は、入力entry順が異なっても同じparent-set contentである。

sideはsnapshot自体へ含めない。Lower/Upperで同じ写像を共有できるためである。sideはoccurrence attachment側に保持する。

### 6.4 Persistent parent-set version

意味上のmodelは、

```rust
struct ParentSetVersionRecord {
    base: Option<ParentSetVersionId>,
    delta: ParentSetChunkId,
    len: u32,
    depth: u16,
    fingerprint: u64,
}

struct ParentSetChunk {
    // canonical entry order。coverage_rootはchunk内unique。
    entries: Box<[ParentSetEntry]>,
}
```

とする。

arenaは次のAPIを提供する。

```rust
impl ParentSetArena {
    fn preflight_extend(
        &self,
        base: ParentSetVersionId,
        draft: &ReplayParentDraft,
        bounds: &TypeBounds,
    ) -> ParentSetExtensionPlan<'_>;

    fn commit_extend(
        &mut self,
        plan: ParentSetExtensionPlan<'_>,
    ) -> ParentSetExtension;

    fn contains(
        &self,
        version: ParentSetVersionId,
        root: UpperReplayClaimId,
    ) -> bool;

    fn representative_claim(
        &self,
        version: ParentSetVersionId,
        root: UpperReplayClaimId,
    ) -> Option<UpperReplayClaimId>;

    fn iter(
        &self,
        version: ParentSetVersionId,
    ) -> impl Iterator<Item = ParentSetEntry>;
}

struct ParentSetExtension {
    version: ParentSetVersionId,
    accepted_delta: ParentSetVersionId,
    changed: bool,
}
```

契約は次になる。

- versionの意味内容は`coverage_root -> representative_claim`有限写像であり、first-admission順を含まない。
- `preflight_extend`はdraftをlegacy admission stream順に処理してwinnerを確定してから、accepted deltaをcanonicalizeする。
- `iter`はversion全体をcanonical entry orderで列挙する。
- canonical entry orderは、`coverage_root`のstable ID、次に`representative_claim`のstable IDによる昇順の辞書式順序とする。coverage rootはuniqueなので、第二keyは全順序を明示するためのtie ruleである。
- `accepted_delta`のiteratorも同じcanonical entry orderを使う。
- HashMap iteration order、base/delta chainの物理配置、draftのentry permutationをiterator順へ漏らさない。
- fingerprintとintern keyはentry permutationに依存しない。同じ有限写像は同じinterned contentとして共有する。
- baseのentryをcopyしない。
- 同じ`(base, accepted delta)`はhash-consしてよい。
- membershipはexpected O(1)、または深さに小さい定数上限を持つ。
- version chainが閾値を超える場合、shared checkpointへcompactしてよい。
- checkpointはlogical relationとcanonical iterator結果を変えない内部処理であり、epochを進めない。
- `changed == false`ならpersistent allocationを行わない。

backendとしてpersistent HAMT、hash-consed chunk＋bounded checkpointなどを選べる。backend選択は意味契約ではないが、`O(Nparent)`の再物理化へ戻る実装は認めない。

### 6.5 Replay occurrence

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ReplayOccurrenceKey {
    result: ConstraintRecordId,
    carrier: BinaryReplayDerivation,
}

struct ReplayOccurrence {
    id: ReplayOccurrenceId,
    result: ConstraintRecordId,
    carrier: BinaryReplayDerivation,

    lower_parents: ParentSetVersionId,
    upper_parents: ParentSetVersionId,

    first_admission_ordinal: u64,
}
```

`ReplayOccurrenceKey`は一意である。

parentsが空のcarrierはclaim-parent occurrence storeへ追加しない。independent replay carrierは既存のreplay derivation、projection proof、clause経路で扱う。これによりno-claim passthroughを保つ。

### 6.6 Attachment block

exact parent deltaのstorage groupingと決定的な列挙順を保持する。

```rust
struct ReplayParentAttachmentBatch {
    id: ReplayParentAttachmentBatchId,
    admission_ordinal: u64,
    side: ReplayParentSide,

    // cohort内で確定したoccurrence順。
    occurrences: Box<[ReplayOccurrenceId]>,

    // 各occurrenceについて新しく受理されたroot -> representative写像。
    accepted_delta: ParentSetVersionId,
}
```

同じparent deltaを受け取るoccurrence cohortだけを一つのattachment blockへ入れる。

block間のtotal orderは次のkeyで定義する。

```text
(admission_ordinal, ReplayParentAttachmentBatchId)
```

`admission_ordinal`を第一keyとする。同じadmission ordinalに複数blockがある場合、append-onlyなblock commit時に単調増加で割り当てた`ReplayParentAttachmentBatchId`をtie-breakerとする。同一ordinal内のID割り当ては決定されたblock commit順に行い、HashMap iteration orderから生成しない。

block内では`occurrences`に保存された順序を使う。`accepted_delta`は§6.4のcanonical entry orderで列挙する。

attachment blockが複数resultやlower recordを含んでも、それはstorage sharingに限る。epoch publicationやA4 atomic batchは§9の境界で分割する。

exact parent列挙では、

```text
(admission_ordinal, attachment batch ID)によるblock total order
    -> block内のoccurrence順
        -> accepted_deltaのcanonical entry order
```

でlogical tupleを生成する。

attachment groupingはrepresentative claimまたはfirst witnessの決定源ではない。両winnerは、元のlegacy admission streamを処理する地点でfirst-winsにより直接確定し、同じadmission eventでcommitする。attachment iteratorを後から列挙してwinnerを再計算してはならない。

### 6.7 Exact occurrence store

```rust
struct ReplayOccurrenceStore {
    occurrences: Vec<ReplayOccurrence>,

    by_key:
        FxHashMap<ReplayOccurrenceKey, ReplayOccurrenceId>,

    by_result:
        FxHashMap<ConstraintRecordId, Vec<ReplayOccurrenceId>>,

    attachment_batches:
        Vec<ReplayParentAttachmentBatch>,
}
```

`by_result`はfirst occurrence admission順を保持する。

### 6.8 Result/root summary

```rust
#[derive(Clone, Copy)]
struct FirstReplayParentWitness {
    occurrence: ReplayOccurrenceId,
    parent_side: ReplayParentSide,
    parent_claim: UpperReplayClaimId,
    admission_ordinal: u64,
}

struct ReplayResultSummary {
    first_parent_by_root:
        FxHashMap<
            (ConstraintRecordId, UpperReplayClaimId),
            FirstReplayParentWitness,
        >,

    // 同じsnapshotを同じresultで何度もsemantic projectionしない。
    projected_parent_versions:
        FxHashSet<
            (
                ConstraintRecordId,
                ReplayParentSide,
                ParentSetVersionId,
            ),
        >,
}
```

`first_parent_by_root`はupper claim materializationの代表lineageを固定する。

各entryは、legacy admission streamを現行と同じ順序で処理している間に、`(result, root)`ごとのfirst-winsで確定する。後続witnessで上書きしない。persistent化するのはwinnerである`FirstReplayParentWitness`の値であり、winner選択に至ったparent permutationではない。

`first_parent_by_root`をattachment blockの列挙後に再計算してはならない。attachment grouping、canonical entry order、cohort化によって得られる列挙順は、first witnessの決定源ではない。

`projected_parent_versions`はappend-only inputの鏡であり、評価結果cacheではない。

### 6.9 Clause/link projection

```rust
struct ReplayClauseProjection {
    clause_by_record_and_occurrence:
        FxHashMap<
            (BoundRecordId, ReplayOccurrenceId),
            RecordProofClauseId,
        >,

    attributed_claim_supports:
        FxHashSet<(BoundRecordId, UpperReplayClaimId)>,
}
```

`clause_by_record_and_occurrence`はcarrierごとに一つのReplayConjunctionを指す。

`attributed_claim_supports`はflat fail-openが必要とする、

```text
この(record, root) supportに少なくとも一つ帰属済みclauseがあるか
```

だけを保持する。

exact replay linkは次から再構成する。

```text
(record, occurrence) -> clause
occurrence.lower_parents ∪ occurrence.upper_parents -> roots
```

両sideに同じrootがある場合、link列挙時に一件へdedupする。

### 6.10 TypeBoundsへの配置

完成形では概ね次を持つ。

```rust
struct TypeBounds {
    // claim/root層。既存のまま。
    upper_replay_claims: Vec<UpperReplayClaim>,
    derived_claim_by_record_and_root: FxHashMap<...>,
    root_claim_by_producer_constraint: FxHashMap<...>,
    live_coverage_by_root: FxHashMap<...>,

    replay_parent_sets: ParentSetArena,
    replay_occurrences: ReplayOccurrenceStore,
    replay_result_summary: ReplayResultSummary,
    replay_clause_projection: ReplayClauseProjection,

    // structural / reduction-routeは小さいため当面flat。
    non_replay_claim_parents_by_constraint:
        FxHashMap<ConstraintRecordId, Vec<ClaimQualifiedParent>>,

    // CDMのexact carrier indexは維持。
    qualified_carrier_index:
        FxHashMap<ConstraintRecordId, FxHashSet<QualifiedCarrier>>,

    // MPC/DPNのclauseとedge。Replay claimed linkだけfactored化。
    record_proof_clauses: Vec<RecordProofClauseRecord>,
    record_proof_clause_by_key: FxHashMap<...>,
    record_proof_clause_ids_by_lower_record: FxHashMap<...>,
    non_replay_clause_links_by_lower_record: FxHashMap<...>,
    non_replay_clause_link_keys: FxHashSet<...>,
    dependent_records_by_premise: FxHashMap<...>,

    // 既存reverse index。変更しない。
    scheme_projection_lower_record_memberships:
        FxHashSet<(UpperReplayClaimId, BoundRecordId)>,

    // その他既存field...
}
```

移行中は旧`claim_parents_by_constraint`と旧link ledgerを並走させる。最終撤去まで旧field名の意味を縮めない。

### 6.11 Query API

consumerが内部表現へ直接依存しないよう、次を境界にする。

```rust
fn replay_occurrences_for_result(
    &self,
    result: ConstraintRecordId,
) -> impl Iterator<Item = ReplayOccurrenceId>;

fn replay_occurrence(
    &self,
    id: ReplayOccurrenceId,
) -> &ReplayOccurrence;

fn first_replay_parent_for_root(
    &self,
    result: ConstraintRecordId,
    root: UpperReplayClaimId,
) -> Option<FirstReplayParentWitness>;

fn exact_replay_parent_is_registered(
    &self,
    result: ConstraintRecordId,
    root: UpperReplayClaimId,
    side: ReplayParentSide,
    carrier: BinaryReplayDerivation,
) -> bool;

fn exact_replay_parents(
    &self,
    result: ConstraintRecordId,
) -> impl Iterator<Item = ClaimQualifiedParent>;

fn replay_claim_support_is_attributed(
    &self,
    record: BoundRecordId,
    root: UpperReplayClaimId,
) -> bool;

fn exact_replay_clause_links(
    &self,
    record: BoundRecordId,
) -> impl Iterator<Item = RecordProofClauseLink>;
```

production hot pathから`exact_replay_parents`や`exact_replay_clause_links`を呼ばない。これらはoracle、debug、portable provenanceの明示的な全列挙だけに使う。

## 7. Admission algorithms

### 7.1 共通pipeline

一つのexact replay carrier admissionは次の順で処理する。

1. planning時にLower/Upper parent draftを確定する。
2. draftのclaim IDをcanonical rootへ正規化する。
3. draft内をroot単位でfirst-wins dedupする。
4. `(result, carrier)`から既存occurrenceを探す。
5. occurrenceの各side versionへdraftをpreflight extensionする。
6. occurrenceもparent deltaも新しくなければexact no-opとしてreturnする。
7. 影響するrecord/constraintのbefore inclusionを取得する。
8. occurrence、parent-set version、attachment block、carrier indexをcommitする。
9. result/root summary、projection proof、clause、attribution、dependency edgeへdeltaを投影する。
10. after inclusionを取得し、net mutationを一回publishする。

preflightとcommitの間にmachine mutationやepoch publicationを挟まない。

### 7.2 New lower

`lower_bound_replay_actions`は次へ変わる。

1. new lowerのparent claim ID列を一つのplan-local draftへ保存する。
2. existing upperごとに、現行と同じ`upper_record_replay_claim_parents`を実行する。
3. covered claimについて、incremental routeが扱うclaimを現行どおり除外する。
4. upperごとのdraftをplan内でinternする。
5. actionはlower draft IDとupper draft IDだけを持つ。
6. canonicalization後、各actionをresultごとのfactored admissionへ渡す。

すべてのactionが同じlower draftを参照するため、lower rootsをupper数だけcloneしない。

異なるresultやlower recordのpublicationを一つへまとめない。draft/versionの共有とatomic mutation batchを混同しない。

### 7.3 New upper

`upper_bound_replay_actions`は次へ変わる。

1. new upperのuncovered claim ID列を一つのdraftへ保存する。
2. existing lowerごとにlower draftを取得する。
3. actionはlower draftと共通upper draftを参照する。
4. exact carrierは現行どおり`UpperBoundAdded`を保持する。
5. resultごとにfactored admissionを行う。

`requires_generic == false`なら現行どおりgeneric replay actionを作らない。

### 7.4 Canonical duplicate

canonical duplicateはsemantic queueへ入らないが、exact carrierとparent relationを必ず登録する。

処理順:

1. `merge_replay_derivation(result, carrier)`。
2. factored occurrenceをpreflightする。
3. exact no-opならpublicationなし。
4. new occurrenceまたはnew root attachmentがあればcommitする。
5. target lower/upper recordが既に存在するため、新規deltaだけをeager materializeする。
6. result/root summaryが既に持つrootはderived claimを再作成しない。
7. new carrierならReplayConjunction clauseを一つ作る。
8. clauseの全root linkはfactored relationとして記録し、expanded HashSetへinsertしない。

CDMの「二件目carrierでもexact記帳を行う」規則を維持する。

### 7.5 Incremental row route

new lower側のincremental route処理は現行規則をそのまま写す。

- generic replayがそのrouteを包含する場合、追加actionを作らない。
- 同じ`(route.upper, carrier)`をplan内でdedupする。
- route claimがある場合、そのclaimだけをUpper draftへ入れる。
- generic upper snapshot側では同じclaimを除外する。
- route claimがない場合、empty Upper draftを使う。
- generic actionとincremental actionが同じcarrierへ到達した場合、ParentSet extensionのexact membershipでunionする。

live upper claim集合から後で再構成しない。

### 7.6 Late claim-parent

既存occurrenceへ新しいparentが届いた場合は、sideごとにversionをextendする。

```text
old version + admission snapshot
    -> accepted root delta
    -> new version
```

既存rootはexact no-opになる。異なるclaim IDでもcoverage rootが同じなら、既存のrepresentativeを置き換えない。

新しいrootだけを次へ送る。

- result/root summary
- upper derived claim materialization
- lower projection claim
- claimed support attribution

既存clauseとdependency edgeを再登録しない。

同一carrierが先にindependent supportとして、後からclaimed supportとして到達した場合、independent occurrence/linkを削除しない。MPC/CDMのadd-only occurrence規則を保つ。

### 7.7 Target recordが後から現れる場合

new semantic constraintでは`materialize_existing_target == false`になり得る。その後、constraint自身のbound admissionがmetadataを消費する。

旧pathの全flat parent cloneに代えて次を行う。

1. `replay_occurrences_for_result(result)`からcarrier集合を取得する。
2. `first_parent_by_root[result]`からunique rootと代表witnessを取得する。
3. upper claimを`(record, root)`ごとに一回materializeする。
4. lower recordについて、occurrenceごとにReplayConjunction clauseを一回登録する。
5. root attributionは`(record, root)`summaryへ一回登録する。
6. exact occurrence→root→clause relationはfactored storeから再構成可能なまま保つ。

bootstrapでexpanded parent tupleを生成しない。

### 7.8 Evidence-only

evidence-only actionはcanonical resultのclaim-parent relationへ入らない。現行のevidence lower/upper record生成と`ReplayEvidence` lineageを維持する。

ただし`BoundReplayAction`はparent draft IDを持つため、evidence pathは必要な時だけsnapshot iteratorを開く。actionごとのparent Vec cloneは行わない。

evidence pathをconsumer summaryへ無理に統合しない。censusで同pathの絶対量が支配的になった場合に別sliceで扱う。

### 7.9 Trivial action

trivial actionは現行どおり`ReplayDropRecord`だけをinternする。

- ReplayOccurrenceを作らない。
- ParentSetVersionをcommitしない。
- summaryを変更しない。
- epochを進めない。

plan-local draftが他actionから共有されていても、trivial action自身のためにpersistent allocationしない。

### 7.10 Structural / reduction-route

censusではstructural parent 30,127件、reduction-route parent 129件であり、replayの50,386,734件に比べて小さい。

初期RCPFではこれらを既存flat relationに残す。

- DerivedUnary premise規則は変更しない。
- DPNのConstraint/RootCoverage評価は変更しない。
- structural/reductionのexact carrier indexは維持する。
- 同じconsumer facadeからreplay factored sourceとnon-replay flat sourceを合流させる。

全parent kindを同時に再設計してblast radiusを広げない。

## 8. Consumer別projection

### 8.1 Constraint evaluator

現行`eval_constraint_uncached`のReplay parent列挙を次へ置き換える。

```text
eval(Constraint(c)):
    source (a): linked lower record
    source (b1): each qualified replay occurrence for c
        -> eval(occurrence.carrier.lower)
           AND
           eval(occurrence.carrier.upper)
    source (b2): each non-replay flat parent
        structural -> eval(parent constraint)
        reduction  -> eval(root coverage)
    source (c): producer root claim
```

一つのoccurrenceはroot数に関係なく一回だけ評価する。

`qualified_carrier_index`または`by_result`はcarrier existenceを答えるが、root-specificなexact qualificationを答える用途には使わない。

A3のevaluation round、before/after view分離、cycle cut後のsharing disableをそのまま使う。RCPF summaryを恒久的なprojectability cacheにしない。

### 8.2 Upper claim materialization

`register_constraint_upper_replay_claims`とdelta版は、Replayについて`first_parent_by_root`を読む。

```text
for each unique root for result:
    if (record, root) is not materialized:
        witness = first_parent_by_root[(result, root)]
        create derived claim using witness.parent_claim/side/carrier
```

これによりcarrier数に比例したroot再処理を行わない。

既存の`derived_claim_by_record_and_root`を正本として維持する。RCPF summaryはその入力索引であり、claim identityを置換しない。

### 8.3 Projection proof

`projection_proofs_by_lower_record`のclaimed supportは、引き続きcanonical root単位で保持する。

新規root deltaだけを`update_scheme_projection_proofs`へ送る。

independent carrier分類は既存`qualified_carrier_index`を使う。`scheme_projection_lower_record_memberships`も変更しない。

Replay occurrenceが追加されたがroot summaryに変化がない場合、

- claimed proof vectorは変わらない。
- exact carrier qualificationは変わる。
- ReplayConjunction clauseは新しくなり得る。

この三つを一つのboolean summaryへ潰さない。

### 8.4 Clause evaluator

一つのqualified replay occurrenceについて、target lower recordに一つのclauseを作る。

```rust
RecordProofClause::ReplayConjunction {
    carrier: occurrence.carrier,
    lower_premise: occurrence.carrier.lower,
    upper_premise: occurrence.carrier.upper,
}
```

exact/semantic censusが一致したため、carrier clauseを併合しない。

同じoccurrenceへrootが追加されてもclauseを作り直さない。

### 8.5 Flat fail-open

`flat_fail_open`が必要とする問いは、

```text
このproof supportに一つでも帰属済みclauseがあるか
```

である。

Claimed supportについては、

```text
attributed_claim_supports.contains((lower_record, canonical_root))
```

を使う。

Independent supportやStandalone/DerivedUnaryの非replay linkは既存exact link ledgerを使う。

factored metadataが欠落・破損している場合はMPC/DPNの規則どおりprojectable側へ倒す。ただしconfirmed pathでこのfallbackが発火すればlandingしない。

### 8.6 Exact clause-link membership

A1 predicateはclause kindでdispatchする。

```text
ReplayConjunction + Claimed(root):
    (record, carrier) -> occurrence
    occurrence.lower/upper parent setにrootが存在するか

その他:
    existing flat exact link key
```

同じclause・異なるrootは別linkであり、no-opにしない。

同じrootがLower/Upper両sideに存在しても、clause-link identityにはsideがないため一件とする。

### 8.7 Dependency edge

ReplayConjunctionのdependency edgeはclause新規作成時に一回だけ登録する。

```text
Record(carrier.lower) -> dependent record
Record(carrier.upper) -> dependent record
```

root attachment追加時にはedgeを追加しない。

`dependent_records_by_premise`の意味とDPNのbounded chain walkを変更しない。

### 8.8 Portable provenance

portable provenanceまたは互換adapterがexact replay parent relationを必要とする場合、factored iteratorから遅延列挙する。

要件:

- exact carrierを保持する。
- rootとsideを保持する。
- 各exact keyのrepresentative claimを保持する。
- blockを`(admission_ordinal, ReplayParentAttachmentBatchId)`のtotal orderで列挙する。
- 各blockでは保存されたoccurrence順を使う。
- 各accepted deltaでは§6.4のcanonical entry orderを使う。
- deterministicとは、このblock total order、occurrence順、canonical entry orderから同じfactored stateに対して同じ列を得ることを意味する。
- deterministicは、legacy flat Vecのhistorical parent permutationやwinner選択途中のloser順を再現することを意味しない。
- consumerが全5,000万tupleを要求した場合、そのコストを明示的なfull expansionとして扱う。
- 通常のlowering、projectability、cache key生成のためにfull expansionしない。

portable oracleは、順序がconsumer-visibleかどうかで比較方法を分ける。

- relationの意味だけを比較する場合:
  ```text
  (result, root, side, carrier) -> representative_claim
  ```
  というunorderedな有限写像としてlegacyとfactoredを比較する。
- iterator順がportable outputへ現れる場合:
  legacy側とfactored側を同じblock total order、occurrence順、canonical entry orderへnormalizeし、canonical sequenceとして比較する。
- legacy flat Vecのraw admission順とのbyte-for-byte比較はoracleにしない。

既存portable provenanceの公開表現は変更しない。必要ならiteratorから既存builderへのadapterを置く。

`explain.rs`のexplanation graphは別レイヤーであり、`claim_parents_by_constraint`を直接列挙しない。その順序は既存のcategory順、edge順、hyperedge parent順に従う。RCPFはこのgraphのdata sourceや順序契約を変更せず、representative claim選択の結果だけをlegacyと一致させる。

### 8.9 Diagnostics / census

診断用に次を別々に数える。

- logical exact parent数。
- physical parent-set entry数。
- ParentSetVersion数。
- attachment block数。
- occurrence数。
- result/root summary数。
- record/root attribution数。
- full expansion回数。
- evaluator occurrence inspection数。

logical exact数とphysical entry数を混同しない。

## 9. Epoch・batch契約

### 9.1 Storage sharingはmutation batchではない

同じparent snapshotを多数のoccurrenceが共有しても、epoch publicationを一つへまとめてよいとは限らない。

publicationは既存の自然な境界で分割する。

- 同一constraint result。
- 同一lower record。
- 同一solver/admission event。
- proof/liveness mutationを跨がない。
- 異なるbefore/after viewを混ぜない。

attachment blockは物理表現であり、atomicityの単位ではない。

### 9.2 Factored admission delta

```rust
struct FactoredReplayAdmissionDelta {
    logical_metadata_changed: bool,

    new_occurrences: SmallVec<[ReplayOccurrenceId; 2]>,
    new_parent_versions: SmallVec<[ParentSetVersionId; 2]>,

    affected_results: SmallVec<[ConstraintRecordId; 1]>,
    affected_records: SmallVec<[BoundRecordId; 2]>,

    clauses_created: SmallVec<[RecordProofClauseId; 1]>,
    roots_materialized: SmallVec<[UpperReplayClaimId; 4]>,
}
```

実装では大きなroot deltaをSmallVecへ展開せず、`ParentSetVersionId`で渡してよい。

### 9.3 Exact no-op

既存occurrenceへ既存rootだけが届き、その他のlogical stateも変化しない場合:

- persistent ledger allocationなし。
- evaluator queryなし。
- clause/link/edge mutationなし。
- owner/global epochなし。
- provenance epochなし。
- cache invalidationなし。

plan-local temporaryについても、empty/no-op fast pathではheap allocationを避ける。

### 9.4 Nonempty admission

処理順を次に固定する。

1. exact relationのpreflight。
2. batch-local duplicate除去。
3. no-opならreturn。
4. affected records/constraintsのbefore view評価。
5. occurrence、parent versions、summary、clause、attributionをcommit。
6. new clauseのdependency edgeを一回登録。
7. after view評価。
8. net resultを一回publish。

before/afterは別の`SchemeProjectionEvaluationRound`を使う。

cycle cut後のsharing disableを継承する。

### 9.5 Metadata-only

approved A3/A4文書では、metadata-only mutationはowner/global epochを進めず、provenance epochを一event一回進める。

ただし現在の`commit_record_proof_clause_link_batch`は、A4 sliceで旧逐次経路とのepoch互換性を優先し、

```rust
publish_record_inclusion_change(
    lower_record,
    was_included,
    is_included,
    false,
)
```

を使う。

RCPFはこの既存差異を独自に変更しない。

移行中の規則:

- shadow/dual-writeはepochを一切publishしない。
- consumer切替後も、各既存入口の現行publication policyを維持する。
- factored store追加を理由に`metadata_changed=true`へ変えない。
- metadata-only provenance publicationの全link admission監査は別の明示的sliceとする。
- その監査が承認されるまで、RCPFのcorrectness oracleには現在のepoch列も含める。

### 9.6 Inclusion flip

net inclusionが変化した場合は既存A4契約を継承する。

- affected active ownerをdedupする。
- global constraint epochを一回進める。
- affected ownerのvar epochを同じglobal epochへ進める。
- provenance publicationを行う。
- batch途中のflipをpublishしない。
- tombstone/owner無しrecordにowner epochを発明しない。

### 9.7 Internal compaction

ParentSetVersionのcheckpoint化、hash-cons tableのrehashなど、logical relationを変えない内部compactionはepochを進めない。

compactionをprojectability評価roundの途中で行わない。IDの安定性が必要な構造をmoveする場合はarena IDを維持する。

### 9.8 A1〜A4対応表

| 既存規則 | RCPFでの対応 |
|---|---|
| A1 exact duplicate | `exact_replay_parent_is_registered`とfactored link membership |
| A2 flat-gate | proof vectorだけのmutationへ従来どおり適用 |
| A3 current round | factored summaryを読む複数root評価でも継承 |
| A3 before/after分離 | factored commit前後を別roundにする |
| A3 cycle cut | cut後はfresh evaluator |
| A4 local dedup | snapshot draft内root dedup、occurrence version差分 |
| A4 before/commit/after | FactoredReplayAdmissionDelta単位で実行 |
| A4 edge一回 | new ReplayConjunction clauseだけがedgeを作る |
| A4 exact no-op epoch | logical delta emptyなら全publicationなし |
| A4 event境界 | storage cohortと分離して維持 |

## 10. Correctness invariants

1. **Exact carrier identity**
   - `pivot/lower/upper/rule`を落とさない。
   - 異なるcarrierへ同じ`ReplayOccurrenceId`を割り当てない。

2. **Exact parent relation equivalence**
   - 到達可能な任意の状態で、
     ```text
     expanded(factored replay relation)
     ==
     legacy replay claim-parent exact set
     ```
     が成立する。

3. **Exact keyの無条件性**
   - rootがresult/recordで既にmaterialize済みでも、新しいcarrierのexact relationを失わない。

4. **First representative**
   - 各`(result, root, side, carrier)`について、legacy admission streamで最初に受理されたparent claimをwinnerとして保持する。
   - 保存対象はwinnerである`representative_claim`の値であり、その選択に至った入力順列やloserの履歴ではない。
   - 後続claimでwinnerを上書きしない。

5. **Event-time snapshot**
   - snapshotはadmission時点で確定した`coverage_root -> representative_claim`写像を表す。
   - root membershipとrepresentative winnerの双方をadmission-time結果として保持する。
   - live endpoint集合やattachment iteratorを後から参照して再構成しない。

6. **Covered/uncovered equivalence**
   - current liveness、endpoint形状、incremental route exclusionを現行と同じ順序で適用する。

7. **Result/root canonicality**
   - derived upper claimは`(record, root)`ごとに一つ。
   - carrier数に比例してclaimを増やさない。

8. **Occurrence/clause correspondence**
   - target lower recordが存在するqualified occurrenceには、一つのexact ReplayConjunction clauseが対応する。
   - root追加でclauseを増やさない。

9. **Logical link equivalence**
   - factored relationから再構成した`(record, support, clause)`集合がlegacy exact link集合と一致する。

10. **Occurrence帰属**
    - claimed supportがどのReplayConjunctionへ属するかをlosslessに列挙できる。
    - lineage kindからclauseを推測しない。

11. **Consumer equivalence**
    - evaluator、projection、generalization、portable provenance、diagnostic入力の結果がlegacy oracleと一致する。

12. **DPN premise semantics**
    - Record/Constraint/RootCoverageの評価規則を変えない。
    - replay sourceだけをoccurrence iteratorへ置き換える。

13. **Cycle safety**
    - tri-color規則を維持する。
    - top-level return時にVisitingを残さない。
    - cycle cut後のDoneを後続rootへ共有しない。

14. **Admission時完全性**
    - accepted deltaは同じevent内で全consumerへ反映する。
    - repair pass、flush、後続fixpointへ依存しない。

15. **Insertion-order invariance**
    - replay action順、parent順、lower/upper到着順を変えてもlogical exact relation、projectability、scheme結果が一致する。
    - representative claimまたはfirst witnessが異なり得る順序については、各入力順でlegacy admission streamが選んだwinnerとfactored admissionが直接保存したwinnerを比較する。
    - first witnessをattachment iteratorから再導出して比較しない。

16. **Atomic net publication**
    - 同一eventの途中状態をepoch/cache consumerへpublishしない。

17. **No-claim passthrough**
    - parent draft、occurrence、snapshot、summary、attachmentを作らない。

18. **Append-only**
    - logical occurrence、accepted parent relation、first witnessはappend-only。
    - liveness変化で削除・再分類しない。

19. **Summary separation**
    - `(result, root)`summaryからcarrier-specific qualificationを推測しない。
    - carrierの問いはoccurrence/indexだけが答える。

20. **Reverse-index維持**
    - `scheme_projection_lower_record_memberships`とVec正本の同期規則を変更しない。

21. **No global scan**
    - admission、evaluation、invalidationのために全bound、全claim、全constraintを走査しない。

22. **No permanent evaluation memo**
    - ParentSet membership indexはappend-only inputの表現であり、projectability結果cacheではない。
    - evaluator memoはround終了時に破棄する。

23. **Diagnostic order isolation**
    - RCPF cutoverの前提として、diagnostic-consuming codeに`claim_parents_by_constraint`の直接列挙者を置かない。
    - diagnostic lineageが使用するrepresentative claimと`derived_claim_by_record_and_root`の選択結果をlegacyと一致させる。
    - `explain.rs`のexplanation graphはclaim-parent ledgerとは別レイヤーであり、category順、edge順、hyperedge parent順という既存契約を維持する。
    - representative claim選択の結果が一致し、explanation graphのdata sourceを変更しない限り、その別レイヤーの順序契約はRCPFのattachment groupingやcanonical entry orderの影響を受けない。
    - 将来diagnostic-consuming codeがflat claim-parent列を直接列挙する場合は、この前提を黙って破らず、RCPF cutover前に別のconsumer契約とoracleを設計する。

### 10.1 Oracle

移行中はlegacy flat ledgerを正しいoracleとして残し、少なくとも次を比較する。

- exact replay parent set。
- 各exact keyからfirst representative parent claimへの写像。
- 各`(result, root)`のfirst witness。
- qualified carrier set。
- `(record, root)`derived claim。
- derived claimのrepresentative lineage。
- projection proofs。
- exact clause set。
- exact clause-link set。
- dependency edge set。
- projectability。
- affected owner set。
- epoch列。
- portable provenance。

exact replay parentとfirst representativeは、

```text
(result, root, side, carrier) -> representative_claim
```

というunorderedな有限写像として比較する。

portable provenanceの順序がconsumer-visibleでない場合は集合または有限写像として比較する。順序がvisibleな場合は、legacy側とfactored側を§8.8の同じcanonical orderへnormalizeしてsequence比較する。legacy flat Vecのhistorical parent permutation自体はoracleにしない。

insertion-order fixtureでは、各入力順についてlegacyが直接選んだrepresentative claimとfirst witnessをfactored側の保存値へ比較する。attachment iteratorからwinnerを再導出しない。

比較はfixture終了時だけでなく、test/debug buildではadmission event境界でも実行可能にする。

### 10.2 必須regression

既存CDM/MPC/DPN/A3-A4のpinned testsを期待値変更なしで維持する。

加えて次を作る。

- 共通lower parent snapshotを多数upperが共有するfixture。
- 共通upper parent snapshotを多数lowerが共有するfixture。
- 同一carrierへのlate root extension。
- 同一root・異なるclaim IDのfirst-wins。
- 同一rootがLower/Upper両sideにある場合。
- generic routeとincremental routeのclaim除外。
- canonical duplicateへのnew carrier。
- canonical duplicateへのexisting carrier/new root。
- occurrenceはnewだがresult/root summaryは既存。
- target lower recordが後から現れるbootstrap。
- independent-first→claimed-later。
- insertion-order反転。
- cycle＋independent arm。
- exact no-opのallocation/evaluator/epoch zero。
- factored exact iteratorとlegacy Vecの集合等価。

## 11. 段階的移行とrollback

各sliceは独立commit・独立rollback単位にする。flat ledger撤去までは旧経路を残す。

### RCPF-0: 追加census

変更:

- resultごとのreplay carrier数。
- carrierごとのLower/Upper root数。
- parent draft/snapshotのunique数。
- snapshot hashごとのreuse回数。
- unique `(result, root)`。
- unique `(record, root)`。
- exact `(record, root, clause)`。
- late extension回数。
- canonical new/duplicate別parent数。
- LowerBoundAdded/UpperBoundAdded別parent数。
- carrier edgeのbiclique被覆率。

Gate:

- event-time snapshotの構成要素が全経路で確定。
- 同じsnapshotを共有できない未確認のmutable dependencyがない。
- reuse率が§12の物理圧縮目標を支持する。

**実施済み(2026-08-02)**: 上記censusおよびRCPF-0bを実施し、§2.6のとおり全Gateを満たした。採用するparent-set表現は、root membershipをdomain、legacy admission streamが選択したrepresentative claimを値とするunorderedな有限写像(§6.3)に確定した。admission順序そのものはpersistent identityに含めない。この結論を反映して§1.1/1.2/4.7/6.2-6.4/6.6/6.8/8.8/10を改訂した。

Rollback:

- instrumentationだけを削除。
- production挙動に影響なし。

### RCPF-A: 型とshadow factored ledger

変更:

- ID型、ParentSetArena、ReplayOccurrenceStoreを追加。
- replay parent admissionからshadow ledgerへ書く。
- consumer、epoch、clause/linkはlegacyのみ。

Gate:

- 全既存test green。
- epoch列不変。
- shadow expanded relationがlegacy exact setと一致。
- no-claim allocation不変。
- shadow overheadを§12以内に収める。

Rollback:

- shadow writerと新fieldをsliceごと削除。
- legacyに影響なし。

### RCPF-B: Dual-write oracleとsummary

変更:

- `ReplayResultSummary`。
- `ReplayClauseProjection`のshadow版。
- event-boundary oracle。
- first witness比較。
- factored exact link iterator。

legacyが引き続きauthorityであり、factored summaryからproduction結果を返さない。

Gate:

- §10.1の全比較一致。
- direct-first/claimed-first一致。
- canonical duplicate/evidence/promotion fixtures一致。
- expanded full census数一致。

Rollback:

- summaryとoracleだけを削除。
- RCPF-A shadow occurrence storeは残してよい。
- production挙動不変。

### RCPF-C: Evaluator切替

変更:

- `eval_constraint_uncached`のReplay sourceを`by_result` occurrence iteratorへ切り替える。
- structural/reduction-routeはlegacy flat iterator。
- test-only flagでlegacy evaluator oracleを残す。

Gate:

- fresh/shared oracle一致。
-全cycle test一致。
- cache on/off一致。
- evaluator replay inspectionがroot数に比例しない。
- projectability、scheme、diagnostic入力一致。

Rollback:

- evaluator adapterをlegacy parent iteratorへ戻す。
- shadow/factored ledgerは残せる。
- clause/linkやepochを変更しない。

### RCPF-D: Upper claim / projection consumer切替

変更:

- upper claim materializationを`first_parent_by_root`へ切り替える。
- lower projectionのclaimed root入力をresult/root summaryへ切り替える。
- `qualified_carrier_index`は継続利用。
- legacy parent materializationをtest oracleへ退役。

Gate:

- `(record, root)`claim集合一致。
-代表lineage一致。
- projection proof vector一致。
- reverse index一致。
- owner/global/provenance epoch列一致。

Rollback:

- consumer adapterをlegacy Vecへ戻す。
- RCPF-C evaluatorは独立して維持可能。
- factored dataはshadowとして残る。

### RCPF-E: Clause-link consumer切替

**着地済み（2026-08-05）**。実装は
[[2026-08-05-rcpf-e-clause-link-attribution-and-ordering-addendum]]
（ユーザ承認済み・正本）の Gap 1（claimed attribution の source-partitioned
union）・Gap 2（A1 preflight の event-local ordering、Factored A1 失敗時の
Phase A 無条件維持）に従い、E2a〜E2e のスライスで完了した
（`00a962b9` writer-boundary 分類 → `a9bafe72` test fixture authority 是正
→ `38147643` Phase B 後の snapshot sealing → `220a2fb4` union read + oracle
→ `159dbb02` A1 preflight 安定化）。§11 の4項目は Codex `gpt-5.6-sol` xhigh
による read-only closure 検証（2026-08-05）で全て PASS 確認済み。
scoped `constraints::` suite は既知4件のみで green。定量性能 gate（下記
12.62B比較、§12目標）は E 後に再計測が必要（未完了）。RCPF-F 着手前提の
soak（quarantine addendum §3.6）も未実施——F は別途着手判断が必要。

**追記（2026-08-05、branch `rcpf-f-bold-attempt` での見落とし発見）**:
上記 closure 検証は §11 の4項目（evaluator・claimed attribution・exact
link predicate・legacy link の oracle 化）の narrow scope では正しかったが、
RCPF-F 実装を実際に試みる過程で、`claim_parents_by_constraint` の
Replay variant entries を無条件（authority 分岐なし）に読む production
consumer が他に5箇所残っていると判明した——`register_constraint_upper_replay_claims`
（upper claim materialization、通常の `add_upper_bound` 経路から直接
呼ばれる）、`register_premise_dependency_chain`（dependency-chain
propagation）、`register_lower_projection_derivation`（lower projection
初期化）、`register_existing_constraint_lower_projection_delta`（lower
projection ledger bootstrap）、bound-vs-carrier delta 分類（parent 列の
長さ比較）。これらは §11 の4項目のいずれにも該当しないため、今回の
closure 検証のスコープ外だった。RCPF-F（legacy ledger 物理撤去）は、
この5箇所を Factored 側から供給する consumer cutover（RCPF-C〜E と
同種のパターン）を先に終えるまで着手できない。実削除は行っていない
（branch 上で read-only 確認のみ、何も commit せず branch は削除済み）。

変更（実施済み）:

- Replay claimed linkをfactored relationへ切り替える。
- claimed flat fail-openを`attributed_claim_supports`へ切り替える。
- exact link predicateをfactored/flat dispatchへ切り替える。
- ReplayConjunction clauseとdependency edgeは既存arenaを維持。
- legacy replay link ledgerはoracleとして残す。

Gate:

- exact replay link集合一致。
- support attribution一致。
- A1 exact duplicate gate。
- A4 before/after query数。
- dependency edge集合一致。
- flat fail-open結果一致。
- 12.62B比較から§12目標まで低下。

Rollback:

- link predicateとflat fail-open adapterをlegacyへ戻す。
- evaluator/upper claim切替は独立して維持可能。
- legacy link ledgerをまだ保持しているため即時rollback可能。

### RCPF-F: Flat replay ledger撤去

変更:

- `claim_parents_by_constraint`からReplay variantの常設entryを除く。
- `replay_claim_parent_keys`をfactored membershipへ置き換える。
- replay claimed linkのexpanded HashSet/Vecを除く。
- compatibility iteratorをfactored store上へ実装。
- structural/reductionのflat storeは残す。

Gate:

- RCPF-Eまでの全oracle一致。
- productionからfull expansion callがゼロ。
- §12のwall time/RSS/operation gate。
- repository test suiteとintegration gate。
- portable provenance比較。
- no unexplained epoch shift。

Rollback:

- RCPF-Eとは別commitにする。
- 問題があればRCPF-Fだけを戻し、dual-write legacy ledgerを復元する。
- RCPF-C〜Eのconsumer変更を同じrollbackへ混ぜない。

### 11.1 Stop conditions

次のいずれかで実装を止め、設計レビューへ戻る。

1. exact relationをevent-time snapshotから再構成できない経路がある。
2. live endpoint集合を読む以外に履歴を保てない。
3. first representative lineageがlegacyと一致しない。
4. factorized exact link集合がlegacyと一致しない。
5. confirmed pathでfail-openが必要になる。
6. snapshot共有のために異なるadmission eventを一batchへ混ぜる必要がある。
7. before/after viewを同じevaluation roundへ混ぜる必要がある。
8. cycle結果がquery順に依存する。
9. exact no-opがallocation、epoch、cache invalidationを発生させる。
10. ParentSet backendが実質的に5,000万tupleを再物理化する。
11. portable provenanceがexact carrier/root/sideを失う。
12. `scheme_projection_lower_record_memberships`との同期が壊れる。
13. metadata-only epoch挙動の変更がRCPF landing条件になる。
14. pinned testの期待値変更が必要になる。
15. RCPF-F前にlegacy oracleを削除しなければ性能測定できない。
16. 各sliceを独立rollbackできない。

## 12. 性能・メモリgate

### 12.1 Correctness census gate

同一input・同一baselineで、factored exact iteratorのlogical値は次と一致しなければならない。

| 項目 | baseline |
|---|---:|
| replay claim-parent | 50,386,734 |
| claim-parent合計 | 50,416,990 |
| exact clause | 847,758 |
| ReplayConjunction | 817,655 |
| exact clause-link | 28,524,776 |
| dependency edge | 1,658,682 |
| qualified carrier | 878,089 |

将来の正しいsolver変更で数値が変わる場合、このbaselineを書き換えて通すのではなく、RCPFと無関係な意味変更として別に説明する。

### 12.2 Structural performance gate

RCPF-F時点で次を必須とする。

1. productionにreplay parent一件ごとの`ClaimQualifiedParent` allocationを残さない。
2. productionにreplay claimed link一件ごとのHashSet entryを残さない。
3. Replay evaluator source inspectionをroot数倍しない。
4. new ReplayConjunction clause一件につきdependency edgeを高々二本登録する。
5. exact relationのfull expansion回数は通常loweringでゼロ。
6. no-claim workloadの新規allocationはゼロ。
7. attachment数はlogical parent数ではなくoccurrence/admission extension数に比例する。
8. factored summary entry数はunique `(result,root)`または`(record,root)`に比例する。

### 12.3 Numeric compression target

現baselineのreplay parent 50,386,734件に対して、次をRCPF完成判定の目標とする。

- physically stored parent-set entries:
  ```text
  < 5,038,674
  ```
  すなわちlogical replay parent数の10%未満。
- attachment block＋occurrence reference:
  ```text
  O(qualified replay occurrence数)
  ```
  current workloadで一occurrenceあたり平均4 attachment referenceを超える場合は分布を再調査する。
- `flat_fail_open`比較:
  ```text
  12,620,754,599 -> 100,000,000未満
  ```
  を第一目標とする。
- replay exact link HashMap insert:
  ```text
  RCPF-F後のproduction hot pathでは0
  ```
  logical insert countはdiagnostic oracleとして別に数えてよい。

snapshot reuse censusで10%目標が不可能と判明した場合、数値だけを緩和せず、ParentSet backendまたはfactorization単位を設計レビューへ戻す。

### 12.4 Wall time

比較baselineはreverse-index追補後の`std::text::parse` lowering 48.705秒とする。測定条件、build profile、cache条件を固定する。

段階ごとの評価:

- shadow/dual-write slice:
  - wall time regressionをbaseline比15%以内に抑える。
  - shadowは診断目的であり、最終性能を評価しない。
- RCPF-C〜E:
  - 各consumer切替後に支配関数を再profileする。
- RCPF-F:
  - 最低成功条件:
    ```text
    24秒以下、またはbaseline比2倍以上の改善
    ```
  - 中間project目標:
    ```text
    15秒以下
    ```
  - product側の最終目標:
    ```text
    数百ミリ秒、目安0.5秒以下
    ```

B+Cは0.5秒到達を保証しない。

RCPF-F後も15秒を超える場合、RCPFを失敗として即revertするとは限らない。logical workとmemoryを大幅に削減できているなら、その結果を新baselineとして、lower×upper region化またはlazy pivot solverを次の設計対象にする。

一方、parent/link workを削減してもwall timeが2倍未満しか改善しない場合は、RCPFだけで性能問題を閉じたと主張しない。新profileから支配要因を再局所化する。

### 12.5 Memory

- peak RSSをbaseline比30%以上削減することを目標とする。
- swap使用量を増やさない。
- full expansion oracleはtest/debug時だけ許可し、production peak RSS測定へ混ぜない。
- ParentSet checkpointが一時的にbaseとexpanded setの両方を長時間保持しない。
- shadow期間にメモリが危険域へ入る場合、sampled oracleまたは短縮fixtureへ切り替え、無制限のdual ledger実行を強行しない。

### 12.6 Suite gate

最終landing前に少なくとも次を通す。

- constraints module tests。
- CDM/MPC/DPN/A1〜A4 pinned tests。
- insertion-order fixtures。
- cache on/off comparison。
- full infer tests。
- std lowering characterization。
- portable provenance comparison。
- no-claim allocation census。
- wall timeとpeak RSS計測。

既知pre-existing failureは新規failureと分離して記録する。

## 13. 棄却案

### 13.1 Exact carrier keyの粗化

`rule`、`pivot`、`lower`、`upper`のいずれかをkeyから落とす案。

棄却理由:

- `95b95586`が閉じたcarrier conflation bugを再導入する。
- pinned testと正面衝突する。
- ReplayConjunction exact/semantic censusに圧縮余地がない。

### 13.2 Semantic clause dedupだけを進める

ReplayConjunctionをpremise pairでdedupする案。

棄却理由:

- 817,655 exact = 817,655 semantic。
- 支配する5,000万parentと2,850万linkを削減しない。
- 実測に反する。

### 13.3 Live endpoint parent集合の参照

carrierがlower/upper record IDだけを持ち、必要時に現在のclaim集合を読む案。

棄却理由:

- covered/uncoveredはlivenessで変わる。
- incremental route除外を再現できない。
- late claimが過去occurrenceへ遡及してしまう。
- first representative lineageを失う。
- admission時完全性ではなく後付け再構築になる。

immutable/versioned snapshotが必須である。

### 13.4 Carrierごとのroot HashSetへ置換するだけ

flat global keyを、carrierごとのHashSetへ移す案。

棄却理由:

- keyのprefix重複は減るが、50,386,734 root membership自体は残る。
-同じendpoint集合をcarrierごとにcopyする構造が変わらない。
- 期待できるのは定数倍改善だけである。

### 13.5 Dense bitset / intervalを先に採用する

root IDをbitsetやintervalで圧縮する案。

現時点では採らない。

- root IDの局所性・連続性を測っていない。
- carrierごとのdense bitsetは逆に巨大化し得る。
- 根本の共有単位を決める前にbackendを固定する理由がない。

ParentSetArenaのbackend候補としてcensus後に評価する。

### 13.6 Lower集合×Upper集合regionを第一段階にする

carrier edgeをbiclique/regionとして保持する案。

現時点では後順位とする。

- all-pair含意自体はworst caseで必要。
- weightsとcanonical resultによりregionが分割される。
- exact carrier clauseは現在817,655件必要。
- 既知のより大きな増幅はcarrier×root relationにある。
- biclique圧縮率をまだ測っていない。

RCPF後にcarrier workが支配的なら正式設計へ進む。

### 13.7 Pivot graphを残すlazy solver

`L <: pivot <: U`を媒介ノードのまま保持し、必要時だけconsequenceを展開する案。

将来候補だが本書では採らない。

- solver replay、weights、row reduction、evidence、provenanceの全面変更になる。
- MPC/DPN premise graphとの相互作用を再証明する必要がある。
- RCPFよりblast radiusと健全性リスクが大きい。

### 13.8 Bound dominanceの強化

新しいsubsumption規則でlower/upper frontierを削る案。

棄却理由:

- endpointだけでなくweights、evidence、claim provenanceを含むimplication証明が必要。
-誤ったpruningは必要なsubtyping consequenceを失う。
-現在の性能問題を理由に意味規則を推測で追加できない。

### 13.9 Global repair / delayed flush

parent relationをdirty-markし、後で再構築する案。

棄却理由:

- CDMが守るadmission時完全性を破る。
- stale-read窓とflush順序を導入する。
- A4のnatural-event atomicityと異なる。
- 不動点反復へ近づく。

### 13.10 Permanent evaluator cache

projectabilityをoccurrence/result単位で恒久memoする案。

棄却理由:

- liveness、proof、clause、dependency、record inclusionの全mutationへ新しいinvalidation義務が生じる。
- A3はround-local memoだけを承認している。
- relation factorizationで先に入力走査量を削るべきである。

### 13.11 異なるrecord/eventを一batchへ混ぜる

shared snapshotを理由に複数resultやlower recordのpublicationを一つにする案。

棄却理由:

- A4のbatch境界に違反する。
- before/after viewを曖昧にする。
- epochのnet changeを正しく帰属できない。

storage sharingとmutation batchingは別概念として保つ。

### 13.12 Structural/reduction-routeも同時にfactorizeする

棄却理由:

- structural 30,127、reduction 129に対し、replayは50,386,734。
- DPN premise意味論まで同時に触る必要がない。
- rollback境界が広がる。
- 既知の支配要因に集中できない。

### 13.13 Clone削減・entry APIだけで閉じる

一時Vec clone、HashMap entry、capacity reserveだけを最適化する案。

棄却理由:

- 5,000万parentと2,850万linkのabsolute volumeが残る。
- 数百ミリ秒目標へ必要な桁の削減にならない。
- RCPF実装中の局所改善としては有効だが、完成形にはならない。

### 13.14 Exact provenanceを捨てる

diagnosticsで使わないという仮定でroot/side/carrier relationを削除する案。

棄却理由:

- exact carrier invariantに違反する。
- MPC occurrence帰属を失う。
- portable provenanceと将来の監査能力を壊す。
- 現在のproduction consumerが少ないことは、意味上不要である証明にならない。

RCPFはexact relationを保存し、通常consumerだけが展開しない設計である。

---

著者: Claude (Sonnet 5)

ユーザ承認済み。
