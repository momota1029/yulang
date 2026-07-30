# derived structural bound の claim propagation 修正設計（ドラフト）

日付: 2026-07-30

状態: **未承認・ユーザレビュー待ち**

本書は後続セッションでの設計判断に供するドラフトである。semantic implementation は開始しない。
推奨案を記すが、選択済みの仕様とは扱わない。

調査基準は `d27a5140f3c9cc32ee2c8cf42d4cc95b1c4fbb46`。
同 commit は URR-H1 / H2 / H3 の完了記録までを含む。
根因の session trace は
`notes/bugs/2026-07-28-local-var-effect-residual-transport-gap.md` の「41回目」と、
同セッションで続けた read-only investigation を正本とする。

本書のコード行番号は `d27a5140` の working tree に対して再確認した。
arena ID は一回の確定 trace を説明するためにだけ使い、test oracle や実装分岐には使わない。

## 0. ドラフト上の推奨方向

本書がレビュー対象として推奨する方向は次の通り。

1. claim lineage を upper-bound replay 専用の付帯情報から、
   **canonical constraint が作る derived bound 全体の proof qualification** へ拡張する。
2. lower / upper bound の replay では、exact `BinaryReplayDerivation` が参照した lower record と
   upper record の両方から claim-qualified parent を採る。一方を record-wide に選ばず、
   parent claim ごとの独立 lineage として result constraint へ登録する。
3. `enqueue_derived_subtype` が作る structural child は、親 constraint の claim-qualified
   parents を exact `StructuralDerivation` とともに引き継ぐ。row rule だけを特別扱いしない。
4. `Pos::Row(...) <: Neg::Var(target)` のような one-sided concrete lower admission でも、
   stable な lower `BoundRecordId` が確定した時点で producer constraint の claim qualificationを
   直接 link する。Var–Var upper record の生成を claim linkage の前提にしない。
5. canonical lower record に covered proof と independent proof が同居する場合は、
   endpoint を一回だけ project し、independent uncovered proof だけを scheme provenance の
   根拠にする。record-wide suppression は行わない。
6. new / duplicate / prefiltered duplicate / evidence-only / promotion の全経路で、
   claim metadata を canonical constraint または exact bound key から定数時間で合流する。
   bounds 全体、constraint graph、derivation graph の global scan は行わない。
7. ordinary no-claim workload は現在の raw passthrough を維持する。claim-aware proof ledger は、
   claim が実際に触れた canonical constraint / lower record にだけ遅延 materialize する。

この方向のうち、特に「両側の claim を同じ result の独立 lineage として扱う」ことと、
「mixed record の independent proof をどの ID で表すか」は genuine design decision である。
ユーザレビュー前に確定事項として扱わない。

## 1. 問題

### 1.1 H1 / H2 / H3 が解いた問題とは異なる

`notes/design/2026-07-29-unweighted-row-reduction-fix.md` の v6 は、次を閉じた。

- H1: canonical upper claim、compressed coverage root、binary replay lineage、
  initial unmatched reduction route の self-tagging、mirror lower record linkage
- H2: scheme compaction の positive lower collectionを
  `scheme_projectable_lowers`へ接続
- H3: positive alias expansion と generalized witness collectionを同じviewへ接続

`d27a5140` までの gate では、287-case contract suite、five-case characterization、
specialize / yulang suite が safe であることが確認された。
最初の covered alias

```text
BoundRecordId(10185)
TypeVar(1669) <- Var(TypeVar(1522))
```

も raw bounds には残る一方、
`scheme_projectable_lowers(TypeVar(1669))` から正しく除外された。
したがって、H1 の claim identity、H2 の compaction wiring、H3 の alias / provenance consumer
wiring のいずれも、この record については契約どおり動作している。

それでも
`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`
（`crates/infer/src/lowering/tests/local_var_effect_boundary_edge_comparison.rs:460-609`）は失敗する。
残る family は `10185` 自体から raw alias consumer を迂回して再流入するのではない。
solver がその後に作った別 owner の concrete-row lower records が、
元 claim と無関係な `Unclaimed` record として schemeへprojectされる。

これは H2 の multihop coalescing bugでも、H3 の consumer bypassでもない。
**derived constraint と one-sided bound admissionを横断する claim propagation contract が
最初から存在しない**ことが新しい根因である。

### 1.2 確認済みの row decomposition 経路

`ConstraintMachine::step_subtype` は row-against-row の concrete constraintを
`crates/infer/src/constraints/machine/propagate.rs:330-332` で
`enqueue_row_items`へ渡す。

`enqueue_row_items` 本体は同ファイル `:708-830` にある。
各 lower item は次の順に分類される。

1. variable item は `variable_items` へ分ける（`:720-724`）。
2. upper prefixと一致する concrete item は row-item matchへ送る（`:726-737`）。
3. 一致しない effect-family marker は `row_tail_items`へ入れる（`:738-740`）。
4. その他の concrete item は upper tailへ直接送る（`:741-751`）。

`row_tail_items` が空でなければ、`:755-780` はその marker 群を同じ `PosId` itemを使う
`Pos::Row(...)`へ再構成し、次の structural childを作る。

```text
Pos::Row(unmatched marker items) <: upper_tail
StructuralDerivationRule::RowItem {
    route: RowItemRoute::MarkerAggregateToUpperTail,
    ...
}
```

upper tail が `Neg::Var(target)` なら、この child は
`step_subtype` の one-sided branch
（`propagate.rs:150-160`）へ入り、`add_lower_bound`だけを呼ぶ。
lower が `Pos::Var` ではないため、同ファイル `:104-129` の Var–Var branchには入らず、
mirror upper admissionも起きない。

`TypeBounds::add_lower` は
`crates/infer/src/constraints/mod.rs:728-756` で次の semantic keyを作る。

```text
BoundSemanticKey::Lower {
    owner: target,
    endpoint: row_pos,
    weights,
}
```

`BoundSemanticKey` 自体も同ファイル `:1883-1895` で owner をkeyに含む。
したがって row type nodeを再利用しても、target ownerが変われば別のcanonical lower recordになる。
confirmed traceでは次の四recordがこの形で作られた。

```text
BoundRecordId(10472)  call owner
BoundRecordId(10478)  result owner
BoundRecordId(10484)  outer aggregate owner
BoundRecordId(10555)  second application owner
```

いずれも `scheme_projectable_lowers` では `Unclaimed` だった。
raw row nodeのidentityは共有されても、bound record identityとclaim linkageは共有されない。

### 1.3 claim identity が最初に失われる地点

最初の causal break は row decomposition そのものではない。
その手前の ordinary lower-bound replay planning にある。

`lower_bound_replay_actions`
（`crates/infer/src/constraints/machine/bounds.rs:1060-1135`）は、
新しい lower record と既存 upper record の各pairから
`BinaryReplayDerivation`を作る。

```text
BinaryReplayDerivation {
    pivot: target,
    lower: lower_record,
    upper: upper_record,
    rule: ReplayRule::LowerBoundAdded,
}
```

confirmed pathでは、この `lower` が claim-linked `BoundRecordId(10185)`を保持する。
しかし `claim_parents` の構築は `bounds.rs:1075-1099` で
**upper record の `uncovered_claims` / `covered_claims` だけ**を読む。
`lower_record`に対応する
`scheme_projection_claims_by_lower_record`は一度も参照しない。

つまり replay provenance は `10185` を exact ID として保持している一方、
claim lineage metadata は同じrecordを見ない。
この時点で result constraint は「claim-linked lowerを使って作られた」というidentityを失う。
後続の row decomposition は、すでに claim-unqualified な parent constraintを正しく分解している
だけである。

### 1.4 downstream で復元できない二つの理由

#### structural child に claim parent を移す契約がない

`enqueue_derived_subtype`
（`crates/infer/src/constraints/machine/entry.rs:1253-1305`）は、
result constraintへ次を登録する。

- `StructuralDerivation { parent, rule }`
- `structural_scheme_routes(parent, rule)` から得た scheme-instantiation route
- canonicalization disposition

new / duplicate のどちらでも、親constraintの
`replay_claim_parents_by_constraint`または同等のclaim qualificationを移さない。
したがって、仮に row-against-row の親constraintまでclaim identityが届いても、
`MarkerAggregateToUpperTail` childへは自動的に届かない。

このhelperはrow専用ではない。`propagate.rs`で次の構造分解が共有する。

- stack / non-subtract normalization、union、intersection（`:11-102`）
- function argument / argument effect / return effect / return（`:210-270`）
- invariant constructor arguments（`:412-443`）
- tuples（`:317-328`）
- records / spreads（`:550-663`）
- variants、row items、row tails

row ruleだけへ局所tagを足すと、同じ欠落を持つ他のstructural productを残す。

#### one-sided concrete lower admission に claim-link hook がない

Var–Var constraintは `propagate.rs:104-129` で lowerをtargetへ、upperをsourceへ登録する。
upper admissionは
`bounds.rs:590-652` の `add_upper_bound` から
`register_constraint_upper_replay_claims`を呼ぶ。
この登録処理は replay / reduction-route parent から derived upper claimを作り、
producer constraintに対応する mirror lowerをscheme projection claimへlinkする
（`bounds.rs:719-783`、
`crates/infer/src/constraints/mod.rs:944-1103`）。

一方、concrete `Pos <: Neg::Var` は lower admissionだけでreturnする。
`add_lower_bound`（`bounds.rs:418-548`）はstable recordを内部で得るが、
claim linkageを登録せず、callerへrecord IDを返さない。

duplicate metadataをeagerにmaterializeする既存helper
`var_var_upper_record_for_constraint`
（`bounds.rs:850-869`）も、lower / upperが
`Pos::Var` / `Neg::Var`でなければ`None`を返す。
したがって `Pos::Row(...) <: Neg::Var(target)`には、
new admissionにもduplicate admissionにもclaimをlower recordへlinkするhookがない。

## 2. 既存設計との関係

### 2.1 local-var effect boundary 文書

`notes/design/2026-07-28-local-var-effect-boundary-fix.md` は、
local callback parameterをbody lowering中はfresh placeholderのまま保ち、
resolved private helperの二段目applicationでconcrete ref structureへ接続するv5 lifecycleを
所有する。

同文書のLVB-A3 / A4はprivate helper schemeとapplication transportを固定し、
単一boundaryとparsed nested controlが正しくdischargeされることを示した。
今回のfailureはlocal-var path文字列、callback helper構造、TypeLevel、
block aggregate constructionを再設計する根拠ではない。

motivating testは発見witnessとして残すが、修正責務はconstraint machineにある。
local-var loweringでconstraint順を変えたり、inner familyだけをfinalize時に消したりしない。

### 2.2 URR v1〜v6 文書

`notes/design/2026-07-29-unweighted-row-reduction-fix.md` は、
one-shot reduction、persistent state、claim / coverage / lineage、
initial unmatched route、scheme-projectable viewと三consumerの共有を段階的に設計した。

本書は次を再設計しない。

- unweighted reduction state の matching / routing
- compressed coverage root と live coverage lookup
- initial unmatched armだけのexplicit self-tag
- `scheme_projectable_lowers`のprojection-time liveness
- compaction / alias / generalized witnessのshared consumer contract

本書が拡張するのは、それらが作ったclaim identityを、
後続のordinary replay、structural decomposition、concrete lower admissionへ運ぶ契約である。
`row_effect.rs:329-345` のinitial matched / unmatched分離と、
`:475-530` のroot claim / exact row carrier登録は現行どおり正しい。

H3 completion gateがこのgapを発見したのは、H3が誤っていたからではない。
H3によって最初のclaim-linked aliasが確実に除外され、
その先にあるunclaimed concrete productsが初めて独立に観測可能になった。

## 3. blast radius

### 3.1 replay planning

`lower_bound_replay_actions`はordinary lower-bound insertionの一般hot pathである。
対象はeffect rowに限らず、新しいlowerと既存upperがmeetする全replayである。

`upper_bound_replay_actions`（`bounds.rs:1170-1215`）にも対称性がある。
現行はupper recordのclaimだけをparentにし、各lower recordのclaim qualificationを読まない。
今回のconfirmed breakはlower-bound-added pathだが、設計は両replay directionを同じcontractへ
揃えなければならない。

### 3.2 structural propagation

`enqueue_derived_subtype`はfunction、constructor、tuple、record、variant、union、
intersection、normalization、row decompositionが共有する。
claim propagationを追加した場合のsemantic blast radiusはsolverのほぼ全concrete structural
subtypingである。

一方、意味が変わるべきrecordは、claim-qualified parent constraintから導かれたchildだけである。
claim metadataを一度も持たないconstraintは、queue、canonical constraint、bound、scheme、
provenanceのすべてでbyte-for-byte no-opでなければならない。

### 3.3 one-sided lower admission

`propagate.rs:150-160` はすべてのconcrete positive shapeからvariable upperへのadmissionを扱う。
rowだけでなく、constructor、function、tuple、record、variant、union、intersection、
normalization productがここへ到達しうる。

Var–Varだけを対象にしたcurrent linkageを形状ごとのbranchで増やすと、
solver全体へ同じhookの複製が広がる。
stable lower record admissionを一つの責務境界にする必要がある。

### 3.4 canonical merge と evidence

replay actionはnew constraintだけでなく、prefiltered duplicate、queue-suppressed duplicate、
evidence-only storageを通る。
現行codeは
`bounds.rs:1397-1429`、`:1431-1525`、`:1527-1555` でこれらを分け、
exact `BinaryReplayDerivation`とcurrent upper-side claim parentを保存している。

新contractは同じ全経路でlower-side / structural claim identityを保つ必要がある。
new pathだけを直すとcanonical duplicateで再現し、evidence pathだけを後回しにすると
production workloadのrouting shadow有無でprojection結果が変わる。

### 3.5 performance

許容する追加探索は次だけである。

- replayがすでに持つexact lower / upper recordにlinkされたsmall claim set
- canonical result constraintにlinkされたsmall claim parent set
- exact lower semantic keyから得るstable `BoundRecordId`
- claimが実際に触れた一canonical lower recordのlocal derivations
- compressed rootからのlive coverage lookup

禁止する探索は次である。

- 全bound recordのscan
- 全claimのscan
- constraint / structural / row derivation graphのpost-hoc逆走査
- row node identityからowner recordを探すscan
- scheme consumerごとの別classification

claim / projection-proof metadataはcanonical
`(result constraint or lower bound, coverage root, carrier kind)`でboundedにする。
alternate proofの完全な説明は既存provenance recordへ残し、claim tableへ全graphをcopyしない。

## 4. 必須 invariant

### 4.1 claim propagation はsubtype relationを作らない

claim metadataは、solverがすでに作るcanonical subtype constraintとboundについて、
どのlogical claimから導かれたかを記録するaccountingである。
claimを理由に新しいrow item、subtype edge、bound、replayを作らない。

### 4.2 exact carrier

replay lineageはexact `BinaryReplayDerivation`をcarrierとする。
lower-side inheritanceでは、carrierの`lower`がparent claimへlinkされたlower recordと一致する。
upper-side inheritanceでは、carrierの`upper`がparent claimのcurrent upper recordと一致する。

structural lineageはexact
`StructuralDerivation { parent, rule }`をcarrierとする。
row path、rule名、endpoint shapeだけからparent claimを推測しない。

### 4.3 per-proof projectability

canonical lower recordは、複数のindependent proofを持ちうる。
covered proofが一つあるという理由でrecord全体を隠さない。
uncovered / unclaimed independent proofが一つでもあれば、endpointを一回projectする。

scheme provenanceはprojectable proofだけを根拠にする。
raw `BoundRecord`、全derivation、covered claimはaudit sourceとして残す。

### 4.4 liveness

derived claimはparentのcompressed coverage rootを使う。
coverageをchild recordへbooleanとしてcopyしない。
rootのlast live stateが外れれば、active raw relationは再びprojectableになる。

### 4.5 duplicate idempotence

同じcanonical result、同じcompressed root、同じcarrier kindへ再到達しても、
claim / projection proofを増やさない。
semantic queueがduplicateとして抑止されてもmetadata mergeは失わない。

### 4.6 fail-open と completeness

claim carrier、parent record、root、lower linkのいずれかが壊れている場合、
release buildでrelationをcoveredとして黙って消さない。
scheme projectionは情報を失わない側へfail-openし、provenance completenessとtimingに記録する。

ただしconfirmed pathでfail-openが一件でも必要な実装はlandingしない。
fail-openは不完全実装を正当化するfallbackではない。

## 5. design questions と推奨回答

### 5.1 replay resultはlower、upper、両方のどこからlineageを継ぐか

#### 案A: upper claimだけを継ぐ

現行方式である。URR-H1のcross-source upper transportには合うが、
claim-linked lower `10185`を見ないためconfirmed gapを再現する。

判断: 採らない。

#### 案B: lower claimだけを継ぐ

今回のpathは閉じる。しかし、unclaimed lowerを使ってcovered upperを別sourceへ運ぶ
URR-H1の既存cross-source contractを壊す。

判断: 採らない。

#### 案C: `ReplayRule`またはinsertion directionで片側を選ぶ

`LowerBoundAdded`ならlower、`UpperBoundAdded`ならupperをownerにする案である。
しかしlower-bound-added replayでも、existing covered upperをunclaimed lower経由で運ぶ
confirmed H1 pathがある。queueへ後から来た側とlogical ownershipは一致しない。

判断: 採らない。

#### 案D: lower / upperの両側から、parent claimごとに継ぐ

exact replay edgeが参照するlower recordとupper recordの双方から、
claim-qualified parentを列挙する。
各parent claimは別のderived lineageを作り、record-wideな「両方covered」booleanへ潰さない。

同じresultにcovered rootとindependent uncovered rootが届けば、
covered lineageだけをschemeから除外し、uncovered lineageがendpointを一回projectする。
lineage carrierにはparent sideを明示する。

```text
ReplayConstraint {
    parent_claim,
    parent_side: Lower | Upper,
    result,
    replay,
    depth,
}
```

推奨: 案D。

理由は、`BinaryReplayDerivation`自体がlower / upper両recordをexactに保持しており、
片側を発見的に選ぶ必要がないためである。
claim数に対する加算的なmergeで済み、lower × upper claimの直積を作らない。

ただし「同じ一replayに付いた両側claimを独立lineageとみなす」という意味判断は
レビュー対象である。両側を一つのconjunctive coverage tokenへまとめる案も理論上ありうるが、
それはcurrent per-claim mixed-record contractを変更し、root集合の直積またはBoolean proof
representationを必要とする。採用するなら別設計としてperformanceとprojectabilityを
再証明すべきであり、本ドラフトの既定案にはしない。

### 5.2 structural childはどうclaim-qualified parentを継ぐか

#### 案A: rowの`MarkerAggregateToUpperTail`だけをtagする

motivating pathには最小だが、function return effect、constructor、tuple、record等の同じ欠落を
残す。rule whitelistが増え、inferenceにtest-shape依存の例外を作る。

判断: 採らない。

#### 案B: `enqueue_derived_subtype`で全structural ruleへ一般的に継ぐ

parent constraintに登録済みのclaim-qualified parentsを、
exact child `StructuralDerivation`とともにresult constraintへmergeする。
new / duplicateの両方で同じ処理を行う。

```text
StructuralConstraint {
    parent_claim,
    result,
    derivation: StructuralDerivation { parent, rule },
    depth,
}
```

trivial childはcanonical resultを持たないためclaimも作らない。
`merge_structural_derivation`もsemantic queueを再実行せず同じmetadataをmergeする。

推奨: 案B。

structural decompositionは親constraintのlogical consequenceを作る共通入口であり、
rowだけを区別する意味上の理由がない。

#### 案C: scheme projection時にstructural graphを逆走査する

production changeは小さく見えるが、全scheme / 全lower queryをnon-local graph walkへ変える。
duplicate、cycle、provenance budget、cache invalidationの責務もprojection側へ漏れる。

判断: 採らない。

### 5.3 one-sided concrete lower admissionをどうclaim-linkするか

#### 案A: concrete lowerにdummy Var–Var upperを作る

current hookを再利用できるが、claim accountingのためだけに新しいsemantic relationとfresh varを
作る。solver結果、replay数、simplificationを変える。

判断: 採らない。

#### 案B: `add_upper_bound`のあとでrow lowerを探索してlinkする

one-sided pathにはupper admissionがなく、ownerまたはrow nodeからrecordを探すglobal scanが要る。
row以外のconcrete shapeにも拡張できない。

判断: 採らない。

#### 案C: stable lower admissionを独立hookにする

`add_lower_bound`またはそのnarrow internal primitiveが、
insert / equivalent / evidence promotion後のstable `BoundRecordId`を返す。
producer constraintのclaim-qualified parentsがあれば、その場でlower recordへlinkする。

queue-suppressed duplicateでclaim metadataだけが後着した場合は、
result constraintの`Neg::Var(target)`とexact
`BoundSemanticKey::Lower { owner: target, endpoint: lower, weights }`からrecordを引く。
lowerが`Pos::Var`かconcreteかは問わない。

推奨: 案C。

これに伴い、claim作成をupper admission、scheme lower linkageをlower admissionへ責務分離する。
Var–Var pathも最終的には同じlower hookを使い、二つのlinkage実装を残さない。

### 5.4 mixed covered / uncovered derivationをどう守るか

#### 案A: claimが一つでもあればrecord全体をcoveredにする

独立direct relationを失い、URR §8.1 / §8.2 / §8.4のmixed controlsを壊す。

判断: 採らない。

#### 案B: uncovered claimが一つでもあれば全derivationをscheme provenanceへ出す

semantic endpointは保てるが、covered proofまでgeneralized witnessへ再混入する。
H3が導入した`BoundClaim`の精度を失う。

判断: 採らない。

#### 案C: lower recordへprojection proof ledgerを遅延構築する

claim-aware lineageが初めてlower recordへlinkされる時点で、
そのrecordのlocal derivationsだけを分類する。

意味形は次とする。

```text
SchemeProjectionProof {
    lower_record,
    support:
        Claimed(UpperReplayClaimId)
        | Independent(ProjectionProofCarrier)
}

ProjectionProofCarrier =
    Constraint(ConstraintRecordId)
    | ReplayEvidence(BinaryReplayDerivation)
    | other exact existing BoundDerivation carrier
```

claimを持たないordinary recordはledgerを作らず、従来の`Unclaimed` fast pathを使う。
ledgerがあるrecordは次で判定する。

```text
projectable supports =
    independent supports
    + claims whose compressed root has no live coverage

supports is empty
    => suppress

supports is non-empty
    => yield endpoint once, with only those supports
```

同じcanonical recordへ後からindependent derivationがmergeされた場合は、
そのlocal insertionでindependent supportを追加する。
同じproducer / carrier / rootはdedupする。

推奨: 案C。

generalized witnessには、claimed supportなら既存`BoundClaim`を使う。
claim-aware mixed record上のindependent supportはraw `Bound(record)`へ戻さず、
exact independent carrierを指す新しいqualified parent、または同等の表現を使う。
そうしなければraw boundからcovered derivationまで展開されるためである。

この新parentをportable provenanceへ安全に表現できない場合は実装を止める。

### 5.5 duplicate / evidence / canonical mergeをglobal scanなしでどう保つか

#### 案A: queue drain後にclaimとboundsを照合するrepair pass

全bounds walkが必要で、incremental solverのepoch / cache / provenance lifecycleと二重管理になる。
production sessionの大きさに比例し、H1のhot-path contractに反する。

判断: 採らない。

#### 案B: admission時metadataとreverse indexを使う

次のindexをcanonical ownerとする。

```text
claim_parents_by_constraint:
    ConstraintRecordId -> small set<ClaimQualifiedParent>

projection_proofs_by_lower_record:
    BoundRecordId -> small set<SchemeProjectionProof>

lower_record_by_constraint:
    ConstraintRecordId -> BoundRecordId

lower_record_by_replay:
    BinaryReplayDerivation -> BoundRecordId

lower_records_by_coverage_root:
    UpperReplayClaimId -> small set<BoundRecordId>
```

- new constraint: parent metadataをconstraint recordへ登録してからqueueへ入れる
- canonical duplicate: metadataをsame resultへmergeし、exact lower keyが既にあればeager linkする
- prefiltered duplicate:既存resultへexact replay / structural carrierとparentをmergeする
- evidence-only: evidence lower insertionが返すrecordへ直接linkする
- promotion: 同じcanonical record identityを使い、support ledgerを移し替えない
- trivial: boundを作らないためprojection proofも作らない

derived claimはcurrent `(target record, compressed root)` coalescingを維持し、
carrier side / kindはprovenanceとしてexact resultへ残す。
projection proofは`(lower record, support identity)`でdedupする。

推奨: 案B。

lookup costは、そのadmissionがすでに知るconstraint / boundと、
そこへlinkされたclaims / supportsに比例させる。
machine全体のclaim数やbound数には比例させない。

## 6. 推奨するデータフロー

### 6.1 replay planning

1. replay actionは従来どおりexact lower / upper recordを持つ。
2. upper recordのclaim parentsに加え、lower recordのscheme-projection claim supportsを読む。
3. parent sideを付けたclaim IDをactionへ載せる。
4. semantic actionはclaim数だけ重複enqueueしない。constraint一件とsmall parent setを作る。
5. new / duplicate / evidence pathがparent setをcanonical resultへmergeする。

covered / uncoveredの判定はaction作成時に固定しない。
parentのcompressed rootだけを引き継ぎ、projection時のlive root lookupを維持する。

### 6.2 structural propagation

`enqueue_derived_subtype`はcanonical childを得た後、親constraintに登録されたclaim parentsを読む。
各parentについてexact structural carrierを付け、childの
`claim_parents_by_constraint`へmergeする。

duplicate childではqueueを再実行しない。
childがすでにone-sided lowerをmaterialize済みなら、exact lower keyからrecordを引いて
eagerにprojection supportを追加する。

### 6.3 lower admission

`Neg::Var(target)`へのadmissionは、lower shapeに関係なく次を行う。

1. extrude / filter / subsumption / canonical addを従来どおり実行する
2. stable lower record IDを確定する
3. producer constraintとrecordの対応を登録する
4. producer constraintのclaim parentsをlower projection supportsへlinkする
5. claim-aware ledgerが既にある場合は、今回のindependent derivationもlocal supportへmergeする
6. semantic insertionがnewの場合だけ従来のreplay / event / dirty処理を行う

claim metadata mergeはsemantic duplicateでもreturn前に行う。
claim linkageのためにreplayをもう一度起動しない。

### 6.4 projection とprovenance

`scheme_projectable_lowers`を唯一のclassification APIとして維持する。
compaction、positive alias、witness collectionは引き続き同じiteratorを使う。

viewのreasonは、少なくとも次を区別できる必要がある。

```text
Unclaimed
Qualified {
    uncovered_claims,
    independent_supports,
}
```

`Qualified`のsupportが空ならyieldしない。
non-emptyならendpointを一回yieldする。
witness collectionはsupportだけをparentへ変換し、raw recordの全derivationを再展開しない。

### 6.5 liveness / epoch

current `scheme_projection_lower_records_by_root`相当のreverse indexへ、
derived concrete lowerも登録する。
rootのlive setがempty / non-emptyを跨いだときだけ、
影響lower ownerのscheme inclusionを再評価する。

constraint epoch、owner epoch、provenance epoch、
`DependencyKey::ConstraintBounds(owner)`の契約はURR-H1を維持する。
新しいglobal invalidation phaseは作らない。

## 7. 採らない方向

### 7.1 row-specific patch

`MarkerAggregateToUpperTail`だけへreduction claimを直接付ける案は採らない。
そのruleの親constraintがどのclaimから来たかをpost-hocに推測し、
他のstructural derivationを未修正のまま残す。

### 7.2 arena ID / family path special case

`BoundRecordId(10185)`、`10472`等、`&buffer` family、
local-var helper名、fixture名を実装条件に使わない。
IDは一回のtrace説明に限る。

### 7.3 concrete row nodeへのclaim埋め込み

同じ`Pos::Row` nodeは複数owner / weights / producerのboundに使われうる。
type nodeへclaimを付けるとcanonical bound identityを失い、
independent derivationを同じcoverageへ巻き込む。

### 7.4 record-wide taint

「covered recordから一度でも導かれた」をbooleanでlower recordへ焼き付けない。
mixed proofとlast-live-state transitionを表せない。

### 7.5 finalizer cleanup

完成済みschemeから特定effect familyを削除しない。
誤ったderived lowerがprojectableになった原因を隠すだけである。

### 7.6 lowering order workaround

parsed controlと同じconstraint orderへhand-built loweringを寄せない。
同じcanonical solver relationの意味がconstruction orderへ依存する状態を残す。

### 7.7 global repair scan

generalization前、queue quiescence後、finalize前のいずれにも、
claim graphとbound graphを全照合するrepair passを置かない。

## 8. regression test specs

production codeを変更する前に、次のtestを
`crates/infer/src/constraints/tests/case_02.rs`を中心に追加する。
arena IDをhard-codeせず、canonical record、claim root、exact carrier、
view reasonを構造的に観測する。

### 8.1 replay lower-side claim inheritance

scenario:

1. covered reduction root `A`を作る。
2. そのmirror lower record `R_lower`がscheme projection claim `A`へlinkされていることを確認する。
3. `R_lower`とunclaimed ordinary upperをreplayさせる。

expected:

- result constraintの`BinaryReplayDerivation.lower == R_lower`
- resultに`parent_side = Lower`、`parent_claim = A`のlineageがある
- child claimのcompressed rootは`A`
- upper-only lookupのままならこのassertionだけがredになる
- semantic constraint / replay countはclaim metadata追加で増えない

### 8.2 existing upper-side inheritance control

scenario:

1. covered upper claim `A`を持つsourceへ、claimを持たない別source lowerを追加する。
2. current URR-H1 cross-source shapeと同じbinary replayを作る。

expected:

- resultは`parent_side = Upper`で`A`を継ぐ
- lower-side supportがないことを理由にlineageを失わない
- §8.1修正後も既存H1 contractのroot / depth / cycle countが変わらない

### 8.3 both-side mixed replay

scenario:

1. lower recordにcovered claim `A`とindependent direct proofを同居させる。
2. upper recordに別root `B`のcoveredまたはuncovered claimを置く。
3. 一つのcanonical replay resultへ到達させる。

expected:

- lower / upperのclaim parentはside付きで区別される
- 同じsemantic replay constraintは一件だけである
- result recordはindependent uncovered supportがある間、一回だけprojectable
- covered `A` / `B` proofはgeneralized witness parentへ混ざらない
- endpoint数をclaim数だけ増やさない

### 8.4 structural row aggregate propagation

scenario:

1. claim-qualified parent constraintを
   `Pos::Row([matched item, unmatched effect marker]) <: Neg::Row(..., tail_var)`の形で作る。
2. `enqueue_row_items`にrow decompositionさせる。

expected:

- `MarkerAggregateToUpperTail` childがexact
  `StructuralDerivation { parent, rule }`を持つ
- child constraintが親のclaim rootを継ぐ
- 再構成された`Pos::Row(marker) <: Neg::Var(tail_var)`のlower recordが同rootへlinkされる
- raw lowerは存在するがlive coverage中はscheme viewから除外される

### 8.5 non-row structural propagation control

scenario:

function return effect、tuple element、constructor invariant argumentの少なくとも二shapeで、
claim-qualified parentからone-sided `concrete Pos <: Neg::Var` childを作る。

expected:

- row ruleと同じgeneric structural carrierでclaimを継ぐ
- rule名のwhitelistやeffect-family classificationを必要としない
- ordinary unclaimed controlのconstraint / bound / schemeはbyte-for-byte不変

### 8.6 one-sided concrete lower admission

scenario:

`Pos::Row([F]) <: Neg::Var(target)`をclaim-qualified producerから直接admitし、
Var–Var upper sideを一切作らない。

expected:

- stable lower recordが作られる
- `var_var_upper_record_for_constraint`に頼らずclaim supportがlinkされる
- live root中はviewから除外、last live state除去後は同じraw recordが再びprojectable
- type node / lower record / claim rootのidentityを別々に観測できる

### 8.7 independent same-key lower remains projectable

scenario:

test 8.6と同じlower semantic keyへ、claim lineageを持たないreal direct constraintを追加する。
順序は「direct first / claimed later」と「claimed first / direct later」の両方を試す。

expected:

- canonical lower recordは一件
- covered proofとindependent supportは別identity
- live root中もendpointを一回projectする
- generalized witnessはindependent supportだけをparentにする
- insertion orderでview / compact / alias / provenanceが変わらない

### 8.8 duplicate / evidence-only preservation

scenario:

同じclaim-qualified structural resultを、
new、canonical duplicate、prefiltered duplicate、evidence-only / promotionの各pathで作る。

expected:

- 全pathで同じcompressed rootとexact carrierを保持する
- semantic queueの再実行なしに既存one-sided lowerへeager linkされる
- claim / projection proof数はcanonical `(lower record, root, support kind)`数で固定
- `IncompleteReplay`またはfail-openを必要としない

### 8.9 motivating integration

既存
`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`
のexpectationを変更せず使う。

expected:

- original alias recordは従来どおりcovered
- call / result / outer aggregate / second applicationのderived concrete row recordsも、
  exact replay + structural carrierを通じて同じcompressed rootへ属する
- それらはraw auditには残るがlive coverage中は`Unclaimed`にならない
- parsed / hand-built outer finalized schemeが一致し、inner familyを含まない
- outer family、ordinary observe effect、stack quantifierの既存assertionは変わらない

## 9. implementation slicing plan

本書がレビューを通るまで、どのsliceも開始しない。
各sliceは前sliceのgateを閉じてから進め、production consumerを先行変更しない。

### DCP-A: red baseline と proof model preflight

変更:

- §8.1〜§8.8のtest helperとtest specを追加する
- lower / upper parent side、structural carrier、one-sided lower record、
  projection supportを観測できるtest-only inspectionを用意する
- motivating test、five-case、287-case、claim / bound / replay census baselineを保存する

gate:

- §8.1、§8.4、§8.6がcurrent gapによりred
- §8.2のexisting upper-side controlがgreen
- §8.7のindependent relationはcurrent semanticsで失われていないcontrolを分離できる
- expected schemeをcurrent leakへ合わせない
- production solver codeを変更していない

### DCP-B: replay両側のclaim parent

変更:

- replay actionへside付きclaim parentsを載せる
- exact lower recordのclaim supportsとupper record claimsを加算的にmergeする
- new / duplicate / prefiltered duplicate / evidence pathへ同じmetadataを通す
- `(result, root, parent side)`のdedup / censusを追加する

gate:

- §8.1、§8.2、§8.3のreplay-lineage assertionsがgreen
- existing URR-H1 binary replay / multihop / cycle testsが期待値無変更
- semantic replay accepted / duplicate / trivial countがbaseline不変
- lower × upper claimの直積を作らず、parent数に線形
- structural childとone-sided lower projectionはまだ未配線として明示される

### DCP-C: generic structural claim propagation

変更:

- `enqueue_derived_subtype`と`merge_structural_derivation`へclaim parent mergeを追加する
- exact `StructuralDerivation` carrierをlineageへ加える
- duplicate childで既存lowerへのeager metadata merge入口を用意する
- structural rule / root / duplicate censusを追加する

gate:

- §8.4、§8.5のconstraint-level lineageがgreen
- function / constructor / tuple / record / variant / rowのexisting structural testsが期待値無変更
- claimを持たないparentではallocation、hash lookup、constraint outputがbaseline不変
- rule whitelist、row path special case、derivation graph walkがない

### DCP-D: one-sided lower linkage と mixed proof ledger

変更:

- stable lower admission resultをnarrow internal APIへ出す
- any `Pos <: Neg::Var` constraintからexact lower recordをlookupできるhelperを追加する
- claim-qualified parentをone-sided lowerへlinkする
- claimが触れたrecordだけprojection proof ledgerを遅延構築する
- independent support用のclaim-qualified generalized parentとportable provenanceを追加する
- current scheme view / reverse root index / epoch mutationへ統合する

gate:

- §8.6、§8.7、§8.8がgreen
- direct-first / claimed-firstの両順序が同じview / compact / provenanceになる
- mixed recordのendpointは一回、witnessはprojectable supportだけ
- last live state transitionでview / compact / alias / witness / cacheが同じsnapshotを表す
- no-claim ownerのraw passthroughがrecord ID、順序、weights、parentを含め完全一致
- portable provenanceがcovered siblingを混ぜずcomplete

### DCP-E: integration / characterization / closeout

変更:

- §8.9 motivating pathをexact lower replay、structural child、one-sided admissionまでtraceする
- claim / projection support / duplicate / evidence / liveness censusをfive-caseへ加える必要が
  ある場合、実測差分をproducerまで説明する
- unrelated refactor、temporary trace、test-only production branchをdiffから除く

gate:

- §8.1〜§8.9がすべてpass
- existing URR regression、scheme view、alias、provenance、compact testsが期待値無変更
- motivating testがcorrected expectationのままpass
- five-case characterizationがpoly / check hashを含めzero-diff
- full 287-case contract suiteが全件pass
- `cargo test -p infer`、`cargo test -p specialize`、`cargo test -p yulang`がpass
- workspace gateの既知unrelated baselineを別にした上で、本変更由来failureがない
- repository-stdでclaim / support count、wall time、peak memory差分を説明できる

## 10. 変更しないもの

- local-var private helper、callback parameterのdeferred concrete-ref connection、
  `ArgEffectContract`を変更しない。
- unweighted row reductionのmatching、state lifecycle、initial unmatched self-taggingを変更しない。
- row item matching、payload invariance、weighted residual、row tail semanticsを変更しない。
- H2 / H3のcompaction、positive alias、witness consumerをraw pathへ戻さない。
- `finalize_generalized_compact_root`でfamily cleanupを行わない。
- co-occurrence analysis、polarity elimination、residual desugaringへrigid / blocked setを足さない。
- `Any`をunknown fallbackに使わず、`Never` / `Unknown`の意味を変えない。
- path、module、function、fixture、arena IDの文字列 / 数値special caseをinferenceへ入れない。
- test名が表す「inner familyをouter finalized schemeから除外する」意図を反転しない。
- current five-case / 287-case expectationを、説明のない実装出力へ合わせない。

## 11. stop / rollback conditions

### 11.1 stop conditions

次のいずれかが判明した時点でsemantic implementationを止め、design reviewへ戻す。

1. `BinaryReplayDerivation.lower`がconfirmed parent lower recordを保持せず、別carrierが必要になる。
2. replay両側のclaimを独立lineageとして扱うと、正しいconjunctive ownershipを失う反例が出る。
3. lower-side inheritanceのためにexisting upper-side H1 lineageを弱める必要がある。
4. replay resultをclaim数だけsemantic enqueueしなければidentityを保てない。
5. lower × upper claimの直積、またはproof path数に指数的なmetadataが必要になる。
6. structural propagationを一般化すると、特定ruleではclaimを継いではならない反例が出る。
   その場合、rule whitelistを足さず意味上の分類を別設計する。
7. `MarkerAggregateToUpperTail`、`FunctionReturnEffect`、row pathだけのspecial caseが必要になる。
8. one-sided lowerへlinkするためdummy upper、fresh var、新しいsubtype relationが必要になる。
9. stable lower recordを得るため全owner boundsまたは全canonical boundsのscanが必要になる。
10. new admissionではlinkできるが、duplicate / prefiltered duplicateでqueue再実行が必要になる。
11. evidence-only / promotionでexact claim carrierを失う、または`IncompleteReplay`へ落ちる。
12. covered proofを除外すると同じrecord上のindependent direct proofまで失う。
13. independent proofを残すためcovered proofまでplain `Bound(record)` parentへ再混入する。
14. mixed proofのportable provenanceをcompleteに表現できない。
15. last live coverage stateが外れた後もactive raw derived lowerがnon-projectableのまま残る。
16. claim / support countがcanonical record / root / carrier数ではなくreplay周回数に比例する。
17. coverage queryがconstraint / replay / structural graphのparent chainを都度walkする。
18. no-claim workloadでper-bound allocationまたはmachine-wide claim lookupが発生する。
19. compaction、alias、witnessが同じrecordについて別々のinclude / exclude判断をする。
20. current URR claim / cycle / liveness testsの期待値を変更しなければ進めない。
21. motivating testをgreenにするためraw concrete rowを一括suppressionする必要がある。
22. five-caseのpoly / check hash、formatted scheme、diagnosticにmotivating narrowing以外の差分が出る。
23. 287-case suiteにbaseline shiftが出て、exact claim root / supportまで説明できない。
24. lower / upper replay、canonical constraint、bound数がmetadataだけでは説明できない形で変わる。
25. fixのためlocal-var lowering、generalize quantifier、specialize comparison、
    finalizer cleanupを変更する必要がある。

### 11.2 rollback unit

- DCP-Aの正しいred regressionは保持する。wrong outputへ期待値を戻さない。
- DCP-Bでlower / upper両側lineageとduplicate / evidenceのいずれかが成立しなければ、
  片側だけの新propagationをlandingしない。
- DCP-Cでgeneric structural contractが成立しなければ、row-specific taggingを残さずslice全体を戻す。
- DCP-Dでone-sided linkage、mixed proof ledger、claim-qualified provenanceのいずれかが
  成立しなければ、record-wide covered flagやpartial consumer wiringを残さない。
- DCP-Eでmotivating testだけgreenでもfive-case / 287-caseにunexplained shiftがあれば、
  expectationを更新せず初めてshiftしたsliceへ戻る。
- performance gateだけが不合格でもglobal repair scanをdefault-onで残さない。

## 12. completion contract

本projectは次をすべて満たしたときだけ完了する。

1. `lower_bound_replay_actions`がexact lower / upper recordの両側からclaim parentを採る。
2. lower-side / upper-side parentはexact `BinaryReplayDerivation`とsideで説明できる。
3. semantic replay actionは一件のまま、claim metadataだけがsmall setとして合流する。
4. `enqueue_derived_subtype`が全structural ruleに共通のclaim propagation contractを持つ。
5. structural child lineageはexact parent constraint / rule / resultで説明できる。
6. `Pos::Row(...) <: Neg::Var(target)`を含むone-sided concrete lowerが、
   Var–Var upperなしでclaim-linked lower recordになる。
7. new / duplicate / prefiltered duplicate / evidence-only / promotionの全pathでidentityを失わない。
8. confirmed call / result / outer aggregate / second application recordsが、
   arena IDに依存せず元covered rootまで辿れる。
9. raw derived concrete rowsはaudit sourceとして残り、live coverage中はschemeへprojectされない。
10. same canonical lower上のindependent proofはprojectableで、endpointは一回だけyieldされる。
11. generalized witness / explanation / portable provenanceはprojectable supportだけをparentにする。
12. last live stateが外れると同じactive raw relationが再びprojectableになる。
13. compaction、positive alias、witness collectionが同じview / liveness snapshotを共有する。
14. ordinary no-claim recordsの順序、weights、compact output、alias、provenance、schemeが不変である。
15. claim / support lookupはexact constraint / bound localで、global bounds / graph scanがない。
16. claim / support数はcanonical `(record, root, carrier kind)`でboundedである。
17. `v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`が
    expectation変更なしでpassし、parsed / hand-built outer schemeがinner familyを含まない。
18. existing URR claim / coverage / lineage / scheme-view testsが期待値無変更でpassする。
19. five-case characterizationのpoly / check hash、formatted scheme、diagnosticがzero-diffである。
20. full 287-case contract suiteが全件passする。
21. infer、specialize、yulangの各suiteがpassし、本変更由来のworkspace failureがない。
22. implementation diffがconstraint-machine claim propagation、projection proof、
    provenance、tests / characterizationだけに限られ、local-var固有patchを含まない。

---
作成者: Codex (GPT-5.6 Sol、設計ドラフト)
状態: **未承認・ユーザレビュー待ち**
承認記録: なし（後続セッションでレビュー予定）
