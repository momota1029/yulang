# generalized witness の claim bridge provenance 欠落修正設計（GWCB・ドラフト）

日付: 2026-08-10

状態: **Claude 査読完了、ユーザ承認待ち**（初回査読の§11 8項目検証で6点の修正要求→反映済み。再査読で内部整合性を確認。実装着手にはユーザ承認が必要）

基準 commit: `f91fa91d`（行番号はこの commit を基準とし、実装時には再確認する）

本書は、Fable 5 が利用できない場合の代替起案手続きに基づく設計ドラフトである。
末尾の著者行は査読担当を示す house convention であり、現時点で Claude の査読完了も
ユーザ承認も意味しない。Claude の査読・確定と、その後のユーザ承認が終わるまで、
本書を `CLAUDE.md` の設計優先順位における承認済み正本として扱ってはならない。

## 0. 結論

generalization が claimed projection support を採用したとき、現行の
`ProjectionClaimSupport { coverage_root, representative_claim }` だけを渡してはならない。
record inclusion を成立させた **exact qualifying clause** と、その clause が指す exact carrier / result を
一緒に凍結した `ClaimedProjectionProof`（実装名は既存命名に合わせてよい）を渡す。

generalized witness の parent には、次の意味を持つ新しい variant を追加する。

```text
GeneralizationParent::BoundClaimProjectionProof {
    bound: BoundRecordId,                  -- audit identity
    coverage_root: UpperReplayClaimId,     -- liveness identity
    representative_claim: UpperReplayClaimId,
    proof: ClaimedProjectionProof,         -- exact qualifying clause snapshot
}
```

`explain.rs` はこの parent を plain `Bound(bound)` として通常展開しない。
同じ `ExplanationNodeId::Bound(bound)` を graph 上の node identity として残しつつ、
その到達についてだけ `proof` が指定する exact edge を展開する。
具体的には motivating path の `ReplayConjunction / ReplayConstraint` なら、

```text
GeneralizedWitness
  -> lower Bound
  -> replay-result Constraint
  -> [exact lower premise Bound, exact upper premise Bound]
  -> original producer Constraint
```

を復元する。bound record 上の他の covered / independent derivation は、この filtered expansion からは
展開しない。node の登録済み／未登録と、どの proof view で incoming edge を展開済みかを別に管理し、
同じ bound が別の正当な raw path から到達された場合だけ raw expansion を許す。

この設計は、DCP の per-proof projectability、MPC の record OR / `ReplayConjunction` AND、
DPN の exact premise、URR-v3 の exact causality を変えない。変更するのは、すでに投影判定に使った
exact proof arm を diagnostic provenance まで失わず運ぶ境界だけである。

## 1. 問題

### 1.1 観測された topology 欠落

二つの characterization test が、同じ 3-node / 3-edge segment の欠落を別々の経路で示している。

1. `constraints::tests::subtype_provenance_characterization::general_subtype_failures_have_infer_analogs_but_carry_no_record_identity`
2. `constraints::tests::pusp_characterization::pusp_a_characterizes_parameter_and_scheme_provenance_gaps`

`general_subtype...` の `tuple-arity` case では、承認済み baseline の local explanation が
35 nodes / 47 edges であるのに対し、現行は 32 nodes / 44 edges になる。差分は次の 3 node である。

- lower `BoundRecordId(29)` — owner `TypeVar(0)`、endpoint `PosId(14)`
- replay-result `ConstraintRecordId(22)` — `PosId(14) <: NegId(17)`
- upper `BoundRecordId(28)` — owner `TypeVar(11)`、endpoint `NegId(17)`

失われた中心経路は次である。

```text
GeneralizedWitness(0 or 2)
  -- Generalization(BoundCollection) --> BoundRecordId(29)
BoundRecordId(29)
  -- Bound(Constraint) --> ConstraintRecordId(22)
ConstraintRecordId(22)
  -- BinaryReplay(UpperBoundAdded) --> [BoundRecordId(26), BoundRecordId(28)]
BoundRecordId(28)
  -- Bound(Constraint) --> ConstraintRecordId(21)  -- original producer
```

現行 graph は、最初の二つの generalized witness edge を直接
`ConstraintRecordId(21)` へ接続する。したがって、producer 自体は残るが、producer へ至る
replay の理由が丸ごと一段短絡される。

PUSP の `inferred-if-condition` parameter query も同じ形である。

- lower `BoundRecordId(14)` — owner `TypeVar(0)`、endpoint `PosId(11)`
- replay-result `ConstraintRecordId(10)` — `PosId(11) <: NegId(12)`
- upper `BoundRecordId(13)` — owner `TypeVar(10)`、endpoint `NegId(12)`
- original producer `ConstraintRecordId(9)`

現行は `GeneralizedWitness(0 or 2) -> ConstraintRecordId(9)` へ短絡し、parameter query は
概ね -3 nodes / -3 edges / max-depth -2 になる。

same-session call query では、definition-side の上記 segment に加え、instantiated-side の

- lower `BoundRecordId(77)` — owner `TypeVar(12)`、endpoint `PosId(36)`
- replay-result `ConstraintRecordId(53)` — `PosId(36) <: NegId(35)`
- upper `BoundRecordId(76)` — owner `TypeVar(33)`、endpoint `NegId(35)`
- original producer `ConstraintRecordId(52)`

が同じ理由で落ちる。そのため差分は概ね -6 nodes / -6 edges / max-depth -2 になる。
imported call control は同じ session の generalized witness からこの route を再構成しないため、
この差分を示さない。

arena ID は調査時の同一 fixture 上の観測値であり、実装条件に使ってはならない。
実装・test は node kind、exact carrier、canonical record relation で同じ構造を固定する。

### 1.2 proof store には exact bridge が存在する

この欠落は proof の未記録ではない。`tuple-arity` の `BoundRecordId(29)` には、
`UpperReplayClaimId(15)` を support とする formula が存在する。claim 15 は

- `coverage_root = UpperReplayClaimId(15)`
- `kind = Direct`
- `full_lineage = Original`
- `producer = ConstraintRecordId(21)`
- `current_record = BoundRecordId(28)`

を持つ。一方、lower record の formula は次の exact clause を持つ。

```text
ReplayConjunction {
    support: Claimed(UpperReplayClaimId(15)),
    carrier: BinaryReplayDerivation {
        pivot: TypeVar(11),
        lower: BoundRecordId(26),
        upper: BoundRecordId(28),
        rule: UpperBoundAdded,
    },
    lower: BoundRecordId(26),
    upper: BoundRecordId(28),
    attribution: Some(ReplayConstraint),
}
```

つまり CPK は、Original claim と exact replay conjunction の両方を保持している。
`CpkProjectionEvaluator` もこの formula を record-local OR arm として評価する。
欠けているのは proof write ではなく、投影結果から generalized provenance へ渡す read-side payload である。

### 1.3 exact information が失われる場所

現行の loss chain は次の五段で確定している。

1. `crates/infer/src/constraints/proof/mod.rs:10-22`
   - `ProjectionClaimSupport` は `coverage_root` と `representative_claim` だけを返す。
   - `ProjectionSupportSet` も `uncovered_claims` と independent carrier だけを持つ。
   - formula のどの `ProjectionClause` が成立したか、その attribution / carrier / result を返さない。
2. `crates/infer/src/constraints/mod.rs:1214-1262`
   - `scheme_projectable_lowers_in_round` は `ProjectionClaimSupport` を
     `representative_claim` の `Vec<UpperReplayClaimId>` へ縮退させる。
   - `SchemeProjectableLowerReason::Qualified` に exact claimed proof は残らない。
3. `crates/infer/src/generalize/provenance.rs:166-220`
   - `WitnessCollector::collect_var` は claimed payload から
     `GeneralizationParent::BoundClaim { bound, claim }` だけを作る。
4. `crates/infer/src/constraints/mod.rs:2513-2607` と
   `crates/infer/src/constraints/explain.rs:1226-1271`
   - `generalization_parent_carriers` は `BoundClaim` の claim record を読む。
   - `full_lineage == Original` なら `claim_record.producer` を直接返す。
   - `visit_generalized_witness_edges` はその短縮済み carrier を忠実に graph 化する。
5. `crates/infer/src/analysis/session/occurrence_provenance.rs:228-310`
   - production の generalized occurrence root collector も `generalization_parent_carriers` を直接読む。
   - exact filtered view を表せないまま plain `Bound` root へ変換すると、`explain.rs` を直しても portable
     occurrence path では mixed record の covered sibling が再混入する。

このほか、`crates/infer/src/constraints/machine/bounds.rs:5494-5536` の target-late test oracle は
production occurrence collector を同じ resolver で mirror している。また
`crates/infer/src/constraints/logical_proof_snapshot.rs:178-189,709-732` は
`generalization_parent_carriers` を経由せず `GeneralizationParent` 全 variant を直接 canonicalize するため、
新 parent に対応する canonical variant と変換 arm が必要である。portable exporter 自体は resolver を直接
読まないが、local `ExplanationQuery` と generalized occurrence root を通じてこの transport を間接消費する。

したがって `explain.rs` 単独の traversal bug ではない。exact clause を捨てた後で
claim lineage だけを読んでも、その Original claim が lower record 上で
`ReplayConjunction` の support になった事実を復元できない。

### 1.4 なぜ直す必要があるか

これは型推論結果の soundness gap ではなく、diagnostic provenance の completeness gap である。
しかし diagnostic consumer にとって、producer が同じであることと、現在の bound がその producer から
どう導かれたかは別の情報である。

短絡後の graph は「この generalized witness は constraint 21 に由来する」ことだけを示す。
実際に必要な説明は「lower relation が replay result 22 により成立し、その replay は exact lower / upper
premise を要求し、upper premise 28 が producer 21 に由来する」である。
特に MPC が導入した AND premise を短絡すると、diagnostic graph から連言所有そのものが見えなくなる。

CPK の suppression / inclusion 判定が正しくても、判定に使った proof arm と説明に出る proof arm が
異なれば、portable export、parameter provenance、subtype explanation は CPK の実際の理由を再現できない。
CPK separation の目的から見て、この差は「表示上の省略」ではなく proof consumer contract の欠落である。

## 2. 先行設計との関係

### 2.1 DCP: per-proof projectability と mixed record

`notes/design/2026-07-30-derived-row-claim-propagation-gap.md`（DCP）§4.2 / §4.3 は、

- replay lineage は exact `BinaryReplayDerivation`
- structural lineage は exact `StructuralDerivation`
- scheme provenance は projectable proof だけを根拠にする
- raw `BoundRecord`、全 derivation、covered claim は audit source に留める

と定める。§5.4 は、mixed claim-aware record の independent support を plain `Bound(record)` に戻すと
covered derivation まで展開するため、exact independent carrier を使うと明記する。

GWCB は同じ規律を claimed support に適用する。`BoundClaim` が claim-local であるだけでは不十分で、
claim が record 上でどの exact clause に所属したかまで保持しなければ、Original producer への短絡が起きる。

### 2.2 MPC: clause attribution と OR / AND

`notes/design/2026-07-31-mixed-proof-conjunctive-ownership.md`（MPC）D2 は、clause 帰属を
claim lineage kind から推測せず、**link event** で決める。Original claim でも replay occurrence 経由で
record に届けば `ReplayConjunction` に所属しうる。今回の claim 15 がまさにその例である。

MPC D3 の論理構造は次である。

- record の複数 clause は OR
- `ReplayConjunction` の lower / upper premise は AND
- exact carrier と stable record ID で dedup
- memo 付き DAG 一回走査、global scan / fixpoint 禁止

GWCB は評価結果を変えない。成立した clause を provenance payload として保持し、説明側でも同じ arm を
展開する。複数の成立 arm があれば exact identity で一回ずつ保持し、record-wide な一つの代表へ潰さない。

### 2.3 DPN: typed premise と event-local exact metadata

`notes/design/2026-08-01-derived-unary-premise-nodes.md`（DPN）は、`ProofPremise` を
`Record / Constraint / RootCoverage` の typed node とし、premise を見つけるための post-hoc graph walk を
禁止する。ReplayConjunction は carrier が持つ exact record 二つを使う。

GWCB の certificate も、説明時に endpoint shape や lineage kind から result を探してはならない。
ReplayConstraint の result、DerivedUnary の premise、ReplayEvidence の exact replay は、clause link admission
またはその単一 writer に付随する O(1) index から event-local に凍結する。

### 2.4 URR-v3: exact causality と preserved logic

`notes/design/2026-08-01-urr-v3-causal-qualification.md`（URR-v3）D4 / invariant 1, 5, 6 は、
exact `ClaimQualifiedParent` route のみを因果根拠とし、record OR、ReplayConjunction AND、constraint route OR、
claim payload を変更せず、global repair scan を導入しないと定める。

GWCB は coverage root の一致だけで bridge を作らない。`(bound, support, exact clause, attribution, result)` が
projection ledger に実在し、preflight を通った場合だけ certificate を作る。したがって URR-v3 の
exact causality と矛盾しない。

## 3. 採らない案

### 3.1 naive fix: `BoundClaim` を `Bound(bound)` に戻す

motivating fixture だけを見ると、`generalize/provenance.rs` で claimed support を
`GeneralizationParent::Bound(entry.record)` にすれば、historical bridge が再び見える。
この案は採らない。

mixed lower record `L` が次を同時に持つ場合を考える。

```text
L.proofs = {
    Claimed(root A) attached to ReplayConjunction R,  -- A は uncovered
    Claimed(root B) attached to another clause,       -- B は live covered
    Independent(carrier I),                           -- 別の正当な proof
}
```

projection が A だけを generalized witness の理由として選んだとき、plain `Bound(L)` の通常 traversal は
`L.derivations` 全体を展開する。すると B の covered proof と、A の理由ではない I まで witness の
provenance に再混入する。これは DCP §4.3 / §5.4 の per-proof contract を record-wide へ後退させる。

さらに bound record は append-only な derivation merge を後から受けうる。capture 時点では derivation が
一つでも、説明時までに別 derivation が追加されれば、plain bound parent は capture 時点の exact reason を
保持しない。capture 時に「今は一つだから安全」と判定するだけでも不十分である。

### 3.2 claim lineage だけを一段深く辿る

`UpperClaimLineage::Original` を producer へ、`ReplayConstraint` を result へ解決する現行規則を、
parent claim chain の再帰だけで拡張する案も採らない。今回の exact replay は claim 15 自身の lineage ではなく、
claim 15 と lower record の **clause link** に記録されている。lineage chain には存在しないため、再帰しても
`ConstraintRecordId(22)` は得られない。

### 3.3 explanation 時の formula / occurrence 全走査

`explain.rs` から `projection_formulas`、`replay_finite_map`、`occurrences` を走査して似た carrier を探す案は
採らない。これは MPC D2 の event-local attribution と DPN の no post-hoc reconstruction に反する。
同じ endpoint / rule / producer を持つ複数 occurrence から exact 一件を選べず、挿入順依存も生む。

### 3.4 producer と replay result を両方 parent に並べるだけ

`GeneralizedWitness -> [producer, replay-result]` と flat に並べても、lower bound がなぜ replay result を
所有するか、ReplayConjunction がどの proof arm かを表せない。AND chain を OR 的な兄弟 parent へ潰すため、
topology 数だけ合わせる修正になる。この案も採らない。

## 4. 提案する表現

### 4.1 exact claimed projection certificate

意味上の型を次とする。Rust の最終配置・visibility・variant 名は GWCB-0 で既存型との重複を再確認する。

```text
ClaimedProjectionProof =
    Standalone {
        bound: BoundRecordId,
        coverage_root: UpperReplayClaimId,
        representative_claim: UpperReplayClaimId,
        producer: ConstraintRecordId,
        attribution: Original,
    }
  | DerivedUnary {
        bound: BoundRecordId,
        coverage_root: UpperReplayClaimId,
        representative_claim: UpperReplayClaimId,
        result: ConstraintRecordId,
        carrier: DerivedUnaryCarrier,
        premise: ProofPremise,
        attribution: StructuralConstraint | ReductionRouteConstraint,
    }
  | ReplayConjunction {
        bound: BoundRecordId,
        coverage_root: UpperReplayClaimId,
        representative_claim: UpperReplayClaimId,
        carrier: BinaryReplayDerivation,
        lower_premise: BoundRecordId,
        upper_premise: BoundRecordId,
        attribution:
            ReplayConstraint { result: ConstraintRecordId }
          | ReplayEvidence,
    }
```

identity は raw audit identity と semantic certificate identity に分ける。

raw audit identity は現行 ledger と同じ

```text
(bound, raw SchemeProjectionProofSupport, raw RecordProofClause)
```

を保持し、event の監査と source-of-truth parity にだけ使う。これは append-only ledger の identity であり、
semantic certificate の dedup key にはしない。

semantic certificate identity は少なくとも

```text
ClaimedProjectionProofKey =
    (bound,
     normalized coverage_root,
     normalized clause kind + exact carrier/premise,
     exact attribution,
     exact result-if-any)
```

を含む。ここで normalized clause は、外側の `SchemeProjectionProofSupport::Claimed(claim)` だけでなく、
`RecordProofClause::Standalone.support` に埋め込まれた claimed support も必ず
`claim_coverage_root(claim)` へ正規化する。これは現行 `ProjectionSupportMatchKey::Claimed(root)` と同じ規則である。
同じ coverage root の representative claim が置換され、raw link が複数残っても、一つの semantic certificate
identity に畳まれる。

`representative_claim` と raw clause/link identity は current projection payload と audit のため certificate payload
に保持できるが、hash / equality / dedup の意味を derived claim ID の入れ替わりへ依存させない。MPC D2-5 と
同様、stable coverage root と normalized clause category、exact carrier / premise / result を identity の中心にする。

`ReplayConjunction` の `result` は現行 `RecordProofClause` 単体には含まれない。
したがって実装は、result を explanation 時に推測せず、次のどちらか一方で凍結する。

1. clause link admission の writer が手元に持つ semantic result を certificate mirror へ同時登録する。
2. exact carrier から result への既存 O(1) occurrence index が全 writer で 1:1 と GWCB-0 で証明できる場合、
   admission 時にその index を読み、prepared transaction に result を含める。

result が一意に得られない、複数 result が同じ carrier identity を共有する、または writer が分散して
transactional exactly-once を保証できない場合は実装を開始しない。§10 の stop condition で設計へ戻る。

### 4.2 projection result payload

既存の `ProjectionSupportSet` と `SchemeProjectableLowerReason::Qualified` は semantic projection
payload なので、その field と計算を変えない。provenance 用の exact evidence は sidecar として分離する。

```text
ProjectionDecision::Included {
    supports: ProjectionSupportSet,             -- 現行 payload、そのまま
    evidence: ProjectionEvidence,               -- 新規 sidecar
}

ProjectionEvidence =
    ExactArms(Vec<ClaimedProjectionProof>)       -- preflight-backed、exact
  | FailOpenIncomplete                           -- include は維持、exact arm は存在しない
```

raw evaluator の内部結果も boolean だけにせず、少なくとも

```text
CpkProjectionEvaluation =
    Excluded
  | Included { evidence: ProjectionEvidence }
```

相当として表す。publication 用 `scheme_projection_record_is_included` は variant を boolean へ射影した値だけを
semantic decision として投影し、evidence を semantic mutation に使わない。`project_lower` は successful preflight 後の同じ evaluation result
から `ProjectionDecision` の sidecar を作る。これにより、direct publication path の fail-open も内部では
`FailOpenIncomplete` として明示される一方、既存 include / exclude と publication behavior は変わらない。

shared evaluation memo の全 node に `Vec<ClaimedProjectionProof>` を複製してはならない。recursive memo は
boolean と fail-open / exact の completeness bit（または同等の小さい state）だけを共有し、exact arm vector は
provenance を要求した top-level record について、同じ evaluation walk と persistent record-local bucket から一回だけ
組み立てる。publication-only evaluation は arm vector を構築しない。この分離で、明示的 fail-open state を得るために
CPK-9 以前の per-call allocation や target-specific payload cache を再導入しない。

`ExactArms([])` と `FailOpenIncomplete` は異なる。前者は preflight を通った同一 evaluation round で
「true になった claimed arm が正確にゼロ」と証明した結果であり、たとえば independent arm だけで include された
record を表せる。後者は、`scheme_projection_record_is_included` が preflight なしで raw evaluator を呼ぶ publication
path において、missing bound、empty supports、formula-key mirror に存在しない qualifying support、missing
constraint / claim / root などの既存 fail-open により `true` を返したが、exact true arm を提示できない状態である。
この二つを空 vector 一つに潰してはならない。

recursive evaluation 中に missing reference その他の fail-open が true premise を成立させた場合、その marker は
memoized child result から caller へ伝播する。top-level inclusion を fully validated な true arm だけで証明できない限り、
result は `FailOpenIncomplete` とする。successful `project_lower` preflight は confirmed path でこの marker を排除する
gate であり、marker を見なかったことにする根拠ではない。

`ExactArms` 内の claimed proof は「uncovered claim ごとに一件」ではなく、target record を include した exact qualifying
clause arm ごとに一件である。複数 arm は record OR の代替理由なので、すべて保持する。
ReplayConjunction 内の lower / upper は一つの certificate に入り、AND を二つの OR-arm へ分けない。

ここで「qualifying clause」と「uncovered support」を同一視してはならない。`Standalone` は support 自体の
qualification を読むが、MPC の `DerivedUnary` と `ReplayConjunction` は typed premise を評価する。
したがって clause link の claimed root が live covered でも、premise が成立してその clause が true になる
場合がある。evidence は `uncovered_claims` と join して再構成せず、evaluator が true とした claimed clause
arm 自身から作る。反対に、true independent clause の provenance は既存
`ProjectionProofCarrier` / `BoundProjectionProof` contract に残す。

`CpkProjectionEvaluator` の boolean 結果と `ExactArms` は同じ評価 round から作る。
boolean を返した後に formula をもう一度全走査して理由を再構成してはならない。実装方法は次を推奨する。

- writer-maintained な record/support-local exact clause-evidence bucket を formula / link admission と同じ
  prepared transaction で更新する。
- target record の評価時、実際に true となった top-level clause identity を evaluator が small result として
  返すか、同じ memo 状態を使って bucket の該当 arm だけ判定する。
- formula のない support その他の既存 fail-open path では certificate を捏造せず、
  `ProjectionEvidence::FailOpenIncomplete` を返す。relation は現行どおり include 側へ倒す。
- fail-open は publication / corruption safety の operational state であり、generalization が exact provenance として
  capture してよい証拠ではない。confirmed fixture がこの fallback を一件でも必要とすれば landing しない。

CPK-9 で解消した O(supports × clauses) を再導入しない。全 `projection_clause_link_keys` の走査、
per-query hash set 再構築、record-local formula の無条件な二回目走査も禁止する。

### 4.3 constraints / generalize transport

`SchemeProjectableLowerReason::Qualified` には field を追加しない。`SchemeProjectableLower` に
`projection_evidence: ProjectionEvidence`（または同等の private sidecar）を追加し、
`constraints/mod.rs:1251-1265` で `ProjectionDecision` から失わず移す。
compact / alias など semantic consumer は従来どおり `reason` だけを読み、generalization provenance collector
だけが sidecar を読む。既存 `uncovered_claims` と `independent_supports` の値・順序・dedup は変えない。

`ProjectionEvidence::ExactArms` のときだけ、generalization collector は exact claimed proof parent を作る。
`FailOpenIncomplete` を受けた場合は、current producer shortcut を complete な parent として再利用してはならない。
semantic projectability は現行どおり保持する一方、その witness edge / scheme record を
`ProvenanceCompleteness::Incomplete` とし、exact claimed parent を一件も捏造しない。既存 independent support に
preflight-backed な exact carrier が別途ある場合も、それは従来の `BoundProjectionProof` として保持するが、
fail-open claimed arm の代用品にはしない。motivating fixture または representative corpus の confirmed complete path が
`FailOpenIncomplete` を一件でも必要とする場合は stop condition とする。

`WitnessCollector::collect_var` は、claimed projection proof について

```text
GeneralizationParent::BoundClaimProjectionProof {
    bound,
    coverage_root,
    representative_claim,
    proof,
}
```

を作る。plain `BoundClaim` は、Standalone の claim-local producer しか根拠がない既存 path、または
GWCB-0 が exact clause certificate の不要性を証明した path に限って残せる。
motivating ReplayConjunction を `BoundClaim` へ落としてはならない。

generalization record は後から説明されるため、parent は current proof store を再解釈する query ではなく、
generalization capture 時点の immutable certificate でなければならない。certificate の全 field は stable arena ID
または immutable exact carrier とし、live coverage の current 値を snapshot の正しさに使わない。

### 4.4 view-aware filtered bound expansion

`explain.rs` の現行 walker は、一つの node-keyed `visited` set を持ち、`visit` が node を emit した直後に
`visit_incoming_edges` を一回だけ呼ぶ。`push_edge` は parent を ordinary `visit` へ即時再帰し、depth check は
raw `has_incoming_edges(id)` を読む。したがって set を一つ追加するだけでは、同じ bound の raw view と
filtered view を traversal-order independent に展開できない。GWCB-C は traversal work item 自体を次へ変える。

```text
ExpansionView =
    Raw(ExplanationNodeId)
  | ClaimedProjection {
        bound: BoundRecordId,
        proof_identity: ClaimedProjectionProofKey,
    }

TraversalWorkItem {
    node: ExplanationNodeId,
    view: ExpansionView,
    depth: usize,
}

emitted_nodes: Set<ExplanationNodeId>
expanded_views: Set<ExpansionView>
```

処理規則は次とする。

1. work item を受けたとき、`node` が未登録なら node を一回 emit し、node budget を一回だけ消費する。
   既に emit 済みでも、未展開の `view` は捨てない。
2. cycle / duplicate expansion は node ではなく exact `ExpansionView` で切る。同じ raw view は一回、同じ
   claimed certificate view も一回だが、raw と filtered は互いを抑止しない。
3. depth check は view-aware にする。`Raw(node)` は現行 `has_incoming_edges` 相当を使い、
   `ClaimedProjection` は certificate が実際に出す exact incoming edge の有無を使う。
   raw record に sibling edge があるという理由で、空の filtered view を depth-truncated と報告しない。
4. edge budget は現行 local `Vec<ExplanationEdge>` に push する一件ごとに消費する。local graph は現在
   edge set ではなく edge vector であり、raw traversal が作る exact duplicate の multiplicity と stable order を
   GWCB は勝手に変えない。
5. `push_edge` 相当は parent node だけでなく、各 parent の次の `ExpansionView` を明示した work item を積む。
   claimed filtered edge の parent を ordinary raw `visit` に落として covered sibling を再混入させない。
6. truncation / completeness は node budget、local edge-vector budget、view-aware depth、underlying incomplete を
   現行と同じ優先順位で合成する。view dedup を理由に本来の truncation を complete と見せない。

`BoundClaimProjectionProof` を受けたとき、graph node と generalized edge の parent identity には既存の
`ExplanationNodeId::Bound(bound)` を使い、incoming expansion だけを
`ClaimedProjection { bound, proof_identity }` にする。

- `Standalone`: exact producer constraint へ `Bound(Constraint)` 相当の edge を一件出す。
- `DerivedUnary`: exact result / premise semantics に従い、structural または reduction-route carrier を一件出す。
- `ReplayConjunction / ReplayConstraint`: bound から exact result constraint へ一件出す。
  result constraint の既存 `BinaryReplay` edge が exact lower / upper premise を AND parent として出す。
- `ReplayConjunction / ReplayEvidence`: semantic result が存在しないため、DCP の independent
  `ReplayEvidence` と同じ exact lower / upper carrier semantics を使う。ただし二 premise を別 clause にしない。
- `FailOpenIncomplete`: filtered proof view を作らない。witness / query を incomplete とし、producer shortcut または
  plain raw bound expansion で穴を埋めない。

同じ bound が別経路から `Raw(bound)` として正当に到達した場合、node は重複登録しないが raw view は別に
一回展開できる。これにより traversal order に依存せず、filtered path が raw expansion を誤って抑止せず、
raw path が先に来ても filtered certificate の exact edge が失われない。

local explanation の edge multiplicity は現行どおり保持する。exact edge dedup は portable exporter が
`ExplanationEdge` を key に行う別 contract であり、local raw vector と同一視しない。同じ child / kind / parents の
edge が raw view と filtered view の双方から local vector へ現れうる場合、その multiplicity と order を GWCB-0 で
観測・固定し、GWCB-C で暗黙に set 化しない。portable export では従来どおり shared edge を一回だけ出す。

production の generalized occurrence root collector も、certificate view を plain
`OccurrenceProvenanceRoot::Bound(bound)` へ平坦化してはならない。`occurrence_provenance.rs` は、同じ
`ClaimedProjectionProofKey` を運ぶ filtered root / anchor（または同値な typed expansion plan）を保存し、portable
query が local walker と同じ exact view を開始できる形にする。target-late test oracle も同じ mapping を mirror する。

### 4.5 corruption / completeness

新 parent を解決するとき、次をすべて検証する。

1. `bound` が存在し、certificate の bound と一致する。
2. representative claim が存在し、その canonical root が `coverage_root` と一致する。
3. normalized semantic certificate key が raw projection ledger の一件以上の exact link から導出でき、
   embedded claimed support を含む全 support が同じ `coverage_root` へ正規化される。
4. result 付き variant は result constraint が存在し、exact occurrence / carrier と一致する。
5. ReplayConjunction の `carrier.lower / upper` が certificate の premise と一致する。
6. DerivedUnary の carrier / premise が formula link と一致する。
7. `ExactArms` は successful preflight と同じ immutable evaluation round から作られ、
   `FailOpenIncomplete` は exact certificate bucket を参照しない。

debug / test build は persistent certificate mirror と full linear source-of-truth scan の parity を assert する。
release build の既存 fail-open / terminal-failure 方針は弱めない。dangling certificate を別の producer へ
近似して complete と報告してはならない。`FailOpenIncomplete` は semantic inclusion を変更しないが、
generalized witness、occurrence root、local / portable explanation の全経路で incomplete を伝播する。

## 5. 必須 invariant

1. **semantic projection 不変**: include / exclude、endpoint、`uncovered_claims`、
   `independent_supports`、coverage / liveness、epoch publication を変更しない。
2. **exact clause attribution**: claimed proof は formula link event に実在する exact clause からだけ作る。
   claim lineage kind、endpoint shape、producer equality から推測しない。raw link と semantic certificate key を分け、
   claimed support は embedded `Standalone.support` まで coverage root へ正規化する。
3. **per-proof only**: filtered expansion は selected clause だけを出す。mixed bound の covered sibling、
   unrelated independent support、後発 derivation を混ぜない。
4. **record OR**: 成立した複数 clause は代替理由として保持する。一つの代表 clause に潰さない。
5. **ReplayConjunction AND**: lower / upper premise を一つの exact replay arm として保持する。
   flat な二つの generalized parent へ分解しない。
6. **typed premise**: DerivedUnary は DPN の `ProofPremise` をそのまま運ぶ。read 時に parent graph を探さない。
7. **exact result**: ReplayConstraint / structural / reduction-route result は writer-time metadata または
   証明済み 1:1 O(1) index から得る。全 occurrence scan を行わない。
8. **capture immutability**: generalized parent は capture 時点の exact proof certificate を保持する。
   後の claim move、bound derivation merge、coverage transitionで意味が変わらない。
9. **fail-open の明示**: `ExactArms([])` と `FailOpenIncomplete` を区別する。fail-open inclusion は現行どおり
   保持するが、producer shortcut、plain bound、別 arm を exact evidence として捏造せず、全 downstream へ
   incomplete を伝播する。
10. **node identity / expansion identity 分離**: node emission と `(node, expansion view)` の展開済み判定を分け、
    traversal order による edge loss / sibling leak を起こさない。depth / cycle / budget も view-aware にする。
11. **local edge-vector contract**: local explanation の edge multiplicity と stable order を保持し、GWCB 内で
    暗黙に set 化しない。node budget は初回 emit、edge budget は local vector push ごとに消費する。
12. **portable parity**: local graph の filtered topology と portable snapshot の deduplicated node / edge set が一致する。
    shared edge の multiplicity は portable 側で一回、local raw vector の multiplicity は現行どおりとする。
13. **fail-hard contract 不変**: CPK preflight / corruption detection を弱めない。confirmed path で
    fallback certificate や incomplete provenance が一件でも必要なら landing しない。
14. **event-local / scan-free**: certificate mirror は clause admission と同じ transaction で維持し、
    global repair、post-hoc derivation walk、fixpoint を導入しない。
15. **linear storage**: certificate entry 数は normalized exact claimed clause identity 数に線形。
    claim × clause の未実在直積、proof path 展開、query 回数に比例して増えない。
16. **exact dedup / insertion-order invariance**: raw link は audit identity で保持し、semantic certificate は
    normalized key ごとに一回だけ登録する。representative claim の置換または admission 順序で
    certificate set、generalized parent set、explanation edge set が変わらない。
17. **no-claim / no-op persistent allocation zero**: claim のない workload、exact duplicate admission、
    independent-only admission、projection を消費しない workload は新 persistent bucket / parent を allocation しない。
    certificate storage は accepted claimed link が一件以上ある場合だけ reserve する。query-local traversal も、
    claimed certificate parent に到達しない query では `ClaimedProjection` expansion view を allocation しない。
18. **hot-path 非回帰**: CPK-9 で除去した O(S×C)、per-query O(C) 再構築、occurrence scan を戻さない。
19. **raw audit 不変**: raw bound、semantic constraint、solver replay、claim identity、formula semantics を変えない。
20. **説明 completeness**: exact certificate がある confirmed path は `Complete` のまま bridge を出す。
    certificate 欠落を producer shortcut で complete と見せない。
21. **全 consumer の filtered-view parity**: local explanation、generalized occurrence root、target-late oracle、
    logical proof snapshot、portable export が同じ certificate identity / completeness を表し、どの入口でも
    plain bound fallback による sibling leak を起こさない。
22. **baseline の理由付き更新**: topology hash または raw cardinality が typed certificate の導入で変わる場合、
    exact node / deduplicated edge set と local edge-vector multiplicity の差分を示してからだけ expectation を更新する。
    historical count 単独を correctness oracle にせず、現行欠落 32/44 や -3/-3 に rebaseline しない。
23. **persistent / temporary allocation の区別**: `PerformanceIndexAllocationCensus` は persistent store の
    len / capacity だけを証明する。admission preparation の temporary `Vec` / `FxHashSet` は別 measurement とし、
    census が測っていない allocation をゼロと報告しない。
24. **名前非依存**: arena ID、fixture 名、module path、function / parameter 名を実装条件に使わない。

これらは DCP §11.1 の列挙型 stop discipline（現行 25 項目）を置き換えない。特に DCP の exact carrier、
mixed proof、portable completeness、no-claim allocation、説明不能な baseline shift の各 gate を継承し、
本書固有の transport / filtered-expansion 条件を追加する。

## 6. motivating tests と green の定義

### 6.1 `general_subtype_failures_have_infer_analogs_but_carry_no_record_identity`

`tuple-arity` case で、次をすべて満たす。

- missing segment は arena ID 非依存の node kind と exact edge endpoint で構造的に確認できる。
- generalized witness から lower bound、replay result、exact upper premise、original producer へ到達する。
- recovery 後の exact node set と deduplicated `ExplanationEdge` set が、pre-regression fixture の同じ
  semantic path と一致し、covered / independent sibling が一件も増えない。これを primary green condition とする。
- local raw edge vector の cardinality / multiplicity / order は別に比較し、差があれば exact duplicate の identity と
  発生 view を説明する。
- 現行 node identity と local multiplicity が保たれる場合、35 nodes / 47 raw edges に戻ることを corroborating
  expectation とする。ただし count 一致だけでは green とせず、exact set が違えば failure とする。
- origin list、canonical constraint / bound counts、record identity は期待値無変更。
- 他の `tuple-arity-through-generic`、`nested-tuple-arity`、`poly-variant-tag` case に、
  理由のない topology shift がない。

現行 characterization は node count、raw edge-vector count、origin list だけを比較し、edge set content を固定しない。
したがって count だけを合わせる test で終えず、arena ID 非依存の小さい fixture で
`BoundClaimProjectionProof` の exact carrier と filtered edge set を直接 assert する。

`0ebc4668` は redundant raw-bound wrapper を正当に除去し、同じ test の 36/48 を 35/47 へ意図的に変更した。
この履歴は、historical cardinality が design intent の有力な証拠であっても、exact topology の代用ではないことを示す。

### 6.2 `pusp_a_characterizes_parameter_and_scheme_provenance_gaps`

`inferred-if-condition` で次を満たす。

- parameter query は definition-side bridge 一件を exact node / deduplicated edge set で回復する。
- same-session call query は definition-side と instantiated-side の bridge 二件を、それぞれの exact carrier / endpoint
  を区別した node / edge set で回復する。
- no sibling leak を含む exact set recovery を primary green condition とする。historical nodes / raw edges / max depth と
  `query_fnv1a64` は、node identity、local multiplicity、stable order が同じなら一致すべき corroborating values とする。
- original parameter bound への到達、origin kinds、source leaves、completeness は保持する。
- imported-cache-loaded control は不変。
- scheme、poly dump、diagnostics、semantic counts、ocast state は不変。

`QueryBaseline.query_fnv1a64` は graph の full debug representation を固定している。
既存 `ExplanationNodeId::Bound(bound)` と local edge-vector contract を保つ filtered expansion なら historical hash の
復元を期待する。ただし hash 一致だけで exact semantic set の一致を代用しない。edge の canonical order、local
multiplicity、または内部表示が、意味上正しい typed certificate のために変わる場合は、GWCB-D で exact node set、
deduplicated edge set、raw vector 差分、順序規則を説明してからのみ expectation を更新できる。
現行短絡 graph の hash へ合わせない。

### 6.3 control tests

最低限、次の contract を直接固定する。

- mixed record で selected claim の replay clause だけが出て、covered sibling が出ない。
- 同じ mixed record の independent proof は既存 `BoundProjectionProof` の exact carrier だけを出す。
- 同じ bound へ filtered path と raw path の両方が届いても、node は一件、deduplicated edge set は必要な和集合になる。
  local raw vector の exact duplicate multiplicity / order は pre-verification baseline を保持し、portable 側だけ一件にする。
- ReplayConstraint / ReplayEvidence / DerivedUnary / Standalone の各 certificate が exact variant へ解決される。
- formula mirror / certificate mirror の linear-scan parity。
- exact duplicate、no-claim、independent-only admission で新 persistent certificate entry / bucket capacity growth がゼロ。
- `ExactArms([])` と `FailOpenIncomplete` が別 variant で、後者が generalized witness / occurrence root / portable
  completeness を incomplete にし、producer shortcut を作らない。
- local raw edge vector の multiplicity は保持し、portable snapshot の deduplicated edge set だけが一回になる。
- local / portable topology set parity。
- corruption fixture で mismatched result / carrier / root を黙って producer shortcut しない。

## 7. 実装スライス

各 slice は前 slice の gate を閉じてから進める。正しい red characterization は保持し、
現行の欠落出力へ expectation を書き換えない。

### GWCB-0: read-only writer / topology pre-verification

変更:

- test-only observation helper と temporary trace のみ。production behavior は不変。
- `RecordProofClauseLinkAdmission` の全 writer を列挙する。
- ReplayConstraint result、ReplayEvidence、DerivedUnary result / premise が各 writer で手元にあるか確認する。
- production writer に加え、test-only generic clause writer が certificate metadata を明示的に供給できるか確認する。
- exact replay carrier -> result の既存 index が 1:1 か、同一 carrier の複数 result がありうるか census する。
- motivating 3-node segment を node / edge set で固定する red unit fixture を追加する。
- mixed bound の covered sibling control と filtered/raw dual-reach control を作る。
- raw evaluator の全 fail-open branch を列挙し、`ExactArms([])` と `FailOpenIncomplete` の red control を分ける。
- local raw edge vector、deduplicated edge set、portable edge set を同じ fixture で別々に記録する。

gate:

- すべての claimed clause link に event-local exact certificate を付けられる。
- result を得るため global scan、shape inference、producer reverse traversal が不要。
- raw claimed link が normalized semantic key へ全件写像され、certificate 数が distinct normalized key 数に一致する。
- motivating 二 test の loss chain が §1.3 の五境界で再現する。
- direct publication evaluation の fail-open が exact arm を捏造せず、incomplete として観測できる。

stop:

- writer が複数に分散し exactly-once transaction を保証できない。
- `RecordProofClause::ReplayConjunction` の carrier から result が一意でなく、writer にも result がない。
- 現行 formula semantics から「どの true arm を provenance に出すか」を決められない反例がある。
- fail-open inclusion と exact-empty evidence を downstream で区別できない。

いずれかなら、新 index shape / proof identity を別途レビューし、本書のまま GWCB-A へ進まない。

### GWCB-A: certificate 型と transactional mirror（read path 不変）

変更:

- `ClaimedProjectionProof` と exact canonical key を追加する。
- raw clause-link identity を audit source として保持し、semantic key は outer / embedded claimed support を
  coverage root へ正規化する。
- clause admission の prepare / commit に certificate bucket を追加する。
- add / exact duplicate / canonical duplicate / evidence-only / promotion の全 writer を接続する。
- test-only linear-scan parity、insertion-order permutation、allocation census を追加する。
- evaluator / generalization / explanation はまだ新 mirror を読まない。

gate:

- 全既存 test は behavior / expectation 不変。
- certificate mirror は raw projection clause link source-of-truth を normalized key へ写像した結果と完全一致する。
- no-claim / no-op / independent-only / exact duplicate の persistent certificate entry と bucket capacity growth はゼロ。
- same-root representative replacement / raw duplicate link で semantic certificate は一件のまま。
- failed reservation で formula と mirror が片肺 commit されない。
- entry 数は raw exact link 数以下で、distinct normalized claimed link identity 数に一致する。

stop:

- mirror を transactionally 維持できない、retraction が存在して remover を列挙できない、
  または一つの link から unbounded certificate が生じるなら slice ごと戻す。

### GWCB-B: projection payload と generalization transport

変更:

- `ProjectionDecision::Included` と `SchemeProjectableLower` に private provenance sidecar を追加する。
- sidecar は `ExactArms` と `FailOpenIncomplete` を型で区別する。
- `ProjectionSupportSet` / `SchemeProjectableLowerReason::Qualified` の semantic payload は変更しない。
- evaluator の同一 round から true top-level exact arms を返す。
- `GeneralizationParent::BoundClaimProjectionProof` を追加する。
- `WitnessCollector::collect_var` で exact certificate を capture する。
- fail-open sidecar は exact parent を作らず witness / scheme completeness を incomplete にする。
- logical proof snapshot / canonical parent 表現に同じ exact identity を加える。
- explanation はまだ compatibility mode で現行 carrier を返し、motivating test は red のままでもよい。

gate:

- include / exclude と現行 payload は byte-for-byte 不変。
- generalized parent certificate set が evaluator の true arm set と一致する。
- `ExactArms([])` は exact independent-only inclusion、`FailOpenIncomplete` は no-certificate incomplete として
  downstream まで区別される。
- 複数 OR arm、ReplayConjunction AND、claim replacement、insertion-order control が green。
- shared `ProjectionEvaluationRound` の cache に stale provenance payload を混ぜない。
- std lowering / representative corpus で CPK-9 performance に有意な回帰がない。

stop:

- reason collection に per-query O(C) reconstruction または O(S×C) が必要。
- evaluator の bool memo と witness arm が別 snapshot を表す。
- semantic consumer が private provenance sidecar のため挙動を変える。

### GWCB-C: view-aware local / occurrence traversal

変更:

- `generalization_parent_carriers` を exact expansion plan を返せる形へ拡張する。
- explanation walker を `(node, expansion view, depth)` work item へ変更し、node emission、view expansion、
  cycle / duplicate、view-aware depth、node / local edge-vector budget を分離する。
- claimed projection parent は existing Bound node identity を保ち、certificate の exact edge だけを展開する。
- local edge vector の multiplicity / stable order を保持し、dedup を portable exporter の責務に留める。
- `analysis/session/occurrence_provenance.rs` の generalized occurrence root に filtered certificate view を運び、
  plain `Bound` root への平坦化を禁止する。
- `constraints/machine/bounds.rs` の target-late test oracle を production occurrence mapping と同じ typed viewへ更新する。
- raw / filtered dual reach、budget、depth、cycle、corruption、fail-open completeness を接続する。

gate:

- §6.1 / §6.2 の missing bridge が構造的に回復する。
- mixed covered sibling control に余分な node / edge が一件もない。
- traversal order を反転して同じ node / deduplicated edge set、completeness、depth になり、local raw edge-vector
  contract と portable deduplicated set の関係が説明可能である。
- node budget は初回 emission、edge budget は local vector push、depth / cycle は expansion view 単位で現行
  truncation contract を保つ。
- local query と generalized occurrence root から始めた portable query が同じ filtered semantic edge set を持つ。
- confirmed path に incomplete / fallback hit がない。

stop:

- same `BoundRecordId` の raw / filtered view を order-independent に表せない。
- filtered traversal のため `ExplanationNodeId` の意味を偽る、または covered sibling を出す必要がある。
- exact edge を出すため proof store の global scan が必要。
- occurrence provenance root が certificate view を運べず、plain bound または producer shortcut へ潰れる。
- local edge-vector multiplicityを理由なく変えるか、portable dedupをlocal walkerへ移す必要がある。

### GWCB-D: portable / logical parity と motivating tests

変更:

- portable exporter が local filtered graph の deduplicated topology をそのまま再現することを固定する。
- logical proof snapshot に新 `GeneralizationParent` の canonical counterpart / normalized certificate keyを追加し、
  canonical parent / ordering / hash を固定する。
- `general_subtype...` と `pusp_a...` を green にする。
- related SUBP / PUSP / DCP / MPC / DPN / URR control を実行する。

gate:

- local / portable nodes と deduplicated edge set が一致する。
- §6 の二 test が exact node / edge-set recovery で green。35/47、PUSP counts / depth / hash は
  corroborating values として比較し、差があれば raw vector / ordering まで理由を示す。
- portable shared edge は一回、local raw vector multiplicityとは比較しない。
- scheme / semantic inference / diagnostic text の無関係な変化がない。

stop:

- exact claimed projection を portable-representable にするため source identity を捏造する必要がある。
- local graph と portable graph の topology parity を保てない。
- 期待値変更が exact certificate / edge order まで説明できない。

### GWCB-E: integration / closeout

変更:

- targeted proof / generalization / explanation tests、safety-scoped infer suite、代表 corpus を実行する。
- wall time、RSS、proof event / occurrence / formula / certificate count、no-op allocation を計測する。
- `PerformanceIndexAllocationCensus` に certificate bucket の persistent map / bucket len・capacity を追加し、
  accepted claimed link がゼロの admission で persistent allocation がないことを測る。
- admission prepare 内の temporary `Vec` / `FxHashSet` allocation は census の対象外と明記し、必要なら
  CPK-9 proof-write self-time / event-count と同じ temporary instrumentation で別測定する。
- temporary trace / observation-only production branch を除去する。

gate:

- CPK-9 の既存 wall-time / RSS / proof-write / cache cold-warm gateを悪化させない。
- persistent certificate count は normalized claimed link identity 数に線形。
- no-claim / independent-only / exact duplicate の persistent certificate entry・bucket・capacity growth はゼロ。
- temporary preparation allocationを測っていない場合、persistent census だけから「全 heap allocation zero」と報告しない。
- 既知 intentional-red 以外の新 failure がない。
- source diff が本設計の cause boundary だけに限定される。

## 8. 変更しないもの

- claim の生成、継承、coalescing、coverage root、liveness、movement。
- `CpkProjectionEvaluator` の include / exclude semantics、record OR、ReplayConjunction AND、
  DerivedUnary premise evaluation、cycle cut、fail-open の向き。
- raw bounds、canonical constraint、solver replay、row reduction、URR state lifecycle。
- independent support の `BoundProjectionProof` と exact carrier semantics。
- generalization の endpoint、type path、role、scheme quantification、compact / alias semantics。
- source origin、portable source location、SUBP の shared-edge dedup contract。
- arena ID、fixture 名、function / parameter 名を使う special case。

## 9. 性能・容量方針

今回の gap は diagnostic read side に見えるが、payload は `scheme_projectable_lowers` の hot path を通る。
したがって correctness だけでなく次を landing 条件にする。

- persistent mirror は claim が触れた record だけに遅延作成する。
- raw link 数ではなく normalized claimed certificate identity 一件につき semantic entry 高々一件とする。
- accepted claimed link が一件以上あり、新 normalized certificate が存在する transaction だけが bucket を reserve する。
  no-claim、independent-only、exact duplicate、same-root representative replacement は bucket len / capacity を増やさない。
- evaluator call ごとの hash set / Vec 再構築をしない。
- formula / occurrence / bound graph の全走査をしない。
- explanation query の追加 work は出力する exact proof edge 数に線形。
- generalized witness が存在しない workload は certificate transport allocation をしない。
- `std::text::parse`、full lowering、representative corpus の cold / warm 測定を GWCB-B と GWCB-E で行う。

`PerformanceIndexAllocationCensus` は test-only に persistent store の map / set / bucket の len と capacity を測る。
certificate mirror も `(map_len, map_capacity, total_entries, total_entry_capacity)` 相当を追加し、既存の
no-claim / exact-duplicate before-after contract に接続する。この census は admission preparation 中の temporary
`Vec` / `FxHashSet` allocation を測らない。temporary allocation が wall time / RSS 上の懸念になる場合は、
GWCB-E で allocator counter またはこの session の proof-write self-time / event-count 測定と同じ一時 instrumentation を
使って別に測り、終了前に除去する。persistent census だけを根拠に全 heap allocation zero と報告しない。

GWCB により std lowering の CPK-9 closeout を再び 180 秒超へ戻す、RSS を説明不能に増やす、
または proof-write self time の operational share を有意に悪化させる場合、後段 cache で隠さず payload / mirror
設計へ戻る。

## 10. stop / rollback conditions

### 10.1 stop conditions

次のいずれかが判明した時点で semantic implementation を止め、Claude / user の設計 review へ戻る。

1. motivating path の exact replay result が clause writer でも既存 O(1) index でも一意に得られない。
2. claimed clause link の writer / remover を完全列挙できない。
3. formula entry の retraction があり、certificate mirror を同じ transaction で remove できない。
4. true clause arm を収集すると evaluator の include / exclude semantics が変わる。
5. `ExactArms([])` と `FailOpenIncomplete` を publication、generalization、occurrence、explanation の全境界で
   区別できない、または fail-open を complete な producer shortcut へ戻す必要がある。
6. provenance arm 収集に O(S×C)、per-query O(C) reconstruction、global scan が必要になる。
7. one certificate を選ぶと正当な alternate OR arm を失い、全 arm を持つと非線形に増殖する。
8. ReplayConjunction の lower / upper AND を flat OR parent にしなければ transport できない。
9. raw `Bound(bound)` を使わなければ historical node identity を保てず、使うと covered sibling が混入する。
10. raw / filtered dual reach を traversal-order independent にできない、または view-aware depth / budget / cycleを
    現行 completeness contract と両立できない。
11. local edge-vector multiplicityを暗黙にset化しなければfiltered traversalを実装できない。
12. local graph は complete になるが generalized occurrence root、portable / logical snapshot が同じ exact
    certificate view / topology を表せない。
13. certificate corruption を producer shortcut で fail-open しなければ confirmed path が動かない。
14. claim move / coverage transition / late derivation merge で capture 済み parent の意味が変わる。
15. same-root representative replacement が semantic certificate を重複させる、または raw audit link を失う。
16. no-claim / independent-only / exact duplicate workload に新しい永続 allocation が発生する。
17. motivating 二 test を通すため、semantic constraint / bound / replay の生成を変更する必要がある。
18. 現行 -3/-3 output へ baseline を下げるか、exact set で説明できない別 topology shift を受け入れる必要がある。
19. DCP / MPC / DPN / URR-v3 の pinned control が、exact cause を説明できず red になる。
20. performance / RSS が §9 の gate を外れ、局所的な後付け cache でしか回復できない。

### 10.2 rollback units

- GWCB-0 の正しい red fixture、writer census、exact topology dump は保持する。
- GWCB-A の mirror は read path へ接続する前の独立 commit とし、parity が成立しなければ全体を戻す。
- GWCB-B の payload / parent variant は一体で landing / rollback し、certificate を作るが捨てる片肺状態を残さない。
- GWCB-C の expansion-view / occurrence-root 変更は local explanation と production occurrence transport の一単位で
  landing / rollback し、どちらにも plain raw Bound fallback を残さない。
- GWCB-D の portable / logical change は local topology と一体で landing / rollback する。
- rollback のために motivating test を現行欠落へ rebaseline しない。

## 11. Claude 再査読時の確認事項

本 revision は初回査読の code verification を反映した。Claude は確定前に、少なくとも次の修正後 contract を
再検証する。

1. result-bearing production writer は minimal boundary で exact result を持ち、ReplayEvidence は result なしと
   明示され、test-only generic writer も metadata を捏造せず接続できるか。
2. `ProjectionClause.attribution` と `RecordProofClauseLinkAdmission.claimed_attribution_source` の対応が
   ReplayConstraint / ReplayEvidence / DerivedUnary の全 writer で完全か。
3. evaluator 内部結果が `ExactArms([])` と recursive fail-open を含む `FailOpenIncomplete` を区別し、publication の
   boolean semantics を変えず、generalization / occurrence / explanation へ incomplete を正しく運ぶか。
4. raw clause-link audit identity と normalized semantic certificate identity が分離され、outer / embedded claimed
   support とも coverage root へ正規化され、representative replacement 後も semantic key が stable か。
5. `(node, expansion view, depth)` work item が current node / local edge-vector / depth budget、cycle、truncation、
   local multiplicity、portable-only dedup と整合するか。
6. direct consumer 三箇所（local explanation、production generalized occurrence collector、target-late test oracle）と、
   direct parent canonicalizer（logical proof snapshot）、indirect portable / source-leaf consumer が全て同じ filtered
   certificate view / completeness を扱うか。
7. motivating test は exact node / deduplicated edge-set recovery を primary gate とし、35/47 と PUSP hash を
   corroborating value として扱い、raw vector / ordering の変化を exact diff なしに承認しないか。
8. CPK-9 の性能改善を壊さず、persistent certificate count / no-op capacity を census に追加し、temporary
   preparation allocationを別 measurement として正直に扱うか。

このうち一つでも未確定なら、Claude は「査読・確定」とせず、未承認ドラフトのまま decision point を返す。

---

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が査読・確定

承認状態: **NOT YET user-approved**。本書は Claude の査読・確定およびユーザ承認待ちのドラフトであり、
承認完了までは設計判断の正本として扱わない。
