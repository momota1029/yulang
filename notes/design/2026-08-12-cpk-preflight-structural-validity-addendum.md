# CPK 追補: projection preflight の構造証明と snapshot-scoped validity reuse

日付: 2026-08-12

状態: **ユーザ承認済み**（2026-08-12）

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定

**署名についての注記**: Codex Solが起案を完了した後、Claude (Sonnet 5)が全文を読み、
数値の整合性（mutable-reference調査§7.2のRMW×3 accepted 926件との一致など）を確認した。
最も懸念すべき論点——§6.3の「structural validityはDPN/MPCのcycle-safety問題と無関係」
という分離主張——については、この文書の起案を一切知らない別のCodexセッションへ
独立した敵対的レビューを依頼し、`A -> B`、`A -> dangling C`、`B -> A`という具体的な
反例形を現行`ProjectionPreflight::validate_record`の実装（cycle再訪時は`Ok(())`を
返すだけで何も偽の主張をしない、という実際のコード挙動）と§5.5のtop-level-unwind規則に
照らして検証させ、「HOLDS（正しく遮断される）」という結論を得た。このレビューで
指摘された2点（publication経路をtermination guardから明示的に分離する必要、および
この反例形を回帰fixtureとして固定する必要）は§5.5と§8.4へ反映済み。
以上により、Claude (Sonnet 5)の独立査読・確定は完了している。2026-08-12、ユーザが
本書の内容（Branch A/B の設計、evaluator memoとの分離、実装スライス構成、性能目標の
非保証の明記を含む）を確認し、承認した。本書はここに正本文書として確定し、
CPK-SV-A以降の実装に着手してよい。

本書は、ユーザ承認済みの
`notes/design/2026-08-05-constraint-proof-kernel-separation-plan.md`
（以下 CPK 計画）に対する追補である。CPK 計画の ownership boundary、canonical
proof model、prepare/commit transaction、failure policy、projection query、既存の
20 invariant を改廃しない。本書が追加・精密化するのは、
`ProjectionPreflight` が同一の proof structure を繰り返し検証するコストを除くための
次の二点だけである。

1. projection formula の canonical order・membership・support relation を admission
   transaction で一度証明する **admission-time structural certificate**。
2. formula から導かれる validation dependency を重複除去した adjacency と、同一の
   structural snapshot 内だけで成功を再利用する **snapshot-scoped structural-validity
   cache**。

本書は、
`notes/design/2026-08-04-mutable-reference-performance-investigation.md`
（以下 mutable-reference 調査）の Mechanism 2 が確認した fresh consequence の意味を
変更しない。また、
`notes/design/2026-08-01-dpn-root-claim-and-cycle-safety-addendum.md`
（以下 DPN cycle 追補）と
`notes/design/2026-08-02-mpc-dpn-projection-evaluation-round.md`
（以下 MPC/DPN round 追補）が定める tri-color evaluator、cycle cut、round-local
projectability memo の寿命を変更しない。

## 0. 決定の要約

1. `ProjectionFormulaBucket` は、formula の raw structure が canonical かつ内部整合
   していることを示す certificate を持つ。certificate は query 時の全走査から作らず、
   clause/link/support admission の prepare で検査し、同じ atomic commit で更新する。
2. certificate が current なら、`ProjectionPreflight::validate_projection_record` の
   order-only full pass を省略する。certificate が無い、dirty、version 不一致、または
   test corruption が検出された場合は、現行の「order-only passを先に完走し、その後に
   validation pass」という二段構造へ戻る。
3. 各recordは、formula incidenceから導かれる validation action の**重複除去済み
   adjacency**を持つ。これは clause の集合を粗い root 集合へ潰すものではなく、同一の
   typed validation actionを一回だけ行うための派生indexである。
4. successful preflight は、`ProofStructuralSnapshotId` が一致する間だけ
   `Valid(snapshot)` を再利用できる。failure、error、`Visiting` 中の暫定結果、
   projectability、cycle-cut結果、decisive evidence は保存しない。
5. census前に想定した「later epochの未変更recordをdelta再検証する」案は採らない。
   RMW×1〜6ではlater formula-mutation serialに跨る未変更record rescanは8件・14 clauses
   だけであり、支配的な重複は**同じ完成snapshotを異なるpreflight roundが再検証する
   こと**だった。
6. Branch AとBranch Bは別々のshadow/cutover sliceとしてlandingする。certificate、
   adjacency、cacheのどれも、oracle parityを確認する前にproduction authorityへ
   切り替えない。
7. legitimate fresh consequence、subtype replay pair、canonical constraint、
   projectability意味論、error precedence、cycle意味論、scheme出力は一切変更しない。

## 1. 問題

### 1.1 再現入力

2026-08-12のpost-QORF性能調査で、loop-carried mutable stateに相当する次の形が、
site数に対して強いsuperlinear scalingを示した。

```yulang
{ my $a = 0; &a = $a; &a = $a; ...; $a }
```

warm compiled std prefixを使うrelease CLIで、RMW site数 `N = 1..6` のsuffix inference
時間は次のように増えた。

| N | suffix inference |
|---:|---:|
| 1 | 97.570ms |
| 2 | 265.142ms |
| 3 | 642.491ms |
| 4 | 1.397s |
| 5 | 2.784s |
| 6 | 4.839s |

入力site数は6倍だが、時間は49.6倍になった。gdb samplingでは
`ProjectionPreflight`と`CpkProjectionEvaluator`が支配clusterだった。

### 1.2 mutable-reference調査との関係

mutable-reference調査 §7.2 のglobal alpha consequence censusは、RMW×3について
次を確認している。

| 分類 | 件数 |
|---|---:|
| pair candidate | 10,744 |
| exact duplicate / trivial | 9,818 |
| accepted consequence | 926 |
| locally isomorphicだがglobally distinct | 898 |
| globally alpha-equivalent | 0 |
| genuinely novel | 28 |

現行post-QORFコードで同じhookを再計測すると、RMW×3はpair candidate 10,772、
accepted fresh consequence 926だった。accepted 926は過去censusと完全一致し、candidate
の28件差は現行writer/route上の実測値として扱う。

この926件をalpha-equivalenceで畳むことはできない。本書は、fresh consequenceや
lower×upper pairを減らす設計ではない。CPK計画 §4 の
「lower×upper replayの件数を意味論的に減らす最適化はnon-goal」をそのまま維持する。

本書の対象は、その正当なrelationが生成された**後**に、proof machineryが同じ
formula、clause、premise、semantic factを何度再検証するかだけである。

### 1.3 現在の増幅機構

現行の`ProjectionPreflight::validate_projection_record`は、lower projection record
ごとに次を行う。

1. supportをresolveし、canonical/duplicate関係を確認する。
2. canonical formula cursorを全走査し、`NonCanonicalProjectionOrder`を先に検出する。
3. matched bufferを確保する。
4. 同じcanonical formula cursorをもう一度全走査する。
5. clauseごとにsupport、carrier、Record/Constraint/Root premise、row derivation等を
   検証する。
6. recursive `validate_record` / `validate_constraint`はround-localなchecked/visiting set
   で再展開を止める。

checked/visiting guardはterminationを守るが、guardへ到達するまでのclause walk、
reconstructed clause、bound lookup、hash lookup、function callを除かない。また、
`ProjectionEvaluationRound`を跨いで成功を再利用しないため、同一snapshotでも別roundは
同じgraphを最初から検証する。

## 2. 実測 evidence

### 2.1 計測方法

release buildへenv-gated thread-local counterを一時的に追加し、各Nを独立したsuffix
として実行した。計測後のinstrumentationは全撤去し、clean sourceからrelease binaryを
再構築した。working treeはcleanである。

「epoch」という語の混同を避けるため、構造censusではnonemptyな
`commit_projection_clause_admission`ごとに単調増加する
`FormulaMutationSerial`を一時的に割り当てた。これはproductionの
`ConstraintEpoch` / `ProvenanceEpoch`を意味しない。formula validationに関係する
mutation境界を最も狭く数えるためのcensus-local serialである。

### 2.2 fresh consequenceとproof callの増加

| N | pair candidates | accepted fresh | `validate_record` calls | `eval_record_memo` | `eval_root_coverage` | canonical cursor yields |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2,792 | 385 | 702,672 | 74,115 | 532,975 | 754,617 |
| 2 | 5,909 | 627 | 2,340,115 | 183,975 | 1,649,621 | 2,464,948 |
| 3 | 10,772 | 926 | 6,058,644 | 390,381 | 4,096,795 | 6,322,976 |
| 4 | 17,783 | 1,282 | 13,650,491 | 752,137 | 8,792,211 | 14,168,784 |
| 5 | 27,344 | 1,695 | 27,989,185 | 1,352,553 | 16,993,504 | 28,946,190 |
| 6 | 39,857 | 2,165 | 50,266,205 | 2,303,756 | 30,335,726 | 51,941,597 |

N=1→6でaccepted freshは5.62倍だった。これに対し:

- `validate_record`: 71.54倍。fresh当たりのcall比は12.72倍増。
- canonical cursor yield: 68.83倍。fresh当たりのyield比は12.24倍増。
- `eval_root_coverage`: 56.92倍。fresh当たりのcall比は10.12倍増。
- `eval_record_memo`: 31.08倍。fresh当たりのcall比は5.53倍増。

pair candidateを分母にしても、`validate_record/candidate`は251.67→1,261.16で
5.01倍増、preflight cursor yield/candidateは254.04→1,261.94で4.97倍増した。
acceptedだけを分母に選んだために見える偽の増幅ではない。

N=6の50,266,205 `validate_record` callの内訳は次のとおりだった。

| disposition | 件数 | 比率 |
|---|---:|---:|
| already checked | 39,848,149 | 79.274% |
| active-path cycle revisit | 10,354,705 | 20.600% |
| genuine expansion | 63,351 | 0.126% |
| tombstone fast path | 0 | 0% |

### 2.3 order passとvalidation pass

N=6の51,941,597 canonical cursor yieldは、次へ正確に分解された。

| consumer | yield | 比率 |
|---|---:|---:|
| preflight order-only pass | 25,148,567 | 48.417% |
| preflight validation pass | 25,148,567 | 48.417% |
| evaluator | 1,644,463 | 3.166% |

order-only passとvalidation passは、同じformula incidenceを同じ件数だけ走査していた。
order-only passはerror precedenceのために導入された正しい挙動であり、根拠なしに削除は
できない。しかし、writerがcanonical構造をtransactionally構築しているなら、その事実を
admission時に証明し、queryごとに再証明する必要はない。

### 2.4 record-local structure

| N | formula mutation events | admitted links | mutated records | expanded lower records | clauses合計 | clauses p50 / p95 / max | distinct direct premises合計 | premises p50 / p95 / max |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1,663 | 41,097 | 447 | 3,142 | 354,639 | 119 / 272 / 392 | 94,143 | 36 / 47 / 56 |
| 2 | 3,577 | 114,261 | 715 | 5,528 | 1,175,144 | 222 / 462 / 648 | 233,201 | 49 / 61 / 72 |
| 3 | 6,587 | 258,667 | 1,040 | 8,806 | 3,036,370 | 363 / 680 / 968 | 481,082 | 62 / 74 / 88 |
| 4 | 10,943 | 510,569 | 1,422 | 13,446 | 6,834,764 | 527 / 940 / 1,352 | 903,781 | 75 / 87 / 104 |
| 5 | 16,895 | 913,728 | 1,861 | 19,936 | 14,007,284 | 733 / 1,242 / 1,800 | 1,592,409 | 88 / 100 / 120 |
| 6 | 24,693 | 1,519,412 | 2,357 | 27,014 | 25,148,567 | 955 / 1,586 / 2,312 | 2,501,783 | 101 / 113 / 136 |

raw clause数 / distinct direct premise数はN=1の3.77倍からN=6の10.05倍へ増えた。
formula全件をvalidation actionへ毎回展開する代わりに、record-localなdistinct
dependency adjacencyを維持する根拠になる。

### 2.5 run-wide duplication

| N | validation clause scans | unique `(record, clause incidence)` | clause multiplier | premise observations | unique `(record, premise)` | premise multiplier |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 354,639 | 30,002 | 11.82x | 1,061,050 | 6,614 | 160.43x |
| 2 | 1,175,144 | 83,619 | 14.05x | 3,522,223 | 14,094 | 249.91x |
| 3 | 3,036,370 | 189,124 | 16.06x | 9,105,585 | 25,822 | 352.63x |
| 4 | 6,834,764 | 372,457 | 18.35x | 20,500,345 | 42,764 | 479.38x |
| 5 | 14,007,284 | 664,816 | 21.07x | 42,017,355 | 65,886 | 637.73x |
| 6 | 25,148,567 | 1,102,657 | 22.81x | 75,440,850 | 96,154 | 784.58x |

N=6ではvalidation clause scanの95.615%、premise observationの99.873%が
同じ`FormulaMutationSerial`内の再観測だった。一つの最大preflightは1,102,639
clauseを走査し、そのrunに存在したunique `(record, clause incidence)` 1,102,657件の
99.998%へ到達していた。別preflightは、ほぼ同じ完成graphをもう一度歩いている。

### 2.6 cross-epoch仮説の反証

N=1〜6のすべてで、later `FormulaMutationSerial`に跨る再走査は同じ小さなbaseline
だった。

| item | cross-serial rescan |
|---|---:|
| clause order scan | 20 |
| clause validation scan | 20 |
| `(record, premise)` | 32 |
| record | 12 |
| うちrecord自体が前回validation後に未変更 | 8 records / 14 clauses |

したがって、per-record mutation epochを精密化してlater-epoch deltaだけを検証する案は、
このworkloadの支配コストを解かない。必要なのは、同じsnapshotで一度成功した構造検証を
別preflight roundが再利用することである。

## 3. 用語とownership

### 3.1 Formula structural revision

一つの`ProjectionFormulaBucket`のraw structureを識別する単調revision。
少なくとも次の変更で進む。

- entry、support group、exact link、canonical run/chunkの追加・削除・置換。
- raw supportとentryの対応、support match key、normalized support summaryの変更。
- canonical comparatorの入力になるmetadataの変更。

revisionはbucket-localな構造のidentityであり、semantic/projectability epochではない。
exact no-opでは進めない。saturationした場合はcertificate reuseを無効にする。

### 3.2 Admission-time structural certificate

```text
ProjectionStructuralCertificate {
    formula_revision,
    canonical_order_valid,
    exact_membership_valid,
    support_relation_valid,
}
```

certificateは次だけを証明する。

- canonical run cursorのflatten順が`ProjectionClause::canonical_cmp`順である。
- run itemが非emptyな実在entry/support groupを指す。
- `(support_id, entry_id)`と`exact_links`が一対一で対応する。
- support groupのraw support、match key、normalized support summaryが同じtransactionで
  構築されたformula relationと整合する。
- duplicate/missing incidenceやdangling arena IDがbucket内部にない。

certificateは、外部のsemantic factの存在、bound state、claim move、root liveness、
row derivation、carrier occurrenceまでは証明しない。それらはBranch Bのstructural
snapshot validationが扱う。

### 3.3 Proof structural snapshot

`ProjectionPreflight`が読む全入力の同一性を表すattempt-localなgeneration。

```text
ProofStructuralSnapshotId(u64)
```

これは`ConstraintEpoch`、`ProvenanceEpoch`、generalization cache generation、
evaluation round IDの別名ではない。proof structural validationに必要なmutationだけを
一つのatomic commit単位で追跡する。saturationした場合は以後のreuseを無効にし、
値をwrapしない。

### 3.4 Structural validation action

formula incidenceを検証するときに必要になるexactなtyped action。

```text
ProjectionValidationAction =
    ResolveSupport(raw_support)
  | ValidateBound(record)
  | ValidateConstraint(constraint)
  | ValidateRoot(claim_or_root)
  | ValidateReplayCarrier(carrier)
  | ValidateStructuralCarrier(derivation)
  | ValidateRowDerivation(derivation)
  | ValidateRowReduction(state)
  | ValidateOrigin(origin)
  | ValidateGeneralizedWitness(witness)
  | ValidateCarrierOccurrence(carrier)
```

実装時のenum名は変更してよいが、異なるidentityやvalidation ruleを粗いroot集合へ
畳んではならない。

### 3.5 Snapshot-scoped structural-validity cache

```text
StructuralValidityCache {
    current_snapshot: ProofStructuralSnapshotId,
    record_valid_at: FactId -> ProofStructuralSnapshotId,
    constraint_valid_at: FactId -> ProofStructuralSnapshotId,
}
```

保存する値は`Valid(snapshot)`だけである。bool projectable、Included/Excluded、
fail-open、cycle cut、decisive evidence、error、owner attributionは保存しない。

cacheは一つのcompilation attempt内だけに存在し、serialize、portable export、
compiled prefix artifact、generalization cacheへ入れない。query時のcache capacity確保に
失敗した場合は、そのqueryを既存preflightで実行し、cacheしない。optionalなcacheのために
新しいsemantic failureを返さない。

## 4. Branch A: admission-time structural certificate

### 4.1 Writer契約

certificateは、既存のfallible prepare / infallible commit境界に含める。

```text
prepare admission:
    exact duplicateを除去
    new entry/support/link/run deltaを構築
    既存certificateとdeltaから次revisionの局所境界を検査
    certificate更新に必要なcapacityをpreflight
    PreparedProjectionStructureDeltaを返す

commit admission:
    entry/support/link/run deltaをcommit
    dependency adjacency deltaをcommit（Branch B landing後）
    formula_revisionを進める
    certificateを同じrevisionのValidとして最後にpublish
```

commit途中のstructureへ新certificateを先行publishしない。prepare failure、reservation
failure、terminal attempt failureでは旧bucketと旧certificateを変更しない。

### 4.2 Incremental proof obligation

既存bucketがcertificate済みなら、delta admissionは全bucketをclone/resortしない。
少なくとも次を検査する。

- new run/chunk内のsuffix order。
- predecessor / inserted delta / successor境界のcanonical order。
- new exact linkのentry/support group存在。
- batch-local duplicateと既存exact membership。
- support match key promotionとnormalized summaryの整合。
- split/rekey/rotation後のnonempty chunk、unique pivot、arena reachability。

一つのtransactionが既存certificateをincrementalに維持できない形を持つ場合は、
commit前のprepareでfull verificationを行うか、certificateをdirtyのままcommitする。
dirtyをvalidとして公開してはならない。

### 4.3 Read contractとerror precedence

```text
if certificate.matches(bucket.formula_revision):
    order-only passを省略
else:
    現行のorder-only passを最初に完走
    order成功後だけallocation / dependency validationへ進む
```

`NonCanonicalProjectionOrder`は、dangling fact、allocation failure、support mismatchより
先に返る現行優先順位を保つ。certificateがvalidならnoncanonical stateはwriter経由では
到達不能である。missing/dirty certificateでは必ず旧二段pathを使う。

test corruption hook、deserialization/migration fixture、direct store constructionが
certificateを迂回した場合もdirty扱いにし、order checkを省略しない。

## 5. Branch B: distinct dependency adjacencyとsame-snapshot reuse

### 5.1 Cross-epoch deltaではない

Branch Bは、当初候補だった「last validated epochとrecord-local mutation epochを比較して、
later epochのdeltaだけ再検証する」案ではない。§2.6の実測では、その機会は14 clauses
しかなかった。

採るのは次の二層である。

1. 一つのrecordを初めて検証するとき、raw clause全件から同じdependencyを繰り返し
   生成せず、admission時に維持されたdistinct adjacencyを一回歩く。
2. そのsnapshotで一度成功したrecord/constraintは、別preflight roundから
   `Valid(snapshot)`を読んでclosure全体をskipする。

### 5.2 Distinct dependency adjacency

各formula bucketは、validation actionのexact membershipと、非empty action列を持つ。

```text
ProjectionDependencyAdjacency {
    actions: flat nonempty storage<ProjectionValidationAction>,
    exact_membership: finite map<ProjectionValidationAction, EntryId>,
}
```

要件:

- nested category×support-groupのempty combinationを訪れない。
- iterationは明示cursorで、実在actionだけを一回yieldする。
- 同一clauseを複数supportが参照していても、同じexact actionは一件にする。
- 同じrootでもrepresentative claim、lineage、carrier、side、row derivation等が異なる場合、
  validation identityが異なるなら畳まない。
- clause/link relationのauthorityは引き続きcanonical formula/exact linkであり、adjacencyは
  派生indexである。membership queryのauthorityを二重化しない。
- append-only relation以外のremove/rekeyが導入された場合は、refcountまたはexact source
  relationなしにentryを消さない。

物理表現はSV-Cでrecord-local分布をcapacity-inclusiveに測定して確定する。単純なflat
`Vec`を採る場合も、writerが大きな既存列を毎event shiftするquadratic worst caseを
許容しない。必要なら既存のfixed-chunk AVLパターンを再利用する。これはsemantic
decisionではなく、§7のwriter-bound gateを満たすための表現選択である。

### 5.3 Failure時のcanonical error oracle

distinct adjacencyは成功pathの重複を除くためのindexであり、error precedenceの
authorityにはしない。unorderedまたはdependency-key順のaction走査でfailure候補を
見つけた場合は、そのerrorを直接返さず、次を行う。

1. adjacency fast attemptの部分結果を破棄する。
2. 現行canonical validation pathを実行する。
3. certificateがmissing/dirtyならorder-only passから、validなら少なくともcanonical
   validation passから再実行する。
4. canonical pathが返した最初のerrorだけを外部へ返す。

したがって、success workloadではdedup効果を得ながら、failure workloadでは
owner attributionとfirst-error semanticsを一切変更しない。failureはcacheしない。

### 5.4 Snapshot identityとinvalidation

次のいずれかが変わるatomic commitは、`ProofStructuralSnapshotId`を一回進める。

1. boundの生成、direction/owner/endpointの変更、active/tombstone transition。
2. constraintの生成/key変更、constraint→lower-record correspondence。
3. projection formula、support、exact link、canonical run、dependency adjacency。
4. upper claimの生成、coverage root、representative/current-record move、producer index。
5. root liveness、live-coverage membership、reduction claim/state mapping。
6. replay occurrence、structural parent、reduction-route parent、dependency index。
7. row derivation、row reduction record/state、processed-lower relation。
8. origin、source boundary、carrier occurrence、generalized witnessの存在・identity。
9. `ProjectionPreflight`が新たに読むようになったその他のmandatory fact/index。

exact no-op、diagnostic-only attachment、portable formatting metadataなど、preflight結果を
変えないmutationでは進めない。新しいpreflight readを追加したのにsnapshot invalidation
表へ追加しないことを禁止する。

snapshot bumpはatomic commitの最後に一回だけpublishする。before-viewとafter-viewは
異なるsnapshotになる。複数fieldを同じeventで更新しても途中snapshotを公開しない。

### 5.5 Cache hit / miss

```text
validate_record(record, snapshot):
    if record_valid_at[record] == snapshot:
        return Ok

    normal tri-color structural traversalを行う
    dependency adjacencyを一回歩く

    top-level traversal全体がOkで終了し、
    visiting_records / visiting_constraintsが空なら:
        このtop-levelでfully resolvedになったcandidate群をValid(snapshot)としてpublish
```

active-path cycleへの再訪を、その場で`Valid`へ変えない。cycle中に一つのnodeがlocalに
returnしても、outer visiting stackが残っている間はcandidateに留める。top-level success
後にのみ一括publishする。途中failureでは、そのtop-levelで得たcandidateを一件も
publishしない。

cache entryのallocation/reservation failureはuncached fallbackにする。partial cache entryが
見えても正しさは変わらない設計だが、実装はreviewを簡単にするためtop-level単位の
candidate publicationを採る。

**実装上の必須分離**: `Valid(snapshot)`のpublication code pathは、`checked_*` set
insertion（termination guardとしての「既に検査済み」マーキング）から直接呼び出しては
ならない。両者は別のtransitionであり、checked-set insertionはtop-level成功前でも
起こり得る（現行`validate_record`のtermination guardと同じ役割）。publicationは、
top-level traversal全体の成功が確定し、`visiting_records` / `visiting_constraints`が
完全に空へ戻った時点でのみ、独立したpublication stepとして実行すること。この分離が
崩れると、cycleの一部でlocalに完結した`checked`状態がtop-level failureの確定前に
`Valid`として漏れ出す経路が生まれる。

## 6. Evaluator memo / cycle safetyとの明確な分離

### 6.1 保存してよいもの

本書のcacheが答える質問は一つだけである。

```text
このexact structural snapshotについて、このproof nodeから到達するmandatory factと
局所構造をcanonical preflight規則で検証し、成功したことがあるか。
```

`Valid(snapshot)`はprojectabilityを表さない。root livenessがsnapshot identityに含まれる
理由は、preflightがそのfactの存在・index整合を検証するからであり、Included/Excludedを
保存するためではない。

### 6.2 保存してはならないもの

- `CpkProjectionEvaluationSummary`。
- `ProofEvalState::Done(projectable)`。
- cycle cutの結果や回数。
- short-circuitで選ばれたOR arm。
- decisive `(support_id, entry_id)`やGWCB evidence。
- before/after overrideを含むevaluation viewの結果。
- fail-open result。
- failure/error/owner attribution。

### 6.3 MPC/DPN契約を変えない理由

DPN cycle追補とMPC/DPN round追補が禁止する恒久memoは、active-path cycle cutにより
評価開始rootへ依存し得る`Done(projectable)`の共有である。cycleを含むqueryでは、
sourceから開始した`Done(false)`をdependentからのfresh queryへ流用できないという
具体的な反例が既に固定されている。

structural validityにはOR-armのtruth valueもshort-circuitもない。cycle edgeの存在は
structural failureではなく、全referenced factが存在し局所invariantが成立していれば
validである。従って、top-level成功後に構造validityを共有しても、後続evaluatorは
従来どおりfresh/round-local tri-color evaluationを行う。

以下をそのまま維持する。

- evaluatorの`Visiting` / `Done`はevaluation round内だけ。
- before viewとafter viewは別round。
- cycle cut発生後はshared evaluator memoを捨て、後続rootをfresh fallbackで評価。
- `Visiting`はtop-level return後に残らない。
- SCC/fixpoint/permanent projectability memoを導入しない。

CPK計画 §4 の「新しいcache architectureはnon-goal」は、一般的なsemantic/result cacheを
導入しないという意味で維持する。本書は、CPK計画 §15-14の
「projectabilityの結果を永続的にmemoしない」を一切緩めず、mandatory preflightの
成功だけに限定した派生cacheを明示的な例外として追加する。

## 7. Required invariants

CPK計画 §15の20 invariantをすべて継承し、次を追加する。

21. **Legitimate consequence preservation**
    - semantic replay candidate、accepted consequence、canonical constraint、queue workを
      certificate/cacheの都合で除去しない。
22. **Certificate revision match**
    - certificateは同じbucketのcurrent `formula_revision`にだけ有効。
23. **Atomic certificate publication**
    - structure commitの途中やprepare failure後にnew certificateを公開しない。
24. **Fallback completeness**
    - certificateがmissing/dirtyなら現行order-only→validationの二段pathを使う。
25. **NonCanonical precedence**
    - `NonCanonicalProjectionOrder`がallocation/dangling/support errorより先に返る現行規則を
      弱めない。
26. **Exact adjacency parity**
    - adjacency action集合はcanonical formulaから導出したtyped action集合とexact一致する。
27. **No coarse identity collapse**
    - representative、carrier、side、lineage、row derivation等がvalidation identityへ
      影響する場合、それらをrootだけへ畳まない。
28. **Snapshot completeness**
    - preflightが読む全mandatory inputのmutationがsnapshotをinvalidateする。
29. **No failure cache**
    - failure、error、fail-open、owner attributionをcacheしない。
30. **Top-level success publication**
    - visiting stackが完全にunwindし、top-level traversal全体が成功した後だけ
      `Valid(snapshot)`をpublishする。
31. **Evaluator separation**
    - structural validityからprojectability、OR-arm、cycle result、evidenceを推定しない。
32. **Saturating identity safety**
    - revision/snapshotがsaturateした後はreuseを止め、wraparoundで古いentryをvalidにしない。
33. **Optional-cache allocation safety**
    - cache capacity failureはuncached validationへ戻り、panicや新semantic failureを生まない。
34. **No empty-topology walk**
    - adjacency cursorは実在actionだけを訪れ、empty category/group combinationを走査しない。
35. **Bounded writer work**
    - adjacency/certificate maintenanceが、一件のsmall deltaに対してunboundedなrecord-wide
      shift/rebuildを要求しない。
36. **No-claim preservation**
    - formulaを持たないno-claim pathにcertificate/adjacency/cache heap allocationを追加しない。

## 8. Oracle / fixture / census strategy

### 8.1 Branch A oracle

- test buildで、certificate-valid bucketについてもlegacy order-only passをshadow実行し、
  pass/failureとfirst offending pairを比較する。
- full std / RMW / GWCB / MPC / DPN / RCPF / PCLF / QORF fixture matrixでmismatch zero。
- full-chunk split、AVL rotation、rekey、comparator-equal prefix、late earlier insertion、
  source-conflict、support promotionを含める。
- missing/dirty certificate、direct corruption、order violation+dangling premise同居fixtureで、
  `NonCanonicalProjectionOrder`が先に返ることを確認する。

### 8.2 Branch B adjacency oracle

- canonical clause/incidence列からlegacy validation actionをlinear reconstructionする
  test-only oracleを保持する。
- adjacencyと、identityごとにdedupしたlegacy action集合をkey-for-key比較する。
- new occurrence、late extension、same clause/new support、same premise/different carrier、
  representative/root move、structural/reduction/replay mixed orderを含める。
- actionのfast traversalがfailureを発見したとき、canonical fallbackがlegacyと同じerror・
  owner・priorityを返すことを確認する。

### 8.3 Snapshot invalidation matrix

§5.4の各mutation classについて、次を独立fixtureで固定する。

1. snapshot `S`でvalidation成功。
2. exact no-opではsnapshotが変わらずcache hit。
3. relevant mutationでは`S' != S`となりcache miss。
4. mutation後のforced-uncached resultとcached-enabled resultがbyte-identical。
5. allocation failureではstate/output/epochが既存挙動と一致。

### 8.4 Cycle fixtures

- DPNのself-cycle、two-node cycle、mixed record/constraint cycle。
- cycle+independent armの両insertion order。
- source→dependent / dependent→sourceの両query順。
- structural cache on/offでprojectability/evidence/cycle-cut/fresh-fallbackが一致。
- top-level failure/cycle unwind前に`Valid(snapshot)`が一件もpublishされない。
- **back-edge cycle + dangling leaf fixture**（独立adversarial reviewで特定した最も鋭い
  反例形）: `A -> B`、`A -> dangling C`、`B -> A`という構造で、Aから開始した
  top-level traversalが`B -> A`の再訪をactive-path cycleとして早期`Ok`扱いし、
  Bがlocalには完結できる状態で、その後`A -> C`がdangling factで失敗する場合を固定する。
  この場合、Bを含めtop-levelで得た全candidateが一件も`Valid`としてpublishされないこと、
  かつ後続の独立したB単体queryが正しくdangling Cを検出できることを確認する。

上記fixtureの位置づけについて: これは新規に発見された未解決の反例ではなく、
現行`ProjectionPreflight::validate_record`のtermination guardの挙動と§5.5の
top-level-unwind-then-publish規則を突き合わせて確認した結果、正しく遮断されることが
確認済みの形である。ただし正しく遮断される理由が実装の細部（§5.5の実装上の必須分離）に
依存するため、回帰を検出できるfixtureとして明示的に固定する。

### 8.5 Performance census

counterはtest/census build限定とし、production hot pathへlogging/synchronizationを残さない。

- formula mutation event/link数。
- certificate hit/miss/dirty fallback。
- order-only cursor yield。
- adjacency action数とraw clause-derived action数。
- structural cache hit/miss、record/constraint expansion、candidate publish/drop。
- canonical fallback error件数。
- evaluator instance/query/node/cycle-cut数（既存MPC/DPN metric）。
- allocation capacity-inclusive bytes、no-claim allocation、peak RSS。

## 9. Implementation slices

各sliceは別commit・別rollback単位とし、authority切替とshadow構築を同じcommitへ混ぜない。

### CPK-SV-A: shadow admission-time certificate

Authority: current order-only pass。

- bucket-local formula revisionとcertificate typeを追加する。
- all production admissionでtransactionally dual-writeする。
- certificateをproduction queryにはまだ使わない。
- §8.1のunit/fixture oracleとenv-gated full-workload exhaustive oracleを追加する。
- capacity/failure injectionを全persistent reserve pointで行う。

Gate:

- certificate/legacy order result mismatch zero。
- formula sequence/exact link/support summary byte parity。
- admission failureでpartial certificate publication zero。
- writer comparison/movementが§7-35のboundを満たす。
- no-claim allocation zero。

Rollback: certificate/revision shadowだけを削除し、query pathを変更しない。

### CPK-SV-B: order-error authority cutover

Authority: valid certificate。missing/dirty時はlegacy fallback。

- production preflightのorder-only passをcertificate checkへ置換する。
- dirty/missing/corruption pathは既存二段validationを維持する。
- shadow legacy passをtest/env-gated oracleとして残す。

Gate:

- certified success pathのorder-only cursor yield == 0。
- `NonCanonicalProjectionOrder`、dangling、allocation、support errorのpriority byte parity。
- full proof tests、pinned cycle tests、motivating tests、full-std oracle green。
- wall/RSS non-regression。

Rollback: query authorityだけをlegacy order passへ戻し、certificate shadowは残せる。

### CPK-SV-C: shadow distinct-dependency adjacency

Authority: canonical formula-derived validation。

- typed action identityとrecord-local adjacencyを追加する。
- admission/rekey/move transactionへadjacency deltaを接続する。
- production preflightはまだlegacy clause walkを使う。
- §8.2のlinear reconstruction oracleを保持する。
- capacity-inclusive footprintとrecord-local action distributionを測る。

Gate:

- action membership mismatch zero。
- mixed-order/move/late-extension fixture parity。
- one-event writer workがbounded。
- no nested empty traversal、explicit cursor codegen確認。
- shadow RSSが18 GiB safety thresholdへ近づかない。

Rollback: adjacency shadowだけを削除する。SV-A/Bのcertificate authorityは残せる。

### CPK-SV-D: snapshot-scoped successful-validation reuse

Authority: certificate + adjacency + structural validity cache。

- `ProofStructuralSnapshotId`と全relevant mutation notificationを接続する。
- adjacency-based success validationをproductionへ切り替える。
- same-snapshot `Valid` hitでrecord/constraint closureをskipする。
- failure時canonical fallback、top-level candidate publication、optional-cache allocation fallbackを
  実装する。
- forced-uncached modeをtest/env-gated oracleとして保持する。

Gate:

- cached/forced-uncached output、error、evidence、cycle behavior mismatch zero。
- snapshot invalidation matrix全項目green。
- full std parity harness green。
- N=6同一snapshotで一つの`(record, snapshot)`を複数回expandしない。
- evaluatorのprojectability memo lifetime/cycle-cut countが既存契約どおり。
- no-claim allocation zero。

Rollback: cache/adjacency read authorityをlegacy clause validationへ戻す。adjacency shadowと
certificate authorityは独立に残せる。

### CPK-SV-E: integration / profiling closeout

- RMW N=1..6のraw counterとwall timeを再採取する。
- cold/warm std、代表corpus、full safety-scoped infer suiteを実行する。
- gdb samplingで`ProjectionPreflight`、canonical cursor、evaluatorのself-timeを再確認する。
- temporary counters、dual-read oracle、migration flagをdesignで保持すると決めたもの以外は
  撤去する。
- final footprint、RSS、error/cycle/portable/logical outputを記録する。

Gate:

- certified pathのorder-only scan zero。
- validation workがraw clause incidenceではなくdistinct actionとsnapshot missに比例する。
- correctness mismatch zero。
- performance改善がprofile/counter/wallの三者で説明できる。

## 10. Performance target

N=7の既存gdb sampleでは`ProjectionPreflight` stackが66/116、56.9%だった。N=6の
4.839sへ単純適用すると約2.75sだが、これは全preflight workを除けるという意味ではない。

N=1のpreflight-yield/fresh比をN=6へ外挿した理論proxyでは、N=6の50.297M二重pass
yieldのうち46.309M、92.07%が増幅分に相当する。しかしmandatoryな最初のvalidation、
semantic lookup、failure fallback、cache bookkeepingは残る。

したがって目標を次のように置く。

- **構造gate**:
  - valid certificate pathのorder-only pass 0。
  - same snapshotで成功済みのrecord/constraint再展開 0。
  - cache miss時のdependency visitはraw clause数ではなくdistinct action数に比例。
- **現実的なwall目標（推定）**: RMW N=6の4.839sから1〜2s回収。
- **非保証**: 2.75s全回収、linear scaling、sub-millisecond、fresh consequence削減。
- **最低landing gate**: correctness/footprintを維持し、wall timeをregressさせず、profile上の
  preflight amplification clusterを有意に縮小する。

counterだけ減ってwall timeが改善しない場合は、完了と宣言せず再profileする。profileが
別の支配costを示した場合、本書の範囲を広げてguess-and-patchしない。

## 11. 採らない案

### 11.1 Accepted consequenceをalpha/isomorphic dedupする

採らない。mutable-reference調査のglobal alpha censusはaccepted 926件中global
alpha-equivalent 0を確認している。locally isomorphicな898件は異なる共有関係を運ぶ。
本書の性能改善と混同しない。

### 11.2 Formula mutation epoch間のdelta revalidationを主案にする

採らない。later serialの未変更record rescanは8件・14 clausesだけだった。支配重複は
same-snapshot cross-roundである。

### 11.3 Projectability evaluatorの`Done`をstructural cacheへ保存する

採らない。DPN/MPCのcycle counterexampleと正面から矛盾する。structural validityから
Included/Excludedを推定しない。

### 11.4 Certificateなしでorder-only passを削除する

採らない。`NonCanonicalProjectionOrder`のerror precedenceを壊し、writer/index corruptionを
silentにする。

### 11.5 Failure/errorをcacheする

採らない。owner attribution、first-error precedence、terminal failure latch、後続mutation後の
回復可能性を変える。

### 11.6 Unordered adjacencyが見つけたerrorを直接返す

採らない。success validationの順序は意味を持たなくても、failureの最初のowner/errorは
canonical orderに依存する。failure時はcanonical fallbackをauthorityにする。

### 11.7 Query時にformulaからadjacencyをcollect/sortする

採らない。full scanとquery-local allocationを別名で再導入する。adjacencyはwriter-boundaryで
transactionally維持する。

### 11.8 Global graph scan / SCC / fixpoint

採らない。DPN/MPCのno-global-scan、no-fixpoint契約を維持する。structural traversalは
reachable graphに限定し、cycle detectionは現行active-path guardを使う。

### 11.9 Cache missを`Valid`やfail-openへ吸収する

採らない。cache missはuncached validationを要求するだけであり、semantic decisionではない。

## 12. Stop conditions

次のいずれかが発生した時点で次sliceへ進まず、本書のレビューへ戻る。

1. certificateとlegacy order-only passに一件でもmismatchが出る。
2. adjacencyとlegacy clause-derived validation action集合に一件でもmissing/extra/mismatched
   identityが出る。
3. `NonCanonicalProjectionOrder`または他のerror precedence/owner attributionが変わる。
4. certificate/cacheを成立させるためにaccepted consequence、queue work、formula clause、
   support/linkを減らす必要が出る。
5. structural cacheへprojectability、cycle result、evidence、fail-openを保存する必要が出る。
6. evaluatorのbefore/after round、cycle-cut sharing-disable、fresh fallbackを変更しなければ
   structural cacheが成立しない。
7. relevant mutationをsnapshot identityへ完全に列挙できない。
8. snapshot saturation/wraparoundで古い`Valid`が再利用され得る。
9. top-level unwind前、failure後、partial commit後に`Valid`がpublishされる。
10. optional cache allocation failureがpanic、semantic error、partial mutationを生む。
11. adjacency writerがsmall deltaに対してrecord全体のunbounded shift/rebuildを要求する。
12. no-claim workloadに新しいpersistent allocationが生じる。
13. cache on/off、forced-uncached、shadow oracleでscheme/projectability/evidence/portable/
    diagnostic出力に差が出る。
14. cycle fixtureの結果がroot query order、clause/link insertion orderに依存する。
15. full-std exhaustive oracleに一件でもmismatchが出る。
16. peak RSSが18 GiB safety thresholdへ近づく、またはcapacity-inclusive footprintを説明
    できない。
17. counterだけ減り、wall/profileが同等以上に悪化し、その原因を説明できない。
18. source changeが本書のproof/preflight cause boundaryを越え、subtype/worklist/row/SCC/
    generalization意味論の変更を必要とする。

stop conditionを、fail-openの拡張、test期待値変更、error順序変更、cache keyの粗化、
organic mismatchの除外で回避しない。

## 13. Rollback units

- **SV-A**: certificate/revision shadowだけをrevert可能。production read不変。
- **SV-B**: certificate authority cutoverだけをlegacy order passへ戻せる。SV-Aのshadowを
  残して再調査できる。
- **SV-C**: adjacency shadowだけをrevert可能。certificate read authority不変。
- **SV-D**: adjacency/cache read authorityをlegacy canonical validationへ戻せる。
  snapshot generationやshadow adjacencyを残す場合もprojectability memoへ転用しない。
- **SV-E**: measurement/cleanup/documentationのみ。新しいauthority変更を混ぜない。

rollback後もCPK計画、MPC/DPN round、DPN cycle、PCLF/QORFの既存authorityとoutputを
変更しない。部分的なcache hit pathや、一部mutationだけがsnapshotをbumpする状態を残さない。

## 14. 既存文書との対応

### 14.1 CPK計画

継承するもの:

- §4のlegitimate replay reduction non-goal。
- §9.2のprepare/commit transaction。
- §10.2のprojection API。
- §11のbefore/after separationとinvalidation。
- §12のmandatory fact / terminal failure policy。
- §15の全invariant、特に13（before/after分離）、14（projectabilityの恒久memo禁止）、
  20（failed attemptから出力しない）。

追加・精密化するもの:

- projection queryのmandatory preflightに、admission-time certificateと
  snapshot-scoped successful structural validationを導入する。
- §4の「新しいcache architecture」non-goalに対し、semantic/result cacheではない
  structural-validity cacheを明示的・限定的な追補として定義する。
- §15へ本書§7のinvariant 21〜36を追加する。

### 14.2 Mutable-reference調査

§7.2のalpha census結論を維持する。本書は「必要なworkを重複と再分類する」のではなく、
必要なworkが作ったproof relationをproof queryが何度読むかを変更する。

### 14.3 MPC/DPN round追補

evaluation snapshot/view/round、before/after、cycle cut後のsharing disable、fresh fallbackを
維持する。本書のstructural snapshotはevaluation viewを含まず、projectability memoを
共有しない。

### 14.4 DPN cycle追補

arena ID順序へ依存せず、active-path cycle guardを維持する。structural validationの
candidate publicationもtop-level unwind後に限定し、`Visiting`をpersistent stateへ
昇格させない。

## 15. Claude独立査読 checklist

1. CPK計画 §4のnon-goalと本書の限定cache例外の境界が曖昧でないか。
2. snapshot invalidation表が現行`ProjectionPreflight`の全readを網羅しているか。
3. support resolve、claim move、live coverage、row/carrier/witnessのどれかがinvalidate漏れして
   いないか。
4. certificateが証明できるbucket-local事実と、Branch Bでしか証明できないexternal factを
   混同していないか。
5. certificate-valid時にorder-only passを省略しても、現行error precedenceが数学的・
   fixture上の両方で保たれるか。
6. distinct action identityがrepresentative/carrier/side/lineage等を粗く畳んでいないか。
7. adjacency fast failure→canonical fallbackがfirst error/ownerを完全に保存するか。
8. active-path cycle中のnodeが早期に`Valid`へpublishされる経路がないか。
9. same-snapshot reuseがevaluation result memoへ実質的に変質していないか。
10. cache allocation failureが既存ResourceExhausted/error precedenceを変えないか。
11. atomic commitの途中にrevision/snapshot/certificateの不整合な組が観測されないか。
12. SV-A〜Eが独立rollback可能で、shadowとauthority cutoverを混ぜていないか。
13. PCLF-Dで問題になったnested empty-visiting iterator topologyをadjacencyが再導入しないか。
14. adjacency writerにPCLF-D0/QORF-D0型のquadratic/unbounded growthがないか。
15. RMW×1〜6、full std、cycle/error fixturesのcounter/gateが結論を反証可能な形になって
    いるか。

## 16. 完了条件

- valid certificate pathのorder-only full scanがゼロ。
- same structural snapshot内で成功済みのrecord/constraintを再展開しない。
- cache missのvalidationがdistinct typed actionに比例し、raw clause重複に比例しない。
- legitimate consequence、queue、formula、projectability、scheme、evidence、portable/
  diagnostic outputがbaselineと一致。
- error precedenceとcycle semanticsが全oracleで一致。
- no-claim allocation、allocation failure atomicity、18 GiB RSS safety gateが成立。
- RMW N=1〜6とstd/corpusのwall/profile/counterを保存し、改善または未達を数字で説明する。
- temporary shadow/oracle/instrumentationをSV-Eで整理する。
- Claude (Sonnet 5)の独立査読・確定とユーザ承認が完了している。

---

著者: Codex gpt-5.6-sol（xhigh）が起案、Claude (Sonnet 5) が独立査読・確定（査読完了、
独立adversarial reviewによる§6.3 cycle-safety分離主張の反証試行を含む）

状態: **ユーザ承認済み**（2026-08-12）。CPK計画への正式な追補として確定した。
CPK-SV-A以降の実装に着手してよい。
