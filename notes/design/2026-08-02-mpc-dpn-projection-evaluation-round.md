# MPC/DPN 追補: projection evaluation round と atomic clause-link mutation batch

日付: 2026-08-02

状態: **ユーザ承認済み**

本書は、`notes/design/2026-07-31-mixed-proof-conjunctive-ownership.md`
（以下 MPC 文書）、`notes/design/2026-08-01-derived-unary-premise-nodes.md`
（以下 DPN 文書）、および
`notes/design/2026-08-01-dpn-root-claim-and-cycle-safety-addendum.md`
（以下 DPN cycle 追補）の性能契約を精密化する追補設計である。

既存文書が定めた投影意味論、`ProofPremise`、tri-color cycle cutting、
逆依存 index、epoch / cache の意味は変更しない。本書が新たに定義するのは、
複数のtop-level queryがmemoを共有できる境界である
**projection evaluation round**と、同一admission eventのclause-link群を
一回のbefore/after判定でpublishする**atomic mutation batch**である。

調査・実装基準は `main` の `9328d043`。A1
（exact duplicate先行判定、`6ecf60e8`）とA2
（proof mutation flat-gate比較、`9328d043`）は実装・検証済みであり、
本書はそれらを再設計しない。

## 1. 背景

DPN-B着地後、`SchemeProjectionEvaluator::eval_record` の起動回数
（以下 evaluator Q）が `std::text::parse` module lowering の支配的コストになった。

前段censusで確認された内訳は次のとおりである。

| 項目 | 観測値 |
| --- | ---: |
| evaluator Q の `7085192b` 基準比 | 13.5倍超 |
| A1前のclause-link登録attemptに占めるexact duplicate | 約70% |
| exact duplicate経路が全evaluator Qに占める割合 | 約51% |
| exact duplicate経路のevaluator Q | 約780万 |
| nonduplicate clause-linkのbefore/after evaluator Q | 約670万 |
| proof mutationのbefore/after組 | 427,406組 |
| 上記proof mutationのevaluator Q | 854,812 |
| A1前の総evaluator Q | 約1,530万 |

総Qと約780万は、前段censusの丸め済み比率・回数から復元した約値である。
exactなraw counter logは現HEADに残っていないため、これらをテスト期待値として
固定しない。A3実装時には§8の三つのmetricを改めて別々に採取する。

支配call siteは
`crates/infer/src/constraints/machine/bounds.rs:931` の
`ConstraintMachine::register_record_proof_clause_link` だった。
A1以前は、exact duplicateでもduplicate判定より先に
`scheme_projection_record_is_included`を一回起動していた。
nonduplicateでは、一linkごとにcommit前後で二回起動していた。

A1は、exactな `(lower_record, support, clause)` linkの存在を
`record_proof_clause_link_is_registered`で先に判定し、duplicateなら
evaluator・台帳mutation・dependency edge・epoch publicationのすべてを
省略する。既存clauseへ新しいsupportを結ぶ場合はduplicateではない。

A2は、proof mutationについて

```text
included(record) = flat_fail_open(proofs) OR clause_eval(record)
```

と分解し、proof vectorを読まない`clause_eval`が不変なら、
before/afterの`flat_fail_open`だけで不要な再帰評価を除去できることを利用した。
実測した427,406組はすべてinclusion no-opだった。

しかしA1+A2適用後も、nonduplicate clause-linkのbefore/afterだけで
約670万回のevaluator起動が残るという事前予測どおり、
`std::text::parse` loweringは300秒でtimeoutした。
A1/A2は正しい局所是正だが、実用速度へ戻すには次の二層が必要である。

- A3: 同一snapshot・同一view内の複数top-level queryでevaluatorを共有する。
- A4: 同一admission eventのclause-link群を一つのatomic batchとしてcommitする。

## 2. 用語

### evaluator-read snapshot

`SchemeProjectionEvaluator`が一回の評価中に読む状態の固定値をいう。
少なくとも次を含む。

- bound recordの存在、state、direction、owner
- projection proof・clause・clause-link台帳
- `claim_parents_by_constraint`を含むconstraint route
- `root_claim_by_producer_constraint`
- canonical coverage rootと`live_coverage_by_root`
- `dependent_records_by_premise`
- constraint recordとlinked lower record
- projectability判定が読むその他のledger metadata

現実装の`SchemeProjectionEvaluator<'a>`は
`&'a ConstraintMachine`を保持する。このborrowが存続している間、
borrow checkerは同じmachineへのmutationを禁止する。したがって
「snapshot」は状態のcloneではなく、不変borrowによって固定された
machine viewとして実装できる。

### evaluation view

snapshotに加えて、評価結果を変えるoverride集合を固定したものをいう。

- current proof view、またはprevious proof override
- current root liveness view、またはprevious root-liveness result override
- current record inclusion view、またはprevious record-inclusion override

snapshotが同一でもoverrideの種類・key・値が一つでも異なれば別viewである。
overrideはround開始前に確定し、最初のtop-level query後に追加・変更しない。

### top-level query

iterator・snapshot作成・mutation publicationなどの呼び出し元が、
一つのroot recordについて開始する`eval_record`をいう。
`eval_record`や`eval_constraint`から再帰的に呼ばれる評価は
top-level queryに数えない。

### evaluation round

**同一evaluator-read snapshot、同一evaluation view、途中にmutationを挟まない**
複数のtop-level queryのまとまりをいう。

round-local memoは、この境界内でだけ共有できる。before viewとafter viewは
同じeventに属していても別roundである。

### atomic mutation batch

同一lower recordに対し、同一admission eventが一度に供給した
clause-link列を、途中のinclusion評価・epoch publicationを挟まずにcommitする
mutation単位をいう。

atomicとは、他の評価やpublicationから部分commit状態を観測させないことを意味する。
失敗時rollbackを備えた汎用transactionを意味しない。

## 3. Exact no-op規則

A1とA2の実装済み規則を次のとおり継承する。

### A1: exact clause-link duplicate

`TypeBounds::record_proof_clause_link_is_registered`
（`constraints/mod.rs:1438`）は、insert pathと同じ
`record_proof_clause_key` / `record_proof_clause_link_key`を使う。

- exactな`(lower_record, support, clause)`が既存なら即returnする。
- evaluatorを起動しない。
- clause・link・dependency edgeを変更しない。
- owner/global epochもprovenance epochも進めない。
- 同じclauseでもsupportが異なれば新しいattributionであり、no-opにしない。
- batch内duplicateにも同じexactnessを使う。

### A2: proof mutationのflat-gate比較

`ConstraintMachine::apply_scheme_projection_mutation`
（`constraints/mod.rs:1153`）は、proof vectorだけが変わるmutationについて
before/afterの`flat_fail_open`を比較する。

- `true -> true`または`false -> false`:
  inclusionは不変。再帰評価を行わず、metadata mutationとして
  provenance publicationだけを行う。
- `true -> false`:
  before inclusionは既知の`true`。afterだけを再帰評価する。
- `false -> true`:
  after inclusionは既知の`true`。before proof override側だけを再帰評価する。

この規則はproof vectorだけが変わり、clause評価が不変である場合に限る。
clause・dependency・liveness mutationへ一般化しない。

## 4. Round-local memo契約

round-local memoは、同一snapshot・同一viewに限って共有する。

次を必須とする。

1. evaluatorまたはround objectの構築時にviewを確定する。
2. 最初のtop-level query後にproof/root/record overrideを変更しない。
3. machine mutation、epoch publication、clause/link/edge登録を跨いで共有しない。
4. beforeとafterは必ず別roundにする。
5. round終了時にmemoを破棄し、`ConstraintMachine`や`TypeBounds`へ保存しない。
6. 恒久cacheとそのinvalidation義務を新設しない。

A3の適用単位は次である。

| 現HEADの入口 | evaluation round |
| --- | --- |
| `scheme_projectable_lowers(var)`（`mod.rs:988`） | 一回のiteratorが問い合わせる全claimed lower recordを一つのcurrent-view roundで評価 |
| `projection_inclusion_snapshot`（`mod.rs:1248`） | mutation前の全dependent recordを一つのbefore roundで評価 |
| `publish_projection_inclusion_snapshot`（`mod.rs:1265`） | mutation後の全dependent recordを一つのafter roundで評価 |
| `record_scheme_projection_liveness_mutation`（`mod.rs:1108`） | previous root-liveness override側とcurrent側を別roundで評価 |
| `publish_record_inclusion_change`（`mod.rs:1211`） | previous record-inclusion override側とcurrent側を別roundで評価 |
| `apply_scheme_projection_mutation` | A2で未知のまま残るprevious proof側とcurrent側を別roundで評価 |

A2によって片側または両側の再帰評価が不要と証明できる場合、
その側のroundは作らない。

`scheme_projection_record_is_included`の単発利用はsingleton roundとしてよい。
複数rootが明示的に並んでいる呼び出し元からこのsingleton入口を繰り返さず、
呼び出し元が一つのroundを所有する。

## 5. Cycle安全性

DPN cycle追補B2のtri-color意味論をそのまま継承する。

```text
EvalState = Visiting | Done(projectable)

Done(v) への再訪 -> v
Visiting への再訪 -> そのcircular routeだけfalse
absent             -> Visitingとして評価し、return前にDoneへ遷移
```

### top-level confinement

`Visiting`は一つのtop-level再帰中だけ存在してよい。
各top-level queryのreturn時、roundのstate tableに`Visiting`が残ってはならない。
到達した全nodeは`Done`であるか、state tableに存在しない。

### cycle cut後の共有禁止

cycleを含む評価で得た`Done`は、評価開始rootに依存し得る。
この反例は
`crates/infer/src/constraints/machine/bounds.rs:3624` の
`dpn_b_cycle_guard_cyclic_route_plus_independent_source_stays_projectable`
から得られる。

同testの`standalone_first == false`側では、sourceが

```text
source = cycle-arm OR independent-arm
dependent = source
cycle-arm = dependent
```

という形を持つ。

sourceを先に評価すると、cycle-armの途中でdependentへ
`Done(false)`が残った後、independent-armによりsource全体は`true`になる。
同じevaluatorで次のtop-level queryとしてdependentを読むと、
このcontext依存の`Done(false)`を返してしまう。
fresh evaluatorでdependentから評価すれば、sourceのindependent-armへ到達して
`true`になる。

したがってroundは次の規則を持つ。

```text
query(root):
    if sharing_disabled:
        return fresh_evaluator(snapshot, view).eval_record(root)

    cuts_before = shared.cycle_cuts
    result = shared.eval_record(root)
    assert(sharedにVisitingが残っていない)

    if shared.cycle_cuts != cuts_before:
        shared = None
        sharing_disabled = true

    return result
```

- cycle cutが一度も発生していない`Done`だけを後続rootへ共有する。
- 一つのtop-level queryでcycle cutが発生した場合、そのqueryの結果は返してよい。
- その後の全top-level queryは、それぞれfresh evaluatorで評価する。
- 同じround内で共有を再開しない。
- SCC構築・fixpoint・恒久memoへ切り替えない。

roundの観測結果は、同一snapshot・同一viewについて
「各rootをfresh evaluatorで評価した結果」をoracleとし、root query順や
clause挿入順に関係なく一致しなければならない。
`cycle_cuts`の回数自体はshort-circuit順によって異なり得るが、
projectable結果は異なってはならない。

## 6. Atomic clause-link batch

A4は、同一lower record・同一admission eventのclause-link群だけをまとめる。

現HEADで自然なbatch境界を持つ代表入口は次である。

- `register_claim_parent_clause_links(lower_record, parents)`
  （`machine/bounds.rs:875`）へ一度に渡されるparent列
- `register_lower_projection_delta`（`:1231`）の一つのlower deltaから得た
  `independent_supports`
- 一つのreplay/evidence admissionが明示的に保持する同一lower record向けlink列

batch処理は次の順序に固定する。

1. existing exact linkをA1のpredicateで除去する。
2. batch内のexact duplicateを除去する。
3. 残りが空なら、evaluator・allocation・epoch publicationなしでreturnする。
4. lower recordのbefore inclusionを一回評価する。
5. 残った全linkをcommitする。
6. batchで新規作成された各clauseについて、dependency edgeを一回ずつ全登録する。
7. lower recordのafter inclusionを一回評価する。
8. before/afterのnet changeを一回だけpublishする。

batch内に同じclause・異なるsupportが複数あっても、それらは別linkとしてcommitする。
dependency edgeはclauseの新規作成に対応するため、一clauseにつき一回だけ登録する。

`ConstraintMachine::register_record_proof_clause_link`
（`:931`）の単一link入口は、singleton batchへのdelegateとして残してよい。
複数linkを持つ自然なeventからこの入口をloopで呼び、per-link before/afterを
復活させてはならない。

次を一つのbatchへ混ぜない。

- 異なるlower record
- 異なるsolver/admission event
- 呼び出し元が同一eventだと証明できない隣接link
- liveness transition
- proof mutationや別のepoch publicationを跨ぐ列
- iteratorや後段scanで事後的に集めたlink

batchの目的は既知のevent境界を保存したままpublicationを一回にすることであり、
広い時間窓のmutationを推測で合流させることではない。

## 7. Epoch/cache契約

epochはper-linkの途中状態ではなく、atomic eventのnet resultに対してpublishする。

### exact no-op

existing duplicateだけ、またはbatch内duplicate除去後に空となるbatchは
何も変更しない。

- owner/global constraint epochを進めない。
- owner var epochを進めない。
- provenance epochを進めない。
- cache invalidationをpublishしない。

### metadata-only mutation

新しいclause/link/edgeまたはproof metadataが追加されたが、
before/after inclusionが同じ場合:

- owner/global constraint epochを進めない。
- owner var epochを進めない。
- provenance epochを進める。
- per-linkではなくadmission event単位で一回publishする。

同じadmission event内の先行`SchemeProjectionMutation::ProofsChanged`が
すでにprovenance mutationをpublishしている場合、そのpublicationを
batch metadataのpublicationとして共有してよい。provenance counterのexactな
増分回数は意味契約にしないが、metadata changeをepochなしで終えてはならない。

### inclusion flip

lower recordまたはdependent recordのinclusionが反転した場合:

- active ownerを重複除去してmutation対象にする。
- active ownerが一つ以上あればglobal constraint epochを一回進める。
- 各affected ownerのvar epochを同じglobal epochへ進める。
- provenance epochも進める。
- 一batch内の途中flipをpublishせず、最終的なnet flipだけをpublishする。

active ownerを持たないtombstone/欠落recordではowner epochを発明せず、
metadata publicationだけを保つ。

### cache同値性

`GeneralizeCompactCache`その他のconstraint/owner epoch consumerについて、
cache onとcache offの最終scheme・projectability・provenance結果は
byte-identicalでなければならない。

- inclusion flipがcacheへ届かない経路を残さない。
- metadata-only mutationをowner/global invalidationへ昇格させない。
- evaluator memoはround終了時に破棄し、cache keyやepochへ持ち込まない。
- batch化前の最終状態とbatch化後の最終状態を同じsnapshotで評価した結果は一致する。

## 8. 性能契約

性能計測では次の三つを混同しない。

1. **evaluator instance数**
   `SchemeProjectionEvaluator::new`の回数。cycle後のfresh fallbackも一instanceと数える。
2. **top-level query数**
   呼び出し元が開始したroot record query数。memo hitでも一queryと数える。
3. **node evaluation数**
   `Record`または`Constraint` nodeがabsentから`Visiting`へ入り、
   uncached bodyを評価した回数。`Done` hitとcycle cutは含めず、別counterにする。

counterはtest/census buildに限定し、production hot pathへ常設の同期・format・logging
コストを載せない。

### A3の計算量

cycle cutのない一roundについて、そのroundの全top-level rootから到達する
proof graphの和集合を`G = (V, E)`とすると、

```text
node evaluations = O(V)
edge/source inspections = O(E)
round全体 = O(V + E)
```

となる。同じnodeをrootごとに再評価しない。

cycle cutが発生したroundでは、以後のrootがfresh fallbackになるため、
round全体のO(V+E)は主張しない。各fresh queryは自身のreachable graphに対して
O(Vq+Eq)であり、cycle発生数・fallback query数を別metricとして記録する。

### A4のquery数

exact duplicate除去後に`K > 0`個のlinkを持つ一batchについて、
clause-link登録が要求するtop-level inclusion queryは

```text
before 1回 + after 1回 = 2回
```

である。`2K`回へ戻ってはならない。`K = 0`なら0回である。

### landing時の実測

A3/A4のlanding時には少なくとも次を保存する。

- `std::text::parse` loweringのwall timeとhard timeout結果
- evaluator instance数
- top-level query数
- node evaluation数
- cycle cutsとfresh fallback query数
- exact duplicate数、batch数、batch内link数の分布
- cache on/off結果

counterだけ減ってwall timeが300秒timeoutのままなら、性能作業は完了ではない。
A3/A4の意味論を保持したまま次の支配コストを再局所化する。

## 9. Regression gates

A3/A4には次のregression gateを必須とする。

1. **fresh/shared oracle同値**
   - 同一snapshot・同一viewのroot列をfresh evaluator列とshared roundで評価し、
     rootごとのbool列が一致する。
   - current、proof override、root-liveness override、
     record-inclusion overrideの各viewを含める。
2. **cycle fixture**
   - `dpn_b_cycle_guard_cyclic_route_plus_independent_source_stays_projectable`
     の`standalone_first`両順序を使う。
   - source→dependent、dependent→sourceの両query順でfresh/sharedが一致する。
   - cycle cut後にcontext依存の`Done(false)`が再利用されない。
3. **insertion-order invariance**
   - clause順、link順、root query順を変えてもprojectability・ledger・edgeが一致する。
4. **Visiting confinement**
   - 各top-level return時にround stateへ`Visiting`が残らない。
5. **A1 exact duplicate**
   - existing exact linkはevaluator 0、mutation 0、全epoch delta 0。
   - existing clause＋new supportはduplicate扱いしない。
6. **batch-local duplicate**
   - 同一batch内のexact duplicateを一linkへ畳み、最終ledgerが逐次exact-dedup oracleと一致する。
7. **atomic net publication**
   - `K` linkのbatchがbefore/after各一queryだけを行う。
   - metadata-onlyではprovenanceのみ、net inclusion flipではowner/globalへ届く。
8. **A2 no-op / one-sided evaluation**
   - flat gate不変ではnode evaluation 0。
   - gate flipでは未知側だけを評価する。
9. **cache on/off同値**
   - projectability、scheme、portable provenance、diagnostic入力が一致する。
10. **no-claim allocation**
    - `dpn_a_no_claim_workload_allocates_no_registration_ledgers`
      を期待値無変更で保つ。
    - no-claim / unclaimed fast pathがround memo・batch dedup table・clause ledgerを
      heap allocateしない。
11. **既存cycle semantics**
    - self-cycle、two-node cycle、mixed record/constraint cycleの期待値を変更しない。
    - cycle＋independent armは独立証拠によりprojectableのまま。

## 10. Stop conditions

次のいずれかが判明した時点で実装を止め、本書のレビューへ戻る。

1. 同一snapshot・同一viewでshared roundとfresh evaluator oracleが一致しない。
2. top-level queryのreturn後に`Visiting`が一つでも残る。
3. roundがmachine mutation、epoch publication、またはview変更を跨がなければ
   必要な性能が得られない。
4. cycleを含むprojectability結果がroot query順・clause挿入順・link挿入順に依存する。
5. cycle cut後のmemo共有を止めてもfresh oracleと一致しない。
6. cache on/offでscheme・projectability・provenance・diagnostic入力に差が出る。
7. inclusion flipがowner/global epochへ届かない経路、またはmetadata changeが
   provenance epochへ届かない経路が見つかる。
8. exact no-opがepochやcache invalidationを進める。
9. atomic batchを成立させるために異なるrecord・event・publication epochを
   一つへ混ぜる必要がある。
10. no-claim workloadに新しいheap allocationまたはledger entryが生じる。
11. acyclic roundのnode evaluationがO(V+E)を超える。
12. SCC、fixpoint、恒久的な判定cache、または新たなinvalidation graphが
    必要になる。
13. 既存MPC/DPN pinned testの期待値変更が必要になる。
14. A3/A4後も`std::text::parse`が300秒timeoutし、次の支配関数を
    metricから説明できない。

stop conditionを、cycle結果の再利用、fail-openの拡張、epochの過剰bump、
広域batchで回避しない。

## 11. Landing/rollback units

A3とA4は別commit・別rollback単位にする。

### A3: cycle-safe evaluation round

変更範囲:

- round ownerとshared evaluatorの導入
- snapshot/view固定
- `scheme_projectable_lowers`、snapshot/publish、liveness/proof/record mutationの
  複数root queryへの接続
- cycle cut検出後のsharing disableとfresh fallback
- §8の三metricと§9.1〜9.4のregression

landing gate:

- fresh/shared oracle同値
- 全既存cycle test期待値不変
- cache on/off同値
- no-claim allocation不変
- acyclic fixtureでO(V+E)
- `std::text::parse`の実測保存

rollback:

- 複数root call siteをfresh evaluator per queryへ戻す。
- A1/A2、tri-color cycle semantics、MPC/DPN台帳・epoch契約は残す。
- roundの一部やcross-root memoだけを残さない。

### A4: natural-event atomic batch

変更範囲:

- 同一event link列のexact local dedup
- nonempty batchのbefore一回・全commit・全edge登録・after一回
- net epoch/cache publication
- `register_claim_parent_clause_links`とlower deltaの自然なbatch接続
- §9.5〜9.10のregression

landing gate:

- batch後のledger・edge・projectabilityが逐次登録の最終状態oracleと一致
- `K > 0`でbefore/after各一query、`K = 0`で零query
- duplicate/no-op epoch、metadata-only epoch、inclusion-flip epochが契約どおり
- A3のfresh/shared gateと既存MPC/DPN testが期待値無変更
- `std::text::parse`の実測保存

rollback:

- event batchをsingleton link登録へ戻す。
- A1 exact preflight、A2 flat-gate、A3 evaluation roundは残す。
- batch APIだけ、またはbatch dedupだけを中途半端に残さない。

A4のrollbackがA3を要求してはならず、A3のrollbackがA4の台帳結果を
変えてはならない。それぞれ単独で意味論的に正しい状態へ戻せる構成にする。

## 12. MPC/DPNとの対応関係

本書は承認済みの既存三文書を編集しない。

### MPC文書

継承するもの:

- D1のclaim層不可侵と`Qualified` payload不変
- D2のoccurrence帰属・exact carrier・clause意味論
- D3のrecord/clause projectability規則、cycle routeの拒否、不動点禁止
- D4のfail-open方向
- D5の逆依存によるinclusion propagation
- invariant 3の線形metadata、invariant 6のno-claim passthrough
- MPC-Dのepoch/cache同値性
- pinned tests、stop/rollback規律

補完・精密化するもの:

- D3およびinvariant 4の「投影passごとのmemo付き一回走査」に対し、
  本書§2/§4がsnapshot・view・round境界を定義する。
- D5のevent-driven再評価に対し、本書§6/§7が
  同一admission event内のatomic net publicationを定義する。
- §6.3の性能条件を、本書§8の三metricとacyclic O(V+E)で精密化する。

MPCのprojectability意味論を上書きしない。

### DPN文書

継承するもの:

- `ProofPremise`のRecord / Constraint / RootCoverage三ソート
- D3の各node評価規則
- D5の逆依存edgeと登録時bounded chain walk
- D6のcanonical root規律
- no global scan、no fixpoint、no permanent memo

補完するもの:

- DPNが「pass-local」と呼んだmemoの有効範囲を、本書§4の
  同一snapshot・同一view roundとして確定する。
- DPN §6.3の評価性能を、本書§8のinstance/query/node evaluation分離で
  観測可能にする。

DPNのpremise表現・route評価・edge登録規則を上書きしない。

### DPN cycle追補

継承するもの:

- B1のarena ID順序非依存
- B2のtri-color、active-path cycle cutting、circular route=false
- cycle以外の証拠源をOR評価し続ける規則
- SCC/fixpoint禁止
- cycle結果の探索順不変というstop condition

精密化するもの:

- cycle追補B2の「pass-local `Done`」は、単一top-level query内ではそのまま有効。
- cross-root共有では、cycle cutなしの`Done`だけを後続rootへ渡せる。
- cycle cut発生後は本書§5がshared memoを無効化し、以後のrootをfresh評価する。
- cycle追補のO(V+E)主張は本書§8によりacyclic roundへ限定される。
  cycle roundは各fresh query単位のO(Vq+Eq)を保証する。

### A1/A2との関係

A1/A2は既存contractの実装是正であり、本書による新規意味論ではない。

- A1はatomic batchのstep 1/2でexact no-op predicateとして再利用する。
- A2はproof mutation roundを作る前のgateとして維持し、不要なround自体を省く。
- A3/A4のrollback時にもA1/A2を戻さない。

本書が新設する契約は、projection evaluation roundと
atomic clause-link mutation batchの二つだけである。

---

著者: Claude (Sonnet 5)

ユーザ承認済み。
