# URR v3: Direct claim の因果的 qualification

日付: 2026-08-01

状態: **ユーザ承認済み**

本書は、次の設計系譜を継ぐ追補設計である。

```text
DCP (2026-07-30)
  -> MPC (2026-07-31)
  -> CDM (2026-07-31)
  -> DPN (2026-08-01)
  -> DPN root-claim / cycle-safety 追補 (2026-08-01)
  -> 本書: URR v3 causal qualification
```

先行文書はすでに着地している。本書はそれらを編集せず、DPN の root claim base case に
**Direct claim が無条件の独立 leaf として振る舞ってよいかを判定する一点**を追加する。
これは既存の base case に新しい決定点を加える設計変更であるため、実装を先行させず、
本草稿のレビューと明示的な承認を経てから実装 slice へ進む。

調査基準は MPC / DPN 着地 commit `df001de9` と、先行調査で追加された red regression
commit `0ae58f1d`。根因・trace・row-effect 層の反証は直前の独立した二つの調査 round で
確定済みであり、本書では再調査せず、設計判断へ形式化する。

## 0. 本書が下す決定の要約

1. `UpperReplayClaimKind::Direct` かつ `UpperReplayClaimLineage::Original` の claim `D` を、
   常に無条件の独立 leaf とみなす現行規則へ、**因果的 qualification** を加える。
2. `D` の producer constraint `c` に exact な `ClaimQualifiedParent` route `P` があり、
   `P` の canonical coverage root `R` が Reduced root であるとき、安定な候補
   `D -> (P, R)` を lazy index `causal_qualification_by_direct_claim` に記帳する。
3. qualification が評価時に有効になるのは、`R` が live であり、かつ `D` の現在の
   upper record に `R` を root とする claim が同居するときだけである。
4. 有効な qualification を持つ `D` は無条件の独立 leaf ではない。`D` の代わりに
   route `P` を DPN の既存規則で評価する。複数の有効 route は、constraint node の
   複数 route と同じく OR で評価する。
5. 有効な qualification を持たない Direct claim は、現行どおり独立 leaf である。
6. MPC D3 の record-clause OR、ReplayConjunction AND、DPN の route 評価、claim の
   coverage / liveness、`Qualified` payload、URR の generic replay 判定は変更しない。
7. materialization move と liveness transition に伴う invalidation の exact hook は、
   意味論を本書で固定する一方、全 write-site と publish 経路の完全性がまだ未確認である。
   実装前の URR-V3-0 で固定できなければ着工せず、設計レビューへ戻る。

## 1. 問題

### 1.1 co-owned survivor gap の由来

この gap は新しく見つかった別系統の問題ではない。
`notes/bugs/2026-07-28-local-var-effect-residual-transport-gap.md` の
2026-07-29 unresolved-items と、
`notes/design/2026-07-29-unweighted-row-reduction-fix.md` v2
（`82c79dd2` / `215ba17f`）で、次期設計項目 **URR v3 / co-owned survivor** として
すでに名前が付いていた。

URR の reduction materialization と、本当に独立した Direct relation は、同じ canonical
upper record に正しく同居しうる。これは claim-local coverage が必要になった理由そのものであり、
同居だけを根拠に Direct claim を covered 扱いしてはならない。

その後 DCP / MPC / CDM / DPN は、claim の継承、節への occurrence 帰属、
ReplayConjunction、DerivedUnary premise、root claim 到達性、cycle safety を順に閉じた。
それでも motivating test
`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`
（`crates/infer/src/lowering/tests/local_var_effect_boundary_edge_comparison.rs`）は、
`&buffer#36:0` family が inner generalized scheme から outer finalized scheme へ漏れる形で
red のままである。

### 1.2 今回確定した gap

MPC / DPN の現行 clause graph は、次の二つを正しく表現する。

- binary replay result は、lower premise と upper premise の AND である。
- 一つの premise record に独立な完結証明が複数あるなら、それらは OR である。

今回の record は、物理的には後者に見える。

1. upper record は、URR の reduction route による Reduced root `R` を持つ。
2. 同じ upper record は、別 producer `c` の Direct Original claim `D` も持つ。
3. `D` 自体は coverage 非 live なので、現行 root base case では projectable な leaf になる。
4. したがって record 全体の OR が true になり、それを premise に持つ
   ReplayConjunction の AND も再び true になりうる。

しかし今回の `D` は、本当に独立な原因から来た代替証明ではない。`D` の producer `c` には、
同じ Reduced root `R` を parent claim とする exact qualified-parent route `P` が別途登録されている。
つまり `c` は、`D` が同居しているその reduction と同じ因果鎖の下流にある。

現行 DPN の `eval(Constraint(c))` は、route `P` と root claim `D` を別々の OR-arm として読む。
route `P` が live coverage により false でも、root base case の `D` が無条件に true になるため、
同じ原因を root leaf が迂回して再び開いてしまう。欠けているのは新しい AND / OR 演算子ではなく、
**この Direct root leaf だけは route `P` によって因果的に qualified されており、
無条件の独立 leaf ではない**という区別である。

### 1.3 production trace の worked example

確定 trace の arena ID は実装条件には使わず、今回の proof shape を説明する worked example
としてだけ記録する。

- leak の surface record は `BoundRecordId(10439)`。
- その projectability は `ReplayConjunction` の AND chain を通り、最終的に
  `BoundRecordId(6064)` と `BoundRecordId(10152)` の upper premise 評価へ到達する。
- それらの survivor には live Reduced root と、
  `ConstraintRecordId(3643)` / `ConstraintRecordId(3662)` を producer とする
  Direct Original claim が同居する。
- 現行評価では Direct claim がそれぞれ無条件の true leaf になるため、
  Reduced 側が false でも upper premise の OR が true になり、AND chain を経て
  `10439` が projectable のまま残る。
- 確定した qualified-parent route を使うと、各 Direct leaf は同じ reduction root へ
  戻る route の評価へ置き換わる。root が live な間、その route は false であり、
  無条件 leaf による迂回は閉じる。

`10439` / `6064` / `10152` / `3643` / `3662` は一回の trace の説明用 ID である。
index、判定、test oracle のいずれも arena ID の値や大小関係に依存してはならない。

### 1.4 二つの独立 round が固定した責務境界

第一の round は constraint-level trace により、Direct claim の producer に exact route があり、
その route の canonical root と同居する live Reduced root が一致することを確認した。

第二の round は `row_effect.rs` 層での test 化を試み、そこで停止した。この層から見える
「同じ upper record に Direct claim と Reduced claim が同居する」という形だけでは、
誤りと正しい独立関係を区別できないためである。既存の green test
`unweighted_row_upper_independent_direct_tail_claim_replays` は、まさに同じ物理的同居を持ちながら、
Direct producer から Reduced root への exact qualified-parent route を持たない。この場合、
Direct claim は独立のままでなければならない。

したがって disambiguation は、row reduction 自身ではなく、
`claim_parents_by_constraint` と DPN proof graph の両方が見える MPC/DPN clause-graph 層
（`crates/infer/src/constraints/mod.rs` / `machine/bounds.rs`）に属する。

## 2. 決定

### D1: 「同じ reduction の因果的下流」を checkable predicate にする

Direct claim `D`、その producer constraint `c`、qualified-parent route `P`、
canonical coverage root `R`、`D` の current upper record `U` について、次を定義する。

```text
DirectOriginal(D) :=
    D.kind == Direct
    AND D.lineage == Original
    AND root_claim_by_producer_constraint[D.producer_constraint] == D

ExactParentRoute(c, P) :=
    P is an exact entry of claim_parents_by_constraint[c]
    -- P は variant、parent_claim、exact carrier を含む occurrence identity

ReducedRoot(P, R) :=
    R == find(P.parent_claim)
    AND root_claim(R).kind == Reduced(_)

CoLocated(D, R, U) :=
    U == D.current_record
    AND claims_by_upper_record[U] contains some claim Q
        such that find(Q) == R

Live(R) :=
    live_coverage_by_root[R] is non-empty

ActiveCausalQualification(D, P, R) :=
    DirectOriginal(D)
    AND ExactParentRoute(D.producer_constraint, P)
    AND ReducedRoot(P, R)
    AND CoLocated(D, R, D.current_record)
    AND Live(R)
```

本書で「`D` は同じ reduction の因果的下流にある」と言うのは、
`ActiveCausalQualification(D, P, R)` を満たすことだけを指す。

重要なのは、root equality や record co-location だけでは成立しない点である。
`P` は `claim_parents_by_constraint[c]` に実在する exact route でなければならず、
endpoint、source、row shape、derivation rule 名、arena ID から推測してはならない。
また、`R` の root claim kind が `Reduced(_)` であることを要求し、通常の Direct root 同士の
偶然の合流へ規則を広げない。

`P` は `ClaimQualifiedParent` の exact occurrence であり、三 variant を既存 DPN の意味で扱う。
本命の confirmed shape は `ReductionRouteConstraint` だが、Replay / Structural route も
同じ Reduced root を exact parent claim として持つなら、同じ checkable predicate を満たす。
variant ごとの評価規則は D3 で新設せず、DPN の既存規則をそのまま使う。

### D2: `causal_qualification_by_direct_claim` は安定候補と瞬間条件を分ける

意味上の index は次である。具体的な small collection 型は既存の index 規律へ合わせる。

```text
CausalDirectClaimQualification = {
    parent: ClaimQualifiedParent,       -- exact route P
    coverage_root: UpperReplayClaimId,  -- 登録時に canonical 化した Reduced root R
}

causal_qualification_by_direct_claim:
    UpperReplayClaimId /* Direct Original D */
      -> small set<CausalDirectClaimQualification>
```

この map が保持するのは `DirectOriginal(D) && ExactParentRoute(c, P) && ReducedRoot(P, R)`
という**安定な因果候補**である。`CoLocated` と `Live` は record movement と liveness transition
で変わるため、map の entry 有無へ焼き込まず、評価時に必ず再確認する。

この二層化により、index 自体は append-only / exact-dedup にできる一方、意味上の
qualification は可逆になる。

- `R` が live になり、同じ record に現れたら active になる。
- `R` の最後の live state が外れたら inactive になり、`D` は現行の独立 leaf へ戻る。
- `D` または `R` を root とする claim が materialization move で別 record へ移れば、
  co-location を失った側では inactive になる。
- 後で同じ record へ再び合流すれば、同じ安定候補が再び active になりうる。

#### D2.1 population path

候補は次の二つの対称な入口で登録する。

1. **late parent admission**: `admit_claim_qualified_parent(c, P)` の exact parent 登録後、
   `root_claim_by_producer_constraint[c]` から `D` を引く。`D` が Direct Original で、
   `find(P.parent_claim)` が Reduced root なら `(D, P, R)` を exact-dedup で追加する。
2. **Direct claim admission / idempotent return**: `original_upper_replay_claim` が Direct claim
   `D` を生成または既存返却するとき、`claim_parents_by_constraint[c]` のその producer-local
   entry だけを見て同じ候補を登録する。これは「parent が先、Direct が後」の順序を
   将来の admission 変更も含めて吸収するための対称 hook である。

全 constraint、全 claim、全 row derivation の scan は行わない。late parent path は O(1) の
producer mirror lookup、Direct admission path は producer-local parent 数にだけ比例する。
同じ `(D, P, R)` は何度通っても一 entry であり、duplicate / evidence / promotion / delta
materialization によって増殖してはならない。

#### D2.2 late admission と insertion order

confirmed regression は Direct claim の生成後に reduction route が追加される形である。
この順序では late parent hook が候補を追加し、その同じ mutation event で affected proof graph
を再評価可能にしなければならない。候補だけを追加して epoch / dependent publication を
行わない状態は許されない。

逆順は現行制御フローでは Direct fallback 自体が作られないことが多いが、意味論を制御フローの
偶然へ依存させない。二つの hook を同じ登録 helper に集約し、最終的な候補集合と評価結果が
順序に依存しないことを regression で固定する。

#### D2.3 materialization move

候補 entry は claim ID、producer identity、exact route、canonical root に属し、record identity
には属さない。したがって `move_upper_replay_claim` で entry を書き換えたり削除したりしない。
評価時の `D.current_record` と `claims_by_upper_record` が現在の co-location を決める。

ただし、**move による active / inactive の反転をどの write-site が publish するかは、
直前調査では完全に固定していない**。少なくとも次を URR-V3-0 で列挙しなければならない。

- Direct `D` 自身の `current_record` が移る経路。
- `R` を root とする Original / derived claim が `U` へ入る、または `U` から外れる経路。
- same-key materialization、replacement / prune / subsumption が
  `claims_by_upper_record` membership を変える全経路。
- TypeBounds 内の membership 更新と、ConstraintMachine 側の inclusion / epoch publish を
  一つの transaction として扱える境界。

これらを global scan、repair pass、flush、不動点なしで既存 event に同期して載せられない場合、
実装へ進まず本書のレビューへ戻る。

#### D2.4 liveness invalidation

意味論は固定する。`Live(R)` の empty / non-empty transition は、active qualification を介して
`D` を leaf / qualified route の間で反転させ、それに依存する record を再評価させる。

一方、既存 `dependent_records_by_premise` のどの edge を追加すれば、upper record 上の `D` から
下流 ReplayConjunction まで transition が完全に届くかは、まだ write-site 単位で固定していない。
候補は次のどちらか、または同値な event-local wiring に限る。

- qualification 登録時と ReplayConjunction 登録時の双方で、
  `RootCoverage(R) -> dependent lower record` の既存 reverse edge を追加する。
- upper record の claim-leaf 結果変化を record dependency へ publish する既存 hook に集約する。

どちらを採る場合も、edge は既存の `ProofPremise` / dependent index を再利用し、
新しい恒久判定 cache は作らない。late qualification、late clause registration、liveness 挿入、
liveness 除去、claim move の全順序で同じ結果になることを URR-V3-0 で pin する。
この wiring が決まる前に URR-V3-A を始めてはならない。

#### D2.5 lifecycle 上の未確定点

本書は qualification の意味論、候補の identity、評価結果を決めるが、次は reviewer と
URR-V3-0 が閉じるべき implementation decision point として意図的に残す。

1. `claims_by_upper_record` membership を変える全 production write-site の census。
2. move 前後の affected record snapshot を TypeBounds / ConstraintMachine のどちらで取るか。
3. `RootCoverage(R)` reverse edge の追記を qualification admission と clause admission の
   どちらへどう分担するか。
4. Reduced root が path compression で別 canonical root へ統合される経路が現存する場合、
   stored `R` の再 canonical 化だけで dependency edge の旧 key を安全に扱えるか。
5. active qualification が複数あるときの OR は本書 D3 で固定するが、その全 entry への
   invalidation edge が線形に維持できるか。

これらは意味論を曖昧にしてよいという意味ではない。D1 / D3 の結果を、既存の event-local・
cycle-safe・scan-free 規律で完全に publish できるかを着工前に確認する gate である。

### D3: SchemeProjectionEvaluator の Direct leaf だけを qualified route 評価へ置き換える

`SchemeProjectionEvaluator` に、coverage liveness をそのまま読む leaf と、
Direct qualification を考慮する leaf を分ける。

```text
eval_raw_root_coverage(K):
    root = find(K)
    return NOT live(root)

eval_claim_leaf(K):
    if claim(K) is not Direct Original:
        return eval_raw_root_coverage(K)

    D = K

    active = all (P, R) in causal_qualification_by_direct_claim[D]
             satisfying ActiveCausalQualification(D, P, find(R))

    if active is empty:
        return eval_raw_root_coverage(D)

    return ANY(active, |(P, _)| eval_qualified_parent_route(P))

eval_qualified_parent_route(P):
    ReplayConstraint { replay, .. }:
        eval(Record(replay.lower)) AND eval(Record(replay.upper))
    StructuralConstraint { derivation, .. }:
        eval(Constraint(derivation.parent))
    ReductionRouteConstraint { parent_claim, .. }:
        eval_raw_root_coverage(parent_claim)
```

`eval_claim_leaf` は、claim が proof graph 上で leaf として使われる既存箇所にだけ適用する。

- upper record の claim OR。
- `Standalone { support: Claimed(D) }` の qualifying 判定。
- DPN `eval(Constraint(c))` source (c) の root claim base case。

coverage payload の収集、URR replay planning、claim root の canonicalization 自体には使わない。
特に `claim_requires_generic_replay` はこの index を読まず、従来の claim-local coverage だけを
読む。これにより solver relation の生成と scheme proof の評価を混同しない。

複数の active qualification は OR である。各 `P` は producer constraint の一つの完結した
qualified-parent route であり、これは DPN D3 の
`claim_parents_by_constraint[c]` の複数 route を OR で読む規則と同じである。
route 内部の ReplayConjunction だけが AND になる。

既存の pass-local tri-color cycle guard はそのまま使う。qualified route が元の record / constraint
へ戻れば、`Visiting` re-entry はその circular route だけを false にし、他の active route や
record clause の OR は評価を続ける。claim node 用の恒久 state や fixpoint は追加しない。

metadata 欠落、root 不正、index と parent ledger の不一致は projectable 側へ fail-open する。
ただし confirmed path で fail-open が一件でも必要なら landing しないという MPC D4 / DPN D4 の
規律は維持する。

### D4: MPC / DPN の論理構造と claim payload は変更しない

本書が変更するのは「Direct root leaf が無条件 true か、exact route の評価へ委譲されるか」だけ。
次は変更しない。

1. **record clause の OR**: `RecordProofClause` の複数 clause は AnyOf のまま。
2. **ReplayConjunction の AND**: lower / upper premise は両方 true のときだけ true。
3. **DerivedUnary**: `ProofPremise` の三ソートと variant ごとの DPN 評価規則はそのまま。
4. **constraint source の OR**: linked lower record、各 qualified-parent route、root source の
   OR 構造はそのまま。root source の leaf 判定だけが D3 を通る。
5. **coverage / liveness**: claim の coverage root、`live_coverage_by_root`、path compression、
   empty / non-empty の意味を変更しない。
6. **payload**: `SchemeProjectableLowerReason::Qualified { uncovered_claims,
   independent_supports }` の収集内容を変更しない。
7. **URR solver behavior**: matching、incremental route、generic replay、state lifecycle、
   materialization、raw bounds を変更しない。

これは MPC D3 の OR / AND を緩める設計ではない。従来「Standalone leaf」と読んでいたもののうち、
D1 の exact predicate を満たす Direct leaf だけに、その leaf の根拠である既存 DPN route を
読ませる refinement である。

### D5: preserved contracts

次の結果は変えてはならない。

- `unweighted_row_upper_independent_direct_tail_claim_replays` は green のまま。
  Direct と Reduced が同居するだけでは qualification されず、exact route が必要である。
- `mpc_a_9_4_premise_alternative_keeps_result_projectable` は green のまま。
  fixture の independent alternative と、qualification を持たない Direct upper leaf は
  現行どおり record の完結した代替証明である。
- MPC §4 の pinned tests、`mpc_a_9_1`〜`mpc_a_9_8`、DPN §4 / §9、
  DPN root-claim / cycle-safety 追補の pinned tests はすべて期待値無変更で green を保つ。
- no-claim workload は index entry、追加 edge、評価分岐の対象にならない。
- `urr_v3_co_owned_survivor_direct_root_does_not_reopen_replay_premise` だけが、
  現行 red の `projection_count == 1` から、期待どおり `0` へ反転する。

## 3. 必須 invariant

1. **exact causality**: qualification は producer constraint の exact
   `ClaimQualifiedParent` entry からだけ作る。root equality / co-location だけで作らない。
2. **Reduced-root限定**: `find(P.parent_claim)` の root kind が `Reduced(_)` の場合だけ候補にする。
3. **瞬間条件の再確認**: live と co-location は評価時に current metadata から読む。
   index entry の古い record snapshot を正しさの根拠にしない。
4. **claim 層の不変**: `D.coverage_root` を `R` に付け替えない。`D` を covered claim に変換せず、
   claim 生成・継承・coalescing・payload 計算を変えない。
5. **論理構造の不変**: record OR、ReplayConjunction AND、constraint route OR を変えない。
6. **event-local / scan-free**: index 維持は producer-local metadata と既存 event で完結する。
   global scan、post-hoc derivation traversal、repair pass、fixpoint を入れない。
7. **exact dedup / insertion-order invariance**: `(D, P, R)` は exact carrier を含む identity で
   一回だけ記帳され、admission 順序で候補集合・評価結果・snapshot が変わらない。
8. **liveness symmetry**: `R` が live なら route 評価、最後の state が外れれば Direct leaf へ戻る。
   再度 live になれば同じ条件で route 評価へ戻る。
9. **movement symmetry**: co-location の成立 / 解消が、claim の移動順序に依存せず評価へ反映される。
10. **cycle safety**: DPN 追補の pass-local tri-color guard を共有し、SCC / fixpoint を追加しない。
11. **payload / replay independence**: qualification index は SchemeProjectionEvaluator の leaf 判定
    だけが読み、`Qualified` payload と `claim_requires_generic_replay` は読まない。
12. **線形性**: entry 数は `(Direct Original claim, exact qualified-parent route)` の実在組数に
    線形。reverse edge も qualification と dependent occurrence の event-local な積を超えて
    増殖せず、duplicate admission 回数に比例して増え続けない。

## 4. pinned test walkthrough

### 4.1 red anchor: `urr_v3_co_owned_survivor_direct_root_does_not_reopen_replay_premise`

場所は `crates/infer/src/constraints/tests/case_02.rs`。
test は `mpc_mixed_replay_fixture(CoveredPremiseFirst, true)` を使う。

初期状態:

- replay result の唯一の clause は `ReplayConjunction`。
- lower premise は live-covered claim を持つが、`Origin` による standalone alternative も持つため
  projectable。
- upper premise `direct_upper_record` は Direct claim を持ち、qualification が無いため
  projectable。
- AND は `true AND true` で、result の `projection_count` は 1。

test が追加する形:

1. Direct claim `D` の producer `c` を取得する。
2. parent に `Constraint(c)` を持つ exact `RowDerivationRule::UnweightedReduction` route `P` を
   intern し、canonical constraint `c` へ収束させる。
3. `register_reduction_route_claim_parent(c, P, coverage_root)` により、
   `ClaimQualifiedParent::ReductionRouteConstraint` を `claim_parents_by_constraint[c]` へ登録する。
4. `direct_upper_record` は uncovered Direct root `D` と live Reduced root `R` の両方を持つ。
5. live coverage を持つのは `R` だけで、`D` 自身は uncovered のまま。

D1 により `ActiveCausalQualification(D, P, R)` が成立する。
upper record の `D` leaf は無条件 true ではなく、DPN の ReductionRoute 規則
`eval_raw_root_coverage(P.parent_claim)` を読む。`R` は live なので false。
同居する Reduced claim 自身も false であり、upper premise 全体が false になる。
lower premise の standalone alternative は true のままだが、ReplayConjunction は
`true AND false` なので result は suppressed、`projection_count == 0` になる。

test は Direct claim を covered へ書き換えることを要求していない。要求しているのは、
同じ record、同じ live Reduced root、同じ producer への exact route が揃ったときだけ、
Direct leaf がその route を根拠として評価されることである。

### 4.2 green control: `mpc_a_9_4_premise_alternative_keeps_result_projectable`

同じ shared fixture の `with_premise_alternative = true` を使うが、Direct producer に
reduction route `P` を後付けしない。

- lower premise の independent `Origin` alternative は true。
- upper premise の Direct claim は候補 index を持たず、現行どおり true。
- ReplayConjunction は `true AND true`。
- result は projectable のまま。

本書は premise alternative の OR を弱めず、result-local standalone link を新設もしない。
したがって test 名と `(result_projected, direct_premise_projected,
raw_result_records, standalone_links) == (1, 1, 1, 0)` の期待は変わらない。

### 4.3 green control: `unweighted_row_upper_independent_direct_tail_claim_replays`

この test も一つの upper record に Reduced claim と Direct claim を同居させる。
しかし Direct producer は、Reduced root を parent claim とする exact qualified-parent route を
持たない。よって D1 の `ExactParentRoute` が false であり、candidate も active qualification も
存在しない。

さらに、この test が観測するのは URR の generic replay behavior である。
D3 / invariant 11 により `claim_requires_generic_replay` は qualification index を読まない。
Direct claim は従来どおり独立 relation として generic replay を一回要求し、
`LateMatchingReplayCounts { generic: 1, incremental_matched: 1 }` と residual family の到達は
変わらない。

### 4.4 production trace への適用

`BoundRecordId(6064)` / `BoundRecordId(10152)` の Direct Original claim について、
producer `ConstraintRecordId(3643)` / `ConstraintRecordId(3662)` に記録された exact route と
同居する live Reduced root が D1 を満たすなら、両 Direct leaf は route 評価へ委譲される。
その結果、`BoundRecordId(10439)` へ至る ReplayConjunction chain の AND は false のままとなり、
`&buffer#36:0` family を outer finalization へ再注入する route が閉じる。

これは implementation gate で motivating integration により確認する。arena ID を hard-code せず、
producer、exact route、canonical root、co-location、liveness を構造的に観測する。

## 5. 採らない案

### 5.1 `row_effect.rs` で Direct + Reduced の同居を抑止する

採らない。`row_effect.rs` は reduction state、materialization、claim co-location は見えるが、
その Direct producer が MPC/DPN clause graph 上でどの exact qualified-parent route を持つかを
完全には見られない。

先行の stopped attempt は、この情報不足を実際に確認した。
`unweighted_row_upper_independent_direct_tail_claim_replays` が固定する正しい独立 shape と、
今回の co-owned survivor は row-effect 層では同型に見える。そこで suppression すると、
正しい Direct `source <: tail` relation まで失う。

### 5.2 MPC D3 の record OR / ReplayConjunction AND を緩める

採らない。現行 D3 は、複数の完結証明を OR、binary replay の二 premise を AND と読む点で正しい。
`mpc_a_9_4_premise_alternative_keeps_result_projectable` は、premise に本物の独立 alternative が
あれば result が projectable に戻ることを pin している。

今回誤っているのは OR / AND ではなく、Direct root `D` を「完結した独立 leaf」と分類する
base case である。演算子を変えると、正しい premise alternative を失うか、covered premise を
再び OR で迂回する。

### 5.3 co-location または root equality だけで Direct を qualified にする

採らない。これは URR 文書 §6.7 が棄却した record-wide suppression / endpoint-wide inference の
再導入であり、`unweighted_row_upper_independent_direct_tail_claim_replays` を壊す。
producer 上の exact route `P` が必須である。

### 5.4 Direct claim の coverage root を Reduced root へ付け替える

採らない。`D.coverage_root = R` とすれば表面上は suppress できるが、claim-local coverage、
generic replay、liveness payload、portable provenance の意味をすべて変える。
本当に独立な Direct claim まで covered 化する危険があり、URR v3/v6 と MPC D1 の invariant に
反する。本書は claim 自体を変更せず、proof leaf の因果的根拠だけを精密化する。

### 5.5 producer constraint 全体を無条件に route-only にする

採らない。producer が一つでも parent route を持つというだけで root source を消すと、
同居する Reduced root との一致がない場合や、別 root に属する独立 route まで巻き込む。
D1 は exact route の root、Reduced kind、live、current co-location の四点を要求し、
今回の shape に必要な範囲だけを狭く変更する。

### 5.6 評価時に row derivation / provenance graph を逆走査する

採らない。因果 route は admission 時に `claim_parents_by_constraint` へすでに記録されている。
評価時の graph 再構築、全 claim scan、全 reduction state scanは、DPN / CDM の event-local・
scan-free 規律に反し、hot path へ重複計算を置く。

### 5.7 trace ID、family 名、fixture 名の special case

採らない。`10439`、`6064`、`10152`、`3643`、`3662`、`&buffer#36:0` は説明用であり、
実装条件ではない。条件は D1 の構造化された claim / producer / exact route / root / liveness
だけで表す。

## 6. blast radius と性能条件

### 6.1 触る範囲

- `crates/infer/src/constraints/mod.rs`
  - `TypeBounds` の lazy index 一つ。
  - `SchemeProjectionEvaluator` の Direct claim leaf helper。
  - qualification に必要な既存 root / claim / record membership の keyed lookup。
- `crates/infer/src/constraints/machine/bounds.rs`
  - exact parent admission と Direct admission の対称な candidate 登録。
  - late qualification / clause admission / liveness / materialization move に必要な
    reverse dependency と inclusion publication。
- `crates/infer/src/constraints/tests/case_02.rs`
  - 既存 red anchor の green 化。
  - index 登録、順序、liveness、move、複数 route、unrelated control の regression。

### 6.2 触らない範囲

- `row_effect.rs` の reduction matching、state、route generation、materialization semantics。
- claim の生成・coverage root・lineage・coalescing・liveness payload。
- `RecordProofClause` / `ProofPremise` の enum shape。
- ReplayConjunction / DerivedUnary の clause 登録と論理演算。
- raw bounds、generalization、compaction、alias expansion、portable provenance の表現。
- local-var lowering、callback lifecycle、finalize、co-occurrence、極性消去、残差脱糖。
- 既存 test の期待値。

### 6.3 性能条件

- no-claim workload は map allocationも追加 lookup も行わない。
- Direct claim が無い record は新しい分岐を実質的に通らない。
- candidate 登録は producer-local parent 数に線形、評価はその Direct claim の candidate 数と
  current upper record の claim 数に線形であり、global collection に比例しない。
- qualification candidate と reverse edge は exact-dedup し、duplicate / evidence / promotion
  回数に比例して増殖しない。
- evaluation pass は DPN 追補どおり reachable proof graph の O(V + E) と pass-local memo を保つ。
- current record の co-location 確認が同じ record 内で支配的になる実測が出る場合は、
  semantics を変える cache で隠さず、既存 record-local index の拡張を別 gate で検討する。

## 7. 実装前の必須検証: URR-V3-0

production behavior を変える前に、test/debug instrumentation だけで次を固定する。

1. Direct Original claim と exact qualified-parent route の admission 順序を列挙し、
   D2.1 の二 hook で candidate 集合が一致すること。
2. `claims_by_upper_record` membership を変える全 write-site と、各 site で old/new active
   qualification を比較して dependent publication できる境界。
3. qualification admission が upper premise の結果を変えたとき、既存
   `dependent_records_by_premise` を通じて ReplayConjunction result まで invalidation が届くこと。
4. `Live(R)` の insert / remove と、Direct / Reduced-rooted claim の move を全順序で組み合わせ、
   active / inactive の結果が一致すること。
5. 複数 active route の OR、circular route の tri-color cut、metadata 欠落の fail-open が
   DPN の既存 evaluator 規則だけで表現できること。
6. production motivating trace の `3643` / `3662` 相当 producer が D1 を満たし、
   unrelated Direct + Reduced co-location は D1 を満たさないこと。

URR-V3-0 の観測に production semantic change を入れない。2〜4 のいずれかが event-local な
既存 hook で閉じず、新しい global phase、scan、fixpoint、恒久判定 cache を要するなら、
URR-V3-A へ進まず設計レビューへ戻る。

## 8. regression test specs

### 8.1 co-owned survivor suppression（既存 red anchor）

`urr_v3_co_owned_survivor_direct_root_does_not_reopen_replay_premise` を期待値無変更で使う。
index に `(D, P, R)` が一件あり、active predicate が true、Direct leaf の route 評価が false、
result の `projection_count == 0` を観測する。

### 8.2 unrelated Direct survivor stays independent

`unweighted_row_upper_independent_direct_tail_claim_replays` を期待値無変更で使う。
必要なら同じ fixture の index census を追加し、Direct claim に candidate が無いことを固定する。

### 8.3 MPC premise alternative stays projectable

`mpc_a_9_4_premise_alternative_keeps_result_projectable` を期待値無変更で使う。
qualification route を追加しない shared fixture では result が一回 project されることを保つ。

### 8.4 late-parent / insertion-order invariance

Direct admission → parent admission と、意味的に同じ最終 graph を作る逆順 / idempotent return を
構成し、candidate set、active set、clause snapshot、projection count が一致すること。

### 8.5 liveness symmetry

active qualification の `R` について最後の live state を外すと Direct leaf が独立へ戻り、
dependent result が projectable になること。再挿入で再び suppressed になること。
cache on / off で結果が一致し、必要な epoch が前進すること。

### 8.6 materialization movement symmetry

Direct claim または `R`-rooted claim を別 record へ移して co-location を解消すると qualification が
inactive になり、再合流で active になること。移動順序を反転して同じ snapshot になること。

### 8.7 multiple routes and cycle safety

同じ `D` に複数の active route を登録し、一つが false、別の完結 route が true なら OR により
Direct leaf が true になること。circular route だけなら tri-color guard で false になり、
他の route / clause の評価は継続すること。

### 8.8 motivating integration

`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization` を期待値無変更で使う。
`&buffer#36:0` family が outer scheme から消えることに加え、Direct qualification が
`3643` / `3662` 相当の exact route と Reduced root の一致によって発火したことを構造的に観測する。

## 9. 実装スライス

各 slice は前 slice の gate を閉じてから進める。既存 red regression は保持し、
実装出力に合わせて期待値を書き換えない。

### URR-V3-0: lifecycle / invalidation の read-only 固定

- 変更: §7 の test/debug observation と census だけ。production 判定は不変。
- gate: admission、move、co-location、liveness の全 write-site と publish 境界が列挙され、
  event-local wiring で D1 / D3 を実現できる。未確定点が一つでも残れば**ここで停止**する。

### URR-V3-A: candidate index と登録 wiring（判定は不変）

- 変更: `causal_qualification_by_direct_claim`、candidate identity / dedup、
  late-parent と Direct-admission の対称 hook、debug completeness census。
  URR-V3-0 で決めた reverse dependency edge を登録するが、Evaluator はまだ index を読まない。
- gate: 全既存 test green。既存 red anchor は `projection_count == 1` のまま red。
  §8.2〜8.4 の登録側観測 green。candidate / edge 数が線形。no-claim passthrough 不変。
- stop: index 登録だけで production projection / replay behavior が変わる、順序で candidate 集合が
  変わる、または confirmed path の candidate が欠けるなら slice ごと戻す。

### URR-V3-B: leaf 評価切替と invalidation

- 変更: D3 の `eval_claim_leaf` と route 委譲、liveness / qualification / movement mutation の
  inclusion publication。判定切替と invalidation は一体で landing する。
- gate: §8.1 が green へ反転。§8.2〜8.7 と全既存 pinned tests が期待値無変更で green。
  cache on / off 同一。cycle / fail-open census に confirmed-path hit が無い。
- stop: red anchor を suppress するために record OR、ReplayConjunction AND、claim coverage、
  payload、generic replay のいずれかを変える必要があれば戻す。

### URR-V3-C: motivating integration / closeout

- 変更: §8.8、関連 characterization、`cargo test -p infer`、full contract suite、
  consumer suite、性能 census。
- gate: motivating test が期待値無変更で green。既存 scheme / poly / check hash の変化が
  qualification 発火 record まで説明可能で、本 scope 外の shift が無い。性能条件を満たす。
- stop: motivating test がまだ red、または unrelated Direct relation が一件でも suppress されるなら、
  後段 cleanup を加えず D1 / lifecycle wiring のレビューへ戻る。

## 10. 変更しないもの

- MPC D3 の OR / AND、DPN の `ProofPremise` と route 評価、DPN 追補の cycle guard。
- Direct / Reduced claim の identity、coverage root、lineage、liveness payload。
- URR の source-local reduction state と generic / incremental replay ownership。
- raw record の保持、subsumption、replacement / prune の意味。
- scheme projection の `Qualified` payload、consumer contract、portable provenance。
- local-var lowering、generalize / instantiate、finalize、specialize。
- Simple-sub の共起分析、極性消去、残差表現。
- 既存 test の名前と期待値。
- arena ID、path、module、function、fixture、family 名を判定条件に使わない。

## 11. stop / rollback conditions

### 11.1 stop conditions

次のいずれかが判明した時点で実装を止め、本書のレビューへ戻る。

1. `urr_v3_co_owned_survivor_direct_root_does_not_reopen_replay_premise` の shape が D1 を
   満たさない、または motivating trace の `3643` / `3662` 相当 route と一致しない。
2. `unweighted_row_upper_independent_direct_tail_claim_replays` または `mpc_a_9_4` を
   期待値無変更で green に保てない。
3. qualification に exact `ClaimQualifiedParent` 以外の endpoint / source / rule-name heuristic が要る。
4. Direct claim の coverage root 変更、claim の covered 化、payload 書換えが要る。
5. record OR、ReplayConjunction AND、constraint route OR のいずれかを変更する必要がある。
6. late parent admission、Direct admission、claim move、liveness transition のいずれかを
   event-local hook で捕捉できない。
7. invalidation に全 record / claim / reduction scan、repair pass、flush、SCC、fixpoint、
   恒久判定 cache が要る。
8. qualification の active / inactive または評価結果が insertion / movement 順序に依存する。
9. path compression 後の canonical root と stored `R` の整合を O(1) keyed lookup で保てない。
10. candidate / reverse edge 数が exact route occurrence に対して超線形になる。
11. no-claim workload または qualification を持たない Direct workload に allocation /
    支配的な lookup regression が出る。
12. confirmed path を通すために metadata 欠落の fail-open が必要になる。
13. cycle guard の結果が traversal 順序に依存する、または既存 DPN pinned cycle semantics が変わる。
14. claim qualification が `claim_requires_generic_replay`、raw solver replay、row reduction lifecycleへ
    漏れ出す。
15. motivating integration だけを通す local-var / family / fixture special case が必要になる。
16. full suite に、qualification 発火 record から説明できない scheme / hash / diagnostic shift が出る。

### 11.2 rollback units

- URR-V3-0 の正しい observation と red regression は保持する。
- URR-V3-A が挙動中立で成立しなければ、部分的な candidate index / hook / edge を残さず
  slice ごと戻す。
- URR-V3-B の leaf 判定切替と invalidation は分割して landing しない。片方だけでは stale cache
  または publish 漏れを作るため、gate を閉じられなければ両方戻す。
- URR-V3-C で motivating test だけ green でも unexplained shift があれば、期待値を更新せず、
  最初に差分が出た slice へ戻る。
- rollback のために Direct claim の coverage 書換え、record-wide suppression、row-effect 層の
  workaround、finalizer cleanup を導入しない。

## 12. 先行文書との関係

### 12.1 URR v2〜v6

URR 文書 §1.4 が区別した「同じ relation の別 proof」と「真に独立した relation」を維持する。
本書は co-location だけで両者を分類せず、producer の exact route を追加の証拠として使う。
URR の claim-local coverage と generic replay は変更しない。

### 12.2 MPC / CDM

MPC の clause occurrence 帰属、record AnyOf、ReplayConjunction AND、payload 不変を維持する。
CDM の admission-time exact parent ledger を因果情報の正本として読み、新しい bulk reconstruction を
作らない。

### 12.3 DPN / DPN root-claim・cycle-safety 追補

DPN の `ProofPremise`、route 評価、constraint source OR を維持する。
DPN 追補の `root_claim_by_producer_constraint` を Direct claim `D` の producer lookup に使い、
tri-color guard を qualified route の cycle safety にも使う。

置き換えるのは、DPN root base case の次の一文だけである。

```text
旧: 通常の Direct root（coverage 非 live）は無条件に projectable。
新: 通常の Direct rootは、D1 の active causal qualification が無い場合だけ
    無条件に projectable。active な場合は exact route P の DPN 評価結果に従う。
```

この差分は本書のレビュー対象であり、承認前に production へ実装しない。

## 13. 波及する文書（本設計の landing 後に更新。本書では編集しない）

- `notes/architecture/claim-propagation-architecture.md`
  - Direct root leaf の qualification predicate と index lifecycle。
  - liveness / movement invalidation の着地した exact hook。
- `notes/bugs/2026-07-28-local-var-effect-residual-transport-gap.md`
  - URR v3 / co-owned survivor unresolved item から本書と各 slice への時系列 pointer。
- 先行する承認済み design documents は編集しない。本書を後継 pointer として扱う。

---

状態: **ユーザ承認済み**

著者: Claude (Sonnet 5)（Codex `gpt-5.6-sol` xhigh の調査・設計提案を統合。Fable 5はサブスクリプション利用制限のため一時利用不可のため、正本文書の慣例からの例外として明記）
