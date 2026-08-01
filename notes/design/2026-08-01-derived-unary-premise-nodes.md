# DerivedUnary premise の証明ノード化（DPN）

日付: 2026-08-01

状態: **ユーザ承認済み（2026-08-01）**

本書は `notes/design/2026-07-31-mixed-proof-conjunctive-ownership.md`（以下 MPC 文書）の
stop condition §12.1-7

> DerivedUnary の premise 解決に global scan が要る、または解決不能率が
> confirmed path 上で非ゼロになる。

が MPC-B 実装試行（2026-08-01）で発火したことを受けた追補設計である。
MPC 文書の節評価意味論（D1〜D6 の骨格、pinned tests、slice 構成）を改廃するものではなく、
**DerivedUnary 節の premise の表現・解決時点・評価規則**だけを置き換える。
ReplayConjunction 節は実装試行で正しく動作することが確認されており、本書はそれを追認する。

調査基準は `main` の `cc53f749`（CDM-A〜E 着地後、MPC-A 着地後）。
根因の正本は 2026-08-01 の Codex session 2 本
（round 1: MPC-B 実装試行——ReplayConjunction 節の実装成功と、structural /
reduction-route admission における premise 解決不能の確定、正しい rollback、
round 2: read-only の全 admission 経路特性づけ——6 経路それぞれの premise 解決可能性と、
gap 点で利用可能な安定 metadata の確定）である。
working tree に round 1 のコード変更は残っていない。

## 0. 本書が下す決定の要約

1. **DerivedUnary の premise を、単一の `BoundRecordId` から多ソートの証明ノード
   （§2-D2 の `ProofPremise`）へ一般化する**。structural 継承の premise は
   carrier が保持する親 `ConstraintRecordId` そのもの、reduction-route 継承の premise は
   link 時に手元にある parent claim の canonical coverage root とする。
2. **premise の「解決」を登録時から評価時へ移す**。登録は carrier が既に持つ ID を
   写すだけで、lookup を一切行わない。MPC D2-4 が指示した登録時の
   `scheme_projection_lower_record_by_constraint` 解決と、解決不能時の
   Standalone fallback は退役する（この fallback が §12.1-7 の発火点であり、
   誤分類そのものだった）。
3. **Constraint ノードの評価規則を新設する**（§2-D3）。評価は admission 時に
   記録済みの `claim_parents_by_constraint` route 群・linked lower record・
   root claim の coverage liveness の OR であり、すべて O(1) keyed lookup で読む。
   global scan・post-hoc graph 再構築は行わない。
4. **root constraint の base case を coverage liveness に統一する**。
   通常 root（Direct root claim、coverage 非 live）は projectable、
   URR root（coverage live）は非投影となり、liveness 対称性（MPC invariant 8）が
   構造連鎖を通して自動的に成立する。
5. **MPC D5 の逆依存 index を premise ノード全ソートへ拡張し、
   edge は登録時の bounded chain walk で張る**（§2-D5）。不動点反復は導入しない。
6. 実装着手前に、**DPN-0（read-only 検証）を必須の前提**とする（§8）。

## 1. 問題

### 1.1 stop condition の発火（確定事実）

MPC-B 実装試行は、MPC §2-D2 のとおり ReplayConjunction 節を実装し、
これは正しく動作した——`BinaryReplayDerivation` carrier が exact な
lower / upper `BoundRecordId` を自身で保持するため、premise 解決に gap がない。

blocking case は MPC-A が §9.8 spec のために導入済みの
`row_structural_claim_fixture`（`crates/infer/src/constraints/tests/case_02.rs:3888`、
使用 test は `mpc_a_9_8_duplicate_evidence_and_promotion_preserve_clause_snapshot`
`:3178` と `dcp_a_8_8_duplicate_evidence_and_promotion_keep_root_and_exact_carrier`
`:2710`）で確定した。この fixture は production 代表的な構造 admission を持つ。

- structural child の `StructuralDerivation.parent` は `ConstraintRecordId(1)`
  （binary replay の result、`row <: Neg::Row([...], tail)`）。
- `scheme_projection_lower_record_by_constraint` に `ConstraintRecordId(1)` の
  entry は**無い**。さらに遡った究極の producer `ConstraintRecordId(0)`
  （`Var(0) <: Neg::Row`）にも**無い**。
- MPC D2-4 の指示ではこの map から premise `BoundRecordId` を解決するはずだが、
  使える entry が存在しない。
- fallback の Standalone 化は不可。`mpc_a_9_8` の pinned snapshot は
  「covered unary clause 1 個・`projected_count: 0`」を要求しており、
  Standalone 化は record を projectable にして snapshot を壊す。
  そして意味的にも、構造的に派生した occurrence を独立証明と誤分類することは、
  MPC が存在する理由（OR の枝と AND の前提の区別）への違反そのものである。

これは合成ケースではなく、§12.1-7 の文言どおり「解決不能率が confirmed path 上で
非ゼロ」になった実例である。試行は正しく rollback された。

### 1.2 根因: map の母集団は「自ら ordinary lower admission をした constraint」だけ

`scheme_projection_lower_record_by_constraint` の write site は
`TypeBounds::add_lower`（`crates/infer/src/constraints/mod.rs:933`）の一箇所であり、
bound derivation が `BoundDerivation::Constraint(producer)` のときにだけ書かれる。
つまり **entry を持つのは、自分自身が ordinary lower bound を admit した constraint に
限られる**。upper bound しか作らない constraint、分解だけを行う constraint は
恒久的に entry を持たない。これは処理順序の一時的な穴ではない——blocking fixture の
両 constraint は child の構造 admission より前に完全に処理済みだった。

なお `lower_record_for_constraint`（`machine/bounds.rs:864`）には map miss 時の
canonical-key fallback が既にあるが、これは constraint の upper が `Neg::Var` の
場合にしか働かない。blocking case は両 constraint とも upper が `Neg::Row` であり、
この fallback でも救えない。

### 1.3 全 admission 経路の特性（round 2 で確定した事実）

- **structural: 系統的に発生**。production の構造親（normalization、union /
  intersection、function、tuple、record、variant、row 分解——
  `StructuralDerivationRule` の全 surface、`mod.rs:2586-2633`）は典型的に
  upper bound の作成か分解だけを行い、自身の ordinary lower admission を持たない。
  row・function-return-effect・tuple の 3 つの異なる production 形状で確認済み。
- **reduction-route: 系統的、かつ無条件**。URR root の producer は定義により常に
  `Var <: Row`（upper-only）であり、linked lower record を持つことが**原理的に無い**。
  edge case ではなく、全 URR root の定義的形状である。
- **replay: 直接は非影響**。`BinaryReplayDerivation` が exact record を自身で持つ。
  ただし replay の result が、後続の構造 admission の「entry 無し親」になる——
  blocking fixture の `ConstraintRecordId(1)` がまさにこの機構である。
- **one-sided lower / evidence-only / promotion: gap を生まないが継承する**。
  record identity は transition を跨いで安定だが、link される proof が structural /
  reduction-route 由来なら上流の同じ gap が伝播する。

つまり map miss は DerivedUnary surface の例外ではなく、structural と
reduction-route に関しては**通常の場合**である。既存の green tests の多くが
これを露呈しなかったのは、fixture が親を map 済みの `Var <: Var` 形状で
人工的に配線していたためであり、実 topology を使う `row_structural_claim_fixture`
だけが捕捉した。

### 1.4 gap 点で利用可能な安定 metadata（確定事実）

- 親と究極の root producer の安定な `ConstraintRecordId`
  （`constraint_records` arena は session 内 append-only）。
- 親自身の `claim_parents_by_constraint` entry（`mod.rs:837`）。
  これは linked lower record の有無と独立に存在し、各 entry
  （`ClaimQualifiedParent`、`mod.rs:516-530`）は **`parent_claim` と
  exact carrier の両方を直接保持する**。
- structural carrier（`StructuralDerivation { parent, rule }`、`mod.rs:2636`）は
  親 ID を field として持つ——解決に lookup 自体が要らない。
- reduction-route link の occurrence では
  `ClaimQualifiedParent::ReductionRouteConstraint { parent_claim, derivation }` が
  手元にあり、parent claim から canonical coverage root へ既存の
  path-compressed lookup で届く。`RowDerivationId` の親連鎖
  （Constraint / Bound / nested RowDerivation）を premise のために歩く必要はない。
- URR root は `claim_parents_by_constraint` entry を持たない（root だから）が、
  original claim・coverage root・original upper `BoundRecordId` の
  安定な root metadata を持つ。通常 root も no-parent fallback
  （`machine/bounds.rs:804-812`）で Direct root claim を持つ。

### 1.5 構造的な結論

現行の「projectable / included」概念は `BoundRecordId` の上にしか定義されていない。
一方 §1.3 のとおり、DerivedUnary の premise の実体は record を持たない
constraint であることが通常である。したがって解くべきは「record を探す方法」ではなく、
**「record を持たない premise の証明状態を、record と同じ規則で評価できる形」**である。
MPC D3 は評価を既に record 上の memo 付き DAG 走査として定義した。本書はその
ノード空間を多ソート化する——それだけである。

## 2. 決定

### D1: MPC の意味論は不変。変えるのは DerivedUnary の premise だけ

次はすべて MPC 文書のとおり維持し、本書は一切変更しない。

- claim 層全体（MPC D1 / CDM D1。生成・継承・coalescing・coverage・liveness・
  `Qualified` payload 計算）。
- 節の occurrence 帰属規則（MPC D2-1）、Standalone 節の定義（D2-2）、
  **ReplayConjunction 節の定義と実装（D2-3）——実装試行で検証済みのまま追認する**。
- record ノードの評価規則（MPC D3 の `eval(record)`、cycle 規則、
  memo 付き DAG 一回走査、不動点禁止）。
- fail-open の向き（MPC D4）と「confirmed path で fail-open が要る実装は
  landing しない」規律（D4-4）。
- MPC §4 の pinned 5 tests、§9 の regression specs、§10 の slice 構成と gate。

置き換えるのは MPC D2 のうち次の 2 点に限る。

- D2 の節定義中 `DerivedUnary { premise: BoundRecordId }` の premise 型（→ 本書 D2）。
- D2-4 の「premise は `scheme_projection_lower_record_by_constraint` から解決し、
  解決できなければ Standalone として扱う」（→ 本書 D2 / D3 / D4。
  この規則は §1.1 のとおり構造的に成立しない）。

### D2: premise は多ソートの証明ノード。登録は lookup ゼロ

```text
ProofPremise =
    Record(BoundRecordId)            -- 従来どおり。ReplayConjunction の両 premise、
                                     -- および record が直接ある場合の unary premise
  | Constraint(ConstraintRecordId)   -- structural 継承の premise:
                                     -- carrier の StructuralDerivation.parent そのもの
  | RootCoverage(canonical root)     -- reduction-route 継承の premise:
                                     -- link 時の parent_claim を登録時に
                                     -- path compression で canonical root へ正規化した値
```

登録規則:

1. **structural link**: 節は
   `DerivedUnary { carrier: StructuralDerivation, premise: Constraint(carrier.parent) }`。
   carrier が親 ID を field で持つため、登録は写経であり lookup ゼロ。
2. **reduction-route link**: 節は
   `DerivedUnary { carrier: RowDerivationId, premise: RootCoverage(root) }`。
   root は occurrence で手元にある
   `ClaimQualifiedParent::ReductionRouteConstraint.parent_claim` を、
   claim 層の既存 path-compressed lookup で canonical root へ正規化した値。
   これも O(1) の event-local 処理である。
3. **replay link**: MPC D2-3 のまま。premise は carrier の exact record 2 つ。
4. 節の識別・dedup は従来どおり (exact carrier, premise) による。
   挿入順で節集合が変わってはならない（MPC D2-6 のまま）。

登録時に「解決」する対象が存在しないため、解決不能という状態が定義から消える。
§12.1-7 の「解決不能率」は、評価側の概念（D3 末尾の評価可能性）に置き換わる。

### D3: Constraint ノードの評価規則

投影時評価（MPC D3 の `eval`）のノード空間を `ProofPremise` の 3 ソートへ広げる。

```text
eval(Record(r)):        MPC D3 のまま（claims / supports / clauses の評価）
eval(RootCoverage(k)):  NOT live(find(k))
                        -- find は claim 層の既存 path-compressed root lookup、
                        -- live は live_coverage_by_root。covered な素材は
                        -- live な間は非投影、liveness が外れれば投影可能
eval(Constraint(c)):    次の証拠源の OR。存在する源だけを評価する
    (a) linked lower record: lower_record_for_constraint(c) が Some(r) なら eval(Record(r))
        -- 既存の map + canonical-key fallback（machine/bounds.rs:864）をそのまま使う
    (b) 各 qualified-parent route（claim_parents_by_constraint[c] の各 entry）:
        ReplayConstraint { replay, .. }
            -> eval(Record(replay.lower)) AND eval(Record(replay.upper))
            -- ReplayConjunction と同一の規則を constraint ノード上で適用するだけ
        StructuralConstraint { derivation, .. }
            -> eval(Constraint(derivation.parent))
        ReductionRouteConstraint { parent_claim, .. }
            -> eval(RootCoverage(find(parent_claim)))
    (c) root claim: c 自身の root claim k が引けるなら eval(RootCoverage(find(k)))
        -- 通常 root の Direct claim は live coverage を持たない → true（projectable）
        -- URR root は live な間 false → 非投影。liveness 除去で true へ戻る
    (a)(b)(c) のいずれも存在しない -> projectable（fail-open、D4）
```

評価の性質:

- route が複数あるのは、canonical な constraint record に複数の導出 occurrence が
  合流した場合であり、各 route は constraint の**完結した導出**である。
  よって OR が正しい——record ノードの AnyOf(clauses) と同じ構造である。
- (a) と (b) の重複は無害である。linked record がある場合、その record の節集合は
  同じ導出の link event から登録されており、OR は単調で、真になる腕が一つでも
  あれば「本物の projectable な導出がある」ことを意味する。偽陽性は生まない。
- Constraint ソートの再帰は well-founded である。`constraint_records` arena は
  append-only で、`StructuralDerivation.parent` は常に child より前に存在するため、
  constraint だけを通る cycle は構成できない。cycle は Record ノード経由でのみ
  起こり得て、そこには MPC D3 の cycle 規則（その節は空虚な証明として非投影）が
  そのまま適用される。
- すべての lookup（map・canonical key・`claim_parents_by_constraint`・root claim・
  liveness）は admission 時に記録済みの keyed metadata への O(1) 参照であり、
  MPC D3 の memo 付き DAG 一回走査の中で行われる。**global scan・derivation graph の
  post-hoc 再構築・不動点反復は導入しない**。禁止されたのは「premise を見つけるために
  全体を探すこと」であって、「event 時に記録した exact metadata を評価時に
  読むこと」は MPC D3 が最初から行っている操作である。

**評価可能性**: すべての premise ノードは評価可能でなければならない。
Record と RootCoverage は常に評価可能。Constraint は (a)(b)(c) の少なくとも一つを
持つべきであり、三つとも持たない constraint が confirmed path 上に現れる比率は
ゼロでなければならない（DPN-0 が実測確認、非ゼロなら stop）。これが §12.1-7 の
「解決不能率ゼロ」の後継の定義である。

### D4: Standalone fallback の退役と fail-open の再配置

MPC D2-4 の「解決できなければ Standalone」は退役する。structural / reduction-route の
link で premise が作れないという状態は D2 により存在しなくなり、
「作れないから独立証明扱いにする」という誤分類の腕そのものが消える。

fail-open（projectable 側へ倒す）は次に限定して残る。いずれも MPC D4 の
方向（抑制は健全性側の失敗なので、異常系は情報を失わない側へ）を継承する。

1. 節へ帰属しない link は現行 flat 規則で評価に参加する（MPC D4-2 のまま）。
2. 評価不能な Constraint ノード（(a)(b)(c) 皆無）は projectable と評価する。
   ただし confirmed path 上でこの腕が必要になった時点で landing しない（D4-4 継承）。
3. metadata 破損・参照不能は projectable 側へ倒す（MPC D4-3 のまま）。

### D5: 逆依存 index の premise ノード拡張と、登録時 bounded chain walk

MPC D5 の `dependent_records_by_premise` の key を `BoundRecordId` から
`ProofPremise` へ広げる。

```text
dependent_records_by_premise: ProofPremise -> small set<BoundRecordId>
```

Constraint / RootCoverage ノードは**状態を持たない評価中間ノード**であり、
record のように自身の inclusion 変化を publish しない。したがって伝播が
それらを通り抜けられるよう、edge は登録時に premise 連鎖を有界に展開して張る。

**登録時 chain walk**（clause を record R へ登録した時点で実行）:

- premise が `Record(r)` → edge `Record(r) -> R` を張り終端。
  record 間の伝播は record 自身の inclusion 変化が担うため、record を跨いで
  さらに展開しない（従来の D5 と同じ一段）。
- premise が `RootCoverage(k)` → edge `RootCoverage(k) -> R` を張り終端。
- premise が `Constraint(c)` → edge `Constraint(c) -> R` を張った上で c を展開する:
  (a) linked record が引ければ `Record(r) -> R` を張り、その枝は終端。
  (b) 各 route について、Replay route は exact record 2 つへ `Record -> R`、
  ReductionRoute route は `RootCoverage -> R`、Structural route は親 constraint へ
  再帰（visited set 付き）。
  (c) root claim があれば `RootCoverage -> R`。

walk は手元の exact carrier / 記録済み route を辿る有界処理であり、深さは
「record を跨がない構造連鎖の長さ」に bounded である（分布は DPN-0 で実測）。
lineage の heuristic 再構築ではない。

**再評価の hook**（すべて既存の単一 write site / 既存 transition に載る）:

1. record の inclusion 変化 → 既存 MPC D5 の伝播。`Record` edge の dependent を再評価。
2. liveness transition → 既存の root 逆引き経路に加え、`RootCoverage(root)` edge の
   dependent を直接再評価する（record を経由しない依存のため）。
3. `add_lower` の map 書き込み（`mod.rs:933`、単一 site）→ 対象 constraint の
   `Constraint(c)` edge の dependent を再評価する（評価が (a) の record 委譲を
   新たに得るため）。
4. `push_claim_qualified_parent`（`machine/bounds.rs:1416` / `:1499` の呼び出し面、
   CDM の差分 hook と同一物）→ 対象 constraint の `Constraint(c)` edge の
   dependent について、新 route の edge を chain walk で追記し再評価する。

edge は append-only で、過剰近似は余分な再評価を生むだけである（安全側）。
不動点反復ではなく、有限 DAG 上の event 駆動の bounded 伝播である。

### D6: 安定 ID 規律の精密化——canonical root は参照してよい

MPC D2-5 は「節は claim ID を参照しない」と定めた。この禁止の対象は、
per-(record, root) の「新しい claim ID が勝つ」coalescing（`mod.rs:1256-1266`）で
**差し替わる derived claim ID** である。`RootCoverage` が保持するのはその
coalescing の**キー側**、すなわち canonical coverage root であり、
`live_coverage_by_root` 自身が key に使っている安定クラスである。

- 登録時に parent claim を canonical root へ正規化してから premise に格納する。
- 評価時にも `find` を通してから liveness を読む。後発の path compression で
  root が更に統合されても、`find` が冪等に吸収する——claim 層が projection 時に
  行っている lookup（MPC D1 が保護する機構）と同一である。
- derived claim ID を節に格納しない規律自体は不変である。

## 3. 必須 invariant

1. **claim 層の不変**（MPC invariant 1 / CDM D1 の継承）: claim の生成・継承・
   coverage・liveness・`Qualified` payload 計算は byte 単位で不変。
2. **exact carrier と安定 ID のみ**: 節と edge の識別は exact carrier・
   `BoundRecordId`・`ConstraintRecordId`・canonical root による。lineage kind・
   endpoint 形状・path 文字列・derived claim ID から推測しない。
3. **登録の event-local 性**: 節登録と edge 登録は link event の手元の値と
   O(1) keyed lookup、および有界 chain walk だけで完結する。global scan 禁止。
4. **一回走査**: 評価は memo 付き DAG walk のまま（ノード空間が広がるだけ）。
   Constraint ソートの再帰は arena 順序で well-founded。不動点反復禁止。
5. **評価可能性**: confirmed path 上のすべての Constraint premise は
   (a)(b)(c) のいずれかの証拠源を持つ。fail-open は未知経路への保険であり、
   既知経路の実装不備を正当化しない（D4-4 継承）。
6. **線形性**: 節数は link event 数に線形（MPC invariant 3 のまま）。edge 数は
   link event 数 × 有界な連鎖深さに bounded。超線形なら stop。
7. **no-claim passthrough**: claim を持たない workload は節台帳も edge も作らず、
   byte 単位で不変（MPC invariant 6 / CDM invariant 8 と同じ gate）。
8. **liveness 対称性**（MPC invariant 8 の継承と拡張）: liveness の除去は
   `RootCoverage` ノードと record ノードの両経路の伝播で dependent へ届き、
   構造連鎖の深さに関係なく suppression が可逆である。§4.6 の walkthrough が
   具体例で示す。

## 4. pinned tests との整合と、blocking fixture の walkthrough

### 4.1 MPC §4 の pinned 5 tests

いずれも期待値無変更で green を保つ。5 本の根拠（MPC §4.1〜4.5）は Standalone 節・
ReplayConjunction 節・payload 計算・claim 層に依存しており、本書はそのいずれにも
触れない（D1）。DerivedUnary の premise 表現は 5 本のどの fixture でも
観測対象になっていない。

### 4.2 `replay_claim_parent_dedup_keeps_each_exact_replay_carrier`

`machine/bounds.rs:2357`（CDM の第一 anchor）。DPN は
`claim_parents_by_constraint` と `qualified_carrier_index` を**読むだけで書かない**。
記帳層に構造的に触れないため不変。

### 4.3 `mpc_a_9_1`〜`mpc_a_9_6`（replay 節中心の specs）

ReplayConjunction 節は D1 で追認・不変のため、期待どおりのまま。
`mpc_a_9_5`（unattributed link fails open）は D4-1 がそのまま維持する。

### 4.4 `dcp_a_8_8_duplicate_evidence_and_promotion_keep_root_and_exact_carrier`

`case_02.rs:2710`。claim 層（exact carrier・root・台帳内容）の観測であり、
D1 により不変。

### 4.5 blocking fixture の walkthrough（`mpc_a_9_8` が pin する結果の導出）

`row_structural_claim_fixture`（`case_02.rs:3888`）の実 ID で本設計を通す。

fixture の構成:

- `ConstraintRecordId(0)` = `subtype(source_pos, upper)` すなわち
  `Var(0) <: Neg::Row([matched_upper], tail = Var(1))`。root admission で
  `source_upper_record`（upper bound）を admit し、no-parent fallback で
  `parent_claim` を得る。**lower admission をしないため map entry 無し**。
  upper が `Neg::Row` のため canonical-key fallback も不成立。
- `add_lower_bound(source, row, Origin)` → `source_lower_record`。
  derivation が `Origin` のため producer 無し、map 書き込み無し。
- `drain()` の binary replay（pivot = source、lower = `source_lower_record`、
  upper = `source_upper_record`）→ result `ConstraintRecordId(1)` =
  `row <: Neg::Row(...)`。`ClaimQualifiedParent::ReplayConstraint
  { parent_claim, parent_side, replay }` が `Constraint(1)` の route として記帳される。
  **`Constraint(1)` も lower admission をしないため map entry 無し**。
- 構造分解 `RowItem { index: 1, route: MarkerAggregateToUpperTail }` →
  child = `marker_lower <: tail = Var(1)`。child の admission は `Var(1)` へ
  lower bound（`lower_record`）を admit する。
- fixture は `coverage_root = root(parent_claim)` へ live coverage state を挿入する。

**登録（旧設計で blocked だった箇所）**: child の structural link の節は

```text
DerivedUnary {
    carrier:  StructuralDerivation { parent: ConstraintRecordId(1), rule: RowItem { .. } },
    premise:  Constraint(ConstraintRecordId(1)),
}
```

carrier の field を写すだけで登録が完了する。lookup ゼロ、解決不能という状態が無い。

**評価**: `eval(Constraint(1))`:

- (a) linked record: 無し（map miss、canonical fallback miss）。
- (b) route: `ReplayConstraint` が 1 本 →
  `eval(Record(source_lower_record)) AND eval(Record(source_upper_record))`。
  - `source_lower_record`: Origin 素材で claim を持たない → Unclaimed → true。
  - `source_upper_record`: `parent_claim` を持ち、その root は live coverage →
    uncovered claim 無し・independent support 無し → false。
  - AND → **false**。
- (c) root claim: `Constraint(1)` は replay result であり root claim を持たない。
- OR → **false**。節は非投影。

child の `lower_record` は他に standalone 証拠を持たないため suppressed となり、
`mpc_a_9_8` の pinned snapshot `projected_count: 0`・「covered unary clause 1 個」と
一致する。

**liveness 対称性**: coverage state を除去すると `parent_claim` が uncovered へ戻り、
`eval(Record(source_upper_record))` が true → `eval(Constraint(1))` が true →
節が projectable へ反転する。伝播は、登録時 chain walk が張った
`Record(source_upper_record) -> lower_record` edge（および
`Constraint(1) -> lower_record` edge）を D5 の hook 1 / 2 が辿ることで届く。

**reduction-route 側の確認**: URR root（`Var <: Row`、map entry が定義的に無い）を
親とする reduction-route link は、premise `RootCoverage(root)` として登録され、
root が live な間は非投影、liveness 除去で投影可能へ戻る。これは claim 層の
coverage 分類と評価結果が一致する方向であり、flat 規則からの挙動変化は
「節帰属が完備になる」ことだけである（D4-1 の unattributed fallback から
正規の節評価へ移る）。

### 4.6 test 空白の明示

`mpc_a_9_8` は duplicate / evidence / promotion 経路の節保存を pin するが、
「premise ノードの評価そのもの」——特に (b) route 評価の再帰、(c) root base case、
D5 の constraint-node 伝播——を固定する unit test はまだ無い。§9 で新設する。

## 5. 採らない案

### 5.1 Standalone fallback の維持（MPC D2-4 現行）

採らない。§1.1 のとおり、これは誤分類そのものであり `mpc_a_9_8` の pinned snapshot と
矛盾する。fail-open は「未知の経路で情報を失わない」ための保険であって、
**構造的に必ず起こる既知の場合**の表現力不足を吸収する装置ではない
（D4-4 / DCP §4.6 / CDM の同規律）。

### 5.2 map の母集団拡張（upper-only constraint への entry 供給）

採らない。`scheme_projection_lower_record_by_constraint` の意味は
「この constraint が admit した ordinary lower record」であり、read site
（`mod.rs:1248-1284`、claim の lineage 解決と claim link）はその意味に依存する。
upper-only constraint は指すべき lower record を**持たない**のだから、
entry を供給するには phantom record の発明か upper record の流用が要る。
前者は record arena / canonical key の意味論への blast radius が大きく、
後者は lower 用の投影台帳へ upper record を混入させる。どちらも
「無いものを有るように見せる」方向であり、無い場合を第一級で表す D2 に劣る。

### 5.3 評価時の post-hoc graph traversal

採らない。「premise の record をどこかから探し出す」ための derivation graph 遡行は
MPC §12.1-7 が既に棄却しており、名前を変えて再導入しない。
D3 の評価が行うのは、admission 時に key 付きで記録済みの metadata
（`claim_parents_by_constraint` / map / root claim / liveness）への O(1) 参照だけであり、
「探索」は存在しない。D5 の chain walk も登録 event の手元の carrier を辿る
有界処理であって、事後の lineage 再構築ではない。

### 5.4 claim lineage kind からの premise 推測

採らない。MPC D2-1 の棄却（`Original` lineage の claim が replay occurrence 経由で
届く実例）をそのまま引き継ぐ。premise は occurrence の carrier からだけ決める。

### 5.5 constraint の projection ledger 第一級化

採らない（先送りでもない——現時点で必要が示されていない）。
constraint ノードに inclusion 状態と mutation publication を持たせれば D5 の
chain walk は一段 edge で済むが、状態面・epoch 面・invalidation 面が
record と constraint の二重になり、blast radius が最大になる。DPN は constraint を
stateless な評価中間ノードに留め、memo は評価 pass 内に限る（MPC §6.3 の
「恒久的な判定 cache は要求しない」を維持）。将来、chain 深さが実測で問題に
なった場合の optimization 候補としてだけ記録しておく。

### 5.6 遅延 repair pass・flush・不動点

採らない。DCP §7.7 / CDM §5.2・§5.5 の棄却をそのまま継承する。
D5 の hook はすべて既存の単一 write site / 既存 transition に同期して載る。

## 6. blast radius と性能条件

### 6.1 触る範囲

- MPC-B の節登録実装: premise 型の 3 ソート化と、structural / reduction-route
  link での登録（写経 + canonical root 正規化）。
- MPC-C の評価関数: `eval` のノード空間拡張（D3）。
- D5 index の key 型拡張と、登録時 chain walk・hook 3 / 4 の接続
  （`mod.rs:933`、`machine/bounds.rs:1416` / `:1499` の面）。
- 必要な場合のみ（DPN-0 の判定次第）: root producer constraint → root claim の
  append-only mirror `root_claim_by_producer_constraint`。生成点は no-parent
  fallback（`machine/bounds.rs:804-812`）の一箇所。CDM D3 と同じ
  「append-only 入力の鏡、無効化不要」クラスである。

### 6.2 触らない範囲

`scheme_projection_lower_record_by_constraint` 自体（write site・既存 read site とも
不変。評価が既存の `lower_record_for_constraint` を読むだけ）、claim 層全体、
CDM の差分機構（hook に載るだけで変更しない）、raw bounds、URR lifecycle、
consumer contract、portable provenance、既存 test の期待値。

### 6.3 性能条件（landing gate）

MPC §6.3 の gate をすべて継承する（CDM は `main` に着地済みのため、
性能実測は現行 baseline に対してそのまま行える）。追加分:

- **連鎖深さ census**: 評価再帰と chain walk の深さが「record を跨がない構造連鎖」に
  bounded であることを、DPN-0 の分布実測と §9 の nested fixture で確認する。
- **edge 線形性 census**: `dependent_records_by_premise` の entry 数が
  link event 数 × 有界深さに収まることを census で示す。
- **評価可能性 census**: confirmed path 上の Constraint premise の
  (a)(b)(c) 皆無率がゼロであること（invariant 5）。

## 7. MPC / CDM 文書との関係

### 7.1 MPC 文書（承認済み・編集しない）

本書が**置き換える**条項:

- MPC D2 節定義の `DerivedUnary { premise: BoundRecordId }` → 本書 D2 の
  `ProofPremise`。
- MPC D2-4（登録時 map 解決と Standalone fallback）→ 本書 D2 / D3 / D4。
- MPC D5 の `dependent_records_by_premise` の key 型 → 本書 D5。
- MPC §12.1-7 の stop condition → 本書の承認をもって解除され、後継の gate は
  本書 invariant 5（評価可能性）と DPN-0 になる。

本書が**精密化する**条項:

- MPC D2-5（claim ID 参照禁止）→ 本書 D6（canonical root は禁止対象外）。

それ以外の MPC の決定・invariant・pinned tests・§9 specs・§10 slices・
§12 の他の stop / rollback 条項はすべて有効なまま残る。
MPC 文書は承認済みのため編集しない。この対応関係の記録は本書側だけが持ち、
architecture 文書への反映は §13 で行う（CDM §7.4 と同じ扱い）。

### 7.2 CDM 文書（承認済み・着地済み・編集しない)

- CDM D1（claim 層と記帳の不可侵）は本書 invariant 1 が継承する。DPN は
  `claim_parents_by_constraint` / `qualified_carrier_index` の**読者**であり、
  記帳側に触れない。
- CDM §7.3 の推奨順序（MPC-B は CDM 着地後、CDM の差分 hook に載せる）は
  既に成立している。本書 D5 の hook 4 は CDM の delta occurrence
  （`push_claim_qualified_parent` の面）と同一物である。
- CDM の bulk oracle（test-only）は DPN の変更対象外である。

## 8. 実装前の必須検証: DPN-0

本書の設計は round 2 の特性づけと本書内の code 読解から導いた構造的結論を含む。
**実装着手前に、次を read-only で確定しなければならない。**

1. **評価可能性の実測**: confirmed workload（five-case の代表 case、および
   既存 mpc / dcp fixture 群）で、structural / reduction-route link の premise に
   なる constraint について、(a) linked record あり / (b) route あり /
   (c) root claim あり / いずれも無し、の分布を取る。
   期待: 「いずれも無し」がゼロ、かつ (a) 無しが多数派（§1.3 の
   「map miss が通常」の確証）。
2. **root claim アクセス経路の確認**: root producer constraint から自身の
   root claim へ、既存 metadata で scan 無しに届くか。届かない場合、
   no-parent fallback（`machine/bounds.rs:804-812`）が root claim 生成の
   単一 site であること（mirror index の生成点として足りること）を確認する。
3. **連鎖深さの分布**: record を跨がない構造連鎖（Constraint ソートだけを通る
   評価再帰の深さ）の分布を同 workload で実測する。有界で小さいことが期待値。

判定と分岐:

- **三点とも期待どおり**: 本設計の前提が成立。§10 の DPN-A（MPC-B 再開）へ進む。
  分布数値は §6.3 の census gate の baseline として保存する。
- **「いずれも無し」が非ゼロ、root claim へ scan が要る、または深さが有界でない**:
  **実装を開始せず、実測を添えて本書のレビューへ戻す。**
  評価不能ノードの実例は、本設計がまだ捉えていない admission 形状の証拠であり、
  fail-open で覆い隠してはならない。

DPN-0 は既存の観測 helper / census helper の read-only 拡張で行い、
production code を変更しない。

## 9. regression test specs

`crates/infer/src/constraints/tests/case_02.rs` を中心に追加する。
arena ID を hard-code せず、canonical record・exact carrier・premise ノード・
節帰属を構造的に観測する（既存 mpc_a 系 specs と同じ規律）。

### 9.1 structural premise resolves through constraint node（本命）

`row_structural_claim_fixture` の topology で、child の DerivedUnary 節が
`Constraint(parent)` premise で登録され、評価が route 経由で
`AND(lower, upper)` に届き、record が suppressed になること
（§4.5 の walkthrough の機械化）。`mpc_a_9_8` の snapshot と同値の観測を
評価側からも固定する。

### 9.2 URR-root reduction premise

reduction-route link の節が `RootCoverage(root)` premise で登録され、
live な間は非投影、liveness 除去で投影可能へ反転すること。
premise 解決に map・RowDerivation 親連鎖のどちらも使わないことを、
map が空のままである fixture 構成で保証する。

### 9.3 root base case の両側

(i) 通常 root（Direct claim、coverage 非 live）を premise 連鎖の終端に持つ
structural chain は projectable（`case_02.rs:1869` の意味論の premise ノード版）。
(ii) 同じ chain の終端が live covered root なら非投影。
同一 fixture の coverage 状態だけを変えて両側を固定する。

### 9.4 nested constraint chain

record を跨がずに Constraint ソートを 2 段以上通る評価
（structural 分解の連鎖）が、深さに比例した有界再帰で正しく評価されること。
一段限りの実装（premise を一段だけ展開する類）では red になる形にする。

### 9.5 constraint-node invalidation

(i) hook 3: premise constraint が後から lower record を admit（map 書き込み）した
とき、dependent record の再評価が publish されること。
(ii) hook 4: premise constraint に後から新しい route が push されたとき、
評価が非投影 → 投影可能へ反転し、edge が追記されること。

### 9.6 insertion-order invariance

9.1 / 9.2 の fixture を link 順・coverage 挿入順を入れ替えて構築し、
節集合・edge 集合・判定・snapshot が一致すること（`dcp_a_8_7` /
`mpc_a_9_6` と同じ規律の premise ノード版）。

### 9.7 census specs

評価可能性 census（(a)(b)(c) 皆無ゼロ）、edge 線形性、連鎖深さ bound を
合成 fixture 上で assert する（wall time は assert しない。CDM §9.6 と同じ扱い）。

## 10. 実装スライス

各 slice は前 slice の gate を閉じてから進める。elapsed-time と進捗報告の規律は
リポジトリの運用方針に従う。MPC §10 の slice 構成は維持し、MPC-B / MPC-C の
中身を本書で改める。

### DPN-0: read-only 検証（§8）

- 変更: test-only の観測 / census helper 拡張のみ。
- gate: §8 の三点が期待どおり確定。反例が出たら**ここで停止**しレビューへ戻す。

### DPN-A: MPC-B の再開（登録層。判定は不変）

- 変更: premise 型の 3 ソート化、structural / reduction-route link の節登録、
  edge 登録の chain walk、（DPN-0 の判定次第で）root claim mirror index。
  §9.1 / 9.2 / 9.6 の登録側観測と §9.7 census を追加。判定は現行のまま（挙動中立）。
- gate: 全既存 test green（挙動不変）。`mpc_a_9_8` の登録側 snapshot green。
  節数・edge 数の線形性 census。confirmed path 上に帰属無し link が
  残っていないこと（MPC D4-4 / MPC-B gate の継承）。

### DPN-B: MPC-C の評価拡張と invalidation

- 変更: `eval` のノード空間拡張（D3）、hook 1〜4 の接続（D5）。
  MPC-C 本体（判定の節評価への切替、mod.rs:678 / :1330 の単一評価関数への集約）と
  同時に landing する（MPC §12.2 の「判定切替と invalidation を分割して
  landing しない」規律の継承）。
- gate: §9.1〜9.6 green。`mpc_a_9_1`〜`9_8` green。MPC §4 pinned 5 本が
  期待値無変更で green。評価可能性 census ゼロ。no-claim passthrough byte 不変。

### 以降: MPC-D / MPC-E

MPC §10 のまま変更しない（epoch / cache 整合、integration / closeout）。
MPC-E の完了条件・287-case・性能実測もそのまま適用される。

## 11. 変更しないもの

- claim の生成・継承・coalescing・coverage root・liveness・`Qualified` payload 計算。
- ReplayConjunction 節の定義・実装・評価（追認、D1）。
- Standalone 節の定義と、MPC D2-1 / D2-2 / D2-6、D3 の record 評価・cycle 規則、
  D4 の fail-open の向き。
- `scheme_projection_lower_record_by_constraint` の write site・既存 read site・意味。
- `ReplayClaimParentKey` と CDM の記帳・差分機構・bulk oracle。
- raw bounds、solver replay、URR lifecycle、consumer contract、portable provenance。
- 既存 test の期待値。特に MPC §4 pinned 5 本、`mpc_a_9_1`〜`9_8`、
  `dcp_a_8_7` / `dcp_a_8_8`、`replay_claim_parent_dedup_keeps_each_exact_replay_carrier`。
- arena ID・family path・fixture 名を実装条件に使わない。

## 12. stop / rollback conditions

### 12.1 stop conditions

次のいずれかが判明した時点で実装を止め、本書のレビューへ戻る。

1. DPN-0 で評価不能な Constraint premise が confirmed path 上に非ゼロで存在する
   （§8 の分岐。着工前の停止）。
2. root claim アクセスに scan が要り、かつ mirror index の単一生成点が成立しない。
3. 連鎖深さが有界でない、または edge 数が link event 数 × 有界深さを超える。
4. `mpc_a_9_8` を含む既存 test のいずれかが期待値変更なしに green を保てない。
5. D5 の hook が admission 時完全性（CDM invariant 5）を破る形
   （flush 遅延・repair pass・不動点）でしか書けない。
6. `RootCoverage` の canonical root が path compression で不安定になり、
   `find` の冪等性で吸収できない。
7. 評価に global scan・claim 直積の実体化・不動点反復のいずれかが必要になる
   （MPC §12.1-5 の継承）。
8. MPC §12.1 の他の条項（本書 §7.1 で解除された 7 を除く）は引き続き有効であり、
   いずれかが発火すれば同様に停止する。

### 12.2 rollback units

- DPN-0 の census helper と §9 の正しい red regression は保持する。
- DPN-A が挙動中立で成立しなければ、部分的な premise 型拡張・edge 登録を残さず
  slice ごと戻す。mirror index は独立に revert 可能な形で commit する。
- DPN-B は MPC-C と一体で landing / rollback する（MPC §12.2 の規律）。
  評価拡張だけ・invalidation だけの片肺状態を残さない。
- いかなる rollback でも、退役した Standalone fallback（旧 MPC D2-4）へは戻さない。
  戻す場合は本書ごとレビューへ戻る。

## 13. 波及する文書（本書 landing 後に更新。本書では編集しない）

- `notes/architecture/claim-propagation-architecture.md`
  - 投影判定の節評価の説明に、premise ノードの 3 ソートと constraint ノード評価を
    追記する。
  - 「確認済みの範囲」を DPN-0 / DPN-A / DPN-B の gate 結果で更新する。
- `notes/design/2026-07-31-mixed-proof-conjunctive-ownership.md`（MPC 文書）は
  承認済みのため編集しない。D2-4 / D2-5 / D5 / §12.1-7 の後継が本書であることは、
  本書 §7.1 が記録する。
- `notes/design/2026-07-31-claim-parent-delta-materialization.md`（CDM 文書）も
  編集しない。hook の同一性は本書 §7.2 が記録する。

---

著者: Claude (Fable 5)

ユーザ承認済み（2026-08-01）。本書は設計判断の正本として扱う。
実装は §10 のスライス（DPN-0 から）に従って着手してよい。
