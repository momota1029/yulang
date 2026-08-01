# mixed proof の連言所有と証明合成台帳

日付: 2026-07-31

状態: **ユーザ承認済み（2026-07-31）**

本書は `notes/design/2026-07-30-derived-row-claim-propagation-gap.md`（以下 DCP 文書）の
stop condition §11.1-2

> replay両側のclaimを独立lineageとして扱うと、正しいconjunctive ownershipを失う反例が出る。

が発火したことを受けた、同文書 §5.1 が予告した「別設計」である。
DCP 文書の承認済み決定（§5.1 案D、§5.4 案C）を改訂するものではなく、
同決定が明示的に先送りした証明合成表現を追補する。

調査基準は `main` の `b1ea4eff`。
根因 trace の正本は、DCP-A〜D 着地後に read-only Codex session 5 round で確定した調査
（round 1: `enqueue_row_derived_subtype` 仮説の実装・実行・空振り確認と破棄、
round 2: 9 root の生成起源、round 3: leak record の carrier 単位 trace、
round 4: 先行 4 文書の突き合わせ、round 5: 候補 4 方向の blast radius 比較）である。
arena ID は一回の確定 trace の説明にだけ使い、test oracle や実装分岐には使わない。
同じ leak の trace でも実行により ID は変わる（例: covered reduction root は
architecture 文書の trace で `36823`、本調査の trace で `36829`）。

## 0. 本書が下す決定の要約

1. **採用する方向**: Direction D（連言証明表現）を、次の形へ絞った
   **証明合成台帳（proof composition ledger、以下 MPC）**として採用する。
   - per-claim の分類・coverage・liveness・claim table・DCP 継承機構は一切変更しない。
   - record 単位の投影判定（projectable / suppressed の yes/no）だけを、
     flat な claim 集合の OR から、節（clause）評価へ置き換える。
   - 節は premise を **record 参照**で持ち、lower × upper claim の直積を実体化しない。
2. **節への帰属は admission occurrence で決める**。claim 自身の lineage kind
   （`Original` / `ReplayConstraint` / ...）から節を推測しない。
3. **評価は投影時の memo 付き DAG 一回走査**とし、不動点反復を導入しない。
4. **fail-open を正の証拠の側に置く**。節へ帰属しない claim は現行 flat 規則で評価し、
   抑制には「全 claim が節へ帰属し、かつ全節が非投影」という正の証拠を要求する。
5. 実装着手前に、**MPC-0（read-only 検証）を必須の前提**とする（§8）。

## 1. 問題

### 1.1 DCP-A〜D が閉じたものと、残ったもの

DCP-A〜D と exact-carrier 修正 2 件（`86071060`、`95b95586`）により、
最初の covered alias `BoundRecordId(10185)` の leak 経路は閉じた。
replay 両側継承、structural 継承、one-sided lower linkage、mixed proof ledger は
DCP 文書の契約どおり動作している。

それでも
`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization`
（`crates/infer/src/lowering/tests/local_var_effect_boundary_edge_comparison.rs:460-609`）
は失敗する。

```text
parsed:     ('a & 'b) -> [std::control::var::observe('b | 'a)] ('b | 'a, 'a)
hand-built: ('a & 'b) -> ["&buffer#36:0"('a & 'b), std::control::var::observe('b | 'a)] ('b | 'a, 'a)
```

leak record は `BoundRecordId(10439)`（owner `TypeVar(1669)`、
producer `ConstraintRecordId(6647)`、constraint `PosId(2133) <: NegId(2055)`）である。
この record は `independent_supports` が空のまま、9 個の uncovered claim を持ち、
現行の投影規則（`crates/infer/src/constraints/mod.rs:678`、
「uncovered claim または independent support が一つでもあれば projectable」）により
schemeへ project され続ける。

### 1.2 9 個の uncovered claim の由来（確定事実）

round 2 の trace で、9 個の coverage root はすべて、URR とは意味的に無関係な
**通常の root constraint** に遡ることが確定した。

- 生成経路は `ConstraintMachine::subtype` → `enqueue_root_subtype` の canonical path
  （`crates/infer/src/constraints/machine/entry.rs:455` / `:924` / `:1205`）である。
- producer の例: `3643`（nested application、`lowering/expr/tail.rs:563/535`）、
  `3650`（test file 内の hand-built local reference、
  `local_var_effect_boundary_edge_comparison.rs:1684/1646`）、
  `3653`（synthetic field-selection method、`tail.rs:312/290`）。
- いずれも構造 / row / replay 由来の derivation を持たず、作成時に claim parent が
  無いため、no-parent fallback（`machine/bounds.rs:804-812`）で `Direct` root claim になる。
- 決定的な点として、これらの root constraint は **URR の登録
  （`row_effect.rs:475`）より前に作られる**。作成時点で URR の root claim は
  存在しないため、作成時に link する因果的な窓が原理的に無い。

つまり architecture 文書「現在も未解決の点」が区別できていなかった二択

1. 9 root は reduction から正当に派生しており、未発見の exact carrier で圧縮すべき
2. 9 root は上流で誤って独立 proof として生成されており、生成側を直すべき

は、**どちらでもない**。9 root は本物の独立な通常制約である。
問題はその独立性ではなく、それらが `10439` へ届く経路にある。

### 1.3 leak の正確な機構（確定事実）

round 3 の trace で、`10439` は 3 本の binary replay carrier から claim を受け取る。

```text
pivot=1670, lower=10402, upper=10389, LowerBoundAdded
pivot=1672, lower=10403, upper=10453, UpperBoundAdded
pivot=1673, lower=10577, upper=10603, UpperBoundAdded
```

これは DCP-B が実装した正規の両側継承そのものであり、機構としてのバグではない。
ただしこの継承は、**URR-covered な素材由来の claim と、§1.2 の通常制約由来の claim を、
同じ physical record 上の flat な集合へ合流させる**。
関与する URR は State `52`、source `TypeVar(1524)`、
producer `ConstraintRecordId(6462)`、original tail `NegId(2055)`、
materialization `BoundRecordId(10172)` である。

### 1.4 なぜ現行規則では直せないか

binary replay の result `R = transitivity(L, U)` の証明は、本来
**（L の証明）かつ（U の証明）の連言**である。
現行実装は DCP §5.1 案D のとおり、両側の parent claim を独立の加算的 lineage として
result へ継承する。これは claim identity・coverage 追跡・監査としては正しいが、
投影判定が flat 集合を OR で読むため、
「covered 前提 ∧ uncovered 前提」だけで導かれた relation が、
uncovered 側の claim を理由に projectable になってしまう。

一方で、既存の per-proof 規則を record-wide に強めることはできない。
`scheme_projectable_lower_keeps_only_independent_claim_on_mixed_record`
（`crates/infer/src/constraints/tests/case_02.rs:1869`）は、
covered claim と Direct uncovered claim が同居する record が、
Direct claim だけを根拠に**一回 project される**ことを要求する。
architecture 文書もこの理由で record-wide suppression を明示的に棄却している。

### 1.5 欠けている区別

したがって本当に必要な区別は、covered / uncovered でも record-wide / per-claim でもなく、
次である。

> record 上の uncovered claim は、その record の**単独で完結した代替証明**（OR の枝）か、
> それとも covered な素材と組んだ**連言証明の前提の片割れ**（AND の入力）か。

`case_02.rs:1869` の direct claim は前者であり、投影を保つべきである。
`10439` 上の 9 claim は（MPC-0 の検証を条件として）後者であり、
それだけでは record の投影を正当化しない。
現行の claim 集合はこの二つを表現し分けられない。DCP 文書 §5.1 の末尾が
「conjunctive coverage token / Boolean proof representation は別設計」と先送りしたのは、
正確にこの表現力の欠落である。

## 2. 決定

### D1: 層を足す。置き換えない

per-claim の機構は一切変更しない。すなわち次はすべて現状のまま残す。

- claim の生成・継承・coalescing（`register_constraint_upper_replay_claims`、
  `machine/bounds.rs:730-814`）
- coverage root の path compression と `live_coverage_by_root` の projection 時 lookup
- `scheme_projection_claims_by_lower_record` /
  `projection_proofs_by_lower_record` の内容と dedup 規則
- `SchemeProjectableLowerReason::Qualified { uncovered_claims, independent_supports }`
  の **payload 計算**（mod.rs:636-676 のループ）
- raw bounds が監査の正本として残ること

変更するのは record 単位の**判定（yes/no）だけ**である。
現行の判定は二箇所にある。

- iterator 側: `scheme_projectable_lowers` の
  `(!uncovered_claims.is_empty() || !independent_supports.is_empty())`
  （`constraints/mod.rs:678`）
- mutation 検出側: `scheme_projection_record_is_included`（`constraints/mod.rs:1330`）

この二箇所は**単一の評価関数を共有**しなければならない。
片方だけを節評価へ切り替えると、inclusion mutation / epoch / cache が
実際の投影結果と食い違う。

判定が projectable の場合の `Qualified` payload は現行計算のまま返す。
これにより、投影される record については consumer（compaction / alias /
generalized witness / portable provenance）から見た出力が完全に不変になる。
変わるのは「これまで projectable だった record が suppressed になる」方向だけである。

### D2: 節（clause）の形と、occurrence 帰属

claim が触れた record にだけ、遅延で節台帳を作る（既存 ledger と同じ laziness）。
意味形は次である。実装名は既存命名へ合わせる。

```text
RecordProofClause =
    Standalone {
        support: SchemeProjectionProofSupport,
    }
  | DerivedUnary {
        carrier: exact StructuralDerivation | RowDerivationId | reduction-route carrier,
        premise: BoundRecordId,
    }
  | ReplayConjunction {
        carrier: exact BinaryReplayDerivation,
        lower_premise: BoundRecordId,   -- carrier.lower
        upper_premise: BoundRecordId,   -- carrier.upper
    }

record の節集合 = AnyOf(clauses)
```

規則:

1. **帰属は link event で決める**。record へ claim / support を link した
   admission occurrence が、その claim の属する節を決める。
   claim 自身の lineage kind から節を推測しない。
   確定 trace では、claim `22206` は lineage `Original` のまま
   replay occurrence 経由で `10439` へ届いている。lineage kind で分類すると
   この claim が単位節扱いになり、bug がそのまま残る。
2. **Standalone**: producer constraint の root admission（no-parent fallback の
   `Direct` を含む）による link、および independent support の link。
   単独で record の完結した証明である。
3. **ReplayConjunction**: binary replay occurrence による link。
   premise は carrier 自身が保持する exact lower / upper record であり、
   新しい探索なしで得られる。同一 replay の両側から継承された claim 群は、
   **一つの**連言節に属する（側ごとに別の節を作らない）。
4. **DerivedUnary**: structural / row / reduction-route 継承による link。
   premise は親 constraint の linked lower record
   （`scheme_projection_lower_record_by_constraint`）から解決する。
   解決できない場合は節を作らず、その link を Standalone として扱う（fail-open、D4）。
5. **節は claim ID を参照しない**。`update_scheme_projection_proofs`
   （`constraints/mod.rs:1256-1285`）は root ごとに「新しい claim ID が勝つ」差し替えを
   行うため、claim ID 参照は staleness を作る。節は exact carrier と
   premise record（いずれも安定）で識別・dedup する。
6. dedup key は claim-parent 側と同じく exact carrier を含める
   （`95b95586` と同じ規律）。挿入順で節集合が変わってはならない。

### D3: 評価規則

投影時に、record ごとに次を評価する。

```text
eval(record):
    proofs が無い、または空          => projectable（現行 Unclaimed と同じ）
    節へ帰属しない claim / support が
    一つでも現行 flat 規則を満たす    => projectable（fail-open、D4）
    いずれかの節が projectable       => projectable
    それ以外                        => suppressed

clause_eval(Standalone{support}):
    support が現行 per-support 規則で qualifying
    （uncovered claim、または independent support）

clause_eval(DerivedUnary{premise}):
    eval(premise)

clause_eval(ReplayConjunction{lower, upper}):
    eval(lower) AND eval(upper)
```

- 評価は **memo 付き DAG 一回走査**とする。一回の評価内で同じ record を
  再訪しない（visited / memo table）。**不動点反復は導入しない**。
- 再帰中に cycle を検出した場合、その経路の節は「この record が証明されるなら
  この record は証明される」という空虚な証明であり、**その節は非投影**と評価する。
  ただし record 全体の判定は他の節と fail-open 規則（D4）が守る。
- premise record が tombstone / 欠落 / 参照不能の場合、その節は
  **projectable と評価**する（fail-open、D4）。

この規則の下で、従来の flat 規則は「全 claim を Standalone とみなす」特殊例である。
形式的には、投影規則は URR 文書 §4.10 の per-claim 規則から
per-proof-tree 規則へ一般化される。

> record は、**projectable な葉だけを使う完結した証明**を一つでも持つとき、
> かつそのときに限り、endpoint を一回 project する。

covered 前提を含む連言でしか導けない relation を suppress できる根拠は、
URR 文書 §4.10 の covered claim と同じである。covered 側の情報は live reduction の
incremental route が既に scheme へ表しており、uncovered 側の通常制約の情報は
その制約自身の record が独立に project する。連言 result を重ねて project することは
reduction の除外を迂回して同じ情報（今回は local family）を再注入することに等しい。

### D4: fail-open は正の証拠の側に置く

抑制は誤ると **effect が scheme から静かに消える**方向、すなわち健全性側の失敗になる。
leak（現状の bug）は過剰近似で目に見えるが、消失は目に見えない。
したがってすべての異常系は projectable 側へ倒す。

1. 節台帳が無い record、節が空の record は現行どおり評価する。
2. **link event に節帰属が記録されなかった claim / support は、現行 flat 規則で
   評価に参加する**。実装は各 link に節 ID を tag し、tag の無い link を
   flat 側へ回す。これにより、節登録を落とした経路は「現状の挙動（leak 側）」へ
   退化し、抑制側へは決して倒れない。
3. cycle・premise 欠落・世代不整合・metadata 破損は projectable 側へ倒す
   （既存 mod.rs:648-668 の fail-open comment と同じ方針）。
4. ただし DCP §4.6 と同じく、**confirmed path で fail-open が一件でも必要な実装は
   landing しない**。fail-open は未知の経路への保険であり、既知の経路の
   実装不備を正当化しない。

### D5: invalidation は節 DAG の逆依存で閉じる

現行の invalidation は root 逆引き
（`scheme_projection_lower_records_by_root`）で、liveness が empty / non-empty を
跨いだとき影響 record の owner へ inclusion mutation を publish する。

節評価では、record の判定が **premise record の判定**にも依存する。
継承が flat claim を全祖先分 record へ運ぶため（`10439` が 9 root を持つのは
このためである）、root 逆引きは多くの場合そのまま完全である。
しかし premise 側だけが後から変わる場合（late link で premise record に新しい root や
independent support が加わり、premise の判定だけが反転する場合）、
dependent record は自分の claim 集合にその root を持たず、root 逆引きから漏れる。

したがって次を追加する。

```text
dependent_records_by_premise: BoundRecordId -> small set<BoundRecordId>
```

- 節登録時に premise → dependent を append する（局所・定数個・append-only）。
- record の inclusion が変化したとき（既存の `was_included != is_included` 判定）、
  この index を辿って dependent の inclusion 変化を再評価し、変化した owner へだけ
  mutation を publish する。有限 DAG の bounded walk であり、不動点反復ではない。
- root 逆引き index は liveness transition の入口として現行のまま残す。

### D6: スコープ外の明示

- `enqueue_row_derived_subtype` の generic 経路（`machine/entry.rs:1416-1462`）は
  本設計のスコープ外とする。round 1 でこの経路への claim-parent 継承を実装・実行した
  結果（589/684 成功）、motivating test へ影響ゼロであることが確定している。
  9 claim はこの経路を通らない。この経路の節化（DerivedUnary 化）は、
  独自の証拠を持つ別 slice として扱い、本工事の代わりにも前提にもしない。
- evidence-only / promotion 経路は、節**登録**を DCP-B と同じ全 admission 経路
  （new / canonical duplicate / prefiltered duplicate / evidence-only / promotion、
  `machine/bounds.rs:1296-1420` の planning と各 admission）へ通すことで扱う。
  architecture 文書が残していた「promotion 後の `ReplayEvidence` 再分類」懸念は、
  節帰属が occurrence 単位で記録されることで、再分類ではなく登録漏れ検出
  （D4-2 の fail-open）の問題になる。

## 3. 必須 invariant

1. **claim 層の不変**: claim の生成・継承・coverage・liveness・
   `Qualified` payload の計算は byte 単位で不変。節は判定にだけ使う。
2. **exact carrier**: 節の識別・dedup・premise 解決はすべて exact carrier
   （`BinaryReplayDerivation` / `StructuralDerivation` / `RowDerivationId`）と
   安定な `BoundRecordId` による。lineage kind・endpoint 形状・path 文字列から
   推測しない。
3. **加算的で線形**: 節数は link event 数（= 既存 claim-parent 登録 + admission 数）に
   線形。lower × upper claim の直積、proof path の列挙、Boolean 式の正規化を
   実体化しない。
4. **一回走査**: 評価は投影 pass ごとの memo 付き DAG walk。全 bound / 全 claim /
   derivation graph の global scan、および不動点反復を行わない。
5. **fail-open の向き**: 情報を失わない側（projectable 側）へ倒す。
   抑制には全 claim の節帰属という正の証拠を要求する。
6. **no-claim passthrough**: claim を持たない workload は節台帳を作らず、
   `Unclaimed` fast path（mod.rs:608 の owner gate）を byte 単位で維持する。
7. **raw 不変**: raw bounds・solver replay・監査経路は変更しない。
   suppression は projection 時の判定に限る。
8. **liveness 対称性**: 最後の live coverage state が root から外れたとき、
   連言節の covered 前提が projectable へ戻り、依存 record も D5 の伝播で
   再び projectable になる。suppression を record へ焼き付けない。

## 4. pinned tests との整合

本設計は次の 5 本を期待値無変更で green のまま保つ。各根拠を記す。

### 4.1 `unweighted_row_upper_other_source_same_endpoint_direct_claim_stays_uncovered`

`crates/infer/src/constraints/tests/case_02.rs:1480`。
gamma の Direct claim は自身の producer（`machine.subtype(gamma_pos, tail, ...)`）の
root admission 由来であり、link event は Standalone 節になる。
per-claim 分類（`coverage_root = self`、lineage `Original`、uncovered）は D1 により不変。
generic replay の成立は raw bounds 側の話であり、本設計は raw を触らない。
すべての assertion が現行値のまま成立する。

### 4.2 `scheme_projectable_lower_keeps_only_independent_claim_on_mixed_record`

`case_02.rs:1869`。本設計の対象 bug と最も近い既存 control である。
fixture の direct claim は独立 producer の link であり Standalone 節、
covered claim の節は非投影。record は AnyOf により projectable、
`Qualified { uncovered_claims: vec![direct_claim], independent_supports: vec![] }` の
payload 計算は D1 で不変、endpoint は一回だけ project される。
`scheme_projection_claims_by_lower_record` の中身も不変（claim 層に触れないため）。

この test と §1.3 の bug の差は、uncovered claim が **Standalone 節を持つか、
ReplayConjunction の前提としてしか record に届いていないか**であり、
本設計はまさにその差だけで判定を分ける。

### 4.3 `dcp_a_8_7_independent_same_key_lower_stays_projectable_in_both_orders`

`case_02.rs:2686`。independent support は常に qualifying な Standalone 節である。
節の識別・dedup が exact carrier によるため（D2-6）、direct-first / claimed-first の
両順序で節集合・判定・snapshot（raw 1 / projected 1 / independent_supports 1 /
exact_replay_carriers 1 / incomplete_replay false）が一致する。

### 4.4 `positive_aliases_keep_mixed_record_uncovered_relation_exactly_once`

`crates/infer/src/generalize/tests.rs:184`。
alias expansion は `scheme_projectable_lowers` を消費する。
covered-only fixture は現行どおり非投影（全節非投影）、
mixed fixture は Standalone 節で projectable のまま一回だけ alias に入る。
consumer 側は判定の結果だけを見るため変更不要。

### 4.5 `mixed_lower_contributes_only_its_uncovered_claim_parent`

`crates/infer/src/generalize/provenance.rs:797`。
generalized witness は `Qualified` payload から `BoundClaim` parent を作る。
mixed fixture の判定は不変（4.2 と同じ）、payload 計算は D1 で不変、
したがって witness parent は現行どおり
`BoundClaim { bound, claim: uncovered[0] }` の一件だけになる。
新たに suppressed になる record は payload 自体が生成されないため、
covered sibling が provenance へ混入する経路も新設されない。

### 4.6 test 空白の明示

上の 5 本はいずれも「独立証明が record に**ある**場合」の control である。
今回の production topology——**URR 登録より前に生まれた通常 Direct root 群が、
後から mixed binary replay 経由で一つの record に合流し、独立証明は無い**——を固定する
unit test は存在しない。これは実在の coverage gap であり、§9 の regression specs で
新設する。

## 5. 採らない案

### 5.1 Direction A: boundary-scope token

`ReductionBoundaryScopeId` を root admission と URR record に載せ、
lexical boundary の一致で coverage を判定する案。採らない。

- §1.2 のとおり 9 root は URR 登録**前**に存在し、solver-lifetime の token では
  結べない。token を lowering まで遡って配ると、blast radius が
  boundary 内の全 root constraint 生成経路・nested boundary・instantiation・
  cache portability に及ぶ。
- より本質的に、lexical な同居は proof ownership を証明しない。boundary 内で
  生まれた本物の独立 relation を偽 covered にする危険があり、それを避けるには
  結局 per-proof の exact 規則が要る。token 単独では分類を解決しない。
- 最悪の silent failure は、handler の lexical scope 内で生まれた正当な effect が
  scope 所属だけを理由に scheme から消えることであり、健全性側に倒れる。

### 5.2 Direction B: URR-owned replay-occurrence carrier（単独では不採用）

特定の replay occurrence を reduction root に対して covered と tag する
`ReductionOwnedReplayOccurrence` 案。単独では採らない。

- occurrence 帰属という洞察は正しく、本設計は D2-1 としてそれを取り込んでいる。
- しかし carrier 単独では premise 側の**代替証明**を評価できない。
  covered 前提の record に独立な standalone 証明が別にある場合、
  「covered parent を持つ replay は covered」という規則はその独立証明ごと
  replay result を偽抑制する。逆に nested chain（replay の前提が replay）は
  一段しか閉じず、leak が一段外へ移るだけになる。
- 正しく評価するには premise record の証明集合への再帰参照が要り、
  それはもはや本設計（節 + DAG 評価）そのものである。

### 5.3 Direction C: mixed-proof 規則の record-wide 変更

「live covered claim があれば Direct uncovered claim を支配する」型の変更。採らない。

- `case_02.rs:1869` と正面衝突する。同 test は構造的に同型の mixed record で
  正反対の結果を要求し、これは意味的に正しい要求である。
- record-wide dominance は architecture 文書と URR 文書 §6.8 が明示的に棄却済み。
  per-proof 分類を boolean の record 属性へ潰し、本物の独立 relation を
  canonical 合流のたびに消す。最悪の silent failure が最も広い案である。

### 5.4 Direction D の素朴版: claim 集合上の Boolean 式の実体化

節を claim ID の集合で持ち、AnyOf(claims) × AnyOf(claims) を式として展開する案。
採らない。

- lower × upper の直積・式の正規化は DCP §11.1-5 の禁止事項（指数的 metadata）に
  抵触しうる。
- claim ID は root ごとの「新しい ID が勝つ」coalescing（mod.rs:1256-1285）で
  差し替わるため、式が stale になる。
- premise を record 参照にすれば、carrier が既に保持する exact record ID だけで
  同じ意味を線形サイズで表せる（D2-5）。実体化する理由がない。

### 5.5 finalizer cleanup / lowering 順序回避 / arena-ID 条件

DCP §7 および URR §6.8 の棄却をそのまま引き継ぐ。完成済み scheme からの family 削除、
hand-built lowering の constraint 順序調整、`10439` 等の ID や family path 文字列を
条件に使う実装は行わない。

## 6. blast radius と性能条件

### 6.1 触る範囲

- 節台帳と逆依存 index の新設（`constraints/mod.rs` の既存 ledger 群の隣）。
- 節登録: claim / support link が起きる全経路。
  replay planning（`machine/bounds.rs:1296-1420`）、
  claim 登録（`machine/bounds.rs:730-814` の各 link）、
  one-sided lower link と independent support merge
  （`machine/bounds.rs:832-1001`、`constraints/mod.rs:1224-1328`）、
  structural 継承（`machine/entry.rs:1253-1390`）、
  duplicate / evidence / promotion の各 admission。
- 判定: `scheme_projectable_lowers`（mod.rs:678）と
  `scheme_projection_record_is_included`（mod.rs:1330）を単一評価関数へ集約。
- invalidation: inclusion 変化の伝播（D5）と epoch / cache の整合。

### 6.2 触らない範囲

claim 層全体（D1）、raw bounds、URR state lifecycle、compaction / alias / witness の
consumer contract、portable provenance の表現（判定不変の record では出力不変。
suppressed record は payload 自体が出ないため新表現は不要）。

### 6.3 性能条件（landing gate）

- 節数と逆依存 entry 数は link event 数に線形であることを census で示す。
- 評価は投影 pass あたり memo 付き一回走査。再帰深さは derivation depth に
  bounded であることを nested chain test で確認する。
- no-claim workload の allocation / lookup が byte 単位で不変（既存 DCP gate と同じ）。
- five-case characterization の poly / check hash、および repository-std の
  wall time / peak memory 差分を実測し、説明できない回帰があれば landing しない。
- 恒久的な per-record 判定 cache は本設計では**要求しない**。導入する場合は
  D5 の逆依存 invalidation を前提とする optimization として別途正当化する。

## 7. DCP 文書との関係

- DCP §5.1 案D（両側 claim の独立 lineage 継承）は**維持**する。claim 層の
  identity / coverage / 監査はその決定のとおり動き続ける。
- DCP §5.1 末尾が先送りした「conjunctive coverage token / Boolean proof
  representation は別設計として performance と projectability を再証明すべき」の
  **別設計が本書**である。projectability の再証明は §4（pinned 5 test の保存）と
  §2-D3（投影規則の一般化とその根拠）、performance は §6.3 が担う。
- DCP §11.1-2 の stop condition は本 bug の確定により発火した。本書の承認をもって
  解除され、実装は §10 のスライスで再開する。
- DCP-E（motivating integration と broader closeout）は本設計の MPC-E と合流する。

## 8. 実装前の必須検証: MPC-0

**実装着手前に、次を read-only で確定しなければならない。**

> `BoundRecordId(10439)`（またはその時点の再現 trace における同役の record）に、
> covered 素材との連言を要しない**完結した standalone 証明の代替**が
> 一つでも存在するか。具体的には、record 上の全 claim / support の link event を
> occurrence 単位で列挙し、各 link が §2-D2 のどの節に帰属するかを確定する。

判定と分岐:

- **代替が無い場合**（全 link が ReplayConjunction 帰属、かつ各連言の少なくとも
  片側前提が covered-only）: これは DCP stop condition の連言所有反例そのものである
  ことの確証であり、本設計の実装により motivating test は green になる見込みが立つ。
  §10 の MPC-A へ進む。
- **代替が有る場合**: 現行 claim 構成の下で leak は意味的に正当（record は本当に
  独立証明を持つ）ということであり、本設計だけでは motivating test は閉じない。
  その standalone link の producer が本当に独立か、それとも生成側の別バグかを
  切り分ける必要がある。**実装を開始せず、trace 結果を添えてユーザへ決定を戻す。**
  本設計自体（連言判定の意味論）が無効になるわけではないが、
  着地順序と test 期待値の扱いが変わるため、先へ進む判断は設計側でしない。

MPC-0 は既存の観測 helper（`observed_replay_lineage`、
`scheme_projection_claims_by_lower_record` 等）の read-only 拡張で行い、
production code を変更しない。

## 9. regression test specs

`crates/infer/src/constraints/tests/case_02.rs` を中心に追加する。
arena ID を hard-code せず、canonical record・claim root・exact carrier・節帰属を
構造的に観測する。

### 9.1 conjunctive-only mixed replay suppression（本命）

covered claim を持つ premise record と、独立な通常 Direct root の premise record を
用意し、一つの binary replay result へ合流させる。result record の全 link が
ReplayConjunction に帰属し、standalone 証明を持たないことを fixture で保証する。

- result は suppressed（endpoint が scheme view に出ない）
- premise 側の通常 Direct record 自身は現行どおり projectable
- raw bounds には result が残る
- covered root の最後の live state を外すと、result は再び projectable

### 9.2 production topology の固定（§4.6 の空白を閉じる）

URR 登録**前**に通常 root constraint 群を作り、URR 登録後に mixed replay で
一つの record へ合流させる。9.1 と同じ期待に加え、
「URR 登録前に生まれた root であること」を fixture の構成で保証する。

### 9.3 nested chain suppression

replay result を premise とする第二の replay result を作る（連言の連鎖）。
一段目が suppressed なら二段目も suppressed であること。
Direction B 型の一段限り修正では red になる形にする。

### 9.4 premise-side alternative keeps result projectable

9.1 の covered premise record に、独立な standalone 証明（別 producer の direct link
または independent support）を追加する。premise の AnyOf が真になるため、
replay result は projectable に**戻る**こと。連言判定が premise の代替証明を
正しく評価している証拠になる。

### 9.5 unattributed link fails open

節帰属 tag を持たない claim link を test 専用経路で作り、record が現行 flat 規則で
projectable のままであること。抑制側へ倒れないことの直接検証。

### 9.6 insertion-order invariance

9.1 / 9.4 の fixture を link 順を入れ替えて構築し、節集合・判定・snapshot が
一致すること（`dcp_a_8_7` と同じ規律）。

### 9.7 invalidation propagation

liveness transition と late link のそれぞれで、dependent record の inclusion 変化が
D5 の逆依存 index 経由で owner へ publish され、constraint / owner / provenance の
各 epoch が前進すること（`case_02.rs:1914` の empty/non-empty test と同型の観測）。

### 9.8 duplicate / evidence / promotion clause preservation

同じ節を new / canonical duplicate / prefiltered duplicate / evidence-only /
promotion の各経路で登録し、節集合と判定が一致すること（`dcp_a_8_8` と同じ規律）。

### 9.9 motivating integration

`v5_corrected_nested_boundary_traces_inner_family_into_outer_finalization` を
期待値無変更で使う。MPC-0 の結果が「代替無し」の場合にのみ、本 test の green を
MPC-E の完了条件に含める。

## 10. 実装スライス

各 slice は前 slice の gate を閉じてから進める。elapsed-time と進捗報告の規律は
リポジトリの運用方針に従う。

### MPC-0: read-only 検証（§8）

- 変更: test-only の観測 helper 拡張のみ。
- gate: `10439` 相当 record の全 link の occurrence 帰属が確定し、
  standalone 代替の有無が判定される。「有り」なら**ここで停止**しユーザへ戻す。

### MPC-A: red baseline と regression specs

- 変更: §9.1〜9.8 の test を追加。9.1 / 9.2 / 9.3 が現行実装で red、
  9.4 / 9.5 / 9.6 / 9.8 の control 側が green であることを確認する。
  five-case / claim census baseline を保存する。
- gate: production code 無変更。pinned 5 test green。期待値を現行 leak へ合わせない。

### MPC-B: 節台帳の登録（判定は不変）

- 変更: 節台帳・逆依存 index のデータ構造と、全 link 経路への節登録。
  link への節 ID tag 付け。判定は現行のまま（挙動中立）。
- gate: 全既存 test green（挙動不変）。節数が link event 数に線形であることの census。
  confirmed path 上に帰属無し link が残っていないことの検査（D4-4）。

### MPC-C: 判定の切替と invalidation

- 変更: 単一評価関数（memo 付き DAG 走査、fail-open 規則）を実装し、
  mod.rs:678 と mod.rs:1330 の両方をそこへ集約する。D5 の inclusion 伝播を同時に入れる。
- gate: §9.1 / 9.2 / 9.3 が green へ反転。§9.4〜9.8 green。pinned 5 test が
  期待値無変更で green。no-claim passthrough byte 単位不変。

### MPC-D: epoch / cache 整合

- 変更: liveness transition・late link・suppression 反転の各 mutation が
  `GeneralizeCompactCache` と provenance epoch に正しく届くことの接続と検証。
- gate: §9.7 green。cache on / off で同一結果。epoch を進めずに判定だけ変わる
  経路が存在しない。

### MPC-E: integration / closeout（DCP-E と合流）

- 変更: §9.9 motivating integration。five-case characterization、287-case
  contract suite、`cargo test -p infer`（`--lib` に加え統合 test target を含む）、
  specialize / yulang suite、および consumer crate の関連 test。
  §6.3 の性能実測。
- gate: motivating test が期待値無変更で pass（MPC-0「代替無し」前提）。
  five-case poly / check hash が説明可能。287-case に unexplained shift が無い。
  DCP 文書 §12 completion contract のうち残項目（17〜22 相当）を本 gate で閉じる。

## 11. 変更しないもの

- claim の生成・継承・coalescing・coverage root・liveness・`Qualified` payload 計算。
- raw bounds、solver replay、subsumption、bound lifecycle。
- URR の matching / state lifecycle / initial unmatched self-tagging。
- local-var v5 lifecycle、private helper、lowering の constraint 挿入順。
- compaction / positive alias / generalized witness の consumer contract と
  portable provenance の表現。
- `enqueue_row_derived_subtype` の generic 経路（D6。別 slice として将来検討）。
- 既存 test の期待値。特に pinned 5 test と motivating test の期待値は変更しない。
- arena ID・family path・fixture 名を実装条件に使わない。

## 12. stop / rollback conditions

### 12.1 stop conditions

次のいずれかが判明した時点で実装を止め、本書のレビューへ戻る。

1. MPC-0 で standalone 代替が見つかる（§8 の分岐。実装開始前の停止）。
2. いずれかの link 経路で、post-hoc graph walk なしに occurrence 帰属を
   記録できない。
3. pinned 5 test（§4）のいずれかが期待値変更なしに green を保てない。
4. 節数または逆依存 entry 数が link event 数に対して超線形になる。
5. 評価に不動点反復、全 bound scan、または claim 直積の実体化が必要になる。
6. confirmed path を green にするために D4 の fail-open を破る
   （帰属無し link を抑制側へ倒す）必要が生じる。
7. DerivedUnary の premise 解決に global scan が要る、または解決不能率が
   confirmed path 上で非ゼロになる。
8. suppression の反転（liveness 除去後の再 projectable 化）が D5 の伝播で
   表現できない。
9. five-case / 287-case に説明できない shift が出る。
10. suppressed record の情報が portable provenance / diagnostics の完全性を
    壊す形でしか表現できない。

### 12.2 rollback units

- MPC-A の正しい red regression は保持する。期待値を leak 側へ戻さない。
- MPC-B が挙動中立で成立しなければ、部分的な節登録を残さず slice ごと戻す。
- MPC-C は判定切替と invalidation を**分割して landing しない**。片方だけの
  状態（再帰判定 + 旧 invalidation）は stale cache を作るため、揃わなければ
  両方戻す。
- MPC-E で motivating test だけ green でも suite に unexplained shift があれば、
  期待値を更新せず、最初に shift した slice へ戻る。

## 13. 波及する文書（本書 landing 後に更新。本書では編集しない）

- `notes/architecture/claim-propagation-architecture.md`
  - 「現在も未解決の点」: §1.2 の確定（9 root は独立な通常制約であり、
    残る問いは連言前提か代替証明かの区別だった）と、本設計による解決を反映する。
  - 投影判定の表: 節評価の行（連言前提のみの record は非投影）を追加する。
  - 「確認済みの範囲」: MPC 各 gate の再検証結果で更新する。
  - DCP slice 表: DCP-E の合流先として MPC を記載する。
- `notes/design/2026-07-30-derived-row-claim-propagation-gap.md` は承認済みのため
  編集しない。同文書 §5.1 の先送り段落と §11.1-2 の stop condition の後継が
  本書であることは、本書側の §7 が記録する。
- `notes/bugs/2026-07-28-local-var-effect-residual-transport-gap.md` へ、
  時系列の続きとして本書と MPC-0 の結果への pointer を追記する（調査記録側の更新）。

---

著者: Claude (Fable 5)

ユーザ承認済み（2026-07-31）。本書は設計判断の正本として扱う。
実装は §10 のスライス（MPC-0 から）に従って着手してよい。
