# claim-parent 登録の差分実体化（CDM）

日付: 2026-07-31

状態: **ユーザ承認済み（2026-07-31）**

本書は `95b95586`（fix(infer): key replay claim-parent dedup on the exact carrier）が
顕在化させた性能リグレッションを閉じるための設計判断である。
`notes/design/2026-07-30-derived-row-claim-propagation-gap.md`（以下 DCP 文書）が導入し、
`notes/design/2026-07-31-mixed-proof-conjunctive-ownership.md`（以下 MPC 文書）が
拡張を予定している claim-propagation 機構について、**意味論ではなく登録コスト**を
対象とする。claim の identity・coverage・投影判定・監査経路は一切変更しない。

調査基準は `main` の `b1ea4eff`。
根因 trace の正本は、2026-07-31 の Codex session 2 round で確定した調査
（round 1: five-case characterization の bisection——`8110fed6` / `86071060` は無回帰、
`95b95586` 単独で 78.66x、round 2: `95b95586` の実 diff と現行 code path に対する
機構特定、および差分処理可能性の data-flow 検証）である。
round 2 の複雑度評価はコード構造からの導出であり、profiler 実測ではない。
この差は §8 CDM-0 が実装着手前に閉じる。

## 0. 本書が下す決定の要約

1. **`95b95586` は正しく、維持する**。exact carrier を含む dedup key
   `ReplayClaimParentKey { result, coverage_root, parent_side, replay }`
   （`crates/infer/src/constraints/machine/bounds.rs:1024-1029`）と、それを固定する
   pinned test `replay_claim_parent_dedup_keeps_each_exact_replay_carrier`
   （`machine/bounds.rs:2357`）は不可侵とする。revert・key の粗化は行わない（§5.1、§5.4）。
2. **採用する方向**: 候補 3 案のうち、**案1（occurrence-delta materialization）を
   統制規律として採用し、案3 の道具から索引 2 つ——exact carrier 索引と
   per-(record, root) 実体化集合——だけを取り込む**（§2）。
   eager 実体化の「全再走査」の腕を「今回挿入された差分だけの処理」へ置き換え、
   record ごとの一回きりの bootstrap を除き、event あたり amortized O(1) にする。
3. **案2（replay-plan batching）は棄却する**。現行機構の admission 時完全性の契約
   （「今拾わないと二度と拾えない」、`machine/bounds.rs:1046-1047` の in-code comment）を
   遅延整合へ変え、stale-read 窓と flush 時序という新しい silent-failure 面を作るためである（§5.2）。
4. **案3 の完全分離（occurrence store / summary の四部構成）は棄却ではなく先送り**とする。
   性能回復に必須ではなく、blast radius が最大で、その occurrence 側の完成形は
   MPC-B の clause 台帳が担うのが自然である（§5.3、§7）。
5. **現行の bulk 再走査コードは削除せず、test-only の equivalence oracle へ退役させる**。
   差分維持された台帳が bulk 再計算と一致することを、pinned fixture と
   characterization 上で機械検証する（§2-D4、§9.1）。
6. 実装着手前に、**CDM-0（コスト中心の実測確認）を必須の前提**とする（§8）。

## 1. 問題

### 1.1 実測されたリグレッション

five-case characterization
`cprov_a_characterizes_constraints_replay_std_and_regressions` は、
歴史的 baseline で 5 case 合計 432.12s だった。現在は外挿で約 41 分に達する。

bisection の結果は一点に確定した。

```text
86071060  fix(infer): register incremental row-route claim as reduction-route parent
          -> std::text::parse module lowering: 6.126s（無回帰）
95b95586  fix(infer): key replay claim-parent dedup on the exact carrier
          -> std::text::parse module lowering: 481.875s（78.66x）
```

同じ DCP-A〜E 系列の `8110fed6`（one-sided lower linkage / mixed proof ledger）と
`86071060` には回帰がない。回帰は `95b95586` の変更単独に帰属する。

### 1.2 `95b95586` はなぜ正しく、なぜ revert できないか

`95b95586` 以前の `ReplayClaimParentKey` は `(result, coverage_root, parent_side)` だった。
同一 (result, root, side) に**異なる exact `BinaryReplayDerivation` carrier** が複数到達した場合、
最初の一件だけが parent link を登録し、以降の carrier は静かに落ちていた。
これは carrier conflation——異なる replay 由来を互換とみなす——という実 correctness bug であり、
DCP 文書 §4.2（exact carrier invariant）への違反である。

`95b95586` は key に exact carrier を加えて `(result, root, side, replay)` とし、この穴を閉じた。
この性質は pinned test

> `replay_claim_parent_dedup_keeps_each_exact_replay_carrier`
> （`crates/infer/src/constraints/machine/bounds.rs:2357`）

が固定している。同 test は `rule` だけが異なる（pivot / lower / upper は同一の）
2 つの `BinaryReplayDerivation` を同じ (result, root, side) へ登録し、
**両方の exact carrier がそれぞれ qualified parent を保持する**ことを
assertion message 込みで要求する。

```text
dedup by result/root/side must not leave a second exact replay carrier unqualified
```

したがって revert は選択肢にない。本書の対象は `95b95586` が**意図せず起動した
コスト経路**であって、`95b95586` の意味論ではない。

### 1.3 blowup の機構（実 diff と現行コードで確定）

C を同一 (result, root, side) に到達する exact carrier 数、P を constraint の parent 総数、
D を lower record の derivation 総数とする。`95b95586` により parent 集合は
おおよそ O(R)（root/side 組合せ数）から O(C·R) へ育つようになった。

そして `register_replay_claim_parents`（`machine/bounds.rs:1005`）は、
新しい (root, side, carrier) key が**一つでも**挿入されるたびに、
eager path（`:1048-1053`）で次を**全量**実行する。

1. `register_constraint_upper_replay_claims`（`machine/bounds.rs:730`）が
   upper record の**全 parent** を clone・再走査する。
2. parent ごとに derived claim の実体化を試みる。ただし claim の実体は
   `derived_claim_by_record_and_root`（`constraints/mod.rs:798`）のとおり
   **(record, coverage_root) 単位で canonical** であり、同一 root への複数 carrier は
   冗長な再処理にしかならない。
3. `register_existing_constraint_lower_projection_proofs`（`machine/bounds.rs:816`）が
   lower record 側でも**全 parent** を clone・再走査する。
4. `independent_projection_supports`（`machine/bounds.rs:883`）が lower record の
   **全 derivation** を歩く。
5. structural / replay / row の各 carrier について、`parents.iter().any(...)` の
   線形走査（`:925` / `:941` / `:955`）で qualification を判定する——O(D·P)。
6. `update_scheme_projection_proofs`（`constraints/mod.rs:1224`）への合流も
   既存 entry の線形走査を伴う。

per-insertion O(P + D·P) が C 回積み重なり、P が C とともに育つため、
総量は O(C²·D)、D≈P≈C の最悪では **O(C³)** に向かう。

### 1.4 なぜこのコストは今まで不可視だったか

`95b95586` 以前は、2 件目以降の carrier が key 挿入の時点で落ちていたため、
この eager path は 2 件目以降について**一度も走らなかった**。
bug の存在自体が、コストを隠していた。

なお eager path は現行コードで既に条件化されている。

```rust
// Newly enqueued constraints consume this metadata during their bound admission.
// Queue-suppressed duplicates need the eager path because no later admission will run.
if inserted && materialize_existing_target { ... }
```

つまり「新規 constraint は自身の admission が metadata を消費する（lazy）／
queue-suppressed duplicate は後続 admission が無いから今拾う（eager）」という区別は
**設計として既に存在する**。本書はこの eager の腕を「全再走査」から
「今回の差分だけ」へ狭める。新しい整合性モデルを発明するのではない。

### 1.5 差分処理の feasibility（data-flow から確定した事実）

- **upper 側**: 実体化の単位は carrier ではなく (record, root) である
  （`derived_claim_by_record_and_root`）。既に実体化済みの root への新 carrier は、
  exact key の記帳（`95b95586` 自身の correctness 簿記）だけが必要で、
  再実体化は no-op である。
- **lower 側**: 新しい parent は lower record へその root の claim link を足すだけであり、
  それ自体は新しい independent support を作らない。
- **全走査が本当に必要なのは、record ごとに一回だけ**——最初の claim がその record に
  触れ、claim 到来以前から存在した raw derivation 群を lazy ledger が
  bootstrap 分類する時である。laziness の境界は現行コードに既にある
  （`ledger_exists` 判定、`machine/bounds.rs:862-868`）。
- bootstrap 後は、すべての admission event を「既に整合な台帳への純粋な差分」として
  処理できる。歴史の再走査は要らない。
- 台帳は現在も full-snapshot rebuild ではない。`update_scheme_projection_proofs` は
  root ごと「新しい claim ID が勝つ」置換（`mod.rs:1256-1266`）と追加だけを行い、
  stale な independent support を**除去しない**（add-only）。現行の全走査は
  snapshot 再構築ではなく、「lazy な台帳に未反映の証拠の冪等な再発見」である。
  この性質が差分化を可能にする——過去に整合済みの部分を再発見し直す理由がない。

## 2. 決定

### D1: `95b95586` の意味層は不可侵。変えるのは処理量だけ

次はすべて byte 単位で不変とする。

- `ReplayClaimParentKey` の 4 成分 key と、key 記帳の**無条件性**。
  2 件目以降の carrier も、root が実体化済みでも、exact key と
  `ClaimQualifiedParent::ReplayConstraint` entry は必ず登録する。
- `claim_parents_by_constraint` に最終的に載る parent 集合の内容。
- claim の生成・coalescing・coverage root・liveness・投影判定・`Qualified` payload
  （MPC 文書 D1 が保護する claim 層全体）。
- 台帳の add-only 意味論と、admission 時完全性（挿入された差分はその場で
  完全に処理され、後続 pass に依存しない）。

変わるのは「一回の挿入が何を**再処理**するか」だけである。
semantic identity には触れず、physical な処理量を O(全量) から O(差分) へ落とす。

### D2: 差分実体化の規律

`register_replay_claim_parents` とその同類は、**今回新しく挿入された parent 群
（差分）**だけを下流へ渡す。

1. **upper 側**: 差分中の各 parent について、coverage root が
   `derived_claim_by_record_and_root` に未登録の場合だけ実体化処理を行う。
   実体化済み root への新 carrier は key / parent 記帳のみ（D1）。
   全 parent の clone・再走査は行わない。
2. **lower 側**: 差分中の各 parent の claim だけを
   `update_scheme_projection_proofs` へ渡す（同関数は claims_to_link の
   リストを取る現行 API のまま、per-root merge が差分入力で正しく動く）。
   independent support の再計算は行わない——新 parent は support を作らないため（§1.5）。
3. **bootstrap**: lower record に台帳が無い状態で最初の claim link が起きたとき、
   一回だけ現行の全 derivation 分類（`independent_projection_supports` 相当）を実行し、
   claim 到来以前の raw derivation を分類する。以後その record は差分モードに入る。
4. **新 derivation の event**: 台帳を持つ record へ新しい derivation が合流する
   admission（duplicate / evidence / promotion を含む）は、**その derivation 一件だけ**を
   現在の qualified-parent 集合に対して分類し、台帳へ追加する。
5. **分類時可視性の保存**: 現行 bulk path は、support 分類を claim link の
   **適用前**の台帳状態に対して行う（`machine/bounds.rs:874` の計算が `:875` の
   更新に先行する。`roots_have_claim_support` / `Some(producer) == current_producer` の
   in-flight 特例 `:896` を含む）。差分実装は同じ可視性順序を保つか、
   D4 の oracle で等価性を証明する。順序の違いを黙って持ち込まない。

「今拾わないと二度と拾えない」保証は差分単位で維持される。差分は挿入時に
完全処理され、過去分は既に整合であることを bootstrap と帰納で保証する。

### D3: 二つの索引。summary は carrier に答えられない形にする

線形走査を置換するため、次の 2 索引を導入する。

```text
qualified_carrier_index:
    ConstraintRecordId -> set<exact carrier>
    -- claim_parents_by_constraint の append-only な鏡。
    -- independent_projection_supports の per-derivation 判定を
    -- O(P) 線形走査から O(1) lookup へ変える。

materialized_root 判定:
    既存 derived_claim_by_record_and_root の (record, root) key 存在判定を流用する。
    新規構造は要らない。
```

設計上の防壁: per-root の実体化判定は **root しか持たない**構造（既存 map の key）で
行うため、carrier 単位の qualification に誤用することが型的に不可能である。
carrier 単位の判定は exact carrier を持つ `qualified_carrier_index` だけが答える。
候補案3 が要求した「summary を carrier qualification に誤用させない API 境界」を、
規約ではなく構造で満たす。

両索引とも append-only データ（parent entry は push-only、(record, root) key は
永続）の鏡であり、**無効化が不要**である。判定結果の memo 化ではないため、
MPC 文書 §6.3 の「恒久的な per-record 判定 cache は要求しない」方針と衝突しない。

### D4: bulk 再走査は test-only oracle として退役させる

現行の全量再計算コードは**正しくて遅い**。これは無償の ground truth である。

- production の per-insertion flow からは bulk path を外す（CDM-E）。
- test / debug build では bulk 再計算を oracle として保持し、
  **差分維持された台帳 ≡ bulk 再計算した台帳**を pinned fixture・順序反転 fixture・
  five-case 上で機械検証する（§9.1）。
- この等価性が CDM の中心的 correctness 主張である。D2-5 の可視性順序のような
  微妙な点は、議論ではなく oracle の一致で決着させる。

### D5: 差分 event を発行する経路の census

差分規律は「全 admission 経路が自分の差分を漏れなく発行する」ことに依存する。
これは MPC 文書 D4-4 と同型の規律で守る。

対象経路（DCP §5.5 案B / MPC §6.1 の列挙と同じ全 admission 面）:

1. `register_replay_claim_parents`（`machine/bounds.rs:1005`、
   呼び出し点 `:1688` / `:1823`——replay action の適用と duplicate 系 admission）
2. `register_reduction_route_claim_parent`（`machine/bounds.rs:1056`。
   現在は挿入一件ごとに無条件で eager 全量処理を行っており、同じ差分規律へ揃える）
3. structural claim-parent merge（`enqueue_derived_subtype` /
   `merge_structural_derivation`、MPC 文書 §6.1 の列挙どおり）
4. one-sided lower linkage と independent support merge
   （`machine/bounds.rs:816-881`、`constraints/mod.rs:1224` 以降）
5. evidence-only / promotion の各 admission

census gate: confirmed path 上に「bulk oracle との不一致」または
「差分を発行しない経路」が一件でもあれば landing しない。
fail-open は未知経路への保険であり、既知経路の実装不備を正当化しない
（DCP §4.6 / MPC D4-4 と同一の規律）。

## 3. 必須 invariant

1. **exact key 不変**: `ReplayClaimParentKey` の 4 成分と key 記帳の無条件性。
   `rule` / `pivot` / `lower` / `upper` のいずれも dedup・qualification から
   落とさない・併合しない。圧縮してよいのは物理表現だけで、意味的 identity ではない。
2. **台帳等価**: 到達可能な任意の状態で、差分維持台帳 ≡ bulk 再計算台帳（D4）。
   claims for linked roots と independent occurrence のどちらも失わない。
3. **(record, root) canonical**: upper 側の derived claim は root ごとに一つ。
   carrier 数に比例して claim を増やさない（現行と同じ）。
4. **occurrence 粒度**: 同一 carrier の先行 INDEPENDENT occurrence と後続 CLAIMED
   occurrence は区別されたまま残る。carrier ごとの global 分類へ潰さない
   （MPC 文書 §2-D2 規則1 の規律。add-only 意味論がこれを自然に保つ）。
5. **admission 時完全性**: 挿入された差分の含意はその場で実体化される。
   後続の repair pass・flush・不動点反復に依存しない。不動点反復は導入しない。
6. **mutation / epoch 到達**: 新 parent が projection inclusion を変える場合、
   その変化は現行どおり `apply_scheme_projection_mutation` 経由で owner の
   mutation / epoch 追跡へ届く。届く時点も現行（挿入時）から変えない。
7. **線形性**: parent entry 数・claim 実体化数・台帳挿入数・索引 entry 数は
   link event 数に線形。global scan・graph 逆走査・全 bound scan を行わない。
8. **no-claim passthrough**: claim を持たない workload は索引も台帳も作らず、
   allocation / lookup が byte 単位で不変（DCP / MPC と同じ gate）。

## 4. pinned tests との整合

### 4.1 `replay_claim_parent_dedup_keeps_each_exact_replay_carrier`

`crates/infer/src/constraints/machine/bounds.rs:2357`。本設計の第一 correctness anchor。

- 同 test は `rule` だけが異なる 2 carrier を登録し、各 exact carrier の
  qualified parent が `claim_parents_by_constraint` に一件ずつ残ることを数える。
- CDM は key 記帳と parent push を無条件のまま保つ（D1）。差分化されるのは
  下流の実体化量だけであり、この test が観測する層には構造的に触れない。
- 決定的な点として、同 test は `materialize_existing_target: false` で呼んでいる。
  つまり **CDM が変更する eager 実体化の腕を通らず、CDM が不可侵とする
  記帳層だけを固定している**。test とその意図が、本設計の変更境界と正確に一致する。
- 2 件目 carrier の実体化を root 単位で skip しても（D2-1）、key と parent は
  登録されるため assertion は成立し続ける。§9.5 がこの「skip しても記帳は残る」
  性質を明示的に固定する。

### 4.2 `scheme_projectable_lower_keeps_only_independent_claim_on_mixed_record`

`crates/infer/src/constraints/tests/case_02.rs:1869`。
mixed record の分類（covered claim と Direct uncovered claim の同居、Direct 根拠での
一回 projection）は claim 層と payload 計算の話であり、D1 により不変。
CDM で変わるのは台帳 entry の**発見経路**（bootstrap + 差分 vs 毎回全量）だけで、
最終的な台帳内容は invariant 2 の等価性が保証する。

### 4.3 `dcp_a_8_7_independent_same_key_lower_stays_projectable_in_both_orders`

`case_02.rs:2686`。direct-first / claimed-first の両順序で view / snapshot が一致する
という規律は、CDM にとって最も鋭い既存 control である。
claimed-first では bootstrap が claim link 時に走り、direct 側 derivation は
後続の差分 event として分類される。direct-first では bootstrap が既存 derivation を
拾う。どちらの経路でも add-only merge と per-root 置換は可換であり、
oracle 等価（§9.1）と順序反転 spec（§9.2）で機械的に固定する。

### 4.4 MPC 文書の pinned 5 の残り

`generalize/tests.rs:184`・`generalize/provenance.rs:797` を含む MPC §4 の 5 本は、
投影判定と `Qualified` payload を観測する。CDM は判定にも payload 計算にも触れず
（D1）、台帳内容は等価（invariant 2）のため、期待値無変更で green を保つ。

## 5. 採らない案

### 5.1 `95b95586` の revert・一時退避

採らない。§1.2 のとおり carrier conflation は実 correctness bug であり、
pinned test `bounds.rs:2357` が正当に固定している。「速いが間違っている」状態へ
戻ることは、本 project の規律（正確性の穴を性能都合で開け直さない）に反する。
一時退避（perf 検証のための revert branch 等）も、期待値改竄と同種の危険を持つため
正規の手順にしない。

### 5.2 案2: replay-plan batching（dirty-mark と flush）

採らない。

- 現行機構の契約は admission 時完全性である（`:1046-1047` の comment が明文）。
  batching はこれを「flush 時完全性」へ変え、mark と flush の間に
  **claim metadata の stale-read 窓**を作る。この窓の間に metadata を読む
  全 consumer の監査という新しい invariant 面が生まれ、owner mutation / epoch の
  発火時序も flush 相対で再定義しなければならない。抑制系の失敗は silent である
  （MPC D4 の議論と同じ非対称）ため、この面の拡大は最も避けるべき方向である。
- batch が小さく頻繁な場合、flush ごとの indexed rebuild O(P+D+R) が
  B 回積もり、residual な準二次挙動が残りうる。実 batch サイズへの依存を
  仮定で消すことはできない。
- 差分化（案1）が同じコスト削減を stale 窓なしで達成できる以上、
  整合性モデルを弱める対価に見合う利得がない。

### 5.3 案3 の完全形: exact-occurrence store / summary の四部分離（今回は先送り）

今回は採らない。棄却ではなく先送りである。

- 四部構成（occurrence 列・carrier 索引・root summary・世代 cursor）は
  長期的には最も整った形だが、`TypeBounds` の台帳族・debug / census helper・
  projection-update API 面へ一斉に触る blast radius が候補中最大である。
- 性能回復に必須なのはその一部——carrier 索引と per-root 判定——だけであり、
  CDM はそれを D3 として取り込む。世代 cursor が担うはずの「どこまで処理済みか」は、
  D2 の差分規律（呼び出し規約で差分を渡す）と bootstrap 境界（`ledger_exists`）が
  既に表現する。
- occurrence 側の本命の完成形は、MPC-B の clause 台帳（link occurrence 単位の
  節帰属）である。四部分離を今やると、MPC-B が同じ場所へもう一度触る。
  継ぎ目を D3 の索引として残し、完成は MPC-B に譲るのが順序として正しい（§7）。

### 5.4 carrier-equivalence の粗化

採らない。`rule` / `pivot` / `lower` / `upper` のいずれかを dedup / qualification の
key から外す・併合することは、`95b95586` が閉じた conflation を再導入する。
`bounds.rs:2357` が red になる変更はいかなる性能利得でも正当化しない。
圧縮してよいのは物理表現（exact carrier を一度だけ格納し root / side を隣接情報で
持つ、等）であって、意味的 identity ではない。

### 5.5 判定結果の memo 化・global repair pass

採らない。判定 cache は無効化義務を生み、MPC §6.3 が明示的に要求から外している。
queue quiescence 後の repair pass は DCP §7.7 が棄却済みで、admission 時完全性とも
両立しない。CDM の索引は入力（append-only 集合）の鏡であって出力の memo ではない
（D3）。この区別を維持する。

## 6. blast radius と性能条件

### 6.1 触る範囲

- `register_replay_claim_parents`（`machine/bounds.rs:1005`）: 差分（今回挿入分）だけを
  下流へ渡す形へ変更。
- `register_constraint_upper_replay_claims`（`:730`）: 差分 parent 列を受け取る
  変種（または引数追加）。per-root 早期 return（D2-1）。
- `register_existing_constraint_lower_projection_proofs`（`:816`）と
  `independent_projection_supports`（`:883`）: bootstrap（全量、record ごと一回）と
  差分（一 parent / 一 derivation）の二形へ分離。線形走査を
  `qualified_carrier_index` の O(1) lookup へ置換。
- `register_reduction_route_claim_parent`（`:1056`）と structural merge・
  one-sided lower linkage・evidence / promotion の各経路: 同じ差分規律へ統一（D5）。
- `update_scheme_projection_proofs`（`mod.rs:1224`）: API は現行のまま差分入力で
  使える見込みが高い（per-root merge は差分入力と可換）。必要なら entry 探索の
  索引化だけを足す。
- 索引 2 つの新設と census / oracle 用 helper（test-only）。

### 6.2 触らない範囲

claim 層全体（生成・coalescing・coverage・liveness・payload）、投影判定
（`mod.rs:678` / `:1330`）、raw bounds、URR lifecycle、consumer contract、
portable provenance、`ReplayClaimParentKey` の形、pinned tests の期待値。
MPC 文書本体も編集しない（§7）。

### 6.3 性能条件（landing gate）

計測は CDM-0 で再取得した同環境 baseline に対して行う。歴史値との機械比較はしない。

- **第一 gate**: five-case characterization 中の `std::text::parse` module lowering が
  481.875s から **15s 以下**へ戻る（`86071060` 時点の 6.126s の 2.5 倍以内、
  32 倍以上の回復）。目標値は 6s オーダーへの完全復帰。
- **第二 gate**: `cprov_a_characterizes_constraints_replay_std_and_regressions`
  5 case 合計が歴史的 432.12s と同オーダーへ戻る。landing 閾値は **550s 以下**とし、
  432.12s との残差は具体的なコスト中心へ帰属説明できなければならない。
- five-case の poly / check hash が zero-diff（挙動等価の機械証拠）。
- census: parent entry・claim 実体化・台帳挿入・索引 entry の各カウントが
  link event 数に線形であることを実測で示す。
- no-claim workload の allocation / lookup が byte 単位で不変。
- 287-case contract suite に unexplained shift が無い。

## 7. MPC 文書との関係と着地順序

### 7.1 意味論の直交性

MPC の節登録（MPC 文書 §2-D2、§10）は本設計と意味的に直交する。節は exact carrier と
premise record を参照し、claim ID にも claim 実体化の機構にも依存しない。
CDM は claim 層に触れない（D1）ため、MPC の意味論的決定を一切変えない。

### 7.2 性能面の依存

- MPC-B が最初から event-local / 差分指向で実装されるなら（admission event ごとに
  節一つ + 逆依存 edge 高々 2 本の append / dedup）、現行の bulk 機構を必要とせず、
  本リグレッションを相続しない。
- 逆に MPC-B が既存 bulk helper を再利用して挿入のたびに
  `claim_parents_by_constraint` を列挙・backfill する実装を選ぶと、節**数**が
  線形でも登録**試行**数が非線形になり、MPC 自身の §6.3 gate に違反する。
- 現状の 482s 環境の上では、MPC-B の性能影響を意味のある形で評価できない。
  MPC §6.3 の性能 gate は、CDM の gate（§6.3）が通った baseline に対して
  評価しなければならない。

### 7.3 推奨する順序と共有 primitive

1. **MPC-0（read-only 検証）と MPC-A（test 追加のみ）は本設計と独立に、
   いつでも進めてよい**。production を変えないため CDM と干渉しない。
2. **MPC-B 以降は CDM 着地後に進める**ことを推奨する。MPC-B の節登録は
   CDM の差分 event（D2 / D5 の hook）にそのまま載せる——「一つの admission
   occurrence」が、CDM では差分実体化の単位、MPC-B では節帰属の単位として
   同一物になる。carrier 索引（D3）は MPC D2-6 の exact-carrier dedup が
   そのまま使える。
3. これは事前評価（両者は独立着地可能）を弱める改訂ではなく精緻化である:
   コード上は独立に着地**できる**が、MPC-B が独自の差分機構をもう一つ
   作る理由がなく、性能 gate の評価順序（CDM が先）は上記のとおり動かない。

### 7.4 MPC 文書への将来の追記（本書では編集しない）

CDM 着地後、MPC 文書は編集せず、次を **MPC 実装時の注記**として扱う。

- MPC §2-D2 規則1 の「link event」は、CDM 着地後は CDM の差分 occurrence と
  同一物を指す（cross-reference を MPC-B の実装 commit / architecture 文書側で記録）。
- MPC §10 MPC-B slice は、節登録の挿入点として CDM の差分 hook を使う。
- MPC §6.3 の性能実測は CDM §6.3 通過後の baseline に対して行う。

## 8. 実装前の必須検証: CDM-0

本書の複雑度分析（§1.3）はコード構造からの導出であり、profiler 実測ではない。
**実装着手前に、次を実測で確定しなければならない。**

> `95b95586` 時点（または現 `main`）で、`std::text::parse` 単独 case を対象に、
> 一時的な counter（または profiler）で次を取得する。
> (i) `register_replay_claim_parents` の呼び出し回数と、`claim_parents_by_constraint`
> の entry 数分布（最大・合計）。
> (ii) `register_constraint_upper_replay_claims` /
> `register_existing_constraint_lower_projection_proofs` /
> `independent_projection_supports` の呼び出し回数と、内側 loop の総 iteration 数。
> (iii) 同一 (record, root) への実体化再試行の重複率。
> あわせて無回帰 baseline（`86071060`）の同数値を再取得し、
> 比較の同環境性を確保する。

判定と分岐:

- **総時間の支配項が §1.3 の loop 群にある場合**（期待される結果）: 本設計の
  対象が正しいことの確証であり、CDM-A へ進む。counter 数値は §6.3 の線形性 gate の
  baseline として保存する。
- **支配項が別の場所にある場合**（例: hash lookup 自体、mutation 伝播の下流、
  型環境側の二次効果）: 本設計の処方は対象を外している。**実装を開始せず、
  実測を添えて設計レビューへ戻る。** 差分化自体が無意味になるわけではないが、
  landing gate を満たす見込みが立たないまま着工しない。

CDM-0 の instrumentation は throwaway とし、commit に残さない
（feature-gate された census helper として残す場合は test-only に限る）。

## 9. regression test specs

`crates/infer/src/constraints/tests/case_02.rs` と `machine/bounds.rs` の
test module を中心に追加する。arena ID を hard-code せず、canonical record・
claim root・exact carrier・台帳内容を構造的に観測する。

### 9.1 差分台帳 ≡ bulk oracle（中心 spec）

test-only の bulk 再計算（現行コードの退役先、D4）を oracle とし、
次の各時点で差分維持台帳との完全一致を assert する。

- pinned fixture（§4 の各 test の fixture を流用）
- 順序反転 fixture（9.2）
- 複数 carrier・複数 root・bootstrap 前後をまたぐ合成 fixture

一致対象は `claim_parents_by_constraint`・`scheme_projection_claims_by_lower_record`・
`projection_proofs_by_lower_record`・inclusion 判定の 4 面とする。

### 9.2 insertion-order invariance

direct-first / claimed-first、および carrier 到着順の入れ替えで、
台帳・索引・判定・snapshot が一致すること（`dcp_a_8_7` と同じ規律を
差分経路に対して再適用する）。

### 9.3 per-path delta census

§2-D5 の全経路（replay new / canonical duplicate / prefiltered duplicate /
reduction-route / structural / one-sided lower / evidence-only / promotion）
それぞれについて、その経路**だけ**を通る fixture で 9.1 の一致が成立すること。
bulk へ黙って fallback している経路が無いことを、経路別に固定する。

### 9.4 occurrence 粒度の保存

同一 carrier が先に INDEPENDENT として、後に CLAIMED として同じ record に
届く fixture で、両 occurrence が台帳上区別されたまま残ること（invariant 4）。
MPC-B が将来この区別に節帰属を載せるための直接の guard になる。

### 9.5 root 実体化の冪等と記帳の無条件性

実体化済み root への 2 件目 exact carrier について、

- `ReplayClaimParentKey` と qualified parent は登録される（`bounds.rs:2357` と同じ観測）
- derived claim は増えない（(record, root) canonical のまま）
- 台帳 entry も増えない

を同一 fixture で同時に assert する。「skip しても記帳は残る」の直接固定。

### 9.6 性能 harness

CDM-0 の counter を test-only census として再利用し、合成 fixture 上で
parent entry・実体化・台帳挿入の各カウントが link event 数に線形であることを
assert する。wall time の assert は行わない（§6.3 の実測 gate は CI 外で行う）。

## 10. 実装スライス

各 slice は前 slice の gate を閉じてから進める。elapsed-time と進捗報告の規律は
リポジトリの運用方針に従う。

### CDM-0: コスト中心の実測確認（§8）

- 変更: throwaway instrumentation のみ。production 挙動無変更。
- gate: 支配項が §1.3 の loop 群にあることの実測確認。「別の場所」なら**ここで停止**し
  設計レビューへ戻す。baseline 数値の保存。

### CDM-A: oracle と regression specs

- 変更: bulk 再計算の test-only oracle 化、§9.1〜9.5 の spec 追加、
  §9.6 census helper。production 挙動無変更。
- gate: 全既存 test green。oracle が現行実装と自明に一致（同じコードのため）。
  pinned test（§4）green。

### CDM-B: 索引の並走導入（挙動中立）

- 変更: `qualified_carrier_index` の新設と全経路での維持。既存線形走査は残したまま、
  debug build で索引と線形走査の結果一致を assert。
- gate: 全既存 test green（挙動不変）。索引 entry 数の線形性 census。
  no-claim workload で索引が作られないことの確認。

### CDM-C: upper 側の差分化

- 変更: `register_replay_claim_parents` が差分 parent 列を下流へ渡す。
  `register_constraint_upper_replay_claims` の差分変種と per-root 早期 return（D2-1）。
  `register_reduction_route_claim_parent` も同規律へ。
- gate: §9.1 / 9.5 green。`bounds.rs:2357` green。five-case hash 無変化。
  parse case の部分的な実測改善を確認（gate 値は課さない）。

### CDM-D: lower 側の差分化と bootstrap 分離

- 変更: `register_existing_constraint_lower_projection_proofs` /
  `independent_projection_supports` を bootstrap（record ごと一回）と
  差分（一 parent / 一 derivation、索引 lookup）へ分離。D2-5 の可視性順序の保存。
- gate: §9.1〜9.4 green。§4 pinned 全 green。oracle 一致が全経路 census（9.3）で成立。

### CDM-E: bulk の hot-path 退役と最終 gate

- 変更: per-insertion flow から bulk path を外す（oracle として test-only に残す）。
  debug assert の整理。
- gate: §6.3 の全性能 gate（parse ≤ 15s、five-case ≤ 550s、hash zero-diff、
  線形性 census、no-claim byte 不変）。287-case・`cargo test -p infer`
  （`--lib` と統合 test target の両方）・specialize / yulang suite・
  consumer crate の関連 test。残差の帰属説明。

## 11. 変更しないもの

- `ReplayClaimParentKey` の 4 成分と、`95b95586` の意味論・pinned test
  `replay_claim_parent_dedup_keeps_each_exact_replay_carrier` の期待値。
- claim の生成・継承・coalescing・coverage root・liveness・`Qualified` payload 計算。
- 投影判定（`mod.rs:678` / `:1330`）と consumer contract。MPC がこの判定を
  節評価へ置換する予定である事実にも触れない（順序は §7.3）。
- raw bounds・solver replay・監査経路・portable provenance。
- 台帳の add-only 意味論と admission 時完全性の契約。
- MPC 文書・DCP 文書（本書は両文書を編集しない。§7.4 は将来の注記の予告である）。
- 既存 test の期待値全般。期待値を現行の遅い実装にも速い実装にも「合わせ」ない——
  挙動等価が要求であり、期待値変更が必要になった時点で何かが間違っている。

## 12. stop / rollback conditions

### 12.1 stop conditions

次のいずれかが判明した時点で実装を止め、本書のレビューへ戻る。

1. CDM-0 で支配項が §1.3 の loop 群の外にある（§8 の分岐。着工前の停止）。
2. いずれかの admission 経路で、差分（今回挿入分）を局所情報だけから
   確定できず、global walk か graph 逆走査が必要になる。
3. bootstrap-once の前提が破れる——台帳を持つ record に、admission event を
   経由せず raw derivation が追加される経路が見つかる（「catch it now or never」の
   hook が存在しない挿入面の発見）。その経路だけ bulk を残す暫定は可視の形でのみ
   許し、silent fallback にしない。
4. oracle 等価（§9.1）が confirmed path 上で不成立になり、原因が D2-5 の
   可視性順序で説明・修復できない。
5. `bounds.rs:2357` を期待値変更なしに green に保てない。あるいは exact key の
   いずれかの成分を落とさなければ性能 gate を満たせない（この場合は性能 gate 側を
   諦めて設計へ戻る。key は落とさない）。
6. occurrence 粒度（invariant 4）を保つと線形性（invariant 7）が成立しない。
7. 索引 entry 数が link event 数に対して超線形になる。
8. CDM-E 後も §6.3 の第一 gate（parse ≤ 15s）を満たせず、残差を具体的な
   コスト中心へ帰属できない。
9. five-case hash・287-case に unexplained shift が出る。
10. 差分規律の実装に不動点反復・flush 遅延・判定 memo 化のいずれかが必要になる
    （それぞれ §5.5・§5.2 の棄却理由に抵触するため、必要になった時点で設計不成立）。

### 12.2 rollback units

- CDM-A の oracle と specs は、以後の slice が戻っても保持する。
- CDM-B の索引が挙動中立で成立しなければ、部分的な索引維持を残さず slice ごと戻す。
- CDM-C / CDM-D はそれぞれ独立に revert 可能な形で commit する。片側だけの
  着地状態（upper 差分 + lower bulk）は、oracle が green である限り中間状態として
  許容する（bulk は正しいため、混在は遅いだけで誤りではない——この性質が
  slice 分割を安全にする）。
- CDM-E で性能 gate だけが不合格の場合、CDM-A〜D（正しくて部分的に速い）を
  保持したまま、bulk 退役だけを戻して再計測・再設計する。
- いかなる rollback でも `95b95586` 以前の key へは戻さない。

## 13. 波及する文書（本書 landing 後に更新。本書では編集しない）

- `notes/architecture/claim-propagation-architecture.md`
  - claim-parent 登録のコストモデル（bootstrap + 差分、索引、oracle）を
    現状説明として追記する。
  - `95b95586` の正しさとコストの分離（§1.2 / §1.4）を「確認済みの範囲」へ反映する。
- MPC 文書は承認済みのため編集しない。§7.4 の cross-reference は MPC-B 実装時に
  architecture 文書側・実装 commit 側で記録する。

---

著者: Claude (Fable 5)

ユーザ承認済み（2026-07-31）。本書は設計判断の正本として扱う。
実装は §10 のスライス（CDM-0 から）に従って着手してよい。
