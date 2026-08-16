# Yulang3 エンジニアリング設計案

- Status: Proposal
- Date: 2026-08-16
- Scope: コンパイラ、型推論、実行系、LSP、WebAssembly、テスト、CI、永続キャッシュ

## 0. 結論

Yulang3 は、現行実装へ新しい世代を追加する形ではなく、**独立した workspace、できれば独立した repository** として始める。

設計の中心は次の七点とする。

1. コンパイラ内部を一方向の依存グラフにする。
2. 各 logical fact の authority を一つに定め、各 phase の出力を immutable な値として固定し、巨大な共有可変状態を持ち回らない。
3. solver の更新を `plan -> validate -> commit` の transaction にし、commit 後の fallible read を禁止する。
4. incremental compilation は module / SCC 単位から始め、owner 単位の細粒度 scheduling は計測で必要になるまで導入しない。
5. CLI、LSP、Wasm は compiler library に依存する leaf application とし、compiler 側から製品コードへ依存しない。
6. PR ごとの必須 test と、夜間の differential / adversarial / performance test を分離する。
7. 性能を「速そうな実装」ではなく、入力規模に対する work count、割当量、wall time の budget で管理する。

Yulang3 の目的は、現行 Yulang の機能を別の名前で写経することではない。言語仕様、公開 contract、代表的な regression corpus は引き継ぎつつ、現行の内部 state、cache layering、test hook、shadow oracle、crate 分割は原則として移植しない。

---

## 1. 現行 Yulang で起きていること

現行実装の問題は、単にコード量や test 数が多いことではない。複数の局所的に妥当な改善が、共有可変 state と広い依存グラフの上で互いの maintenance cost を増幅している。

### 1.1 観測できる症状

| 症状 | 現行 repository での観測 | 結果 |
| --- | --- | --- |
| workspace の広域再ビルド | root `Cargo.toml` に 14 workspace member があり、frontend、複数 IR、複数 runtime、CLI、LSP、Wasm が同じ build graph に入る | 小さな変更でも広い compile/test が発生する |
| test dependency の逆流 | `infer` の dev-dependency が `specialize`、`control-ir`、`evidence-vm` を引く | `infer` の test 一件だけを filter しても、test 選択とは別にこれら三 crate を含む広い dependency graph が build される |
| product と library の混線 | `yulang` が frontend、runtime、LSP を直接束ね、`wasm` は `yulang` へ通常依存と build-dependency の両方を持つ | CLI や Wasm の変更が compiler core の rebuild boundary を曖昧にする |
| 巨大 module | `crates/infer/src/constraints/mod.rs` は約 166 KB、`proof_inventory.rs` は約 138 KB、`crates/yulang/src/cache.rs` は約 247 KB、`server.rs` は約 164 KB | 一つの変更が多くの invariant と test を巻き込む |
| assurance scaffolding の常設化 | exact snapshot、shadow oracle、always-solve control、mutation contract、failure injection、publication audit が production module 周辺へ積層している | correctness を守るほど実装面積と test cost が増える |
| CI の長時間化 | frontend test と yulang test に各 90 分の timeout、contract runner に 4 個の 45 分 shard が必要。commit `4463af53` の message には characterization test 一件が当時約 41 分かかったと記録されているが、これは point-in-time の測定であり現在値ではない | feedback が遅く、timeout 引き上げが根本原因を隠す |
| contract manifest の集中 | `tests/yulang/cases.toml` が約 130 KB に成長し、多数の tag と cross-field rule を一箇所で管理する | case 追加時の局所性が失われる |
| persistent cache の多層化 | `.yucu`、`.yuir`、`.yumo`、`.yuvm`、`.yures` に加えて `.yuskey` source-key index など、複数の persistent artifact kind が重なり、prefix merge と ID remap まで compiler core が担う | cache correctness が compiler architecture の大部分を占める |

これらは個別には理解できる。問題は、巨大な `ConstraintMachine` / analysis session を中心に、optimization、incrementality、explanation、cache、LSP、安全性検査を後付けしているため、**新しい read 一つが mutation vocabulary、publication、scheduler、oracle、contract matrix、adversarial test の全更新を要求する**点にある。

### 1.2 根本原因

#### A. state ownership が広すぎる

推論中の state、proof provenance、dirty scheduling、snapshot、public projection、cache import が同じ object graph を読む。どの mutation がどの consumer を invalidate するかを、型ではなく protocol と test で保証する必要が生じている。

#### B. phase boundary が値ではなく手続きになっている

「lowering が終わった」「solve が終わった」「public interface が確定した」という境界が immutable output type として強く表現されず、後段が前段の arena や session を直接読む。そのため、commit 後に追加 read が失敗する、古い snapshot を読む、raw ID を別 artifact へ持ち出す、といった状態が作れる。

#### C. correctness の代償を test が全面的に負っている

現行の厳密な test は価値が高い。一方で、同じ production path を shadow execution、exact snapshot、fault injection、full-std characterization で繰り返し確認する構造は、architecture が許している invalid state を test で塞いでいるとも言える。

#### D. optimization の粒度が細かすぎる

owner-level dirty scheduling、snapshot reuse、prefix cache merge などが、module boundary や immutable interface が十分単純になる前に導入されている。細粒度 optimization は hit した場合の利益より、dependency tracking の完全性を証明する cost が大きくなりやすい。

#### E. application が compiler core の leaf になっていない

`yulang` crate が compiler frontend / runtime と CLI、server、cache、contract runner を直接束ね、compiler API と product orchestration の境界が薄い。Wasm は別 crate だが、`yulang` へ通常依存と build-dependency の両方を持つため、この広い build graph の外には出ていない。`cargo test` の filter 自体は一致した test だけを選ぶが、crate の test target と dev-dependency の compile scope は別であり、無関係な一件の test でも広い build を起こしうることが問題である。

---

## 2. 目標と非目標

### 2.1 目標

- 変更の影響範囲を crate、module、phase output のいずれかで局所化する。
- 1 ファイル変更時の通常 feedback を秒から数分以内に保つ。
- 入力が 2 倍になったとき、linear であるべき phase の semantic work が概ね 2 倍に収まることを機械的に確認する。
- clean compile と incremental compile が常に同じ `PublicInterface` / `CoreModule` を生成する。
- solver の termination、determinism、public evidence hygiene を、小さな kernel invariant と model test で説明できるようにする。
- runtime performance と compiler performance を別の benchmark / PR で改善できるようにする。
- test suite の correctness coverage と実行時間の両方を budget として扱う。
- authoritative document を少数に保ち、現在の設計判断を短時間で追えるようにする。

### 2.2 非目標

- Yulang2 の内部構造や private diagnostic を完全互換にすること。
- 最初から fine-grained incremental solver を作ること。
- 最初から複数の persistent artifact layer を作ること。
- 既存の optimization と assurance scaffolding をすべて移植すること。
- crate 数を機械的に最小化すること。
- Yulang3 の最初の release で現行 standard library 全体を動かすこと。

crate 数そのものは KPI ではない。独立して安定する API、ownership、rebuild boundary が同じ場所にあるときだけ crate を分ける。

---

## 3. 基本原則

### 3.1 一方向依存

production dependency は必ず source から backend へ一方向に流す。test の都合でも逆向きの dev-dependency を張らない。

### 3.2 immutable handoff

各 phase は、次 phase が必要とする情報を所有した immutable value を返す。後段は前段の mutable session を直接読まない。

### 3.3 fallible planning、infallible commit

semantic state を変える操作は、必要な read と検証を commit 前に終える。

```text
snapshot -> plan() -> validate() -> commit()
```

`commit()` 後に query、allocation、I/O、borrow acquisition、cache lookup のような失敗しうる処理を置かない。

### 3.4 coarse first

最初の incremental unit は file / module / SCC とする。owner、constraint、selection 単位の再利用は、module-level invalidation が実測上の bottleneck になった後にだけ検討する。

### 3.5 reference before optimization

単純で deterministic な reference implementation を先に作る。optimized path は同じ immutable output に対して differential test できる形で追加する。

### 3.6 application is a leaf

CLI、LSP、Wasm、playground、contract runner は compiler library を呼ぶだけにする。compiler core は application crate、Tokio、LSP protocol、browser API を知らない。

### 3.7 observation is not semantics

metrics、trace、proof explanation、debug dump は semantic mutation と分離する。観測を追加しても solver result や scheduling が変わらないことを API で保証する。

### 3.8 fact family の single authority

constraint、canonical type / effect node、provenance edge、cache entry、incremental query result など、主要な logical fact family は実装前に authority registry へ一行ずつ登録する。各行は少なくとも次を宣言しなければならない。

| 必須 field | 宣言する内容 |
| --- | --- |
| identity key | 同じ logical fact を同定する stable key |
| fact class | current value / append-only occurrence / historical provenance のいずれか |
| authoritative writer | commit を行う唯一の transaction / component |
| authoritative reader | current fact を読む唯一の query interface |
| authority / derived | 他の map、vector、index、certificate が authority か derived view か |

同じ logical tuple を複数の物理 store に置く必要があっても、同格の authority を二つ作らない。既存 authority から projection できる tuple を新しい store に複製する場合は、on-demand view では満たせない contract と、その view の lifecycle を先に文書化する。

---

## 4. 推奨 workspace 構成

Yulang3 の実装は現行 `yulang` workspace の member として追加しない。推奨順は次の通りである。

1. 独立 repository `yulang3` を作る。
2. 同一 repository が必要なら orphan branch / 独立 workspace とし、現行 root workspace から参照しない。
3. `crates/yulang3-*` を現行 workspace に足す案は採らない。

推奨構成は次の通り。

```text
crates/
  yu-syntax/       lexer, parser, CST, source coordinates
  yu-hir/          module graph, stable IDs, name resolution, immutable HIR
  yu-types/        canonical type/effect representation, schemes, public types
  yu-solver/       constraint collection, solve, generalize, role resolution
  yu-core/         typed core IR, specialization-neutral program representation
  yu-backend-vm/   specialization, control lowering, verifier, VM/runtime
  yu-compiler/     query database, phase orchestration, in-memory cache, API

apps/
  yulang/          thin CLI
  yulang-lsp/      LSP adapter
  yulang-wasm/     browser adapter

support/
  yu-test-support/ fixture builders used only by integration/nightly tests

tests/
  ui/
  contracts/
  solver-model/
  differential/
  corpus/
  perf/

tools/
  xtask/
```

### 4.1 dependency graph

```text
yu-syntax
    |
    v
yu-hir -----> yu-types
    |              |
    +------+-------+
           |
           v
       yu-solver
           |
           v
        yu-core
           |
           v
     yu-backend-vm

              yu-compiler
        depends on and orchestrates all phases
                  |
          +-------+--------+
          |       |        |
         CLI     LSP      Wasm
```

`yu-solver` は `ConstraintBatch` の構築で `HirModule` を読むため `yu-hir` へ直接依存し、canonical type / effect 表現のため `yu-types` にも依存する。`yu-compiler` は orchestration layer であり、semantic type の定義場所にはしない。application は `yu-compiler` の public API だけを使う。

### 4.2 crate ごとの禁止事項

| crate | 所有するもの | 所有しないもの |
| --- | --- | --- |
| `yu-syntax` | token、CST、parse error | module resolution、type、runtime |
| `yu-hir` | source file、module、stable `DefId`、resolved name、HIR | constraint store、VM value |
| `yu-types` | canonical type/effect node、scheme、public type | mutable solver queue、source CST |
| `yu-solver` | solve session、constraint/provenance ID、solution | LSP、filesystem、persistent cache、runtime |
| `yu-core` | frozen typed program、backend-neutral operation | solver arena、diagnostic session |
| `yu-backend-vm` | specialization、verified image、VM state | parser、module loader、LSP |
| `yu-compiler` | query key、revision、phase cache、configuration | CLI parsing、terminal output、web API |
| applications | protocol / UX / process orchestration | semantic state ownership |

### 4.3 graph rule

CI で `cargo metadata` を読み、次を自動検査する。

- core crate から application crate への依存を禁止する。
- upstream crate から downstream crate への dev-dependency を禁止する。
- Wasm crate から CLI crate への依存と build-dependency を禁止する。
- `yu-test-support` を production dependency にすることを禁止する。
- feature によって dependency direction が反転する構成を禁止する。

---

## 5. phase model

Yulang3 では、compiler pipeline を明示的な value transition として表す。

| Phase | Input | Output | mutable state の lifetime |
| --- | --- | --- | --- |
| Parse | `SourceText` | `ParsedFile` | call 内だけ |
| Resolve / Lower | `ParsedFile` + imported interfaces | `HirModule` | module builder 内だけ |
| Collect | `HirModule` | `ConstraintBatch` | collector 内だけ |
| Solve | `ConstraintBatch` + dependency interfaces | `SolvedModule` | `SolveSession` 内だけ |
| Project | `SolvedModule` | `PublicInterface` + diagnostics | なし、pure function |
| Core lowering | `SolvedModule` | `CoreModule` | local builder 内だけ |
| Backend | `CoreModule` + backend config | `ProgramImage` | backend builder 内だけ |

推奨する代表型は次の通り。

```text
SourceText
ParsedFile
HirModule
ConstraintBatch
SolvedModule
PublicInterface
CoreModule
ProgramImage
```

phase をまたぐ raw arena ID を禁止する。必要な ID は phase-specific newtype とし、serialized artifact には stable symbol key か明示的な remap table を保存する。

`AnalysisSession` や `BodyLowering` のような object が parse から cache import、LSP formatting、runtime lowering まで生存する構造は作らない。

---

## 6. solver kernel

### 6.1 kernel の最小構成

`yu-solver` の hot path は次の五要素に絞る。

1. `CanonicalArena`: type / effect node の interning。
2. `ConstraintStore`: append-only の semantic constraint。
3. `WorkQueue`: canonical key で deduplicate された work item。
4. `SolveTransaction`: read、計画、検証、mutation buffer。
5. `Solution`: frozen substitution、bounds、role result、unresolved facts。

proof explanation、debug dump、cache serialization、LSP 用 span formatting は kernel へ直接入れない。

### 6.2 transaction rule

mutation は必ず transaction buffer へ書く。

```text
begin(snapshot)
  -> read semantic facts
  -> compute affected keys
  -> construct mutations
  -> validate invariants and budgets
  -> commit all mutations atomically
```

commit 後の publication planning や query failure を許さない。commit が始まった後に失敗しうるなら、その処理は plan phase に置く。

通常の admission / commit path が処理してよいのは、新しく受理した fact と affected consumer の delta だけである。既存 prefix 全体の scan、sort、rebuild を ordinary commit ごとに起動することを禁止し、full rebuild は明示的な batch boundary または offline verifier に限定する。snapshot 単位の rebuild が必要な場合も、versioned snapshot に bind して同じ snapshot では一度だけ計算する。

これにより、terminal latch、deferred publication fence、post-commit query denial、partial journal publication のような状態を architecture 上作れなくする。

### 6.3 semantic fact と provenance の分離

solver の correctness に必要な semantic state と、説明用 provenance を別 store にする。

- semantic constraint は小さく canonical に保つ。
- provenance は `CauseId` の compact edge として append-only log へ記録する。
- full explanation graph は solve 後に lazy に構築する。
- provenance budget を超えても semantic result は変えない。
- release build では不要な provenance level を落とせるようにする。

formula、provenance edge、index が「現在の」location、live state、bound などを参照するときは、その値を自身へ copy しない。`(stable fact ID, expected root)` のような stable obligation だけを保持し、query 時の immutable snapshot から semantic authority へ join して late-bind する。snapshot ID は cache validity には使えるが、複数 writer の ownership reconciliation や semantic conflict の代用にはしない。

この split 自体が、semantic authority から provenance log、さらに full explanation graph への derived-view relation を新設する。したがって実装前に少なくとも次の contract を固定する。

| field | semantic / provenance split の contract |
| --- | --- |
| source authority | `ConstraintStore` が current semantic state の authority であり、full explanation graph の source authority は frozen solve result の `Solution` と causal edge の provenance log である。provenance update は `SolveTransaction` receipt の committed delta だけから導出する |
| owner | provenance edge は一つの `ProvenanceRecorder` だけが書く。lazy explanation graph は provenance log と `Solution` から on-demand で構築する `ExplanationGraphBuilder` が owner であり、derived view なので別の persistent writer は置かない |
| update unit | committed fact ごとの event-local delta。full explanation graph は solve 後の明示的な query / batch でだけ構築する |
| invalidation | graph は source solution と provenance log の content identity に bind し、revision またぎで暗黙に再利用しない |
| readers / cardinality | 単一 error の hover / diagnostic explanation は `decisive one`。`この bound に寄与した全 cause` export は configured / explicit cap `N` の `bounded N`。外部 tooling 向け portable-proof export は caller の contract が complete graph を要求する場合に限り `full set`。debug / trace dump は `stream` |
| physical budget | provenance log は solve session ごとに constraint count に比例する edge / byte / logical-to-physical amplification cap 内に保つ。budget pressure では古い entry を drop または detail-reduce し、semantic result は変えない。exact multiplier は Phase 3 / 6 の profiling で定める |
| retirement | provenance level が不要なら log を生成しない。生成した provenance log は frozen `Solution` に対応する causal authority として solve session / snapshot lifetime の間だけ保持し、その retirement とともに破棄する。lazy graph は query / snapshot lifetime の終了時に破棄する |

### 6.4 termination

termination は timeout や replay clamp ではなく、次の monotone measure で説明する。

- canonical constraint set は有限で、同じ key を二度 accept しない。
- bounds update は有限 lattice 上で単調に進む。
- residual / row split は canonical key で hash-cons する。
- work item ごとに生成数、accept 数、duplicate 数、fan-out を数える。
- debug build では measure が後退した時点で invariant violation にする。

### 6.5 determinism

- HashMap の iteration order を semantic order に使わない。
- diagnostics、public interface、specialization key は stable order へ normalize する。
- parallel solve を導入しても、commit order と final serialization は deterministic にする。
- clean / incremental / cached の三経路で同じ content hash を得ることを test する。

### 6.6 role resolution と effect row の index

全候補 scan を避けるため、検索 key を最初から明示する。

- role candidate: `(RoleId, nominal head / structural shape class)`
- method candidate: `(method name, receiver head)`
- effect operation: `(ActId, operation id)`
- row residual: canonical `(source, consumed head, residual weight)`
- specialization: `(DefId, canonical type args, evidence shape)`

performance test は wall time だけでなく candidate probe 数を検査する。候補数を 16 倍にしたとき、無関係 bucket の追加で probe 数が増えないことを直接確認する。

### 6.7 reference solver

Yulang3 の最初の solver は、incremental reuse や fine-grained scheduling を持たない deterministic reference solver とする。

optimized solver を追加する場合は次を守る。

- output type は reference solver と同じ `SolvedModule`。
- differential test は専用 test crate / nightly lane で行う。
- production hot path で常時二重 solve しない。
- optimization ごとに独立した kill switch と removal criterion を持つ。
- mismatch が一件でも出たら optimized path を fail closed で無効化する。

nightly differential の結果は release configuration gate の入力にする。mismatch は optimized-path enablement marker を無効にし、source を自動 revert せずに次の release candidate を reference solver へ戻す。owner が原因を修正し、対象 corpus を含む differential lane が再び通るまで marker を復帰できず、optimized path を有効にした release は blocking issue が解決するまで作れない。

### 6.8 query / certificate の cardinality contract

Yulang3 の query / read API と certificate はすべて、`decisive one`、`bounded N`、`full set`、`stream` のどれを返すかと worst-case output cardinality を interface contract に含める。bounded query は N の根拠を、stream は保持 memory と cancellation boundary を定める。

「正しさの保険」として全 candidate、全 parent、全 trace を materialize することを default にしない。full set を返すのは caller の semantic contract が全件を必要とすると示せる場合に限り、それ以外は decisive result、summary、bounded result、または stream を選ぶ。

---

## 7. incremental compilation

### 7.1 最初の query graph

最初は次の粗い query で十分である。

```text
parse(FileId, source_hash)
resolve(ModuleId, source_hash, direct_interface_hashes)
infer(ModuleId, hir_hash, direct_interface_hashes)
interface(ModuleId, solved_hash)
core(ModuleId, solved_hash)
backend(RootId, transitive_core_hash, backend_config_hash)
```

private body の変更で `PublicInterface` hash が変わらなければ、dependent module の infer を無効化しない。

### 7.2 stable identity

- `FileId` は workspace-relative normalized path と realm identity から作る。
- `ModuleId` / `DefId` は declaration の stable structural key を持つ。
- source offset だけを identity にしない。
- arena index は session-local とし、cache key に入れない。
- compiler schema version、language feature set、target、std interface hash を artifact key に含める。

### 7.3 persistent cache は後から足す

最初の Yulang3 は in-memory incremental cache だけでよい。persistent cache は phase output と invalidation rule が安定してから追加する。

初期の persistent artifact は最大でも次の二種に絞る。

1. `ModuleArtifact`: `PublicInterface` と必要な `CoreModule`。
2. `ProgramArtifact`: backend 済み `ProgramImage`。

parse cache、namespace cache、typed arena cache、mono cache、VM cacheを別 extension として同時に公開しない。必要性が計測で確認された layer だけを増やす。

### 7.4 cache safety

- deserialize 後に schema / content hash / dependency interface hash を検証する。
- cache miss と cache corruption は同じ source fallback へ落とす。
- cache import は fresh compile と同じ immutable phase output を返す。
- raw ID の直接保存を禁止する。
- artifact merge は generic arena concatenation ではなく、stable symbol table 経由にする。
- byte budget と LRU を持ち、無制限に solver snapshot を保持しない。

### 7.5 LSP snapshot

LSP は compiler database の immutable revision snapshot を読む。

- edit ごとに revision token を発行する。
- 古い revision の computation は cancellation できる。
- diagnostics / hover / completion は一つの completed revision からだけ publish する。
- thread-local fault injection や process-wide environment mutationを使わず、明示的な `CompilerConfig` / test double を渡す。
- LSP-specific fallback は semantic result を作らず、`Unavailable` として UI layer で扱う。

---

## 8. runtime と backend の高速化

compiler speed と runtime speed を同じ変更で扱わない。runtime は `CoreModule` 以降の leaf optimization として独立させる。

### 8.1 representation

- instruction、definition、constant、handler metadata は contiguous arena と compact ID で持つ。
- debug label と provenance は side table に置き、hot runtime object を膨らませない。
- verified `ProgramImage` を作り、runtime loop 内の構造検査を減らす。
- effect-free function と direct call に明示的な fast path を持つ。
- handler lookup は compile-time に可能な範囲で index 化する。

### 8.2 continuation

Yulang は multi-shot continuation を必要とするため、すべてを単純な move-only continuation にできない。そこで path を分ける。

- single-shot と証明できる continuation は stack segment を move する。
- multi-shot は immutable snapshot + copy-on-write / explicit clone を使う。
- continuation capture で毎回全 stack を clone しない。
- branch 数、capture bytes、resume count、clone bytes を metric にする。

### 8.3 benchmark

runtime benchmark は少なくとも次を分ける。

- cold startup / warm startup
- direct recursion
- ordinary function call
- effect operation / handler return
- single-shot capture / resume
- multi-shot nondeterministic branch
- mutable-state effect
- text/list allocation
- representative showcase

benchmark regression と semantic change を同じ commit で直さない。profile で hot path を確認してから一つずつ変更する。

---

## 9. 性能 contract

### 9.1 wall time より先に work count を測る

wall time は machine noise、linker、cache、並列度の影響を受ける。complexity regression の primary gate は deterministic counter とする。

| Phase | 最低限持つ metric |
| --- | --- |
| Parse | bytes、token 数、syntax node 数 |
| Resolve | definition 数、import edge 数、lookup probe 数 |
| Collect | type var 数、constraint 数、origin 数 |
| Solve | generated / accepted / duplicate work、max fan-out、SCC 数 |
| Role | demand 数、bucket probe 数、candidate match 数 |
| Generalize | root 数、iteration 数、canonical node 数 |
| Core | definition / expression / evidence node 数 |
| Specialize | unique key 数、cache hit、duplicate request 数 |
| Runtime | instruction 数、allocation bytes、continuation capture / clone bytes |
| Incremental | invalidated query 数、recomputed module 数、retained bytes |

metric は machine-readable JSON でも出せるようにし、user-facing output と混ぜない。

### 9.2 scaling fixture

最低限、次の family を generator から作る。

- declaration chain: 1k / 2k / 4k
- independent modules: 10 / 100 / 1000
- import fan-out / fan-in
- deep effect row
- wide record / union
- role candidate bucket
- recursive SCC
- repeated generic specialization
- nested handler / multi-shot branch

linear であるべき family では、入力を 2 倍にしたとき accepted work と allocation が原則 2.5 倍未満に収まることを gate にする。例外は design document に complexity と理由を書く。

### 9.3 初期 engineering budget

数値は固定 runner と baseline commit を記録した上で運用する。最初の目標値は次を推奨する。

| 項目 | 初期 budget |
| --- | --- |
| warm `cargo check -p yu-solver` | 20 秒以内 |
| core crate の fast unit suite | 90 秒以内 |
| fast test 一件 | 2 秒以内 |
| module integration test 一件 | 30 秒以内 |
| required PR CI の p95 | 15 分以内 |
| required job 一件 | 10 分以内 |
| full nightly | 60 分以内 |
| private body edit | interface 不変なら dependent infer 0 件 |
| clean / incremental parity | mismatch 0 件 |

これは言語 semantics ではなく engineering budget である。budget を超えたら timeout を上げる前に、test class の誤り、fixture 再構築、重複 std compile、dependency graph、algorithmic regression を調べる。

`required PR CI の p95` は各 job 単体ではなく、job dependency を含む critical path の wall time に適用する。したがって `contract-build -> contract-shards` では、`contract-build` と最長 shard の合計を 15 分以内に収めるよう、各 job の 10 分上限の内側で両者へ budget を配分する。並列 shard の時間は合算しないが、最長 shard は critical path に含める。

---

## 10. test architecture

### 10.1 五層に分ける

| Layer | 内容 | 実行頻度 | 目標 |
| --- | --- | --- | --- |
| L0 kernel unit | parser combinator、canonicalization、constraint transition | 全 PR | millisecond |
| L1 phase integration | 1 module / 小 SCC / 小 runtime image | 全 PR | seconds |
| L2 language contract | stable syntax、public type、diagnostic、runtime behavior | 全 PR、shard | minutes |
| L3 differential / adversarial | Y2 parity、reference solver、full std、fuzz corpus | nightly | tens of minutes |
| L4 performance | scaling family、allocation、runtime bench | nightly / manual | trend gate |

full std を読む characterization test は L0/L1 に置かない。PR では同じ invariant を小さな synthetic fixture で確認し、full std は L3 で確認する。

### 10.2 directory が分類を表す

一つの巨大 manifest に全 taxonomy を集めない。

```text
tests/
  ui/pass/
  ui/fail/
  contracts/stable-core/
  contracts/std-api/
  solver-model/
  differential/yulang2/
  corpus/replay/
  corpus/handlers/
  perf/compile/
  perf/runtime/
```

metadata が必要な case だけ sidecar file を持つ。case 名、kind、default backend、expected success は directory から推論する。global index は手書きせず生成する。

### 10.3 test rule

- bug 一件につき最小 reproducer 一件を基本とする。
- implementation path の call count より、immutable phase output と invariant を検査する。
- source text の substring で architecture を検査しない。
- wall-clock scaling test より、probe / work / allocation counter を優先する。
- production module に thread-local injection point を追加しない。
- test-support API は `yu-test-support` または test-only constructor に隔離する。
- process-wide environment variable を並列 test から変更しない。config object を渡す。
- timeout は deadlock detector としてだけ使い、正常 test の所要時間を正当化するために使わない。
- ignored / TODO test を contract suite に入れない。
- snapshot は public output だけに使い、raw ID や内部 dump は typed assertion で検査する。

### 10.4 property / metamorphic test

手書き matrix を増やす代わりに、次の性質を generator で検査する。

- alpha-renaming で public interface が変わらない。
- unused private binding の追加で public interface が変わらない。
- independent declaration order の変更で normalized output が変わらない。
- clean compile と incremental compile が一致する。
- serialize / deserialize 後の output が一致する。
- reference solver と optimized solver が一致する。
- explanation level を変えても semantic result が一致する。
- metrics on/off で semantic result が一致する。

### 10.5 fixture reuse

standard library や大きな support graph は test ごとに再構築しない。

- immutable compiled fixture を test process 内で共有する。
- isolation test だけ fresh temporary database を使う。
- contract shard は一つの compiler process 内で database を再利用し、case ごとの user state は明示的に reset する。
- shared fixture の build time と case execution time を分けて表示する。

---

## 11. CI と build

### 11.1 PR gate

推奨 job は次の通り。

1. `format-and-graph`: format、manifest、dependency direction。
2. `core-check`: core default member の `cargo check`。
3. `core-unit`: L0。
4. `phase-integration`: L1。
5. `contract-build`: release に近い CLI binary を一度 build。
6. `contract-shards`: 上の binary artifact を使って L2 を実行。
7. `wasm-smoke`: relevant path の変更時と定期実行。

`cargo build --workspace --all-targets` を全 PR の先頭 dependency にしない。all-targets、全 feature、全 platform は nightly / release で回す。

### 11.2 workspace default

root `Cargo.toml` の `default-members` は core + CLI に限定する。Wasm、LSP、benchmark tool、generator は明示指定時だけ build する。

### 11.3 shard

contract shard は case 数ではなく過去の duration で balance する。shard 数を増やす前に、各 shard が std / compiler を重複 build していないかを見る。

### 11.4 changed-path optimization

path に応じて追加 job を選択してよいが、次の smoke は常に回す。

- parser smoke
- solver model smoke
- one public-type contract
- one diagnostic contract
- one runtime contract
- clean / incremental parity smoke

### 11.5 nightly

nightly へ次を移す。

- full std characterization
- Yulang2 differential corpus
- reference / optimized solver differential
- adversarial replay / handler corpus
- all-targets / all-features
- full Wasm build
- scaling / allocation benchmark
- long-running cache corruption / recovery test

---

## 12. code organization

### 12.1 module rule

- 一つの module は一つの ownership と一つの reason to change を持つ。
- `mod.rs` は module 宣言と narrow re-export に限定し、主要 algorithm を置かない。
- 1,500 行を超えた file は split review の対象にする。
- 3,000 行を超える hand-written file は、明示的な例外理由なしに認めない。
- generated code は専用 directory / crate に隔離し、hand-written code と混ぜない。
- test が production file の半分以上を占める場合、`tests.rs` / submodule へ分ける。

行数は correctness rule ではない。ただし巨大 file は authority と test fixture が混ざった兆候として扱う。

### 12.2 public API

- `pub use *` と大規模な compiled surface re-export を避ける。
- phase output の constructor は crate-private にし、invalid combination を作れなくする。
- public field を最小化し、query method は owned / immutable value を返す。
- query / read method は section 6.8 の cardinality class と worst-case output を contract に持つ。
- raw arena reference や mutable store guard を phase boundary から返さない。
- error type は phase ごとに分け、fallback を `Any` / `Never` の semantic valueで表現しない。

### 12.3 configuration

- CLI flag、environment、LSP option を `CompilerConfig` へ一度変換する。
- compiler core から environment variable を直接読まない。
- default behavior を変える optimization flag は owner、導入日、removal condition を持つ。
- test-only feature が production authority を広げないようにする。

### 12.4 data layout

logical relation の identity を consumer struct の field layout で定義しない。stable ID と normalized relation schema を先に定め、flat view、ordered cursor、portable export、diagnostic sequence はその schema からの projection とする。edge や tuple ごとに full payload を埋め込むことを default にせず、exact semantics の保持と payload の物理 copy を分離する。

- frequently traversed node は contiguous arena と compact integer ID を使う。
- small row / argument list は inline small storage を検討する。
- canonical node は intern し、deep clone を避ける。
- clone bytes と retained bytes を metric にする。
- diagnostic string を hot semantic node に埋めず、span / symbol / cause ID を保持する。

storage schema と read topology は同じ design review で決める。iterator の nesting、empty bucket の skip、ordered cursor の resume、result-local traversal、chunk locality を後付けにしない。point lookup、ordered traversal、result-local traversal、full export のそれぞれについて complexity、allocation、ordering contract を示し、normalized storage であることだけを hot-path cost の説明にしない。

### 12.5 derived view registry

index、cache、certificate、materialized query、shadow store などの derived view を追加する design は、authority registry と同じ review unit に次の表を置く。空欄のまま実装を始めない。

| 項目 | 必須内容 |
| --- | --- |
| source authority | どの fact family と revision から導出するか |
| owner | 更新できる唯一の component |
| update unit | event-local delta / batch / snapshot rebuild のどれか |
| invalidation | source mutation と view invalidation の対応 |
| readers | production / test consumer と各 read contract |
| physical budget | entry、bytes、logical-to-physical amplification の上限 |
| removal | permanent である理由、または temporary view の削除 gate と期限 |

registry は code census と同期させ、authority graph、実在 reader、retirement 状態を review できるようにする。section 6.3 の provenance store / explanation graph も例外ではなく、同節の具体的な表をこの registry の entry として管理する。

---

## 13. 文書と変更管理

### 13.1 authoritative document

次の三階層に限定する。

1. `docs/architecture.md`: 現在の全体像。
2. `docs/invariants/<subsystem>.md`: 現在守る invariant。
3. `docs/adr/NNNN-*.md`: irreversible decision と代替案。

ADR は `proposed / accepted / superseded / rejected` を持つ。新しい addendum で古い文書を暗黙に上書きせず、superseded link を明示する。

historical review log は architecture の source of truth にしない。必要なら release note、issue、git history へ残す。

### 13.2 change rule

一つの PR で次を混ぜない。

- semantic change
- architecture migration
- optimization
- metrics instrumentation
- test framework redesign
- cache schema migration

大きな migration は horizontal に全 solver を一度に変えず、immutable boundary を一つ追加する vertical slice に分ける。

### 13.3 dual path の期限

old/new path を並存させる場合、導入 PR に次を書く。

- owner。
- authority はどちらか。
- parity の判定方法。
- removal condition。
- removal issue / milestone。
- 最大存続期間。
- 最大 supported workload と memory budget。
- production default から到達する期間。
- deletion PR / migration slice。
- rollback artifact の保存方法。

この要件は solver の dual path だけでなく、migration 中に導入するすべての shadow store、legacy facade、oracle、adapter、test-only bridge に適用する。authority cutover だけを完了条件にせず、old writer / reader の停止、old store / adapter / oracle の物理削除、legacy fixture の retirement、wall time / memory の再測定までを migration manifest の独立した追跡項目にする。期限なしの並存や、物理削除を未計画の follow-up にすることを認めない。

### 13.4 archive

旧実装を active repository tree に複製して残さない。release tag / branch /別 repository で参照できるため、通常 build tree からは削除する。

---

## 14. Yulang2 から Yulang3 への移行

### Phase 0: freeze と baseline

- Yulang2 の reference release を tag する。
- stable-core、public type、diagnostic、runtime の contract subset を確定する。
- current benchmark を固定 machine で採る。
- Yulang2 では correctness fix 以外の大規模 architecture change を止める。

**Gate:** compatibility corpus と baseline JSON が repository にある。

### Phase 1: 独立 skeleton

- 新 repository / workspace を作る。
- dependency graph checker、format、core CI を最初に入れる。
- `tools/xtask` を導入し、graph check と生成 task の入口を一つにする。
- `yu-syntax`、`yu-hir`、`yu-types` の空 boundary を作る。
- performance metric format を先に決める。

**Gate:** application を含めず、core check が 1 分台で終わる。

### Phase 2: syntax と HIR

- grammar と parser fixture を選択的に移す。
- stable file/module/definition identity を決める。
- name resolution と source diagnostic を immutable `HirModule` にする。
- cross-crate fixture が初めて必要になる時点で、test-only の `yu-test-support` を導入する。
- full Yulang2 parser internals をコピーしない。

**Gate:** representative stable-core source が deterministic HIR になる。

### Phase 3: reference solver

- effect、row、role、subtyping の最小 kernel を実装する。
- incremental reuse、dirty scheduler、persistent cache は入れない。
- small model、property test、termination counter を作る。
- `SolvedModule` と pure public projection を確立する。

**Gate:** stable-core の public type corpus が通り、solver test が 90 秒以内に収まる。

### Phase 4: core IR と最小 runtime

- typed core IR を定義する。
- effect-free call、basic handler、single-shot、必要な multi-shot の順で VM を作る。
- standard library は stable-core に必要な部分だけ移す。
- stable-core の end-to-end 実行に必要な thin `yulang` CLI を application leaf として追加する。

**Gate:** stable-core runtime contract が通る。

### Phase 5: compiler database と LSP

- module-level query / in-memory cache を導入する。
- clean / incremental parity を常時確認する。
- LSP は revision snapshot API の adapter として実装する。

**Gate:** private body edit で dependent infer が 0 件、公開 interface change では dependency closure だけ再計算される。

### Phase 6: persistent cache と optimization

- profile で最大 bottleneck を一つ選ぶ。
- optimization は一件ずつ追加し、reference output と比較する。
- stable artifact が必要になった時点で二層 cache を追加する。
- runtime と compiler の optimization PR を分ける。

**Gate:** required PR CI 15 分以内、scaling fixture に unexplained superlinear regression がない。

### Phase 7: compatibility 拡大と cutover

- Yulang2 corpus を feature group ごとに移す。
- Yulang2 / Yulang3 differential は nightly で回す。
- 差異を language change、Yulang2 bug、Yulang3 bug に分類する。
- `yulang-wasm` browser adapter と Wasm playground を application leaf として追加する。
- release contract を固定した後、その contract version を検査する installer を追加する。
- public release 前に Yulang3 の contract version を明示する。

**Gate:** 合意した contract subset、installer、Wasm playground、LSP smoke が通る。

---

## 15. 引き継ぐもの、引き継がないもの

### 引き継ぐ

- 言語仕様の数学的・意味論的内容。
- stable-core と明示された public contract。
- 小さく再現できる regression fixture。
- representative examples。
- scaling benchmark の入力 family。
- public evidence hygiene、handler hygiene、row polarity、termination といった invariant。

### 原則として引き継がない

- 現行 `ConstraintMachine` / `AnalysisSession` の field layout。
- owner-level dirty scheduler。
- permanent shadow oracle / always-solve production scaffolding。
- 複数の persistent artifact kind を同時に持つ cache layering。
- compiled surface merge の current API。
- thread-local / feature-gated fault injection seam。
- CLI と LSP と cache と runtime を同じ crate に置く構成。
- downstream backend を frontend unit test の dev-dependency にする構成。
-巨大 central contract manifest。
- 旧世代の source copy を active build tree に置く運用。

invariant は移植するが、その invariant を守るために現行実装が必要とした scaffolding は移植しない。

---

## 16. Yulang3 の completion criteria

Yulang3 を「新しい実装」と呼ぶ最低条件を次とする。

- core dependency graph が一方向で、application dependency が逆流していない。
- phase output が immutable type として分離されている。
- solver commit 後に fallible semantic read がない。
- major fact family の single authority と、derived view の owner / invalidation / retirement が registry で追える。
- query / certificate の最大 cardinality が API contract にある。
- reference solver と optimized path の authority が明確である。
- clean / incremental / cached output の parity test がある。
- module-level invalidation が interface hash で説明できる。
- required PR CI が budget 内にある。
- slow test が class と理由を持ち、unit suite に紛れていない。
- scaling fixture が machine-readable metric を出す。
- public contract が一つの巨大 manifest に集中していない。
- authoritative architecture / invariant / ADR の所在が明確である。
- migration の完了条件に legacy store / adapter / oracle の物理削除が含まれる。
- Yulang2 の内部最適化を移植しなくても stable-core が動く。

---

## 17. 最初に着手する十項目

1. Yulang2 の reference tag と stable-core corpus を確定する。
2. 独立した Yulang3 repository / workspace を作る。
3. dependency direction を検査する CI を入れる。
4. `SourceText -> ParsedFile -> HirModule` の immutable boundary を作る。
5. stable `FileId` / `ModuleId` / `DefId` を決める。
6. canonical type/effect arena と小さな reference solver を作る。
7. `ConstraintBatch -> SolvedModule -> PublicInterface` を確立する。
8. clean / incremental parity harness を先に作る。
9. stable-core の最小 runtime slice を一つ end-to-end で通す。
10. baseline を超えた箇所だけを profile し、最初の optimization を選ぶ。

最初の optimization を決める前に、最初の end-to-end slice を完成させる。Yulang3 で最も避けるべきなのは、実行できる小さな縦切りがないまま、solver、cache、LSP、runtime の高度な仕組みを並行して作り始めることである。
