# 現在のタスク: yulang — playground 公開後の公開準備

2026-06-17 時点では、新世代 pipeline は playground で主要 smoke が動くところまで来ている。
ここからは、言語機能を無闇に広げるより、公開して触れる状態にするための足場を優先する。

入口と責務は引き続き次を基準に見る。

- `crates/sources` → `crates/infer` → `crates/poly` → `crates/specialize`
- runtime 側: `crates/mono` / `crates/control-vm` / `crates/mono-runtime`
- 共有 UI/LS 側: `crates/yulang-editor` / `crates/yulang-lsp` / `web/playground`
- CLI 入口: `crates/yulang`

作業規約は `/.rules`（= `AGENTS.md`）と `crates/.rules` を見る。
旧実装は仕様ではない。挙動が食い違ったら spec と手計算で正解を確かめる。

## 現在地（2026-06-23）: hardening phase

`ref.update` / directed stack weight の修正で、public type boundary、row-tail polarity、
replay termination、handler hygiene が同じ問題として見えるようになった。
ここからしばらくは新機能より hardening を優先する。

入口:

- `docs/infer-solver-invariants.md` — solver 不変量の作業契約
- `notes/diagnostics/2026-06-23-ref_update.md` — 今回のハングと private evidence leak の原因整理
- `notes/todo/yulang-hardening-phase.md` — 直近一週間と一ヶ月の作業順

直近で守ること:

- solver 大改造や高速化を始める前に、public signature golden test と opt-in metrics を置く。
- `compose_for_replay()` に `pop(n) -> pop(1)` clamp を戻さない。
- same-boundary alias-cycle subsumption を型等式として説明しない。
- public scheme に `#...` / `AllExcept(...)` / private tail が漏れたら regression として扱う。
- WSL2 が落ちやすいため、長い test は必ず `timeout` を付ける。

## 現在地（2026-07-01）: diagnostics / API fixed week

今週は「使いたい言語」へ寄せるため、性能 VM の深追いより public surface を優先する。

主軸:

- Diagnostics:
  - CLI / LSP / playground が同じ構造化 diagnostic を読める状態へ寄せる。
  - まず public CLI golden で、型注釈 mismatch、未解決名、parser error、
    role/method error、effect/runtime error の代表例を小さく固定する。
  - `check` の lowering / syntax diagnostic は compact summary、source frame、
    stable code、hint、型比較 related information の床まで入った。次は
    specialize/role/effect 側の source range と expected/actual provenance を増やす。
    - 2026-07-02 時点で role/method の unresolved / ambiguous failure は
      `run` の user-facing compile error として残しつつ、
      `unresolved_method_diagnostic` / `ambiguous_method_diagnostic` の
      `kind = "check"` manifest case でも structured `SourceDiagnostic` を固定済み。
      `compile-error` manifest tag は run route の user-facing error contract を守る印であり、
      role/method に check coverage が無いという意味ではない。
      2026-07-03 に source diagnostic は specialization oracle bridge から、
      emission なしの `specialize::role_method_check` を読む check-stage owner へ移った。
      run 経路の `SpecializeError` は従来どおり残る。残りは LSP / playground parity の broadening。
- API fixed:
  - 標準 API の安定性は `spec/2026-07-01-stable-standard-api.md` を現行 anchor とする。
  - filesystem は `spec/2026-07-01-file-resource-api.md` を file-specific anchor とする。
  - server API は stable standard API contract の中で、resource lifetime / scope exit /
    host capability / request-response resource として固定する。先に薄い関数群や HTTP
    framework を増やさない。
  - FFI は標準 API の実装境界になりうるが、public surface では host capability /
    effect boundary として扱い、native ABI 直結は後段に回す。

この週の変更では、parser / infer / std の意味を診断や API メモの都合で変えない。

Pro review の次方針として、`docs/status.md` に public contract spine を置いた。
以後の作業は、機能追加そのものではなく次の契約を強くする方向を優先する。
最初の executable contract 入口は `tests/yulang/cases.toml` とし、CLI runtime /
diagnostics / runtime error / public signature / public example の focused fixture から
manifest 化を進める。
2026-07-02 には `docs/language/stable-core.md` を追加し、`stable-core` tag を
Yulang Contract v0 の実行可能 subset として定義した。`yulang contract` は
`--contract stable-core` filter と unknown tag rejection を持ち、
hardening / archive smoke も representative stable-core cases を通す。
`docs/language/contract-v0-evidence.md` は、Contract v0 の完了証拠を
roadmap ではなく現状証拠として固定する。以後「Contract v0 を本物にする」という
曖昧な指摘には、まず欠けている manifest case / public signature /
structured diagnostic / release gate を具体的に要求する。file transaction、
server resource、host act FFI は Contract v0 の未完ではなく、次の contract slice である。
次の優先順位は `notes/todo/contract-v1-file-resource-priority.md` に置く。
Contract v1 は File / Host Resource Contract とし、最初に file resource の
mock / native / unsupported host contract を閉じる。

- public signature golden
- public runtime regression
- structured diagnostics
- release artifact / install smoke
- filesystem / server / FFI の API boundary

## 2026-07-02 追記: Evidence VM proof は静的 route 昇格へ寄せる

Claude (Fable 5) のユーザ承認済み文書として、次を現行 runtime 高速化の入口にする。

- `notes/design/2026-07-02-speedup-proof-system.md`
  - 既存 Evidence VM の cert / plan / invariant 群を翻訳し、
    現在の弱点を「Koka が静的に済ませる証明を signal ごとに動的再演している」
    ことだと整理する。
- `notes/design/2026-07-02-static-route-promotion-plan.md`
  - 提案 1（静的 route 昇格）と提案 2（evidence slot 静的インデックス化）の
    authoritative implementation instruction。

今後の performance work は、まず Stage 0 の被覆率計測 pass から始める。
Stage 0 は挙動変更なしで、静的解決できる operation call site と runtime hits を測る。
判定表の停止条件を無視して Stage 1 へ進まない。
`StaticHandler × TailResumptive` の direct execution は、Stage 0 の数字と
Stage 1a shadow mismatch 0 が揃った時だけ行う。

動的 cert / shadow は安全策として残すが、完成形ではない。
静的に証明できる経路は mono / specialize 時に発行し、実行時の gate 検査を消す。
静的に判定できない site は Dynamic(reason) として現行 fallback に残す。

## 現在地（2026-07-03）: Contract v1 follow-up

Contract v1 の closeout は `docs/language/contract-v1-file-evidence.md` /
`notes/todo/contract-v1-file-resource-priority.md` / `tests/yulang/cases.toml`
で現状証拠を固定済み。次の主戦場は file-resource の追加ではなく、
host resource surface と diagnostics / server driver の残りを小さく閉じること。

活性トラック:

- Host act registry: `std::io::file` / `std::io::console` /
  `std::time::clock` は compiler-produced manifest と evidence-vm registry dispatch に載った。
  根拠は `notes/todo/contract-v1-file-resource-priority.md` の優先 2。
- Structured concurrency: scheduler branch identity、cancel queue、suspend 中 branch の
  immediate-drop は実装済み。次は server surface の in-process driver。
  根拠は `notes/design/2026-07-03-structured-concurrency-decisions.md` と優先 5。
- Diagnostics: role/method unresolved / ambiguous 診断は specialization oracle bridge から、
  emission なしの `specialize::role_method_check` を読む check-stage owner へ移った。
  run 経路の `SpecializeError` は従来どおり残る。根拠は
  `crates/specialize/src/specialize2/role_method_check.rs` と
  `crates/yulang/src/source/mod.rs`。
- 次候補: 優先 5 の server in-process driver。HTTP framework ではなく、
  accept suspend/resume、request resource、one-shot response、double respond failure を
  executable contract で固定する。

## 現在地（2026-07-11）: std-prefix cache boundary / Option 1 Stage 2 blocker

今日の std-prefix cache 境界の性能問題調査から canonical cache interface（Option 1）
Stage 2 着手までの到達点は、次のコミット順で固定されている。

1. `5d94a670` `Normalize role fallback floor view`
   - generalize の fallback が solve 時と異なる floor 正規化を使っていたバグを修正した。
   - Yumark HTML の warm 実行は 15.97 秒から 9.93 秒へ改善した。
2. `84153826` `docs: record std-prefix cache boundary concretization analysis`
   - cache 境界が suffix の role predicate を具体化させる機構を解明し、記録した。
3. `a0934e57` `fix: fall back from unsafe std-prefix boundaries`
   - 自己完結性を証明できない std prefix は conservative に cold compile へ fallback する。
   - `crates/yulang/src/std_prefix_cache_safety.rs` を新設した。
   - Yumark HTML の warm 実行は 9.93 秒から約 1.3〜2 秒へ改善した。
4. `f213047c` `docs: specify canonical cache interface for Option 1`
   - 本解となる canonical cache interface を実装可能な水準まで仕様化し、8 stage に分解した。
   - 正本は `notes/design/2026-07-11-canonical-cache-interface-spec.md`。
5. `749c550c` `test: add canonical cache interface stage 0 oracle`
   - `crates/infer/src/interface_oracle/` に closure scanner と alpha-view を実装した。
   - Stage 0 の証拠により、Yumark HTML fixture は非 alpha 同値、Markdown fixture は
     alpha 同値と確定した。
6. `6db5ee8d` `test: promote std-prefix cache perf regressions from scratch examples`
   - `examples/zz_perf_repro_{html,md}.yu` を
     `tests/yulang/regressions/cache/std_prefix_yumark_{html_fallback,markdown_workload}.yu`
     へ正式昇格した。
7. `4126d915` `feat: add stage 1 compiled boundary cache schema`
   - 空の `CompiledBoundaryInterface` を typed/runtime surface へ配線した。
   - 本番挙動はまだ変更していない。

既知の暫定トレードオフ: Markdown は Stage 0 で alpha 同値と確定しているにもかかわらず、
現在の粗い conservative fallback により `full-miss` へ回される。以前の
`std-prefix-hit`（約 9.96 秒）より遅い約 12.5〜15 秒になっている。regression test は
Markdown の route（`full-miss` / `std-prefix-hit`）を固定していないため、Option 1 が
完成すれば自然に解消する設計である。

### Stage 2 の停止地点

Stage 2（canonical scheme export and boundary capture）の試作から、次が確定した。

- HTML fixture では、boundary capture が cold の抽象形、すなわち
  `Bounds(Union(Var, Concrete), Var)` 相当の open interval を再現した。capture の根本方向が
  正しいことを示す肯定的な証拠である。
- strict no-new-constraint audit（freeze 中に新しい constraint を発見してはならない）では、
  Yumark fixture と無関係な std 自身の `std.control.flow.label_sub.sub` に、既存の
  generalization が解決していない subtype/dominance key が 2 件見つかった。
- 設計doc Section 5.2 は、この状態で capture を再実行せず、既存 generalization loop 側の
  問題として扱うよう要求する。今回も「generalization loop 自体の変更が必要と判明したら
  実装を進めず停止する」というスコープ制約に従った。Stage 2 の実験差分はすべて巻き戻し、
  commit していない。停止時の worktree は clean で、試作の実装変更は残っていない。
- Markdown fixture の merge では一見新規の key が 23 件検出されたが、既存 generalization の
  適用済み key と照合すると全件が既知だった。ただし std 側 blocker で先に停止したため、
  Markdown の最終的な abstract-shape 検証までは到達していない。

Stage 2 は、`std.control.flow.label_sub.sub` の 2 件を次のどちらと分類するか確定するまで
再開しない。

1. 既存 generalization が本来解決すべき dominance/subtype 事実を素通りさせている。
   この場合、修正場所は Stage 2 ではなく既存 generalization loop である。
2. Stage 2 freeze 試作の順序または component 構成が、既存にはない dominance 条件を
   作っている。この場合、Stage 2 側のアルゴリズムを見直す。

次のセッションは、まず 2 件の key が `std.control.flow.label_sub.sub` のどの型変数と
どの制約を要求しているかを特定する。帰属を切り分ける前に Stage 2 の実装を再開しない。

### Stage 2 再開: boundary capture slice 1

`15209b7e` `fix: apply post-alias dominance constraints` により、前記 2 件は既存
generalization loop の post-alias lane で適用されるようになった。前回と同じ strict
no-new-constraint audit を再構築して `std.control.flow.label_sub.sub` に実行した結果は
`generated=2, unapplied=0` であり、Stage 2 blocker は解消した。

Stage 2 の最初の実装 slice では、finalized generalized compact schemes を入力として、
次を infer-internal な pre-canonical boundary draft まで実装した。

- `Q/R` を除いた unit-owned `B` seed の分類と、value restriction の generalization
  boundary の保持
- live `ConstraintMachine` の lower/upper bounds と再帰 bound を、各変数 1 回の worklist で
  推移 capture
- normal generalization が適用した merge/subtype key の保持と、freeze/capture の strict
  no-new-constraint audit
- open interval、value-restricted `B`、未適用 dominance key の拒否、`label_sub.sub` blocker
  解消の focused tests

この slice は non-empty `CompiledBoundaryInterface` の typed/runtime surface 出力や import を
まだ有効化しない。次は captured bounds を exported scheme と jointly compact し、shared floor /
co-occurrence / sandwich / polarity elimination を一度だけ適用して、pruned canonical draft と
closure validation を作る。artifact 配線と boundary-aware import は、その後の仕様上の stage に
残す。

### Stage 2 joint compact/freeze slice 2

captured `B` bounds と selected generalized schemes を一つの compact component へ合流し、
normal generalization と同じ floor cleanup 3 pass と shared simplification をそれぞれ一度だけ
適用する infer-internal finalizer を実装した。boundary bounds は recursive binder として保護せず、
一時的な invariant carrier として main roots / residual roles / true recursive bounds と同じ
occurrence accounting に参加する。

joint view から scheme roots、residual roles、recursive bounds、boundary bounds を再分離した後、
次を検証する。

- 現行表現で `R ⊆ quantifiers` でも、概念上の binder class は effective `Q` / `R` / unit `B`
  のいずれか一つになる。
- scheme の全自由変数はその scheme の `Q ∪ R` または unit `B` に閉じる。
- boundary bound は `B` と closed concrete structure だけを参照し、scheme-local `Q/R` に依存しない。
- missing/conflicting boundary entry、unbound scheme variable、binder class collision は構造化エラーで
  拒否する。
- simplify 後の dominance key は normal generalization の applied key、または capture 直後の raw
  boundary consistency key に既知でなければ `FreezeProducedConstraint` で拒否する。
- scheme から到達しなくなった provisional `B` entry は有限 worklist で prune する。

この slice でも、新しい solver loop、boundary-rigid / blocked pair / through flag は追加していない。
次は pruned compact draft を一度だけ poly arenaへfreezeし、typed/runtimeが同じdraftを消費できる
production handoffを作る。artifact encode/importの有効化は、そのhandoffとvalidatorが揃った後に行う。

### Stage 2 poly arena freeze / production handoff slice 3

pruned `CanonicalCacheInterfaceDraft` を値として一度だけ消費し、既存のcompact finalizerで
scheme・role predicate・recursive bound・unit boundary boundを同じclone済みpoly arenaへ
構造freezeする入口を実装した。freezeは再簡約やconstraint生成を行わず、対応するpoly scheme
targetが欠ける場合はarenaへ書き込む前に構造化エラーで拒否する。

typed/runtime surfaceはcrate-internalな`CompiledCacheInterfaceSurfaces` handoffから同じfrozen arenaと
boundary tableを受け取る。value restrictionで残るnon-empty `B`を使い、両surfaceのarena node列、
boundary table、scheme各fieldが一致するfocused testを固定した。公開APIと既存artifact構築routeは
変更していないため、non-empty artifact encode/importとboundary-aware importはまだ有効ではない。

確認済みはinfer interface oracle、cache interface focused tests、infer全体（578 passed / 既知の
`mark_expr_block_*` 5 failed）、std-prefix Yumark / role-polymorphic cache regression。次はStage 3の
boundary-aware import and instantiationであり、このsliceからは有効化しない。

### Stage 3 boundary-aware import slice 1: §6.1 Import once

Stage 3は仕様書Section 6に従い、次のサブステップへ分かれる。

1. §6.1 Import once: imported boundary tableを`BodyLoweringPrefix`で保持し、sessionごとに
   `B`のpersistent substitutionを一度だけ作ってboundsをbatch seedする。
2. §6.2 Scheme instantiate: `Q/R`をuseごとにfreshenし、`B`はsession mappingを共有する。
   canonical routeでunmapped free variableを残さない。
3. §6.3 Role candidate freshening: candidate-local head variableはfreshenしつつ、candidate内の
   `B`をschemeと同じsession mappingへ接続する。
4. Exit witness: 2回のinstantiationで`Q/R`が別、`B`が同一であることをtest witnessと
   Oracle Aで確認する。

今回実装したのは最初の§6.1のみである。runtime importがscheme・candidate・boundary boundsを
同じ`CompiledTypeImporter`でremapする既存入口を使い、remap済みboundary tableを
`BodyLoweringPrefix`から新しいboundary-aware `AnalysisSession` constructorへ渡すようにした。
session初期化では全`B`をroot levelで先にfresh allocateし、persistent
`poly TypeVar -> infer TypeVar` substitutionを保持する。同じmappingで全bound graphをcloneし、
lower/upper制約を一つのbatchで投入して、既存surfaceのseedより前に通常のconstraint eventを
routeする。cold routeは空boundaryを透過し、公開APIは変更していない。

確認済みは新規focused tests 3件、infer interface oracle 9件、cache interface / boundary /
canonical handoff、instantiate関連、std-prefix regression 5件。infer全体は581 passed / 既知の
`mark_expr_block_*` 5 failedであり、直近baseline 578 passedに新規3件を加えた結果と一致する。

同じ空cacheからstd prefixをseedした実測では、Markdown workloadは`full-miss`のままで、
`run.build_poly=28.425s`、`run.total=29.625s`、wall 32.71秒だった。HTML workloadも
`full-miss`を維持し、`run.build_poly=5.411s`、`run.total=6.578s`、wall 9.66秒だった。
structural oracleでもHTMLは引き続き非alpha同値であり、誤ってhit扱いされていない。

ここでMarkdownが`std-prefix-hit`にならないことは、§6.1の失敗ではなく仕様上のstage境界である。
non-empty canonical artifactのproduction integrationはStage 5、program-sensitive fallbackの退役は
Stage 7に属する。したがってStage 3を完了するだけでもMarkdownのhit化は成立せず、Stage 5の
artifact integrationとStage 7の明示的なfallback retirement判断まで必要になる。

次sliceは§6.2 Scheme instantiateである。現在sessionが保持するpersistent boundary substitutionを
`SchemeInstantiator`へpreloadし、`Q/R`だけをuseごとにfreshenして`B`を共有する。recursive boundsは
per-use mappingへcloneする一方、boundary boundsはuseごとにreplayしない。canonical routeでmappingの
ないfree `TypeVar`をsource IDのまま残す挙動を構造化errorへ変え、共有/非共有を示す正常系・否定系の
instantiation witnessを追加する。

## 仕様（実装の根拠）

- `spec/2026-05-31-effect-variable-subtractable.md` — stack 重みによる effect subtraction
- `spec/2026-06-02-role-system.md` — role 制約と discharge
- `spec/2026-06-04-method-selection.md` — ドット選択
- `spec/2026-06-06-invariant-type-sandwich.md` — 不変型と sandwich
- `spec/2026-06-06-syntax-design.md` — 表面構文（parser 実装から抽出）
- `spec/2026-06-07-principal-monomorphization.md`
- `spec/2026-06-14-control-artifact-cache.md` — control artifact cache

spec に無い判断をしたら、コードでなく spec か `notes/design/` に追記する。

## 現在地（2026-06-17）

- playground では list update、nondet once triple、method / property highlighting などの主要 smoke を通した。
- `specialize2` の function candidate 比較は、arg/ret だけでなく arg_effect/ret_effect も見るようになった。
- tuple length / record required field / polyvariant constructor mismatch は direct concrete subtype でも落ちる。
- `std.control.nondet.nondet.#act-method:once` は deep handler 型として export される。
- 直近の確認済み:
  - `cargo fmt --check`
  - `timeout 120s cargo test -q -p specialize -p control-vm -p mono-runtime -- --test-threads=1`
  - `timeout 120s cargo test -q -p yulang -- --test-threads=1`

WSL2 が落ちやすいため、長い test は必ず `timeout` を付ける。

## 2026-06-22 割り込み: directed stack weight proof

`research/effect-mini-language/directed_stack_weight_principal_letrec_colored_soundness_ja.tex` で、
effect subtraction の主性と colored soundness の定式化が更新された。
公開準備・高速化より先に、現行 infer の stack weight / row split がこの定式化に合っているかを直す。

実装メモ: `notes/design/2026-06-22-directed-stack-weight-implementation.md`

特に優先して見るもの:

- `ConstraintWeights` は左重みと右重みを別構造として扱う。
- `row_effect.rs` は row split 前に `weights.left.compose(&weights.right)` で左右を合成しない。
- row upper で消費できる head は `K ∩ Common(L)` だけ。
- residual key は `(source, J, L minus J)` を基準にし、target tail を含めない。
- `protect` は `PWeight(take(Empty), rho)` として扱い、専用保護集合を足さない。
- `filter` は static check で、runtime marker として扱わない。
- pop-growth cap は停止性側の暫定実装であり、型等式として扱わない。

## 直近の優先順位

0. hardening freeze を置き、`ref.update` 修正で得た不変量をテスト・文書・metrics へ固定する。
   - `docs/infer-solver-invariants.md` を solver 変更前の入口にする。
   - `std.control.var.ref.update` などの public signature golden test を先に足す。
   - metrics は opt-in の観測だけにし、最適化や clamp と混ぜない。
1. public regression suite を先に固める。
   - playground で見つけた例、effect/thunk/specialize2 の境界、concrete subtype mismatch を小さい fixture にする。
   - 今後の refactor と release 作業の足場になるため最優先。
   - 詳細: `notes/todo/testing.md`
2. `yulang-editor` を LS と playground の共有面に育てる。
   - token classification、diagnostics range、hover/type display を共有する。
   - playground だけ色や型表示がずれる状態をなくす。
   - 詳細: `notes/todo/language-server.md`
3. release / packaging を cargo 前提から外す。
   - 配布 binary、std bundle、cache/bootstrap、playground artifact、Zed/LS binary discovery を決める。
   - 詳細: `notes/todo/release.md`
4. realm/band と compiled-unit cache を pipeline に統合する。
   - source identity、artifact manifest、SCC cache、cross-realm dependency surface を整理する。
   - 詳細: `notes/design/source-realm-band-plan.md`, `notes/todo/static-analysis-speed.md`
5. 高速化は計測を先に置く。
   - phase timing、intern 候補、cache hit/miss、Rowan cost を測ってから触る。
   - 詳細: `notes/todo/static-analysis-speed.md`
6. Yumark は value model から決める。
   - syntax parse 済みの先、AST/IR/type/runtime/playground 表示を設計する。
   - 詳細: `notes/todo/yumark.md`

## 今すぐやる slice

2026-06-17〜2026-06-19 の control VM frame runtime / performance slice は
`tasks/done/2026-06-19-control-vm-frame-runtime-history.md` へ退避した。
現在のactive sliceはcanonical cache interface Option 1 Stage 3 boundary-aware import and
instantiationである。Stage 2のboundary capture、joint compact/freeze、poly arena freezeと
typed/runtime production handoffに続き、Stage 3 §6.1 Import onceまで完了した。次は§6.2で
scheme instantiationへpersistent `B` mappingをpreloadし、`Q/R`のper-use fresheningと`B`の
session共有を固定する。Markdownの`std-prefix-hit`化はStage 3完了だけでは成立せず、Stage 5の
non-empty artifact integrationとStage 7のfallback retirement判断まで待つ。

## 守る不変条件

- 型が決まらないから Top 相当へ逃がす処理は入れない。
- path / module / fixture 名の文字列比較で型を決めない。
- 再現ケースだけを通す局所分岐ではなく、一般規則として説明できる修正にする。
- infer に不動点計算のような重たい反復を足さない。まず一回の線形パスで設計する。
- テスト期待値を実装出力に合わせて書き換えない。
- effect row subtraction の shallow/deep handler 境界を後段の整形で潰さない。

## 外側の予定

- 相談先の先生への研究相談（effect row subtraction / handler hygiene の切り出し）は、
  2026-06-24 に送信済み。返信待ちの間は、新機能より hardening を続ける。
  相談素材は `notes/research/consultation/technical-brief.md` と公開 docs の
  `web/docs/reference/effects.md` / `web/docs/reference/type-theory.md` を正本として扱う。
- 2026 年 7 月以降は忙しくなる予定。12 月のアドベントカレンダーが公開目標。

## 旧 roadmap

2026-05-25 起点の post-native roadmap（monomorphize / runtime type surface、
static analysis speed、parser combinators、host IO、native backend の退役整理）は
`tasks/done/2026-05-25-post-native-roadmap.md` へ退避した。
そこに残る TODO は、archive の参照が必要なときだけ現行 crate へ拾い直す。
