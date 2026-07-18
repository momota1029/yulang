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

## 現在地（2026-07-18）: Yumark static core / thin path closeout

Yumark は algebra-passing production migration、lazy per-hover evaluation の LS live 接続、
structural blank-line / line-doc-continuation の言語意味論修正まで完了した。
現状と残件は `notes/todo/yumark.md`、設計と履歴の参照先は
`notes/design/2026-07-17-yumark-converged-design.md`、
`notes/design/2026-07-18-yumark-structural-boundaries.md`、
`notes/design/2026-07-08-yumark-value-model-tagless-final.md`、
`notes/bugs/2026-07-17-yumark-generalization-memory-exhaustion.md` とし、
このファイルには詳細を重複させない。

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

### Stage 3 boundary-aware import slice 2: §6.2 Scheme instantiate

session生成時に既存poly surfaceからseedしたscheme defをimported targetとして記録し、そのuseだけを
canonical instantiation入口へ流すようにした。`SchemeInstantiator`はsessionが保持するpersistent
boundary substitutionを借用してpreloadし、per-use mapには`Q`と`R`だけをfresh allocateする。
これにより、同じimported schemeの複数useで`Q/R`は別のinfer `TypeVar`へ写り、`B`だけが同じ
session-level targetを共有する。recursive boundsはfreshened `R`へuseごとにcloneするが、boundary
boundsは§6.1のsession初期化以外ではreplayしない。

canonical schemeはclone前にread-only closure scanで一度だけ検証し、結果をimported def単位で
memoizeする。`Q ∪ R ∪ B`に属さないfree `TypeVar`は`UnmappedFreeTypeVar`、preloaded `B`とper-use
binderの衝突は`BoundaryBinderIsPerUse`という構造化errorにする。source `TypeVar`をそのままtargetへ
返すfallbackはcanonical routeでは使わず、拒否されたschemeはuse constraintを部分投入しない。
suffix内でgeneralizeされたlocal schemeとcast用schemeは従来の非canonical入口を維持する。

focused testでは同じdefを2回actual `AnalysisSession::instantiate_use`へ通し、tuple witnessから
`Q/R`がuseごとに異なり`B`がpersistent mappingと一致することを直接確認した。否定系では未知の
free variableが構造化errorになり、use側にlower boundが追加されないことを固定した。確認結果は
infer interface oracle 9 passed、instantiate関連9 passed、infer全体583 passed / 既知の
`mark_expr_block_*` 5 failed、std-prefix regression 5 passedである。

次sliceは§6.3 Role candidate fresheningである。candidate-local head variableを従来どおりfreshenしつつ、
同じpersistent boundary substitutionをcandidate importerへpreloadし、scheme occurrenceとimpl
prerequisite occurrenceの`B`が同じinfer variableを指すことをfocused witnessで固定する。
Markdownの`std-prefix-hit`化は引き続きStage 5のnon-empty artifact integrationとStage 7のfallback
retirement判断まで待つ。

### Stage 3 boundary-aware import slice 3: §6.3 Role candidate freshening

session初期化で既存poly surfaceのrole impl candidateをinfer arenaへfreshenする入口に、§6.1/§6.2と
同じpersistent boundary substitutionを借用preloadした。`SchemeInstantiator::clone_var`は
candidateごとのlocal mapping、preloaded boundary mapping、fresh unmappedの順に解決する。これにより
candidate-local head variableは従来どおりfreshになり、candidateのhead / associated type /
prerequisiteに現れる既知の`B`だけがscheme occurrenceと同じsession-level infer variableを指す。

candidateに対するstrict unmapped errorはこのsliceでは追加していない。prerequisite-only variableの
binder解釈とcanonical candidate closureはStage 4の責務であり、Stage 3で先に拒否すると既存の
pre-Stage 4 candidate semanticsを変えるためである。focused characterizationでは、この種のunmapped
prerequisite variableがsource IDを流用せず従来どおりfreshになることを固定した。candidate closureの
拒否はStage 4でhead bindersと`B`の分類が完成した後に行う。

この変更はStage 3専用の別経路だけには閉じていない。`freshen_role_impl_candidate`は
`AnalysisSession`生成時点のpoly arenaにある全role candidateへ一度ずつ適用されるため、既存の
std-prefixを含むfinalized poly surfaceのcandidate freshening全体に及ぶ。一方、source lowering中に
新規作成されて直接infer tableへ入るcandidateは対象外である。空boundaryでは従来と同じ全var fresh、
non-empty boundaryでもtableに明示された`B`だけを共有し、他のvarはすべて従来どおりfreshになる。

focused testは、actual session lifecycleでscheme useとimpl prerequisiteの`B`が同じmappingを指し、
candidate headが別のfresh varになることを直接確認した。確認結果はinfer interface oracle 9 passed、
instantiate関連9 passed、role関連57 passed、infer全体585 passed / 既知の`mark_expr_block_*` 5 failed、
std-prefix regression 5 passedである。

次sliceはStage 3 Exit witnessである。§6.1〜§6.3で作ったsession mapping、2回のscheme instantiation、
scheme / candidate間の`B`共有を一つのtest-only witnessへまとめ、Stage 3 exit条件のOracle Aを確認する。
production artifact integrationには進まない。Markdownの`std-prefix-hit`化は引き続きStage 5の
non-empty artifact integrationとStage 7のfallback retirement判断まで待つ。

### Stage 3 boundary-aware import exit: Oracle A1 binder lifetime witness

Stage 3の出口条件とStage 5のartifact integrationの前後関係に循環が見つかったため、Claude Sonnet 5と
ユーザの2026-07-11承認に基づきOracle Aを二つのgateへ分割した。Stage 3のOracle A1は、in-memoryで
構築した`CompiledBoundaryInterface`をfresh sessionへseedし、import / instantiationのbinder lifetimeを
直接検証する。production compiled-unit artifactの正規encode/decodeと、decode後のfresh session importを
検証するOracle A2は、non-empty artifactを有効化するStage 5の出口条件へ移した。これはvalidationの
削除ではなく、Stage 5で初めて成立するproduction decoder前提を正しいstageへ割り当て直したものである。

Oracle A1の統合witnessでは、同じimported defを2回instantiateし、`Q`と`R`がuseごとに別のinfer
`TypeVar`へfreshenされる一方、`B`は両useで同じsession-level mappingを指すことを一つのfixtureで確認した。
同じsessionにimportされたrole candidateについても、candidate-local headはfreshになり、prerequisiteの
`B`がscheme occurrenceと同じinfer `TypeVar`を指すことを直接固定した。これにより§6.1 Import once、
§6.2 Scheme instantiate、§6.3 Role candidate fresheningを束ねたStage 3 exit条件は完了した。

確認結果はExit witness 1 passed、infer interface oracle 9 passed、instantiate関連9 passed、role関連
57 passed、infer全体586 passed / 既知の`mark_expr_block_*` 5 failed、std-prefix safety 6 passed、
std-prefix CLI regression 4 passedである。次はStage 4 principal impl prerequisite interfaceで、
prerequisite-only変数のbinder分類、candidate head / prerequisiteのjoint canonicalization、canonical
candidate closureを実装する。Markdownの`std-prefix-hit`化は引き続きStage 5のnon-empty artifact
integration / Oracle A2とStage 7のfallback retirement判断まで待つ。

### Stage 4 principal impl prerequisite slice 1: candidate binder inventory

Stage 4は、(1) candidate head / associated anchorと既知`B`に対するbinder inventory、(2) headと全
prerequisiteを一つのcomponentとして扱うper-candidate joint compact normalization、(3) centerless
invariant headを保ったstructural freezeとprerequisite sort/dedup、(4) head binders + `B` closureの
validation / runtime handoff、の順に分解する。candidate searchやrecursive prerequisite dischargeは
freeze中に行わず、candidateごとに一回のnormalizationだけを許す。

最初のsliceでは、infer arena上のraw candidateを次sliceへそのまま保持する
`CapturedCandidateInterface`を追加した。head inputsとassociated typesに現れる変数から既知のunit
boundary bindersを除いたものをcandidate-local head binderとし、head / prerequisite全体に現れる既知
`B`をcandidate boundary inventoryとして記録する。headにも既知`B`にも属さないprerequisite-only
variableは、便宜的にquantify / boundary化せず`prerequisite_only` inventoryへ明示的に残す。この段階で
rejectするとnormalizationで正当に消えるvariableまで早期拒否するため、構造化
`UnboundCandidateVariable`への変換は次sliceのjoint normalization後にだけ行う。このcaptureはrole
resolution、candidate simplification、constraint追加を一切行わない。

このhelperは新しいStage 4 captureとfocused testsだけに閉じており、既存のrole solve、
`collect_role_impl_member_prerequisites`、`finalize_poly_role_impls`、Stage 3 candidate fresheningにはまだ
接続していない。正常系はhead-localとscheme由来の共有`B`をhead / prerequisite横断で分類できること、
否定系はprerequisite-only varをbinderへ誤分類せずunclassified inventoryへ残すことを直接確認した。
確認結果はcandidate capture
2 passed、infer interface oracle 9 passed、instantiate関連9 passed、role関連57 passed、infer全体
588 passed / 既知の`mark_expr_block_*` 5 failed、std-prefix safety 6 passed、std-prefix CLI regression
4 passedである。

次sliceは、captured candidateのheadと全prerequisite、および共有`B`のbound carrierを一つのcompact
componentへ入れ、既存のfloor / co-occurrence / sandwich / polarity simplificationを一回だけ適用する
per-candidate joint normalizationである。substitution後にhead / `B` inventoryを書き直してclosureを
再検証する。candidate-only variableのunit ownershipを既存level / sharing decisionから導けないケースに
遭遇した場合は、仕様§7.3 / §13どおりbinder意味を推測せず設計判断のため停止する。Markdownの
`std-prefix-hit`化は引き続きStage 5のnon-empty artifact integration / Oracle A2とStage 7のfallback
retirement判断まで待つ。

### Stage 4 principal impl prerequisite slice 2: joint candidate normalization

仕様§13.4のprerequisite-only binder意味について、Claude Sonnet 5とユーザの2026-07-12承認により
strict canonical rejectionを採用した。joint normalization後もhead binderにも既知のunit `B`にも属さない
variableが残るcandidateは`UnboundCandidateVariable`として非canonicalにし、cache routeではなく既存の
full-compile fallbackへ倒す。証明できないinterfaceをcacheしないという既存方針に揃えたもので、暗黙の
quantification、candidate-only `B`への昇格、existential binderの新設は行わない。provenance追跡は
Stage 6計測でstrict gateによる実害が確認された場合だけ将来再検討する。

slice 2では`CapturedCandidateInterface`の各candidateについて、raw head、全prerequisite、candidateが
直接参照する`B`から到達可能なboundary bound carrierを同じcompact role componentへ入れた。既存の
floor interval equality、floor variable sandwich、floor redundant elimination、co-occurrence / sandwich /
polarity simplificationをcandidateごとに一回だけ適用し、merge / dominance constraintが通常pipelineで
未適用なら既存`FreezeProducedConstraint`で拒否する。candidate search、recursive prerequisite discharge、
retry loop、boundary protectionは追加していない。

normalization後は実際のcompact head / prerequisites occurrenceとnormalized substitutionから
`head_binders` / `boundary`を再構築する。slice 1時点でprerequisite-onlyだったaliasがhead binderへ
coalesceした正常系では、inventoryとcompact prerequisiteの両方が新representativeへ書き換わることを
確認した。invariantなprerequisite-only varが生存する否定系では、candidateの`impl_def`・role path・varを
持つ`UnboundCandidateVariable`を直接確認した。

このnormalizerはStage 4 helperとfocused testsだけから呼ばれ、既存のrole solve、candidate compact
cache、`collect_role_impl_member_prerequisites`、`finalize_poly_role_impls`、Stage 3 importには未接続である。
確認結果はcandidate capture / normalization 4 passed、infer interface oracle 9 passed、instantiate関連
9 passed、role関連57 passed、infer全体590 passed / 既知の`mark_expr_block_*` 5 failed、std-prefix
safety 6 passed、std-prefix CLI regression 4 passedである。

次sliceはcanonical candidate freeze / orderingである。normalized headとprerequisitesをcenterless invariant
intervalのままpoly arenaへstructural freezeし、associated typesをname順、prerequisitesをbinder-normalized
structural key順にsort / dedupする。candidate methodsとhead / prerequisite間の共有var identityを保持し、
closure validator / runtime handoffへの接続はその次のsliceに残す。Markdownの`std-prefix-hit`化は引き続き
Stage 5のnon-empty artifact integration / Oracle A2とStage 7のfallback retirement判断まで待つ。

### Stage 4 principal impl prerequisite slice 3: canonical candidate freeze / ordering

candidate failureの粒度はunit batch全体のstrict rejectionを維持した。現行compiled-unit artifactから失敗
candidateだけを除くと、prefixで定義されたimplがsuffixのrole resolutionから消えてfull compilationとの
意味論が変わりうる。semantics-preservingなper-candidate fallback / overlayは存在しないため、全candidateの
canonical orderingを検証してから一括freezeし、どれか一つでも失敗したら既存full-compile routeへ倒すのが
現在のartifact粒度で安全な判断である。

slice 3では`NormalizedCandidateInterface`を`FrozenCandidateInterface`へstructural freezeする入口を追加した。
headとprerequisiteのassociated typesをname順へ揃え、head binderとunit `B`を別ordinal namespaceへ二段
remapしたcompact structural fingerprintをprerequisite keyとして一度だけ計算し、sort / dedupする。同じ
fingerprintでstructural keyが異なる衝突は`NonCanonicalCandidateOrdering`としてbatchを拒否するため、hash
collisionで順序や意味を黙って選ばない。

freezeはcompact boundsをstack-weight type argumentごとpoly arenaへremapした後、`Neu::Bounds(lower,
upper)`ならそのcenterless pairをそのまま`RoleConstraintArg`へ使う。exact neutral shapeも正負へ構造的に
projectするだけでcenter varを新設しない。candidate methodsは無変更で移し、TypeVar identityをremapしない
ためhead / prerequisites間の共有binder identityも保持する。全candidateのorderingをpoly arena変更前に
確定するので、batch error時に一部candidateだけがfreezeされることもない。

focused witnessでは同じnormalized candidateのprerequisite入力順を逆転して別poly arenaへfreezeしても
出力が完全一致し、duplicate prerequisiteが一件へ縮約され、head / prerequisite associatedがname順、
methodsと共有TypeVarが保持され、head intervalが`Pos::Var` / `Neg::Var`のcenterless pairであることを直接
確認した。別の否定witnessでは一つのunbound candidateがclosed candidateを含むunit batch全体を拒否する
呼び出し規約を固定した。

このfreeze helperもStage 4 focused testsだけから呼ばれ、既存のrole solve、candidate cache、
`finalize_poly_role_impls`、compiled runtimeには未接続である。確認結果はcandidate capture / normalization /
freeze 6 passed、infer interface oracle 9 passed、instantiate関連9 passed、role関連57 passed、infer全体
592 passed / 既知の`mark_expr_block_*` 5 failed、std-prefix safety 6 passed、std-prefix CLI regression
4 passedである。

次sliceはStage 4最後のclosure validation / handoffである。scheme / boundary draftとfrozen candidatesを一つの
canonical draftへ統合し、poly arena上でもcandidate varsがhead binders + `B`に閉じること、candidateの
共有`B`がunit boundary tableを参照することをvalidatorで再確認して、typed/runtime共通handoffへ渡す。
Stage 5のartifact有効化自体には進まない。Markdownの`std-prefix-hit`化は引き続きStage 5のnon-empty
artifact integration / Oracle A2とStage 7のfallback retirement判断まで待つ。

### Stage 4 principal impl prerequisite slice 4: closure validation / common handoff

Stage 2のscheme / boundary draftとStage 4のfrozen candidate batchを
`CanonicalCacheInterfaceHandoffDraft`へ一度だけ束ねるhandoffを追加した。handoff消費前に、同じpoly arena上の
candidate headと全prerequisiteをStage 0のmemoized `ClosureScan`で一回走査し、実際の変数集合がcandidate
head binders + unit `B`へ閉じることを再検証する。candidateが宣言する`B` inventoryは実際のcandidate内の
unit-boundary occurrenceと完全一致しなければならず、unit tableにない`B`、未閉包変数、binder inventory
不一致、未束縛`SubtractId`はすべて構造化errorでunit batch全体をfail-closedにする。

validator成功後にだけ、既存のone-shot scheme / boundary freezeを同じpoly arenaへ適用し、frozen candidate
batchで`poly.role_impls`を一括置換する。これによりtyped/runtime共通handoffが受け取る一つのarena内で、scheme
occurrence、candidate head / prerequisite、unit boundary tableが同じ`TypeVar` identityを共有する。validatorは
role resolution、scheme instantiation、constraint mutation、追加simplificationを行わず、新しい反復も持たない。
失敗はscheme / candidateを書き込む前に判定するため、非canonical unitが部分的にhandoffされることもない。

focused統合witnessでは、同じopen `B`がscheme predicate、candidate head、candidate prerequisite、compiled
boundary entryのすべてで同じ変数になることと、candidate batchがpoly arenaへ実際にinstallされることを直接
確認した。対称な否定witnessではcandidateの`B` inventoryを欠落させ、
`CandidateBinderInventoryMismatch`でscheme / candidate write前に拒否されることを固定した。

このhandoffはStage 4 focused testsだけから呼ばれ、既存のrole solve、candidate生成、通常の
`finalize_poly_role_impls`、compiled artifact構築にはまだ接続していない。そのため既存経路の意味論・性能には
波及しない。確認結果はhandoff focused 2 passed、candidate capture / normalization / freeze 6 passed、infer
interface oracle 9 passed、instantiate関連9 passed、role関連57 passed、infer全体594 passed / 既知の
`mark_expr_block_*` 5 failed、std-prefix safety 6 passed、std-prefix CLI regression 4 passedである。

これでStage 4 principal impl prerequisite interfaceは完了した。次はStage 5 artifact integrationで、この共通
handoffをproduction compiled-unit構築へ接続し、non-empty boundary / candidate artifactのencode/decode、fresh
session import、Oracle A2、Oracle Bを有効化する。Stage 5はMarkdown経路の実速度差をproduction artifact上で
初めて観測できる段階だが、恒久的な`std-prefix-hit`要求とprogram-sensitive fallbackの退役判断は引き続き
Stage 7まで行わない。

### Stage 5 artifact integration slice 1: one canonical draft for both surfaces

Stage 5は仕様のChanges列に沿い、(1) scheme / boundary / candidateを一つのcanonical draftからtyped/runtime
両surfaceへ渡す、(2) non-empty boundary artifactのfingerprint / format / encode/decodeを有効化する、(3)
production envelope往復とfresh-session importを通すOracle A2、(4) 明示的`std-prefix-hit`でsuffix
scheme/candidate alpha同値とruntime同値を確認するOracle B、(5) merge / malformed artifact rejection、の5sliceに
分ける。Stage 5全体の出口はOracle A2とOracle Bであり、offline structural validation以外のsolver loopは
追加しない。

既存warm-route regressionを監査した結果、safe role canaryとminimal std-prefix reuseは
`std-prefix-hit`、HTML Yumarkは`full-miss`を明示assertしている。一方、
`compatible_std_prefix_cache_boundary_yumark_workloads_hold`のMarkdown分岐は`full-miss`と
`std-prefix-hit`の両方を許すため、このtestのpassだけではwarm route成功を証明できない。現在までの実測も
Markdownは`full-miss`である。Stage 5 Oracle Bではこの既存許容を成功根拠にせず、routeを
`std-prefix-hit`へ固定する専用witnessを必須とする。

slice 1では`AnalysisSession::prepare_cache_interface_handoff`を追加し、export対象schemeを決めた後、unit
boundaryを一度だけcaptureして、その同じpre-normalization `B` tableからscheme / boundary draftとnormalized
candidate batchを作るようにした。`CompiledCacheInterfaceSurfaces::from_lowering`は一つのpoly cloneへcandidateを
structural freezeし、Stage 4のclosure handoffでcandidateとscheme / boundaryをjoin / validate / installしてから、
同じarenaとboundaryをtyped/runtimeへ分岐する。boundary再capture、surface別freeze、candidate search、追加
simplification、新しい反復はない。

正常系witnessではopen `B`を持つexported schemeとclosed role candidateを同じloweringに置き、typed/runtimeの
type arenaとboundaryが完全一致し、runtime arenaへcanonical candidateが保持されることを確認した。否定系では
prerequisite-only変数を持つcandidateを注入し、common surface構築が`UnboundCandidateVariable`でunit batchを
拒否し、source lowering arenaへcandidateをinstallしないことを確認した。

このconstructorは依然としてinfer crate内のfocused testsだけから呼ばれ、`crates/yulang/src/cache.rs`の現行
artifact writerはempty boundaryをtyped/runtimeへ別途渡す旧経路のままである。したがって今回のsliceはStage 5
専用handoffに閉じ、既存std-prefix cache route、artifact format/fingerprint、conservative fallbackの意味論・
性能には波及しない。確認結果はcommon handoff 2 passed、infer interface oracle 9 passed、instantiate関連9
passed、role関連57 passed、cache interface関連7 passed、infer全体595 passed / 既知の
`mark_expr_block_*` 5 failed、std-prefix safety 6 passed、std-prefix CLI regression / characterization 5 passedで
ある。

次sliceはStage 5の(2) non-empty boundary artifact有効化である。canonical structural fingerprint、cache format
bump、typed/runtime fingerprint agreement、production writer/decoderのfail-closed接続を実装する。Oracle A2 / B、
merge / malformed tests、fallback retirementにはまだ進まない。

### Stage 5 artifact integration slice 2a: conservative non-empty boundary structural fingerprint

Stage 5のnon-empty artifact有効化は、(2a) arena-aware canonical structural key / fingerprint、(2b) cache
format bumpと旧format miss、(2c) typed/runtimeのexact structural-key agreement、(2d) production writer / decoder
接続、へさらに分割した。このsliceでは(2a)だけを実装し、format、manifest、writer、decoder、fallbackは変更して
いない。

任意のmutually-recursive `B` graphの完全なalpha canonicalizationは仕様§13でpartition refinementとcanonical
SCC encodingのどちらを採るか未確定であり、単純なbinder permutationは禁止されている。そのため(2a)は、各
boundary entryを「宣言binder = local ordinal 0、ほかの`B`は構造上の初出順」でarena ID非依存にmemoized
encodeし、そのexact structural root keyが全entryで一意な場合だけsortする保守的方式を採った。sort後に
unit全体のcanonical ordinalを再割当てして二段目のexact keyを作り、そこから既存と同じFNV fingerprintを得る。
raw `TypeVar`、`PosId` / `NegId` / `NeuId`、入力table順はfingerprintへ入らない。

重複binder、unit `B`外のfree variable、invalid arena ID、未設計のnon-empty stack weight、同一local root keyを
持つ対称 / 曖昧graphは`None`でfail-closedにする。特に、現在未確定のrecursive graph canonicalizerを不完全な
partition refinementで代用しない。2cではtyped/runtimeのexact keyを先に比較してからu64 fingerprintを採用し、
hash collisionだけで異なるsurfaceを一致扱いしない必要がある。

focused正常系ではbinder ID、arena先頭のpadding node数、boundary entry順をすべて変えたalpha同値tableが同じ
fingerprintになり、同じ入力の反復計算が決定的で、empty tableのfingerprintが従来v1値と完全一致することを
確認した。否定系ではconstructor構造差が異なるfingerprintになり、二つの対称なself-bound rootが曖昧として
`None`になることを固定した。既存のpre-boundary format miss、typed/runtime fingerprint mismatch、manifest
mismatch testsも通り、旧artifactがクラッシュせず安全側へ倒れる経路を維持している。

新しいarena-aware APIはcrate-internalで次sliceまでproduction未接続である。補助encoderも理由付きの限定的な
dead-code境界へ置き、`cargo check -p infer`がwarningなしで通ることを確認した。確認結果はfingerprint focused
2 passed、infer interface oracle 9 passed、cache interface関連7 passed、infer全体597 passed / 既知の
`mark_expr_block_*` 5 failed、std-prefix safety 6 passed、std-prefix CLI regression / characterization 5 passed、
既存cache fail-closed focused 3 passedである。

次は(2b) cache format bump / old-format missである。ただしproduction writer / decoder接続は(2d)まで行わず、
empty-boundaryの意味とrouteを変えない。2026-07-12にClaude Sonnet 5とユーザは、対称 / 曖昧なboundary
graphを恒久的に`None`によるcache missへ倒す保守的方針を確認した。完全なcanonical SCC方式はStage 6の計測で
この拒否が実際のcache miss頻発原因だと判明した場合だけ将来検討する。

### Stage 5 artifact integration slice 2b: cache format 19 / old-format miss

compiled-unit cache formatを18から19へbumpした。format 19はnon-empty boundary artifactを受け入れるための
schema世代を示すが、production writer / decoderはまだ(2d)未接続であり、このsliceが実際に書くboundary payloadは
従来どおりemptyのままである。manifest / typed/runtime fingerprint agreement、conservative fallbackの判定も
変更していない。

decoderは先頭のformat wordをpayloadより先に検査し、旧empty-boundary-only format 18、pre-boundary format
17、未知のversionをすべて非互換cache missとして返す。format word自体がtruncate / corruptされてu32として
読めない場合もpanicやdecode errorにせずmissへ倒す。一方、format 19と宣言した後のpayload破損は従来どおり
構造化された`CacheError::Decode`であり、version非互換とcurrent schema破損を混同しない。既存のversion 18
on-disk artifactは更新後の初回だけ意図的にmissとなり、新しく生成したversion 19 artifactは同一schemaで通常の
build / hit対象になる。

focused testではformat 19 envelopeのmanifest / syntax surface byte round trip、full version 18 envelopeと
version 17 envelopeのmiss、未知versionとtruncateされたformat wordのmiss、disk cache readでのversion 18 missを
直接確認した。既存std-prefix CLI regression / characterizationは5 passedで、新しいversion 19を使うfresh cacheの
empty-boundary build / hit挙動は不変である。確認結果はinfer interface oracle 9 passed、cache interface関連7
passed、infer全体597 passed / 既知の`mark_expr_block_*` 5 failed、std-prefix safety 6 passed、compiled-unit
format focused 4 passed、std-prefix CLI regression / characterization 5 passedである。

次は(2c) typed/runtimeのexact structural-key agreementである。u64 fingerprint一致だけでsurface同一性を判断せず、
arena-aware canonical structural keyを比較してからartifact fingerprintを採用する。(2d) production writer /
decoder接続、Oracle A2 / Bにはまだ進まない。

### Stage 5 artifact integration slice 2c: typed/runtime exact structural-key agreement

slice 1のcommon handoffは一つのpoly arenaをtyped/runtimeへ分岐するため、生成直後の両surfaceは同じtype graphを
持つ。しかしartifactではtyped側の`CompiledTypeArena`とruntime側の`PolyArena.typ`が独立にserializeされ、decode
やmergeでは別々のarenaとして再構築される。このsliceのagreementは生成時の冗長assertではなく、malformed /
corrupt artifactや将来の独立remapをu64 hash collision込みでfail-closedにするproduction decode前契約である。

`CompiledTypedSurface::boundary_fingerprint_agreeing_with_runtime`を追加した。これは各surfaceの所有arenaから
`CompiledBoundaryInterface::canonical_structural_key`を独立に作り、`Vec<u8>`の完全一致を確認した後だけ共通keyを
FNV fingerprintへ縮約する。key不一致、一方のinvalid arena参照、unit外free variable、対称 / 曖昧graphは
`None`となる。raw canonical key自体はcrate-privateのままにし、yulang crateの(2d) production decoderが誤って
u64同士だけを比較しないよう、surface-level agreement methodだけをpublic APIとして追加した。新しいsolver
iteration、arena mutation、fallback緩和はない。

focused witnessでは、raw binder ID、arena padding、boundary entry順が異なるtyped/runtime独立arenaから同じexact
keyが得られて同じfingerprintが受理されることと、constructor payload構造が異なる場合にkey不一致をhash前に
拒否することを直接確認した。確認結果はagreement focused 1 passed、既存non-empty fingerprint 2 passed、infer
interface oracle 9 passed、cache interface関連7 passed、infer全体598 passed / 既知の`mark_expr_block_*` 5
failed、std-prefix safety 6 passed、std-prefix CLI regression / characterization 5 passedである。

このmethodはまだproduction cacheから呼ばれず、既存empty-boundary routeとartifact accept/reject判定には波及
しない。次は(2d) production writer / decoderのfail-closed接続で、format 19のnon-empty boundary payloadを実際に
生成し、このexact agreementをmanifest fingerprint採用前に必須化する。Oracle A2 / Bにはまだ進まない。

### Stage 5 artifact integration slice 2d: production writer / decoder fail-closed connection

2026-07-12にClaude Sonnet 5とユーザは、prefix-only writerとsuffix-dependent safety gateを独立させる方針を
確定した。writerはprogram reuse判定を待たずcanonical handoffを一度だけ試し、capture / candidate closure /
exact structural-key agreementが成功した場合はnon-empty boundaryのtyped/runtime pairを保存する。いずれかが
失敗した場合は、従来と同じempty boundary pairを保存する。suffixに応じてartifact内容を変える二段writerは
採用しない。

production `compiled_unit_artifact_from_lowering_with_syntax_and_key`をこの入口へ接続した。infer crateからはprivateな
`CompiledCacheInterfaceSurfaces::from_lowering`と`BoundaryCaptureError`を露出せず、artifact-readyなexact agreement
済みpairだけを返す`canonical_cache_interface_surfaces_from_lowering`を最小public wrapperとして追加した。
decoder、manifest、mergeはすべて`boundary_fingerprint_agreeing_with_runtime`を共通入口にし、format 19のnon-empty
payloadもcanonical keyがbyte完全一致した後だけmanifest fingerprintとして受理する。

focused正常系ではexpansive exported valueからnon-empty artifactを実際にencode / decodeし、runtime boundaryだけを
emptyへ改変してruntime hashを更新してもexact-key mismatchでcache missになることを確認した。否定系では
prerequisite-only変数を持つcandidateを注入し、canonical closure失敗後にempty artifactがdiskへwrite / readできる
ことを確認した。compiled-unit cache focusedは10 passed、infer interface oracle 9 passed、cache interface関連7
passed、infer全体598 passed / 既知の`mark_expr_block_*` 5 failed、std-prefix safety 6 passed、std-prefix CLI
regression / characterization 5 passedである。

`std_prefix_cache_safety.rs`と`main.rs`のreuse gate呼び出しは無変更である。fresh cache実測はseedが
`std-prefix-build` (`run.total` 5.929秒)、Markdownが`full-miss` (`run.build_poly` 32.588秒、`run.total`
33.930秒)、HTMLが意図どおり`full-miss` (`run.build_poly` 6.128秒、`run.total` 7.451秒)だった。Markdownのsafety
判定自体は従来どおりsafeだが、(2d)完了時点では後続warm import経路がhitを成立させていない。次はStage 5の
Oracle A2 production encode/decode/fresh-session-import witnessで、どのimport前提が残っているかを固定する。Oracle B
とfallback retirementにはまだ進まない。

### Stage 5 Oracle A2: production artifact round trip

Oracle A2の6段階を一つのproduction integration witnessへ固定した。value-restriction boundary `B`を持つexported
scheme、通常のquantifier `Q`を持つexported identity scheme、recursive bound `R`を持つprivate finalized scheme、
head-local binderと共有`B` prerequisiteを持つrole candidateを同じlowering fixtureへ置く。test-onlyの`R`は
finalized poly schemeへ直接構築するが、その後はほかのbinderと同じproduction writer、format 19
encode/decode、runtime arena importを通り、raw envelope decodeやsynthetic boundary importで代用しない。

pre-serialization canonical artifactから各schemeの期待`SchemeAlphaView`を作り、実byte round trip後のruntime
surfaceから元のloweringとは別の`AnalysisSession::new_with_imported_boundary`を作る。suffix constraint追加前に
同じschemeを2回instantiateし、decode前後のalpha view一致、各useのalpha view一致、`Q/R`のper-use freshness、
`B`のsession-level共有、scheme occurrenceとcandidate prerequisite occurrenceの`B`一致、candidate-local head
binderのfresheningを直接確認する。これで仕様§9.3のOracle A2を完了した。

production instantiatorのclone処理を共通化したが、通常入口が返すcompactなpredicate / role predicatesとconstraint
追加順は変えていない。recursive-bound metadataはOracle入口だけが収集する。import時に一度cloneしたboundary
boundsはsession substitutionへ保持し、witnessが実際のtarget arena上で`SchemeAlphaView`とQ/R/B inventoryを作れる
ようにした。yulangからfresh-session直後を観測するため、runtime surfaceへ`#[doc(hidden)]`の構造化Oracle APIを
追加したが、production warm loweringとcache routeからは呼ばれない。safety gate、writer、decoder、artifact schema、
fallback判定の変更はない。

確認結果はOracle A2 focused 1 passed、Stage 3 Oracle A1 augmented witness 1 passed、infer interface oracle 9 passed、
cache interface関連7 passed、instantiate関連9 passed、infer全体598 passed / 既知の`mark_expr_block_*` 5 failed、
std-prefix safety 6 passed、std-prefix CLI regression / characterization 5 passedである。

次はStage 5 Oracle Bである。cold full-sourceと明示的`std-prefix-hit` warm routeのsuffix scheme / candidate alpha同値、
runtime結果、routeを一緒に固定する。Markdownは現時点では引き続き`full-miss`であり、Stage 5 Oracle BとStage 7の
program-sensitive fallback retirement判断より前にwarm成功とは扱わない。

### Stage 5 Oracle B: cold/warm suffix-result equivalence control and Yumark blocker

Oracle Bの比較機構を、まず小さいclosed suffix fixtureで実装した。prefix artifactはproduction writerで構築後、
実cache formatのbyte encode/decodeを通す。cold full-source buildとそのprefixを使ったwarm buildの
`CompiledNamespaceSurface`から、suffix valueをmodule path / exported nameで対応付け、両compiled runtime surfaceの
unit boundary tableを含む`SchemeAlphaView`を比較する。candidateはheadを専用marker付きrole predicate、全
prerequisiteを通常role predicateへ写した一つのsynthetic schemeとして構造化し、head binderとprerequisite内の
共有identityを同じalpha namespaceで比較する。candidate methodはrequirement / implementation labelと、candidate
head binderを明示的に閉じたmethod scheme alpha viewで比較する。raw `DefId` / `TypeVar` / arena node IDは同値判定に
使わない。

新設`std_prefix_oracle_b_small.yu`はsuffix-owned quantified identity、selected exported scheme、closed role
candidateとmethodを持つ。direct cold/warmではschemeとnon-empty candidate batchがalpha同値になり、実CLIではcold
route `disabled`、warm route `std-prefix-hit`を明示assertし、runtime resultも双方`run roots [42]`で一致した。
これによりOracle B harness自体がsilent full-missに依存せず動くことは確認できた。

一方、mandatory Yumark Markdown fixtureは引き続き`full-miss`である。2026-07-12の再実測は
`run.build_poly=31.784s`、`run.total=33.062s`だった。原因はsuffixの`where`付きimplにより
`std_prefix_cache_safety`がopen-boundary scanを実行し、現行`scheme_has_open_boundary`がformat 19の
`CompiledBoundaryInterface`を閉包binderとして参照せず、canonical `B`を未量化free variableとしてopen判定する
ためである。変更禁止のsafety gateは一切触らず、従来`full-miss` / `std-prefix-hit`の両方を許していたMarkdown
regressionを現在の事実である`full-miss`明示assertへ変更した。HTMLも非alpha同値caseとして引き続き
`full-miss`を明示assertし、golden runtime outputを維持している。

確認結果はsmall Oracle B focused 1 passed、Markdown blocker focused 1 passed、std-prefix CLI suite 7 passed、
infer interface oracle 9 passed、std-prefix safety 6 passed、infer全体598 passed / 既知の
`mark_expr_block_*` 5 failedである。production code、public API、safety gate、cache artifact schemaへの変更はない。

したがってOracle Bの比較・route witness機構とsafe controlは完成したが、仕様§9.4 / Stage 5 exitが要求する
Markdownの明示的`std-prefix-hit`は未達で、Oracle B全体はblockedのままである。次の設計判断は、Stage 7の
fallback retirementまで待つ既存計画を維持するか、Stage 5 exitを満たすためcanonical boundary-aware safety判定を
別sliceとして先行させるかである。今回の絶対条件に従い、どちらも選ばず停止する。merge / malformed artifact
testsにも進まない。

### Stage 6 slice 1: std-prefix boundary table size telemetry

Stage 6は、(1) boundary table sizeとcanonical validator cost / outcome、(2) cold/warm role-resolution timeと
candidate expansion counter、(3) routeを変えないfallback shadow result、(4)反復計測が安定した後だけ導入する
performance threshold、の順に分ける。wall clockは補助値とし、route assertionとsolver / structural counterを
主指標にする。Stage 7のsuffix CST scan / fallback retirementは、これらのevidenceとユーザの明示判断まで行わない。

最初のsliceでは`--runtime-phase-timings`の`RuntimePhaseTimings`へoptionalな
`run.cache_interface.std_prefix_boundary_entries`を追加した。std-prefix artifactをreadまたはbuildした直後、
program-sensitive safety gateを呼ぶ前にruntime boundary entry数を記録する。このため`std-prefix-build` / hit /
gate reject後の`full-miss`のいずれでもgateが実際に見たartifact sizeを観測できる。timing flagなしの出力、artifact
内容、writer / decoder、route selection、safety判定には変更がない。

focused witnessではempty minimal stdがbuild / hitともentries `0`、value-restricted exported schemeを持つcustom
stdがbuild / hitともentries `1`となり、metricがempty/non-emptyを区別しcache round trip後も安定することを確認した。
一方、実repository std prefixはentries `0`だった。これはStage 5時点の「non-empty canonical Bをlegacy gateが
読まない」という診断だけでは説明を閉じられない。ただしsize telemetry単独では、canonical handoffが成功して
export boundaryを空と判断した場合と、構造的失敗からwriterのlegacy empty pairへfallbackした場合を区別できない。
確定したのはpersisted repository std boundaryが空という事実だけである。したがって現時点でsafety gateを退役
させる根拠はなく、Stage 7へ進んではならない。

確認結果はboundary metric focused 4 passed、std-prefix CLI suite 8 passed、infer interface oracle 9 passed、
std-prefix safety 6 passed、infer全体598 passed / 既知の`mark_expr_block_*` 5 failedである。Markdownの
gate-rejected `full-miss`でもentries `0`が出ることを確認し、metricがsafety判定前のartifact観測であることも
固定した。

次sliceはcanonical validator / handoffのcostと構造化failure outcomeのshadow telemetryである。writerのfallback
意味論は変えず、repository stdがどのclosure / candidate / fingerprint理由でemptyへ倒れるかを計測可能にする。
その後にrole-resolution counterとfallback shadow比較へ進む。performance thresholdはまだ設定しない。

### Stage 6 slice 2: canonical handoff cost and structured failure telemetry

既存の`canonical_cache_interface_surfaces_from_lowering -> Option`は互換入口として残し、観測専用の
`canonical_cache_interface_surfaces_from_lowering_observed -> Result`を`#[doc(hidden)]` public APIとして追加した。
内部`BoundaryCaptureError`自体はcrate外へ露出せず、stableなfailure kindとoptional `def` / definition label / role /
var、およびdebug detailを持つ`CanonicalCacheInterfaceHandoffError`へ写す。typed/runtime exact structural-key
disagreementも独立kindとして扱う。これはinfer/yulang crate境界を越えてproduction writerの失敗理由を観測するための
追加APIで、既存APIの破壊変更ではない。

yulang writerには観測版entrypointを追加した。`--runtime-phase-timings`付きのstd-prefix buildだけがこの入口を使い、
canonical handoff全体のelapsedと`success-empty` / `success-non-empty` / `failure`を
`run.cache_interface.canonical_handoff*`へ記録する。timing flagなしの既存writerは従来のOption入口を使い続ける。
cached hitではwriter自体が走らないためoutcome/costを再掲せず、slice 1のpersisted boundary sizeだけを出す。成功時の
surface採用、失敗時のlegacy empty pair構築、manifest、cache write、safety gateの順序と判定は変えていない。

repository stdの実測結果は正常なcanonical-emptyではなく、canonical handoff failureだった。単回観測costは
`7.9ms`、failureは`FreezeProducedConstraint`、definitionは
`std.control.nondet.nondet.#act-method:once:223` (`DefId(223)`)、boundary `None`、merge constraints `0`、subtype
constraints `1`である。その後writerは仕様どおりlegacy empty pairへfallbackし、persisted boundary entriesは`0`に
なる。したがってMarkdownの直近blockerは、repository std export handoffで`once` schemeのjoint freezeが新しい
subtype constraintを一件生成することであり、そのempty artifactを現行safety gateもopenとして拒否している。

focused正常系ではvalue-restricted artifactが`Canonical { boundary_entries: 1 }`、empty minimal stdが
`success-empty`となることを確認した。否定系ではsynthetic candidate closure failureが
`UnboundCandidateVariable`のrole / varを保持しつつ、従来どおりwritableなempty artifactへfallbackすることを確認した。
確認結果はhandoff telemetry focused 6 passed、std-prefix CLI suite 8 passed、infer interface oracle 9 passed、
cache interface関連7 passed、std-prefix safety 6 passed、infer全体598 passed / 既知の`mark_expr_block_*` 5 failedで
ある。

次sliceはcold/warm role-resolution timeとcandidate expansion counterである。`once`の
`FreezeProducedConstraint`自体を直すこと、safety gate変更、performance threshold導入はこのsliceの範囲外とする。

### Stage 6 follow-up: bounded post-stack-cleanup dominance re-check

Stage 6 slice 2で見つかった`std.control.nondet.nondet.#act-method:once`の
`FreezeProducedConstraint`を調査した結果、post-alias scan時には`SubtractId(31)`のpop weightを持つ
`Secondary('a) <: Primary('a)` keyが適用済みだが、その後の`cleanup_stack_weights_in_root_and_roles`がspent
weightを除去して別のunweighted keyを作り、final schemeに対するstrict auditだけがそのkeyを未適用と判断していた。
Claude Sonnet 5とユーザの承認に従い、auditのorigin/weight同値判定は緩めず、`15209b7e`と同じbounded companion
passを採用した。

alias-expanded compactを`prepare_stack_cleaned_alias_expanded_compact_root`でstack cleanup済みの中間値へ進めた直後、
そのrootとresidual rolesへ`collect_interval_dominance_constraints_with_metrics`を一度だけ適用し、既存の
`applied_subtype_constraints`へ`apply_compact_subtype_constraints`で記録する。実constraintが変化した場合だけ既存の
event routingを一度呼び、その後`generalize_stack_cleaned_compact_root`でquantifier / stack-quantifierを確定する。
generalizationの再起動、追加loop/fixpoint、rigid/blocked/through保護はない。このpassはcanonical cache専用ではなく
通常generalizationの全schemeへ作用するが、intervalを持つcleanup済みcompactの線形scan一回に限定される。

focused fixtureではrepository `once`と同じnondet deep handler、local recursive `loop`、`opt 'a` invariant resultを
構築し、公開schemeが`'a [std::control::nondet::nondet; 'b] -> ['b] std::data::opt::opt 'a`のまま、strict
cache-interface auditが成功し、不要なboundary binderを作らないことを固定した。fresh repository stdでは`once`の
scheme auditを通過したが、canonical handoff全体は次の別根failureで停止した。新しいfirst failureは
`std::core::fmt::Debug`の2-tuple impl（run-local `DefId(379)`、`lib/std/core/fmt.yu`の
`impl ('a, 'b): Debug`）をcandidate normalizationする際の`FreezeProducedConstraint`で、merge constraints `1`、
subtype constraints `0`である。headは2-tuple、prerequisitesは`'a: Debug`と`'b: Debug`で、candidate compact時に
未記録merge keyが一件出る。これはlate stack-weight cleanup subtype keyとは別lane・別根なので、このfollow-upでは
修正せず停止する。writerは引き続きlegacy empty boundaryへfallbackし、repository std boundary entriesは`0`である。

確認結果はpost-cleanup focused 1 passed、infer interface oracle 9 passed、cache interface関連7 passed、std-prefix
safety 6 passed、std-prefix CLI suite 8 passed、infer全体599 passed / 既知の`mark_expr_block_*` 5 failedである。

次はこのtuple `Debug` candidate merge failureを独立に診断する必要がある。cold/warm role-resolution counter、safety
gate変更、Stage 7、performance thresholdにはまだ進まない。

### Stage 6 follow-up: Tuple direct-child merge implication

`std::core::fmt::Debug`の2-tuple impl failureを追跡した結果、candidate headのlower / upperをrecording compact
した時に、2つのelement interval mergeに加えてTuple wrapper全体のmerge keyが生成されていた。element keyは
通常generalizationで適用済みだが、既存role solverはcandidate headをnon-recording compactして局所的に構造を
mergeするため、wrapper key自体は通常pipelineのapplied集合へ入らない。これはlate cleanupではなく、Stage 4の
candidate strict auditが直積構造の含意を認識していなかったことが原因だった。

Claude Sonnet 5とユーザの承認に従い、candidate merge auditだけにTuple限定のdirect-child implicationを追加した。
未適用constraintのlhs / rhsが同じ長さのTupleで、各positionが同値または対応するmerge keyを既存applied集合に
持つ場合だけ、wrapperは新しいsolver factを要求しないものとして未適用countから除く。既存のstrict counterは
scheme / boundary向けにそのまま残し、nested Tupleの再帰含意、constructor、function、record、poly variant、
associated-type carrierへの一般化は行わない。新しいsolver pass、loop / fixpoint、rigid / blocked / through保護も
追加していない。

focused testsでは、(1) Tuple wrapper未適用・全direct child適用済みなら受理、(2) structural keyが異なるchildの
一部が未適用なら拒否、(3) 同じchild集合でもnon-Tuple constructor wrapperなら拒否、を固定した。fresh repository
stdでは`fmt::Debug` 2-tuple candidateは通過した。次のfirst failureは`lib/std/data/list.yu`の
`impl (list 'a): Index int`相当（run-local `DefId(469)`、role `std::data::index::Index`、associated `value`）の
candidate joint normalizationが生成する別根の`FreezeProducedConstraint`で、merge constraints `0`、subtype
constraints `1`、handoff costは単回`19.3ms`だった。writerは引き続きlegacy emptyへfail-closedし、boundary
entriesは`0`である。このsubtype failureは今回修正しない。

確認結果はTuple implication focused 3 passed、infer interface oracle 9 passed、cache interface関連7 passed、
std-prefix safety 6 passed、std-prefix CLI suite 8 passed、infer全体602 passed / 既知の`mark_expr_block_*` 5 failedで
ある。次は`list Index int` candidateの未適用subtype constraintを独立に診断する。その後にStage 6のcold/warm
role-resolution counterへ戻る。safety gate / Stage 7には進まない。

### Stage 6 investigation hold: `ref (list)` Index candidate dominance

上記の次failureを追跡した結果、実際のcandidateは最初の`impl (list 'a): Index int`ではなく、
`lib/std/data/list.yu`の`impl (ref 'e (list 'a)): Index int`（role `std::data::index::Index`、associated
`value = ref 'e 'a`、run-local `DefId(469)`）だった。candidate normalization後の未適用constraintは、effect
binder `'e`（run-local `TypeVar(8162)`）について、概略
`Secondary('e, SubtractId(109) pop∞) <: Secondary('e, unweighted)`となる一件である。

これは`15209b7e`のpost-alias dominanceや`8bad9363`のpost-stack-cleanup dominanceとは根本原因が異なる。
normalization前のcandidate surfaceをscanした時点でdominance constraintsが3件あり、その3件すべてが通常の
dominance / apply laneを一度も通っていなかった。その後、Stage 4 candidate normalization固有の
`coalesce_floor_interval_equalities`がweighted alias `TypeVar(26113)`をhead binder `TypeVar(8162)`へcoalesceし、
最終的な一件へ縮約した。したがって「通常generalizationの最後のscan後にalias expansion / stack cleanupがsurface
を変えた」という既存のbounded companion-pass問題ではなく、candidate内部のconstraints自体が一度も
`ConstraintMachine`へapplyされたことがない、より根本的なlifecycle / proof-boundary問題である。

修正選択肢は次の三つを保留する。

1. candidate head / associated / prerequisite constraintsを、scheme確定前のmutable analysis lifecycleへ正式に参加させる。
   solver factとして最も強いが、zero-method / multi-method implとprerequisite完成時期を含むlifecycle設計が必要になる。
2. floor coalescingがcandidate-local invarianceを保存することを構造的に証明し、その証明に基づくcanonical audit規則を
   設計する。immutable handoffへ閉じられる可能性はあるが、raw candidate constraints自体も未適用なので、既存keyの
   単純renameでは足りない。
3. 既存role solverと同様にcandidate headをnon-recording local compactとして扱う。変更は小さいがstrict auditの
   安全網を弱めるため、独立した健全性証明なしでは非推奨とする。

Claude Sonnet 5の判断として、これはcanonical cache interfaceの健全性の土台に関わり、今夜ユーザの明示判断を
必要としたOracle A分割、§13.4 prerequisite-only binder、ambiguous SCC graph方針と同じ重さの設計判断である。
そのためユーザの承認なしに三案のいずれも実装しない。この件は2026-07-12 16:00以降のユーザ判断まで保留し、
Stage 7 / safety gate変更には進まず、作業線はStage 6本来の残りであるcold/warm role-resolution time、candidate
expansion counter、fallback shadow resultの計測へ戻す。

### Resolution (2026-07-15): partial option 1 (head/associated-only mutable lifecycle participation)

Adopted direction: candidate head and associated-type variables participate in the mutable analysis lifecycle (ordinary dominance/apply lane) before Stage 4's canonical joint freeze, so their internal constraints are proven via the same constraint machine as ordinary bindings rather than assumed sound by an unproven coalescing argument. Prerequisite variables are explicitly excluded from this first activation and continue to be governed by the existing strict fail-closed audit (`FreezeProducedConstraint` rejection on any unapplied prerequisite-side constraint is unchanged).

This decision is independent of option 2 (no floor-coalescing soundness axiom is introduced or assumed) and independent of the generic-role-impl-conformance project's Stage 5 (no production conformance enforcement is required or assumed as a precondition). A 2026-07-15 re-scoping pass confirmed neither dependency exists in current code, and confirmed the full (unscoped) version of option 1 is now estimated at L-XL/very-high risk (comparable to or exceeding the two-stage method lifecycle project) — this partial, head/associated-only slice is adopted specifically to avoid that scope.

Initial blast radius is limited to zero-prerequisite candidates. The concrete blocker (`impl (ref 'e (list 'a)): Index int`) has no prerequisites, so this scope is sufficient to reach it. Candidates with non-empty prerequisites continue to hit the existing strict rejection path unchanged; extending this design to prerequisite-bearing candidates is explicitly deferred as a separate future decision, not assumed to follow automatically.

Claude Sonnet 5 and the user approved this direction on 2026-07-15, following the same weight of judgment as the Oracle A split and the Section 13.4 resolution.

### Stage 6 slice 3: cold/warm role-resolution telemetry

既存`RoleResolveStats` / `AnalysisTiming`には、全role solve callを集約した`demands`、top-level
`candidate_scans` / `candidate_matches`、recursive prerequisiteの`prerequisite_demands` /
`prerequisite_candidate_scans` / `prerequisite_candidate_matches`、candidate cache hit / missがすでにあった。
新しいsolver counterは追加せず、`--runtime-phase-timings`時だけ、full-source loweringまたはcompiled-prefix suffix
loweringが既に収集した`BodyLoweringTiming`をCLIへ渡すobservation-only sibling entrypointを追加した。role-resolution
時間は`generalize_resolve_roles + method_role_solve`、当初のYumark病的再帰の主counterは
`prerequisite_candidate_scans`とする。通常entrypoint、role solver、writer、safety gateの意味論は変更しない。

fresh repository stdと`std_prefix_role_equivalence.yu`を使った2026-07-12の単回実測は次の通りだった。

- cold `--no-cache` (`run.cache: disabled`): role-resolution `548.8ms`（generalize `304.5ms`、methods
  `244.4ms`）、demands `701`、candidate scans / matches `6178 / 392`、prerequisite demands / scans /
  matches `10 / 300 / 8`、candidate cache hits / misses `1570 / 4908`、build poly `4.833s`。
- warm fresh-cache `std-prefix-hit`: role-resolution `16.1ms`（generalize `16.1ms`、methods `0us`）、
  demands `3`、candidate scans / matches `90 / 3`、prerequisite demands / scans / matches `24 / 720 / 24`、
  candidate cache hits / misses `720 / 90`、build poly `536.2ms`。

warmはsuffix-only loweringによりrole-resolution総時間とtop-level candidate scanを大幅に減らす一方、病的再帰の
直接指標であるprerequisite candidate scansは`300 -> 720`（2.4倍）へ増えた。repository std artifactは保留中の
`ref (list)` Index candidate failureによりlegacy empty boundaryのままなので、これはOption 1 canonical boundaryが
病的展開を減らした結果ではない。むしろ現状ではStage 6 exit（warm pathで病的recursive candidate expansionを
解消）を満たさないことを数値で固定した。Index candidateの三案とStage 7 safety gateは引き続き変更しない。

focused witnessはsmall Oracle B controlでcold/warm両routeにrole candidate scanが存在すること、Yumark role
equivalence controlでcold/warm双方のrecursive prerequisite scanがnon-zeroであること、runtime結果と明示routeが
従来通り一致することを確認する。確認結果はinterface oracle 9 passed、std-prefix safety 6 passed、std-prefix CLI
8 passed、infer全体602 passed / 既知の`mark_expr_block_*` 5 failedで、新規failureはない。

### Stage 5 item 5: merge and malformed-artifact witnesses

Stage 5の残件だった§4.3 / §9.4のartifact mergeとmalformed validator witnessをtest-onlyで固定した。既存mergeは
各入力artifactについてmanifest fingerprintとtyped/runtime exact structural keyを検証してから、surfaceごとの既存
type importerでboundaryとscheme/candidate参照を同じmappingへremapする。別unitのraw `TypeVar`が衝突してもfresh
targetはdisjointで、merge後にtyped/runtime structural agreementとmanifest fingerprintを再計算する。production
merge / decoderの変更は不要だった。

non-empty production artifactを2 unitから作るtestでは、同型のsingle self-boundary root同士は2026-07-12に確定した
ambiguous/symmetric graph方針どおり`MergedBoundaryInterfaceMismatch`へfail-closedすることを固定した。一方のboundに
canonical structural markerを持たせてrootを一意にした場合は、merge後も2つの`B` scopeがcoalesceされずdisjoint、
typed/runtime fingerprintが一致、merge input順を反転してもsemantic fingerprintが一致し、format 19 encode/decodeを
round tripすることを確認した。

malformed witnessはvalid non-empty artifactのtyped/runtime双方へ同じboundary binderを重複挿入し、typed/runtime
payload hashも改竄後payloadへ合わせ直す。単なるhash mismatchを除いた状態でもcanonical structural validatorが
duplicate declarationを拒否し、decodeはsafe miss、mergeは入力prefixの`BoundaryInterfaceMismatch`になることを確認した。

確認結果はfocused 2 passed、yulang cache filterでlib 50 / main 6 / CLI 14 passed、interface oracle 9 passed、
cache-interface 7 passed、std-prefix safety 6 passed、std-prefix CLI 8 passed、infer全体602 passed / 既知の
`mark_expr_block_*` 5 failedで、新規failureはない。これでStage 5項目(5)のtest coverageは完了したが、Stage 5 exit
自体はMarkdown `std-prefix-hit`待ち、Stage 6 exitはlegacy empty boundary下のpathological prerequisite expansion待ちの
ままである。Index candidate三案とStage 7 safety gateには手を出さない。

### Stage 6 slice 4: route-preserving canonical/empty boundary shadow

repository std版`std_prefix_oracle_b_small.yu`はIndex candidate failureによりboundary `0`なので、canonical/empty
比較の入力には使えない。同じfixtureを、既存positive controlと同じvalue-restricted minimal std
（`identity`経由のexpansive exported `computed`、canonical boundary entries `> 0`）上で実行するtest-only shadowを
追加した。production CLIはfresh cacheで`std-prefix-build`の`success-non-empty`を確認後、同じfixtureを明示的
`std-prefix-hit`で実行する。比較本体は同じproduction prefix artifactをdirect warm loweringへ2回渡し、一方だけ
typed/runtime boundary tableをemptyへ差し替える。改変artifactはmanifest/decoderへ渡さず、production writer / decoder /
safety gate / role solverのrouteと意味論は変更しない。

2026-07-12の単回shadow実測は次の通りだった。

- canonical boundary: role-resolution `1.116986ms`、candidate scans / matches `4 / 3`、prerequisite candidate
  scans / matches `0 / 0`。
- empty boundary shadow: role-resolution `1.194298ms`、candidate scans / matches `4 / 3`、prerequisite candidate
  scans / matches `0 / 0`。

counterは完全一致し、時間差`0.077312ms`は閾値を置けないnoise範囲である。このsmall fixtureはnon-empty `B`をsessionへ
importするが、そのprefix schemeをsuffixのrole resolutionでinstantiateせず、candidate prerequisiteも持たない。したがって
shadow配線、suffix scheme / candidate alpha同値、route非変更のcontrolにはなるが、Option 1がpathological prerequisite expansionを減らすという性能効果の
証拠にはならない。削減が無いのではなく、このfixtureのcounterが効果に感度を持たない、というinconclusive結果として
固定する。imported `B`を実際に消費しrecursive prerequisiteを持つcanonical fixtureが必要だが、現在のrepository stdでは
保留中のIndex candidateがそれを阻む。性能thresholdは置かない。

確認結果はfocused shadow 1 passed、Oracle B filter 3 passed、std-prefix CLI 9 passed、interface oracle 9 passedである。
Index candidate三案とStage 7 safety gateには引き続き手を出さない。

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
6. Yumark の「value model から作る」候補は完了した。
   - static core / thin path の到達点と、command / injection、span-carrying diagnostics、
     playground preview の明示的な残件は `notes/todo/yumark.md` を見る。

## 今すぐやる slice

Contract v1 file-resource track には、現在これ以上の immediate slice は
queued されていない。unscoped ambient line-editing idiom
（`$doc.lines.each` style）の cross-host parity は 2026-07-16 に閉じた。
現状と明示的に保留された範囲は
`notes/todo/contract-v1-file-resource-priority.md` の「NEXT SLICE — CLOSED」と
「DEFERRED / POST-V1」を見る。deferred 項目を次の slice として自動昇格しない。

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
