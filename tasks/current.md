# 現在のタスク: post-native archive roadmap

Yulang は、"この言語は成立するか" から "実用的な scripting language になれるか" へ
進むだけの core language / runtime 機能を持ち始めた。

2026-05-25 の整理で native backend と旧 monomorphize pipeline は active workspace
から外れた。現在の主戦場は、VM を user-facing 実行面として保ちながら、
monomorphize / runtime lowering / diagnostics / static-analysis cache を小さく健全に
していくこと。

広い backlog:

- `notes/todo/index.md`

直近の handoff:

- `notes/progress/daily/2026-05-28-parallel-cache-flake-handoff.md`
- `notes/progress/daily/2026-05-26-infer-monomorphize-handoff.md`
- `notes/refactors/finalized-vm-handoff-2026-05-25.md`

完了履歴:

- `tasks/done/2026-05-14-native-backend-history.md` — archived native backend の節目
- `tasks/done/2026-05-14-host-filesystem-history.md` — Track 2 の parser/lowering 特例削減

## Current Focus

今はデバッグ中の canary を広げすぎず、次の順に進める。

1. `vm_inserts_cast_at_if_branch_boundary` の false-positive diagnostic を切り分ける。
   まず `collect_surface_diagnostics` に届く `TypeError` と expected-edge /
   preserved cast boundary の対応を見る。solver 全体を広く変えない。
2. `type surface` audit を進める。runtime / monomorphize 出口に残る型 surface を列挙し、
   substituter / projector / audit が同じ site set を読む形へ寄せる。
3. compiled std artifact / control VM cache を、std 専用特例ではなく source dependency
   surface として説明できる形へ寄せる。
4. public docs / status / examples を current implementation と合わせる。

守る不変条件:

- `Any` は Top、`Never` は Bottom、`Unknown` は唯一の不明型。
- 型が決まらないから `Any` に逃がす処理は入れない。
- path / module / fixture 名の文字列比較で型を決めない。
- 再現ケースだけを通す局所分岐ではなく、constraint / evidence / runtime surface の
  一般規則として説明できる修正にする。

## Active: Monomorphize / Runtime Type Surface

現在の問題は「単一化そのもの」だけではなく、runtime / monomorphize の出入口に残る
型 surface を網羅的に置換・投影・監査できていないこととして扱う。

設計参照:

- `notes/bugs/type-substitute.md`
- `notes/bugs/type-monomorphize.md`
- `notes/bugs/type-monorphized-refactor.md`
- `notes/progress/daily/2026-05-26-infer-monomorphize-handoff.md`

方針:

- `Expr.ty` / pattern ty / binding scheme / evidence / handler residual /
  thunk effect / adapter / coercion など、runtime へ残る型 surface をまず列挙する。
- 置換、runtime projection、residual audit が同じ surface list を読む形へ寄せる。
- fallback-to-old-`expr.ty` は telemetry を通して理由付きにし、monomorphized 出口で
  strict に落とせるようにする。
- 型推論・monomorphize の途中に path / module / fixture 名依存の分岐は入れない。

直近 TODO:

- `vm_inserts_cast_at_if_branch_boundary` を canary にする。
- `collect_surface_diagnostics` に届く `TypeError` が、どの `ExpectedEdgeId` /
  `ExpectedEdgeKind` と対応しているか trace する。
- expected edge が `IfBranch` / `ApplicationArgument` で、preserved boundary が
  export 可能な closed cast の場合、surface diagnostic として fatal にするべきかを
  diagnostics 側で切り分ける。
- `MissingImpl` / `AmbiguousImpl` は false positive と一緒に握りつぶさない。
- monomorphize へ進めた後、finalized/runtime IR に `Cast int -> user_id` の apply が
  入るか確認する。
- `type_surface.rs` 相当の collector / folder / audit entrypoint を足す。
- collector と substituter が同じ site set を覆う parity test を入れる。
- poison type test で `ApplyEvidence`、`HandleEffect`、`ThunkEffect`、
  `AddId.allowed`、nested pattern bind などの漏れを見つける。
- `YULANG_STRICT_MONO_RUNTIME_TYPES=1 RUSTC_WRAPPER= cargo test -q -p yulang-runtime`
  相当の strict check を、現在の crate split に合わせて再定義する。
- `substitute_type` の推移的置換、recursive binder capture、effect row matching は
  `Subst` / free-vars / row matcher の責務として切り出す。

確認済み canary は handoff note に寄せる。`tasks/current.md` には次の一手だけ残す。

## Active: Static Analysis Speed

最近の performance work は、引き続き playground の目標と揃っている。

現在の参照:

- `notes/design/static-analysis-speed-plan.md`
- `notes/design/partial-compilation-cache-plan.md`
- `notes/design/algebraic-effect-optimization-plan.md`
- `notes/bugs/type-substitute.md`
- `notes/bugs/type-monomorphize.md`
- `notes/bugs/type-monorphized-refactor.md`

現在の checkpoint:

- principal-unify は default monomorphize route。
- specialization body rewrite は queue 化され、target ごとに profile される。
- block rewrite は redundant pre-walk を避け、`showcase` の monomorphize time を減らす。
- compiled-unit artifacts は syntax / namespace / typed / runtime surfaces を持つ。
- wasm は std compiled-unit artifacts を embed し、source std を fallback として使う。
- hidden debug control VM path は source-fingerprint artifact cache を持つ。

次 TODO:

- type surface audit を先に通し、strict residual 型を見つける入口を作る。
- typed-surface import の role / impl / effect fidelity を広げる。
- compiled-unit manifest validation を厳しくする。
- persistent cache を user dependency SCCs に一般化する。
- `bench/static_analysis_bench.sh` を代表性のある benchmark として保つ。
- control VM artifact / compiled std cache の説明を public docs と internal notes で揃える。

## Track 1: Parser Combinators

parser combinators を Yulang 側から使える capability として実装する。

設計参照:

- `notes/design/parser-dsl-desugar.md` — `rule { ... }` / `~"..."` の desugar 方針

直近 TODO:

- public parser result と error type を定義する。
- minimal combinator kernel を実装する。
  - `item`
  - `satisfy`
  - `map`
  - sequencing / bind
  - choice
  - repetition
  - token/string matching
- cut / commit と error merging の挙動を決める。
- 最初の API が nontrivial なものを parse できるようになってから examples を追加する。

重要な制約:

- compiler parser はまだ書き直さない。library parser API を先に独立して試す。

## Track 2: Host / IO Semantics

host capabilities、特に IO / filesystem behavior を安定させる。

設計参照:

- `notes/design/error-handling-plan.md`
- `notes/design/std-fs.md` — 旧 std::fs 最小設計

現在の実装:

- 新 std source は `std::io` に output / diagnostics / filesystem helper をまとめる。
  - `out` / `err` / `warn` / `die` act
  - `file` act
  - `io_err` typed error
  - `read_text` / `read_at` / `write_text` / `write_at`
  - `open` / `open_text` / `open_in`
  - `exists` / `is_file` / `is_dir`
- `std::prelude` は `fail` を parser/lower 特例ではなく `prefix(fail)` operator として export する。
- `not` / `return` / `last` / `next` / `redo` / arithmetic / comparison / `and` / `or`
  は parser/lowering 特例から std operator export へ寄せた。
- `lib/std.yu` を std root module とし、`std::core` / `std::num` / `std::data` /
  `std::text` / `std::control` / `std::io` / `std::prelude` へ分ける。
- wasm / playground は filesystem request を unresolved のまま残す。

直近 TODO:

- `result` の導入 / 安定化より先に error handling design を進める。
- 正確な `std::io` filesystem API は unstable として扱う。
- API 拡張の前に error handling を決める。
  - `opt`
  - `result`
  - structured host-request errors
  - effect-style error operations
- `enum` / `error` の `from` entry で generated `Cast` を作る仕様を決める。
- `fail err` を typed error effect の user-facing surface として設計する。
- `std::control::nondet` の branch rejection は `reject` として扱い、error の `fail` と分ける。
- `die` / `warn` / `say` の最小 std surface を決める。
- `io_err::raise` のような generated aggregation handler を、role ではなく error namespace の
  関数として設計する。
- text read/write が落ち着いた後に、最初の directory API を決める。
- browser examples を作る前に playground capability policy を決める。

重要な制約:

- host-only filesystem behavior が wasm / playground でも portable に見えないようにする。

## Ongoing: Diagnostics and Examples

言語が experimental な間は、examples を public contract として保つ。

TODO:

- playground examples を CLI からも runnable に保つ。
- feature behavior を説明できる程度に安定してから examples を追加する。
- parser / type / runtime errors の user-facing diagnostics を改善する。
- ordinary user paths で internal monomorphize / runtime errors を露出しない。
- public docs / README / `docs/status.md` が active workspace の実行入口と矛盾しないように保つ。

## Ongoing: Testing

Yulang code から小さい regression test を書ける形を作る。

次 TODO:

- Yulang-facing test API の最小形を決める。
- fixture 置き場と CLI runner の入口を決める。
- examples のうち重要なものを regression test に写す。
- diagnostics golden は必要な範囲だけ固定する。

## Archived: Native Backend

native backend は 2026-05-25 に active workspace から外れた。
`yulang run --native`、`yulang native`、`yulang run --mmtk` は current CLI surface ではない。

今後の扱い:

- public status は `README.md` / `README.ja.md` / `docs/status.md` の「退役済み」に合わせる。
- historical notes は `docs/native-backend.md` と `docs/native-experimental-release.md` に置く。
- 詳細な実装履歴は `tasks/done/2026-05-14-native-backend-history.md` と
  `notes/refactors/finalized-vm-handoff-2026-05-25.md` を見る。
- native-specific TODO は active queue に戻さない。将来の実行 backend を再開する場合は、
  VM/runtime semantics、type surface audit、compiled-unit cache が落ち着いてから新しい track として切る。

native 由来でまだ active な知見:

- VM は behavioral oracle のままにする。
- control-heavy benchmark で runtime `Expr` clone が重いという観測は、hidden control VM /
  VM compile path の改善として扱う。
- CPS / effect-region optimization の design note は、将来の execution work の材料として残す。
