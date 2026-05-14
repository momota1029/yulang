# 現在のタスク: post-core roadmap

Yulang は、"この言語は成立するか" から "実用的な scripting language になれるか" へ
進むだけの core language / runtime 機能を持ち始めた。

現在の作業は、主に 3 つの track を中心に整理する。

広い backlog:

- `notes/todo/index.md`

完了履歴:

- `tasks/done/2026-05-14-native-backend-history.md` — Track 1 のここまでのマイルストーン
- `tasks/done/2026-05-14-host-filesystem-history.md` — Track 3 の parser/lowering 特例削減

## Track 1: Native Backend

明示的な control representation と effect-aware CPS lowering の両方を見ながら、
Cranelift backend を作る。

設計参照:

- `notes/design/native-backend-plan.md`
- `notes/design/cps-effect-lowering-plan.md`
- `notes/design/native-value-abi-plan.md`
- `notes/design/native-cps-mainline-plan.md`
- `notes/design/source-realm-band-plan.md`

方針:

- native 実行の本線は CPS representation backend に寄せる。
- value backend は effect-free fast path と boxed `VmValue` helper の供給元として扱う。
- まず `notes/design/native-cps-mainline-plan.md` の milestone に沿って、
  backend selection 境界、CPS `RuntimeValuePtr` lane、汎用 thunk / closure /
  resumption value の順に進める。
- `select_native_backends` は runtime module から root ごとに
  `ValueFastPath` / `CpsMainline` / `Unsupported(reason)` を返す。
  `native-run` は effect / handler / thunk boundary を含む root を CPS repr
  executable path へ直接送る。
- CPS repr Cranelift は `RuntimeValuePtr` を root return と handler /
  resumption payload に通せる。string / list / record / variant payload の
  小さい handler 境界は VM / CPS eval と合わせて regression 済み。
- `Continue` / `Branch` / `DirectCall` / `ApplyClosure` も runtime value
  pointer を保持する regression を追加済み。
- CPS repr closure / continuation env は 4 slot 固定 helper から外れ、
  `*_many(ptr, len)` helper で larger effect-flow closure env を運べる。
- CPS repr thunk env も 4 slot 固定 helper から外れ、
  `yulang_cps_make_thunk_i64_many(ptr, len)` で larger thunk capture を運べる。
- CPS repr ABI lane に `ClosurePtr` を追加し、closure pointer と
  `RuntimeValuePtr` / `ThunkPtr` の境界を明示した。
- top-level function の partial application は CPS closure として生成し、
  残りの引数が揃った時点で direct call へ戻る。
- forced CPS repr executable path で std `list.map` / `filter` / `fold` の
  小さい source program を確認済み。

近い形:

```text
runtime/core IR
  -> pure debug control IR / effect-aware CPS IR
  -> closure/environment layout
  -> Cranelift IR
```

現在の距離感:

- まだ Yulang 全体を実行する処理系ではない。
- Go module/package よりの source identity として realm / band を採用する。
  realm は versioned distribution boundary、band は realm 内の import /
  namespace / build unit。band identity は resolved realm + band path で決まる。
- source から runtime IR / effect-aware CPS / CPS repr / ABI lane /
  Cranelift JIT まで通る細い実行可能パスはできている。
- source-defined algebraic effect と multi-shot resumption の小さい scalar
  program は VM と CPS repr Cranelift で比較できる。
- まだ prototype と呼ぶべき理由は、値表現が主に `i64` scalar に限られ、
  thunk / closure / string / list / record / variant / std 全体を広く扱う
  backend にはなっていないため。
- 当面は VM を oracle にしたまま、native 対応 root だけを増やす。
  将来的には native unsupported root を VM に戻す fallback policy を決める。

直近 TODO:

- `crates/yulang-native` の native control IR skeleton を育てる。
- 最初に support する subset を小さい compare harness で固定する。
  - pure first-order functions
  - primitive numeric/string operations
  - representation が明確なら simple records / variants
- VM result と native-control result を比較する test helper を広げる。
- direct monomorphic calls の範囲を広げる。
  - 残: root binding の扱いと、closure capture を明示拒否する diagnostics を決める。
- algebraic effects と resumptions は design に残すが、最初の compiled milestone にはしない。
- effectful 本線は CPS / continuation lowering を先に設計し、その後に closure conversion へ渡す。
  - `MultiShot` continuation は最初の CPS IR から持つ。
  - Yulang の値・closure・environment は不変なので、continuation / closure clone は構造共有を基本にする。
  - `std::undet` 系の finite nondet は early target として扱い、後付けの難物にしない。

これまでの主なマイルストーン (CPS lowering / CPS repr Cranelift JIT / value-lane Cranelift /
dynamic handler frame / guard stack / finite nondet など) は
`tasks/done/2026-05-14-native-backend-history.md` に退避。

## 処理系化へ近い次の順番

1. CPS repr Cranelift の guarded thunk effect-flow を設計する。
   Dynamic handler frame / guard stack の scalar runtime layout は入った。
   次は thunk callback が guard scope をまたぐ時に、どの stack を capture /
   restore / rebase するかを CPS repr evaluator と一致させる。
   - 残: なし（このプランの完了済み小項目は退避履歴に記録）。
2. CPS repr Cranelift の source 回帰を広げる。
   `let` / `if` / primitive / direct call / simple handler / value arm を
   VM と比較しながら固定する。
   - 残: lazy operator / thunk 引数インラインの境界を設計メモへ切り出す。
     現在は CPS scalar prototype のために、thunk 引数を持つ direct call を
     呼び出し地点で展開している。保存・返却される thunk value はまだ扱わない。
   - 残: 条件式の scalar regression は一旦区切りにし、value ABI
     か fallback policy へ進む。
3. value ABI を広げる。
   `int` / `bool` / `unit` だけでなく、`str` / `list` / tuple / record /
   variant を pointer lane で通す。
   - 現状: tuple / record / variant construction と record field selection は
     source から value-lane Cranelift まで通る。VM / native-control eval /
     native ABI eval / value-lane Cranelift を boxed `VmValue` root で比較する
     regression harness も追加済み。string equality、string range/splice、
     list range/splice/view 系も同じ harness で VM と比較している。
   - 残: boxed scalar value の範囲を整理する。
     value lane 用の int/bool/unit/float は boxed `VmValue` として動くので、
     次は native scalar lane と boxed value lane の境界をどこで選ぶか決める。
4. Cranelift object backend を JIT と並べて育てる。
   - 残: string/list view 系を value-lane helper 化するか、thunk /
     closure value 境界へ戻るか決める。
5. thunk / closure value を backend 境界で実体化する。
   汎用 thunk invocation と closure environment を扱えるようにする。
6. fallback policy を設計する。
   native で扱える root は native、unsupported root は VM へ戻す混在実行を
   CLI / playground で試せるようにする。

## 次 milestone

CPS repr Cranelift の source 回帰を広げる。

焦点:

- mutable ref 以外の user-defined state/effect wrapper を VM 比較へ足す。
- std `undet.once` は finite list の object/executable compile path まで通った。
  ただし実行値はまだ VM と一致しない。次は function-returned effectful thunk
  が caller handler frame を持てるようにしてから、`each` / `fold_impl` /
  `sub::sub` をまたぐ thunk force と dynamic handler stack の意味論を VM と揃える。
- effectful callback の handler frame は関数境界をまたいで選択できるように
  なった。次は handler candidate と captured env をより ABI 明示的な構造へ寄せる。
- 保存・返却される thunk value はまだ扱わず、direct thunk callback subset の
  境界を明文化する。
- CPS repr Cranelift の手書き IR では 5 slot 以上の thunk capture env を
  force できる。
- source の `sub` を list などの構造値へ入れた時の二重 escape routing は修正済み。
  handler arm entry がすでに installed escape continuation へ進む場合、CPS /
  CPS repr / Cranelift は arm result を二度目の ScopeReturn として包まない。
- 再帰 handler wrapper は direct call site で inline しない。`std::undet.list`
  のように handler arm 内で同じ wrapper を再帰呼び出しする関数は、CPS 関数として
  残してから return-frame / resumption 経路で扱う。
- `branch().list`、`(each [1, 2, 3]).logic`、`(each [1, 2, 3]).list`
  は forced CPS repr executable path で通る。`each.list` の false branch は
  CPS eval / CPS repr eval の時点で `[[1, ()]]` に漏れていたが、Return(Thunk)
  の pre-force が top continuation を直接再開せず、retained return frame を
  消費する前に thunk body を force してから return-frame chain へ戻すようにした。
  これで fold callback の `()` は残りの fold へ流れ、末尾の `reject()` に届く。
- nested finite-list nondet も forced CPS repr executable path で通る。
  `(each [1, 2, 3] + each [10, 20]).list` / `.logic` は VM / CPS eval /
  CPS repr eval / Cranelift JIT で一致し、`.once` も VM / CPS eval /
  CPS repr eval / Cranelift JIT で `just 11` を返す。handler arm が
  installed escape へ到達済みのときも retained return-frame chain を続行し、
  CPS repr / Cranelift の `ApplyClosure` は resumption pointer を
  closure-like callable として扱う。
- callback-return hygiene の observable source regression を forced CPS repr
  executable path に追加した。inner `sub` 内の直呼び `f()` は inner handler に
  捕まり outer root が `2` まで進む一方、thunk callback 経由の `h()` は inner
  handler を越えて outer `sub` から `0` を返す。
- native CLI の現状は `docs/native-backend.md` の Public CLI に集約済み。
  `yulang native` は value backend を優先し、effect / handler /
  thunk-boundary control が見えた root は CPS repr backend を選ぶ。
  `run-value-exe` / `run-cps-repr-exe` は debugging 用の強制 path として残す。
- value backend と CPS repr backend の fallback policy を、握りつぶしではなく
  structured unsupported reason で選べる形へ寄せる。

## 重要な制約

- VM は behavioral oracle のままにする。Native code は置き換えではなく、VM の横に追加する。
- 現 VM は nondet continuation の clone cost が大きい。playground/docs examples では
  無限選択を早めに絞り、VM 参照化は native backend / control IR 作業と一緒に扱う。

## Track 2: Parser Combinators

parser combinators を Yulang 側から使える capability として実装する。

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

## Track 3: Host / Filesystem Semantics

host capabilities、特に filesystem behavior を安定させる。

設計参照:

- `notes/design/error-handling-plan.md`

現在の実装:

- `std::console` は `print` / `println` を持つ。
- `std::fs` は暫定 native-host surface として存在する。
  - `read_text: str -> opt str`
  - `read_text_or_throw: str -> [fs_err] str`
  - `write_text: (str, str) -> bool`
  - `exists: str -> bool`
  - `is_file: str -> bool`
  - `is_dir: str -> bool`
  - `error fs_err:` prototype と手動 `Throw fs_err`
- `std::prelude` は `fail` を parser/lower 特例ではなく `prefix(fail)` operator として export する。
- 現在の `fail` は effect operation を前置で読ませる暫定 no-op。generated data-value `fail` は未実装。
- `not` は parser builtin から外し、`std::ops` の operator export として扱う。
- `return` / `last` / `next` / `redo` は parser builtin から外し、prelude の operator export として扱う。
- `+` / `-` / `*` / `/` / 比較演算子は `std::ops` に operator export を置き、lowering bridge も外した。
- `!=` は lower 特例から外し、`std::ops` の ordinary operator wrapper として扱う。
- `lazy` operator header を追加した。lazy operator は operand をすべて unit thunk として受け取る。
- `and` / `or` は lower 特例から外し、`std::ops` の `pub lazy infix` operator として扱う。
- list の末尾取得は `xs.last` を優先し、`last xs` という関数呼び出し互換は持たない。
- native CLI / basic host はこれらの request を処理する。
- wasm / playground は filesystem request を unresolved のまま残す。

直近 TODO:

- `result` の導入 / 安定化より先に error handling design を進める。
- 正確な `std::fs` API は unstable として扱う。
- API 拡張の前に error handling を決める。
  - `opt`
  - `result`
  - structured host-request errors
  - effect-style error operations
- `enum` / `error` の `from` entry で generated `Cast` を作る仕様を決める。
- `fail err` を typed error effect の user-facing surface として設計する。data constructor と same-name effect operation の文脈解決もここで固める。
- `std::undet` の branch rejection は `reject` として扱い、error の `fail` と分ける。
- `die` / `warn` / `say` の最小 std surface を決める。
- `io_err::raise` のような generated aggregation handler を、role ではなく error namespace の関数として設計する。
- parser/lowering の特例削減を続ける。
  - 残る本丸は primitive family table を persistent compiled-unit artifact metadata から渡すこと。std source へ専用 metadata を足す方向にはしない。
  - これまでの完了済み撤去項目は `tasks/done/2026-05-14-host-filesystem-history.md` に退避。
- path を `str` のままにするか、`path` type にするか決める。
- text read/write が落ち着いた後に、最初の directory API を決める。
- browser examples を作る前に playground capability policy を決める。

重要な制約:

- native-only filesystem behavior が wasm / playground でも portable に見えないようにする。

## Ongoing: Static Analysis Speed

最近の performance work は、引き続き playground の目標と揃っている。

現在の参照:

- `notes/design/static-analysis-speed-plan.md`
- `notes/design/partial-compilation-cache-plan.md`

現在の checkpoint:

- principal-unify は default monomorphize route。
- specialization body rewrite は queue 化され、target ごとに profile される。
- block rewrite は redundant pre-walk を避け、`showcase` の monomorphize time を大きく減らす。
- compiled-unit artifacts は syntax / namespace / typed / runtime surfaces を持つ。
- wasm は std compiled-unit artifacts を embed し、source std を fallback として使う。

次 TODO:

- typed-surface import の role / impl / effect fidelity を広げる。
- compiled-unit manifest validation を厳しくする。
- persistent cache を user dependency SCCs に一般化する。
- `bench/static_analysis_bench.sh` を代表性のある benchmark として保つ。

## Ongoing: Diagnostics and Examples

言語が experimental な間は、examples を public contract として保つ。

TODO:

- playground examples を CLI からも runnable に保つ。
- feature behavior を説明できる程度に安定してから examples を追加する。
- parser / type / runtime errors の user-facing diagnostics を改善する。
- ordinary user paths で internal monomorphize / runtime errors を露出しない。

## Ongoing: Testing

Yulang code から小さい regression test を書ける形を作る。

次 TODO:

- Yulang-facing test API の最小形を決める。
- fixture 置き場と CLI runner の入口を決める。
- examples のうち重要なものを regression test に写す。
- diagnostics golden は必要な範囲だけ固定する。
