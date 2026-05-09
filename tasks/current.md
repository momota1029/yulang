# 現在のタスク: post-core roadmap

Yulang は、"この言語は成立するか" から "実用的な scripting language になれるか" へ
進むだけの core language / runtime 機能を持ち始めた。

現在の作業は、主に 3 つの track を中心に整理する。

広い backlog:

- `notes/todo/index.md`

## Track 1: Native Backend

明示的な control representation と effect-aware CPS lowering の両方を見ながら、
Cranelift backend を作る。

設計参照:

- `notes/design/native-backend-plan.md`
- `notes/design/cps-effect-lowering-plan.md`
- `notes/design/native-value-abi-plan.md`

近い形:

```text
runtime/core IR
  -> pure debug control IR / effect-aware CPS IR
  -> closure/environment layout
  -> Cranelift IR
```

直近 TODO:

- `crates/yulang-native` の native control IR skeleton を育てる。
- 最初に support する subset を小さい compare harness で固定する。
  - pure first-order functions
  - primitive numeric/string operations
  - representation が明確なら simple records / variants
- VM result と native-control result を比較する test helper を広げる。
- direct monomorphic calls の範囲を広げる。
  - `if` は branch + merge block param として lowering / native-control eval / VM compare まで追加済み。
  - local block binding は simple `Bind` / `Wildcard` pattern だけ lowering / VM compare まで追加済み。
  - direct monomorphic call は non-polymorphic binding の curried lambda を `NativeFunction` に落とし、root expression からの direct call を lowering / native-control eval / VM compare まで追加済み。
  - call arity mismatch は lowering の構造化エラーにした。
  - 複数 binding と小さい再帰 call は VM compare まで追加済み。
  - 次は root binding の扱いと、closure capture を明示拒否する diagnostics を決める。
- algebraic effects と resumptions は design に残すが、最初の compiled milestone にはしない。
- Cranelift dependency は control IR / compare harness が安定してから入れる。
- effectful 本線は CPS / continuation lowering を先に設計し、その後に closure conversion へ渡す。
  - `MultiShot` continuation は最初の CPS IR から持つ。
  - Yulang の値・closure・environment は不変なので、continuation / closure clone は構造共有を基本にする。
  - `std::undet` 系の finite nondet は early target として扱い、後付けの難物にしない。
  - CPS IR skeleton / validator / evaluator は追加済み。pure subset は `VM == native-control eval == CPS eval` で比較している。
  - effect operation / handler / resumption value の最小 IR と evaluator は追加済み。手書き CPS IR で同じ `MultiShot` resumption を二回呼ぶ finite nondet 核を確認している。
  - runtime `Handle` / `EffectOp` / resumption call から CPS IR への最小 lowering を追加済み。現時点では single arm / no guard を扱う。
  - body が direct effect operation application の形と、primitive / direct call の引数位置に effect operation が出る形は、rest-of-computation を resume continuation に落とす。
  - block の let-binding / expr statement に effect operation が出る形も、残りの stmt/tail を resume continuation に落とす。
  - effectful handle body の `BindHere* -> Thunk -> body` は handle body 実行 wrapper の 1 塊として扱う。`BindHere` 単体を個別に剥がさない。
  - perform site ごとに resume continuation を作る形へ広げた。
  - if body は、条件が pure で両分岐が同じ handled effect を投げる限定形を CPS lowering できる。
  - CPS continuation に `captures` field を追加した。lowering 後に `infer_cps_captures` を走らせ、validator は continuation params と captures だけを visible value として扱う。
  - `layout_cps_environments` は continuation captures を stable slot layout に落とす。これは closure conversion / backend が読む environment layout の最初の形。
  - `closure_convert_cps_module` は CPS continuation を code id / params / environment slots の組へ変換する。
  - `lower_cps_repr_module` は CPS continuation を executable representation IR の code object として残す最小入口。pure continuation flow と multi-shot resumption flow を `eval_cps_repr_module` で確認している。
  - CPS repr evaluator は `Perform` を handler entry continuation へ入り、resume continuation + captured value snapshot を resumption value として渡す。これは Cranelift value/closure lane へ effectful control を渡す前段。
  - `analyze_cps_repr_values` は CPS repr value を `Plain` / `Resumption` / `Unknown` に分類する。handler entry の payload/resumption param と `Resume` の result kind を構造から追い、resumption を heap pointer lane へ落とす前段にする。
  - `analyze_cps_repr_abi_lanes` は CPS repr value / continuation return を `ScalarI64` / `NativeFloat` / `RuntimeValuePtr` / `ResumptionPtr` / `Unknown` に分類する。effect 名や std path は見ず、handler entry の第 2 引数と `Perform` / `Resume` の構造から resumption lane を出す。
  - `lower_cps_repr_abi_module` は CPS repr に lane 情報を貼り、continuation params / environment slots / return lane を Cranelift lowering が読みやすい形へ束ねる。まだ machine layout は選ばず、effectful control を codegen 境界まで運ぶための ABI skeleton に留める。
  - `compile_cps_repr_abi_module` は scalar CPS repr ABI を Cranelift で実行する最初の入口。pure 関数は continuation を Cranelift block、`Continue` は jump、`Branch` は brif に落とす。
  - effectful 関数では CPS continuation を個別の JIT 関数に分ける。`Perform` は resume continuation の code pointer と captured scalar environment snapshot から heap resumption を作って handler entry へ渡し、`Resume` は helper 経由で resumption を呼ぶ。non-tail resume と同じ resumption の複数回呼び出しは確認済み。現時点では scalar i64 / environment 4 slot までの prototype。
  - runtime `Handle` / `EffectOp` 由来の CPS repr Cranelift 比較を追加した。単純 resume、同じ resumption の複数回呼び出し、perform 後の rest-of-computation、effectful branch を VM と比較している。
  - source から CPS repr Cranelift へ入る `eval_source_cps_repr_i64(_with_options)` / `compare_source_cps_repr_i64(_with_options)` を追加した。prelude なしの小さい `act` / `catch` source は VM と CPS repr Cranelift で比較済み。
  - CLI に `--native-cps-repr-i64` を追加した。source から runtime lower / monomorphize した module を VM と CPS repr Cranelift scalar i64 で比較する debug entrypoint。
  - CPS lowering は root から reachable な runtime binding だけを lower する。std/prelude を読む source でも、到達不能な std の非関数 binding / unsupported binding が CPS repr Cranelift の scalar prototype を止めないようにした。
  - prelude ありの source literal と、prelude ありの小さい source-defined `act` / `catch` は CPS repr Cranelift で VM 比較済み。
  - `std::flow::sub::sub { std::flow::sub::return 41 }` は CPS repr Cranelift で VM 比較済み。CPS lowering は、`fun x -> handle x ...` 形の thunk handler wrapper が thunk 引数へ直接適用される場合、thunk を汎用値 lane にせず handle body へインライン展開する。
  - CPS repr value / ABI lane 解析では `Unknown` を初期未確定値として扱い、既知 lane / value kind で精密化するようにした。異なる既知 lane が衝突した場合だけ `Unknown` に戻る。
  - 汎用 thunk value lane / thunk invocation はまだ未対応。wrapper を越えて thunk を保存・返却・複数箇所で渡す場合は次の段階で扱う。
  - `compile_runtime_module_to_cps_repr_jit` は runtime module -> CPS -> CPS repr -> CPS repr ABI -> Cranelift まで通す helper。現時点では pure scalar root の実行確認用。
  - `compare_cps_repr_cranelift_i64` は VM と CPS repr Cranelift の scalar root を比較する regression entrypoint。まず `20 + 22` の runtime module で固定した。
  - ordinary native-control closure conversion skeleton として `closure_convert_module` を追加した。
  - runtime `Lambda` は native-control の generated function + `MakeClosure` に lowering する。non-direct `Apply` は `ClosureCall` に lowering する。
  - immediate lambda call と captured local を持つ lambda call は VM compare まで追加済み。
  - `NativeFunction.captures` で closure-generated function の capture params を明示する。`closure_convert_module` は captures を environment slots に分離し、通常 params と分ける。
  - `yulang-native::source` に実験用の文字列 source entrypoint を追加した。現時点では `source -> infer/export -> runtime lower/monomorphize -> native-control eval` の薄い adapter で、backend 本体は引き続き `runtime::Module` を入口にする。
  - closure-converted body 側に `LoadEnv` を追加し、capture param を entry block param から外して environment slot load として明示するところまで追加済み。
  - `MakeClosure` は closure-converted IR 上で code target + environment slot values の allocation として表す。
  - closure-converted function は `NativeClosureAbi` を持ち、code ref / environment slot count / non-capture params を backend が読める形に分ける。
  - `lower_closure_module_to_abi` は closure-converted IR を backend-neutral ABI IR に落とす。`LoadEnv` / `AllocateClosure` / `IndirectClosureCall` / `DirectCall` が Cranelift 手前の境界になる。
  - `validate_abi_module` は function/block/value uniqueness、use-before-def、env slot range、terminator target を検査する。
  - `validate_cranelift_prototype_subset` は最初の Cranelift prototype 用に、int/float/bool/unit literal、数値/bool primitive、direct call、局所 closure allocation/call を許可する。string/list は runtime ABI が固まるまで明示 unsupported。
  - `format_abi_module` は ABI IR を stable text dump にする。Cranelift prototype 前の golden/debug 出力に使う。
  - `compile_abi_module` は Cranelift JIT prototype を追加した。現時点では `i64` scalar ABI として int/bool/unit literal、int/bool primitive、direct call、branch/jump/return を扱う。float/string/list は runtime ABI が固まるまで scalar JIT では unsupported。
  - `eval_source_i64_with_options` は `source -> runtime -> native control -> closure -> ABI -> Cranelift JIT` を一本で通す scalar prototype entrypoint。
  - `compare_source_i64_with_options` は source 起点で VM / native-control / Cranelift scalar result を比較する。std に依存しない int/bool/function-call examples を固定した。
  - `compare_source_i64` は native default source options を使い、std prelude operator から primitive binding へ繋がる `1 + 2` / `1 < 2` も VM / native-control / Cranelift で比較する。
  - `eval_abi_module` は backend-neutral ABI IR を評価する。closure environment slots と ordinary params を分け、`AllocateClosure` / `LoadEnv` / `IndirectClosureCall` の意味を Cranelift 実装前に固定する。
  - `compare_module` / `compare_source_i64` は ABI eval も oracle に含める。Cranelift が closure/env を持つ前でも、closure-converted ABI IR の意味は VM / native-control と比較できる。
  - Cranelift scalar prototype は、局所 `AllocateClosure` を lowering 中の target/capture table として保持し、`IndirectClosureCall` を hidden env args 付き direct call へ戻す限定形を扱う。closure value を return / block arg / scalar primitive へ流す形はまだ unsupported。
  - Native lower は `fun x -> block(...; fun y -> body)` 形の curried wrapper に、元の partial-call 用関数を残したまま追加 direct arity target を生成する。Cranelift は root から reachable な関数だけ JIT するため、未使用の closure-returning wrapper は compile しない。
  - 関数内の `x + 1` は source-level compare へ戻した。`my inc x = x + 1; inc 41` は VM / native-control / ABI eval / Cranelift で比較している。
  - CLI は `--native-compare-i64` で VM / native-control / ABI eval / Cranelift scalar result を比較できる。`bench/native_compare.sh` は同じ入口を quick bench/debug 用に呼ぶ。
  - source-level compare examples は bool primitive / source `if` / small function 内 `if` まで広げた。
  - source `if` の条件に primitive/operator call が入る形も追加した。`1 < 2` などで prelude の junction/handler wrapper が見えるため、native lower は effect-free な `Handle` / `Thunk` / `BindHere` / effect-id scope wrapper を中身へ進める。実際の `EffectOp` はまだ unsupported のままにする。
  - `str` / `list` / `record` は `notes/design/native-value-abi-plan.md` の opaque runtime value pointer lane で進める。scalar-only `compile_abi_module` は残し、value lane は別 entrypoint として追加する。
  - `analyze_abi_reprs` は ABI function/value を `Int` / `Bool` / `Float` / `List(element)` / `RuntimeValuePtr` / `ClosurePtr` / `Unknown` に分類する。`List` は machine boundary では pointer lane のままだが、singleton/index/merge/range 系で分かる範囲の element repr は伝播する。tuple/record repr は後続の runtime type 連携で足す。
  - `compile_value_abi_module` は scalar-only `compile_abi_module` と別の Cranelift value-lane prototype entrypoint として追加した。現時点では string literal と `StringConcat` primitive/direct call を Rust helper 経由で `VmValue::String` に戻す。
  - `eval_source_value_lane_with_options` は source から value-lane Cranelift まで通す実験入口。`"hello"` / `"a" + "b"` の round-trip と、source からの string/list ABI repr analysis をテストで固定した。
  - CLI は `--native-abi-lanes` で source から native ABI repr classification を表示できる。未使用の closure-returning wrapper と reachable scalar direct wrapper の違いを見るための debug entrypoint。

重要な制約:

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
  - `+` / `-` / `*` / `/` / `==` / `<` / `<=` / `>` / `>=` の role method 直結は `std::ops` operator 定義へ寄せた。
    - `std::ops` 分離、古い `+ -> add` internal-name fallback の撤去、forward direct role method call の constraints import で、operator wrapper 内の未解決 `ref_*` は閉じた。
  - `and` / `or` は `lazy` operator へ寄せた。
  - `sub` / `for` / `var` の synthetic act は糖衣展開の入口として分離する。
  - runtime monomorphize の handler 消費 effect 判定は、binding body の `handle` 構造や runtime type shape から拾う。
  - 末尾名 `add` / `fold` / `fold_impl` / `find` だけで associated demand signature closure を入れる特例は撤去した。
  - 残っている `std` path / `ends_with` / 末尾名判定は `notes/design/std-special-case-audit.md` に洗い出した。sugar 入口以外の挙動特例は primitive family table / canonical id 比較へ寄せて消す。
  - `AssociatedSignatureKind` と associated demand signature closure を撤去した。monomorphize は binding body/type/primitive/role impl graph から target を分類して signature hole を補完しない。
  - monomorphize の effect path matching から任意 suffix match を外した。effect parent / child operation の prefix 関係だけ残す。
  - `Fold::item` の demand closure も撤去した。list/range item を role impl graph から推測して callback signature を補完しない。
  - complete principal export からも `item` / `list` / `range` の名前ベース補完を外した。role requirement から型を逆算せず、call slot / exported bounds / expected evidence だけを substitution source にする。
  - runtime effect compatibility から、`std::flow::loop` を expected effect に含めると任意の actual effect を通す分岐を外した。
  - numeric widening / union join / VM cast は任意末尾名 `int` / `float` を見ない。context を持たない層では bare `int` -> bare `float` の bootstrap fallback だけ残す。
  - monomorphize normalization から末尾名 `sub` の payload 後付け補完を外した。
  - VM effect operation erase から consumed effect namespace の末尾名に単一 operation を合わせる解決分岐を外した。
  - ordinary role method call resolver から `cast` method 名の特別分岐を外した。明示 coercion は専用 entrypoint のまま残す。
  - ref list index projection は compiler export の専用分岐を外し、`lib/std/list.yu` の `Index (ref 'e (list 'a)) int` impl へ移した。
  - lower / validate / refine の `nil` / `just` / `list` 末尾名判定を減らした。constructor は期待型との親子関係、list pattern は暫定的に単一 type arg shape を見る。
  - monomorphize の list / opt payload 抽出、var/ref 内部 refine、debug filter から std path 再判定を減らした。`associated.rs` / `check.rs` / `emit.rs` は、list / opt / ref の result type constructor を直書きせず、既存 signature / runtime type に出ている `Named` constructor を再利用する。runtime monomorphize / lower / refine / validate の production scan では `path_is(... ["std", ...])` / `path_has_prefix(... ["std", ...])` / `ends_with(...)` / `path_ends_with` は検出されない。
  - infer の `std_var_ref_path` / `is_std_var_ref_path` は `Infer::ref_type_paths` metadata へ寄せた。selection は `Infer::is_ref_type_path` を見る。
  - infer の role method prefix suffix match を外し、canonical role path の完全一致だけにした。
  - `for` / `sub` / labelled loop sugar 入口の `std::flow` path 構築は `std_flow_paths` へ集約した。
  - runtime lower の `std_types` は `primitive_types` に置き換えた。`Lowerer` は `RuntimePrimitivePathTable` を持ち、literal / bool / unit は expression / pattern / evidence / effect helper まで table 経由で型を作る。
  - primitive type family metadata は `CoreGraphView::primitive_types` に載せた。infer export は `LowerState::primitive_paths` から graph node を吐き、runtime lower は graph metadata を優先して table を作る。
  - compiled runtime surface merge は primitive metadata を保持し、同じ family が異なる path を指す場合は conflict として拒否する。
  - infer primitive bootstrap の型/value path は `builtin_types` に集約した。`LowerState` は `PrimitivePathTable` を持ち、list literal / list pattern / string concat は state table 経由で path を読む。
  - `$x` fallback と var synthetic act helper source は `std_ref_paths` 経由にした。
  - ref field projection selection は `Infer::primary_ref_type_path` から ref constructor を再利用し、固定 `std::var::ref` path を再生成しない。
  - `for` / `sub` / labelled loop / `$x` / `&x = v` は標準 protocol への糖衣展開として扱い、新しい compiled artifact metadata は導入しない。
  - 残る本丸は primitive family table を persistent compiled-unit artifact metadata から渡すこと。std source へ専用 metadata を足す方向にはしない。
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
