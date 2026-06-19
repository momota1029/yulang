# Track 1 (Native Backend): 完了履歴 (2026-05-14 時点)

`tasks/current.md` Track 1 から退避した完了済みマイルストーンの記録。
active な計画は `tasks/current.md` を参照。

## 直近 TODO に積まれていた完了済み事項

### Native control IR / closure conversion

- `if` は branch + merge block param として lowering / native-control eval / VM compare まで追加済み。
- local block binding は simple `Bind` / `Wildcard` pattern だけ lowering / VM compare まで追加済み。
- direct monomorphic call は non-polymorphic binding の curried lambda を `NativeFunction` に落とし、root expression からの direct call を lowering / native-control eval / VM compare まで追加済み。
- call arity mismatch は lowering の構造化エラーにした。
- 複数 binding と小さい再帰 call は VM compare まで追加済み。
- ordinary native-control closure conversion skeleton として `closure_convert_module` を追加した。
- runtime `Lambda` は native-control の generated function + `MakeClosure` に lowering する。non-direct `Apply` は `ClosureCall` に lowering する。
- immediate lambda call と captured local を持つ lambda call は VM compare まで追加済み。
- `NativeFunction.captures` で closure-generated function の capture params を明示する。`closure_convert_module` は captures を environment slots に分離し、通常 params と分ける。
- closure-converted body 側に `LoadEnv` を追加し、capture param を entry block param から外して environment slot load として明示するところまで追加済み。
- `MakeClosure` は closure-converted IR 上で code target + environment slot values の allocation として表す。
- closure-converted function は `NativeClosureAbi` を持ち、code ref / environment slot count / non-capture params を backend が読める形に分ける。
- `lower_closure_module_to_abi` は closure-converted IR を backend-neutral ABI IR に落とす。`LoadEnv` / `AllocateClosure` / `IndirectClosureCall` / `DirectCall` が Cranelift 手前の境界になる。
- `validate_abi_module` は function/block/value uniqueness、use-before-def、env slot range、terminator target を検査する。
- `validate_cranelift_prototype_subset` は最初の Cranelift prototype 用に、int/float/bool/unit literal、数値/bool primitive、direct call、局所 closure allocation/call を許可する。string/list は runtime ABI が固まるまで明示 unsupported。
- `format_abi_module` は ABI IR を stable text dump にする。Cranelift prototype 前の golden/debug 出力に使う。

### CPS lowering / CPS repr / CPS repr ABI

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
- CPS eval / CPS repr eval の plain `VmValue` primitive は native-control evaluator を再利用する。これで string/list の range / splice / view / equality / conversion が value backend と同じ意味になる。
- `analyze_cps_repr_values` は CPS repr value を `Plain` / `Resumption` / `Unknown` に分類する。handler entry の payload/resumption param と `Resume` の result kind を構造から追い、resumption を heap pointer lane へ落とす前段にする。
- `analyze_cps_repr_abi_lanes` は CPS repr value / continuation return を `ScalarI64` / `NativeFloat` / `RuntimeValuePtr` / `ThunkPtr` / `ResumptionPtr` / `OpaqueI64` / `Unknown` に分類する。effect 名や std path は見ず、handler entry の第 2 引数と `Perform` / `Resume` の構造から resumption lane を出す。
- `lower_cps_repr_abi_module` は CPS repr に lane 情報を貼り、continuation params / environment slots / return lane を Cranelift lowering が読みやすい形へ束ねる。まだ machine layout は選ばず、effectful control を codegen 境界まで運ぶための ABI skeleton に留める。
- CPS repr value / ABI lane 解析では `Unknown` を初期未確定値として扱い、既知 lane / value kind で精密化するようにした。異なる i64 系 lane が合流した場合は `OpaqueI64` に上げ、未確定値へ戻して固定点を揺らさない。

### CPS repr Cranelift JIT

- `compile_cps_repr_abi_module` は scalar CPS repr ABI を Cranelift で実行する最初の入口。pure 関数は continuation を Cranelift block、`Continue` は jump、`Branch` は brif に落とす。
- effectful 関数では CPS continuation を個別の JIT 関数に分ける。`Perform` は resume continuation の code pointer と captured scalar environment snapshot から heap resumption を作って handler entry へ渡し、`Resume` は helper 経由で resumption を呼ぶ。non-tail resume と同じ resumption の複数回呼び出しは確認済み。現時点では scalar i64 / environment 4 slot までの prototype。
- runtime `Handle` / `EffectOp` 由来の CPS repr Cranelift 比較を追加した。単純 resume、同じ resumption の複数回呼び出し、perform 後の rest-of-computation、effectful branch を VM と比較している。
- source から CPS repr Cranelift へ入る `eval_source_cps_repr_i64(_with_options)` / `compare_source_cps_repr_i64(_with_options)` を追加した。prelude なしの小さい `act` / `catch` source は VM と CPS repr Cranelift で比較済み。
- CLI に `--native-cps-repr-i64` を追加した。source から runtime lower / monomorphize した module を VM と CPS repr Cranelift scalar i64 で比較する debug entrypoint。
- CPS lowering は root から reachable な runtime binding だけを lower する。std/prelude を読む source でも、到達不能な std の非関数 binding / unsupported binding が CPS repr Cranelift の scalar prototype を止めないようにした。
- prelude ありの source literal と、prelude ありの小さい source-defined `act` / `catch` は CPS repr Cranelift で VM 比較済み。
- handler の value arm は CPS lowering で扱う。pure body は value arm continuation に入り、resume で戻った値は VM と同じく value arm を再適用しない。
- `std::flow::sub::sub { std::flow::sub::return 41 }` は CPS repr Cranelift で VM 比較済み。CPS lowering は、`fun x -> handle x ...` 形の thunk handler wrapper が thunk 引数へ直接適用される場合、thunk を汎用値 lane にせず handle body へインライン展開する。
- 汎用 thunk value lane / thunk invocation はまだ未対応。wrapper を越えて thunk を保存・返却・複数箇所で渡す場合は次の段階で扱う。
- `compile_runtime_module_to_cps_repr_jit` は runtime module -> CPS -> CPS repr -> CPS repr ABI -> Cranelift まで通す helper。現時点では pure scalar root の実行確認用。
- `compare_cps_repr_cranelift_i64` は VM と CPS repr Cranelift の scalar root を比較する regression entrypoint。まず `20 + 22` の runtime module で固定した。

### Value-lane Cranelift

- `yulang-native::source` に実験用の文字列 source entrypoint を追加した。現時点では `source -> infer/export -> runtime lower/monomorphize -> native-control eval` の薄い adapter で、backend 本体は引き続き `runtime::Module` を入口にする。
- `compile_abi_module` は Cranelift JIT prototype を追加した。現時点では `i64` scalar ABI として int/bool/unit literal、int/bool primitive、direct call、branch/jump/return を扱う。float/string/list は runtime ABI が固まるまで scalar JIT では unsupported。
- `compile_abi_module_to_object` は Cranelift object backend の最小入口。JIT と同じ scalar ABI lowering を使い、`NativeAbiModule` から object bytes を出す。source 起点の `compile_source_object(_with_options)` も追加済み。CLI の `--native-object <path>` でも source から object file を保存できる。CLI の `--native-exe <path>` は一時 C harness と system `cc` で scalar root を呼ぶ実行ファイルを作る。現時点では prototype harness で、runtime helper symbol を必要としない scalar subset に限定する。
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
- `str` / `list` / `record` は `archive/notes/design/native-value-abi-plan.md` の opaque runtime value pointer lane で進める。scalar-only `compile_abi_module` は残し、value lane は別 entrypoint として追加する。
- `analyze_abi_reprs` は ABI function/value を `Int` / `Bool` / `Float` / `List(element)` / `RuntimeValuePtr` / `ClosurePtr` / `Unknown` に分類する。`List` は machine boundary では pointer lane のままだが、singleton/index/merge/range 系で分かる範囲の element repr は伝播する。tuple/record repr は後続の runtime type 連携で足す。
- `compile_value_abi_module` は scalar-only `compile_abi_module` と別の Cranelift value-lane prototype entrypoint として追加した。現時点では string literal と `StringConcat` primitive/direct call を Rust helper 経由で `VmValue::String` に戻す。
- `eval_source_value_lane_with_options` は source から value-lane Cranelift まで通す実験入口。`"hello"` / `"a" + "b"` の round-trip と、source からの string/list ABI repr analysis をテストで固定した。
- value-lane Cranelift は int literal を opaque `VmValue::Int` pointer として作れるようにした。`ListEmpty` / `ListSingleton` / `ListMerge` も Rust helper 経由で `VmValue::List` を作る。`[1, 2, 3]` は source から value-lane Cranelift まで round-trip 済み。
- `compile_value_abi_module_to_object` は value-lane Cranelift lowering を object backend でも使う。JIT では host `Box<str>` を生存保持し、object では literal bytes を data section に置くため、生成 executable でも string / int literal pointer が有効なままになる。
- CLI の `--native-value-exe <path>` は一時 C entry harness、value-lane object、`yulang-native` staticlib を system `cc` で link する。`int` / `str` / `list` は Rust `native_runtime` の `VmValue` ベース helper を呼び、`"a" + "b"` と `[1, 2, 3]` が executable として動く。
- `native_runtime` module を追加し、JIT value helper の本体を Rust API 境界へ移した。内部表現はまだ `VmValue` だが、Cranelift から見る helper API は `make_int` / `make_string` / `concat_string` / `list_*` に集約した。
- value-lane Cranelift は bool / unit / float literal も opaque `VmValue` pointer として作れるようにした。`ListLen` / `ListIndex` も Rust helper 経由で `VmValue` を返す。JIT と native runtime API の小さい regression で固定した。`--native-run-value-exe` でも `true` / `()` / `1.5` と `[1, 2].len` / `[1, 2].index 1` の executable 出力を確認済み。
- value-lane Cranelift は `ListIndexRangeRaw` も Rust helper 経由で `VmValue::List` を返す。`std::list::index_range_raw [1, 2, 3, 4] 1 3` は JIT / object 生成 / `--native-run-value-exe` で確認済み。
- value-lane Cranelift は `ListIndexRange` も Rust helper 経由で range 値を正規化して `VmValue::List` を返す。`std::list::index_range [1, 2, 3, 4] (std::range::range 1 3)` は JIT / object 生成 / `--native-run-value-exe` で確認済み。
- value-lane Cranelift は `ListSplice` / `ListSpliceRaw` / `StringIndexRange` / `StringIndexRangeRaw` / `StringSplice` / `StringSpliceRaw` も Rust helper 経由で `VmValue` を返す。list splice と string range/splice は JIT / object 生成 / `--native-run-value-exe` で確認済み。
- value-lane Cranelift は tuple / record / variant も opaque `VmValue` pointer として作れるようにした。native IR / ABI IR には構造値 stmt を追加し、codegen では `tuple_empty` / `tuple_push`、`record_empty` / `record_insert`、`variant` helper へ落とす。`--native-value-exe` で `(1, 2)` / `{x: 1, y: 2}` / `:label "send"` の executable 出力を確認済み。
- value-lane Cranelift は `ListViewRaw` と record spread expression も Rust helper / record base lowering 経由で扱う。`std::list::view_raw []` / `[1]` / `[1, 2]` と `{ ..{x: 5}, y: 6 }.x` / `{ x: 7, ..{y: 8} }.y` は JIT / object 生成で確認済み。
- value-lane Cranelift は branch / jump と Bool helper を追加し、effect-free `if` と variant / tuple pattern match の小さい核を扱う。`:just (1, 2)` の tuple payload bind と `std::list::view_raw [1]` の `:leaf x` match は JIT / object 生成で確認済み。
- value-lane Cranelift は boxed `VmValue` equality helper を追加し、literal pattern match も扱う。`case 2` と `case ()` の literal arm は JIT / object 生成で確認済み。
- value-lane Cranelift は list pattern の長さテストと irrefutable な prefix/spread/suffix bind も扱う。`[head, ..middle, tail]` と `[..init, z]` は JIT / object 生成 / executable で確認済み。
- value-lane Cranelift は pattern 全体の Bool 条件を `BoolAnd` で合成し、refutable list item test も扱う。`[0, x]` fallback 後の `[1, x]` は JIT / object 生成で確認済み。
- value-lane Cranelift は closure を opaque runtime handle として作り、target id と environment value list を native runtime 側に保持する。`IndirectClosureCall` は handle から target id を読み、同じ arity の compiled function 群へ Cranelift 上で dispatch する。これにより closure value は block param / jump をまたいで indirect call できる。ABI repr 解析も jump block param へ value repr を伝播するようになり、closure root や tuple/list/record/variant の `VmValue` helper に closure handle を渡す形は codegen 前に structured unsupported として止める。source 側の `my f = if true { \x -> x + base } else { \x -> x }; f 2` も、0 引数 binding を closure-producing callee として評価してから indirect closure call する形で `--native-run-value-exe` まで確認済み。さらに top-level 関数の部分適用は `#partialN` wrapper を生成し、bare function value を `#partial0` の closure handle として扱う。`my add x y = x + y; my f = add 40; f 2` は source から value-lane executable まで確認済み。ABI validate / value-lane Cranelift の定義済み値解析は、function params と predecessor block で定義された値を後続 block の開始時点へ伝播するようにした。これにより std の `list.map` / `list.filter` / `list.fold` が source から `--native-run-value-exe` まで通る。ただし closure を printable `VmValue` root として返す形や、tuple/list/record 内の普通の構造値として扱う形はまだ未対応。
- value-lane Cranelift は guarded pattern match も扱う。pattern match 後に pattern locals を bind した guard block を挟み、false guard は次 arm へ fallthrough する。bool literal guard と pattern-bound bool guard は JIT / object 生成で確認済み。guard 内で `n < 50` / `n + 1` のように std 演算子 wrapper を引く source も value-lane Cranelift で確認済み。
- record pattern shorthand は infer lowering で pattern node と guard/body が同じ local definition を共有する。`{flag, width}` は関数引数 pattern と guarded case arm の両方で確認済みで、value-lane Cranelift の guarded match でも `{ok, n}` を JIT / object 生成で確認済み。
- record-spread pattern は VM で明示 field を除いた残りの record を spread pattern に渡す。native control IR / ABI IR には `RecordWithoutFields` を追加し、value-lane Cranelift でも同じ helper 経由で VM 比較済み。

### Source identity / cache layout

- `yulang-sources` に realm / band の薄い identity 型を追加した。既存の `SourceSet` は「今回コンパイルに集めた source aggregate」のまま残し、realm / band を source identity layer として上に置く。
- cache layout は `target/yulang` / persistent user cache / project lock に分ける。`YulangCachePaths` は `target/yulang`、`YULANG_CACHE_DIR` / `XDG_CACHE_HOME/yulang` / `~/.cache/yulang`、`realm.toml`、`yulang.lock` を一箇所で定義する。compiled-unit artifact と fetched realm は user cache 側、debug dump と native experiment output は `target/yulang` 側に置く。`target/yulang` の中は `bin` / `obj` / `build` / `dump` に分ける。CLI の native executable link scratch は `target/yulang/build` を使う。`--native-object` / `--native-exe` / `--native-value-exe` は output path を省略した場合、それぞれ `target/yulang/obj/<entry>.o`、`target/yulang/bin/<entry>`、`target/yulang/bin/<entry>-value` に出す。`--native-run-exe` / `--native-run-value-exe` は同じ場所に link してから生成実行ファイルをそのまま実行する。
- `CompiledUnitArtifactCache` は full compiled-unit artifact の JSON write/read を persistent user cache 側へ行う。現在は保存層のみで、lowering pipeline の cache hit/miss へ繋ぐのは次段。
- CLI は `--native-abi-lanes` で source から native ABI repr classification を表示できる。未使用の closure-returning wrapper と reachable scalar direct wrapper の違いを見るための debug entrypoint。

### CPS lowering: effectful 拡張

- CPS lowering は primitive binding を普通の CPS function として扱う。`std::int::add` のような prelude operator wrapper 経由の primitive call を effect handler arm から呼べる。
- CPS repr Cranelift は entry continuation params を function params として bind する。これにより primitive binding や ordinary multi-arg CPS function を JIT できる。
- source-defined `act` / `catch` で、同じ resumption を複数回呼び、その結果を primitive call で合成する scalar program は VM と CPS repr Cranelift で比較済み。
- handler arm body の direct call / local block binding / value arm も source から CPS repr Cranelift まで通している。
- source `if true: ... else: ...` のような bool match に落ちる handler arm branch は CPS repr Cranelift まで通る。分岐先 continuation が捕捉する scalar / resumption pointer environment も小さい helper で作って渡す。
- source `if x < 0: ... else: ...` のように prelude の比較演算子が `std::junction::junction` handler へ展開される形も CPS repr Cranelift まで通る。CPS handler boundary は複数 effect arm を持てるようにし、`Perform` は実際の effect operation から arm entry を選ぶ。到達しない handler arm は materialize せず、direct function の thunk 引数は必要な範囲だけインラインする。
- source `if x < 0 or x == 0: ... else: ...` / `and` も CPS repr Cranelift まで通る。lazy operator wrapper への direct call は、thunk 引数を持つ場合に reachable binding として JIT 対象へ入れず、呼び出し地点で限定インラインする。これにより `std::ops::or` / `and` の closure parameter call を、汎用 closure value lane がない段階でも regression として固定できる。
- source 条件式の追加回帰として `not (x < 0)`、nested `if` condition、let-bound condition も CPS repr Cranelift で VM 比較済み。plain bool に落ちる条件式の範囲では、現行の限定 thunk インラインと continuation capture 伝播でかなり自然に動く。
- CPS capture 推論は、`Continue` / `Branch` / `Perform` が呼び出す先の continuation environment を作るために必要な captures を分岐元・呼び出し元へ伝播する。branch 先が resumption pointer を捕捉する場合も Cranelift 側で null environment に落ちない。
- `BindHere` は handler body 全体の wrapper としては単独 unwrap しない。ただし primitive / direct call の引数位置や block statement 内で effect operation を見つけるときは実行位置 marker として透過する。

### Dynamic handler frame / guard stack

- effectful control を native に載せるには、CPS repr に VM と同等の dynamic handler stack と effect-id hygiene が必要。CPS evaluator / CPS repr evaluator は resumption に handler stack を持たせ、`ResumeWithHandler` で再開先を新しい handler の内側へ rebase できる。`LocalPushId` / `PeekId` / `FindId` は CPS guard stmt へ lowering する。`AddId` は allowed effect から blocked guard を判断し、CPS `Perform` へ blocked id を伝播するところまで追加済み。`EffectIdRef::Var` は enclosing `LocalPushId` の guard 値へ解決する。handler body 専用 lowering でも同じ scope map を使うため、`g h` のような callback force 境界で `h()` 由来の effect boundary を落とさない。
- CPS repr evaluator は guard id を偽値に潰さず、handler frame ごとの guard stack snapshot を resumption / thunk に保持する。`Perform` は blocked id が handler frame の snapshot に含まれる場合、その frame を skip して外側の handler を探す。これを `skips_handler_frame_blocked_by_guard_snapshot` で固定した。
- CPS repr ABI lane 解析は direct call argument lane を callee params へ固定点で伝播する。recursive thunk callback のように thunk value が callee param を経由して返る場合も、`ThunkPtr` lane として見える。
- CPS repr Cranelift は continuation environment を持つ関数を、effect の有無に関係なく continuation function path へ回す。lazy branch condition が thunk-valued continuation param を経由する場合は、branch の直前に thunk を force して bool として判定する。
- CPS repr Cranelift helper は JIT / object runtime の両方で thunk pointer を registry に登録し、force helper は値が登録済み thunk pointer である限り trampoline として実行を続ける。これは scalar CPS repr subset 用であり、generic runtime value pointer を force しないために `ThunkPtr` lane と `RuntimeValuePtr` lane を分ける。
- CPS repr Cranelift に scalar guard stack helper を追加した。`FreshGuard` は fresh id を stack に push し、`PeekGuard` は top を読み、`FindGuard` は stack membership を返す。
- CPS repr Cranelift の scalar runtime は resumption / thunk に handler stack snapshot と guard stack snapshot を保存する。`Resume` は snapshot を復元して continuation を呼び、`ResumeWithHandler` は現在の guard stack を持つ handler frame を resumption の handler stack へ追加してから再開する。
- CPS repr Cranelift の `Perform` は静的 handler entry へ直行せず、runtime helper で現在の handler stack を走査する。effect に合う handler id mask と blocked guard id を渡し、blocked frame を飛ばして選ばれた handler entry へ分岐する。`jit_skips_handler_frame_blocked_by_guard_snapshot` で scalar JIT の回帰を固定した。
- CPS repr Cranelift の thunk 作成時に、利用可能な handler arm environment を handler frame へ snapshot するようにした。これで handler entry が捕捉する scalar 値を perform 側 continuation から無理に読む問題は一段進んだ。
- mutable reference regression は CPS lowering / validation / Cranelift 実行まで VM と一致する。`run state (thunk (k unit))` のような handler re-entry は `ResumeWithHandler` に落とし、再設置する handler arm environment を scalar runtime へ渡す。
- same-function handler re-entry は最小形を通した。Cranelift は `ResumeWithHandler` の rebase 時に handler arm env を pending frame として capture し、handler 選択時に entry ごとの env を復元する。

### Undet / finite nondet

- `std::undet.once` は統合 target として重すぎるため、`archive/notes/design/native-undet-plan.md` に分解計画を置いた。現在の native regression は local `choice` act で `branch` / `reject` / DFS once を scalar root に畳む段階まで通している。
- finite list nondet は `fold` / `sub` を使わず、`std::list::uncons` と local `choice::branch` / `choice::reject` だけで scalar root へ畳む regression が Cranelift CPS repr と VM で一致する。
- `std::undet` の `.once` は finite list の例で CPS repr object/executable まで compile できる。ただし `each [1, 2, 3] .once` の native-run result はまだ VM と一致せず、現状は `:just 0` になる。handler id は module 内で global に renumber され、`Perform` codegen は effect に合う handler arm を module 全体から候補化するところまで入ったが、`each` / `fold_impl` / `sub::sub` をまたぐ thunk force と dynamic handler stack の意味論は未完了。

## 「処理系化へ近い次の順番」プラン 1 完了分

CPS repr Cranelift の guarded thunk effect-flow 設計。

- 完了: `run state (thunk (k value))` は handler wrapper 構造を見て `ResumeWithHandler` へ落とす。
- 完了: mutable ref regression は VM/JIT compare のまま通り、`ignore` を外した。
- 完了: 最小 `once` kernel として、tail effect operation と boolean match condition の `branch` を handler が `k true` で再開する source regression を追加した。
- 完了: queue を使わない DFS once kernel と、`fold` / `sub` を使わない finite list choice を scalar root の VM/JIT compare に足した。
- 完了: `sub` / `return` の callback hygiene は source-level CPS repr compare に足した。`g` 内の direct `f()` は内側 `sub` で捕まり、callback `h()` は外側 `sub` へ抜ける。
- 完了: CPS repr Cranelift は `IntToString` を prototype string handle へ lower し、`1.show` のような scalar-to-string root を executable path で表示できる。
- 完了: CPS repr Cranelift は `IntToHex` / `IntToUpperHex` / `BoolToString` も同じ prototype string handle へ lower できる。
- 完了: CPS repr Cranelift は `NativeFloat` lane を `f64` として扱い、float literal / arithmetic / comparison / `FloatToString` を非 capture の scalar path で実行できる。
- 完了: CPS repr Cranelift は plain value に挟まる `ForceThunk` で `NativeFloat` lane を i64 force helper へ落とさず、そのまま f64 として次の primitive / direct call へ渡す。source の `(1.5 + 2.0).show` / `(5.0 - 2.0).show` / float equality console 出力は native CPS repr exe で確認済み。
- 完了: CPS repr Cranelift は string literal と raw string primitive の小さい核 (`StringConcat` / `StringEq` / `StringLen` / `StringIndex` / `StringIndexRangeRaw` / `StringSpliceRaw`) を prototype string handle へ lower できる。`println "hello"` / `println ("yu" + "lang")` は native CPS repr exe で確認済み。
- 完了: CPS repr Cranelift は `range::within` / `bound` variant を読んで、`ListIndexRange` / `ListSplice` / `StringIndexRange` / `StringSplice` を raw helper と同じ prototype heap value 上で実行できる。`("aあ🙂z").index (1..<3)` と `([1, 2, 3, 4].index (1..<3)).len` は native CPS repr exe で確認済み。
- 完了: CPS repr Cranelift は record construction / field selection を prototype heap value として扱える。`({ answer: 42, other: 10 }).answer` は native CPS repr exe で確認済み。
- 完了: CPS repr Cranelift の prototype heap value 表示を `ptr(...len=...)` ではなく Yulang 値に近い形へ寄せた。`(1, [2, 3], { answer: 42 })` は native CPS repr exe で同じ形に表示される。
- 完了: CPS repr Cranelift の unhandled host console effect fallback を追加した。`console.print` / `println` は payload を出力して unit で resume する。これで `println b.show` を含む direct/callback `sub` hygiene 例も native CPS repr exe で動く。
- 完了: `each_head(xs): [choice] int` のように effectful thunk を返す inlinable な source-defined helper は、caller の active handler scope で inline され、`lower_inline_direct_apply` が返した thunk を direct call site で force するようにした。CPS eval / CPS repr eval / Cranelift JIT のすべてが VM と一致する。
- 完了: `each_list` のような recursive helper も runtime handler stack 経由で caller の handler に effect を届けるようになった。CPS lowering は handler scope の入口と出口に `InstallHandler` / `UninstallHandler` stmt を生成。CPS evaluators は `DirectCall` / `ApplyClosure` / `ForceThunk` で `active_handlers` / `guard_stack` を callee に伝える。Cranelift は thread-local handler stack を扱う既存 runtime に `yulang_cps_install_handler_i64` / `yulang_cps_uninstall_handler_i64` を追加して同じ semantics を実現している。`each_list [1, 2, 3]` の Milestone 6 regression は VM と一致する。
- 完了: pure higher-order call の第一歩として、lambda を CPS closure に lower し、Cranelift CPS repr で indirect apply できるようにした。

## 達成済み「直近 milestone」

CPS repr Cranelift に dynamic handler frame / guard stack を入れ、mutable reference regression を native 実行対象へ戻す。これは達成済み。

- CPS repr evaluator 側では handler frame guard snapshot と blocked skip を固定済み。
- Cranelift 側には scalar guard helper があり、scalar effect-flow の `ResumeWithHandler` は mutable ref regression で確認済み。
- resumption object は continuation env だけでなく handler stack snapshot と guard stack snapshot を持つ。
- handler frame は handler entry、captured environment、entry guard snapshot を runtime に渡せる layout にする。
- `Perform` lowering は compile-time の handler entry 直行をやめ、blocked guard を見て外側 handler へ送れるようにする。
