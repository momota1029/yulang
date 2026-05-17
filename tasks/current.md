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
- `notes/design/native-direct-style-islands.md`
- `notes/design/source-realm-band-plan.md`

方針:

- native 実行の本線は effects backend（内部実装は CPS representation）に寄せる。
- user-facing な実行入口は `yulang run --native` とする。将来的に native が標準に
  なったら、interpreter は `yulang run --interpreter` 側へ寄せる。
- フル機能の native 化は、CPS を遅い実行方式として固定するのではなく、
  effect-aware CPS IR を最適化してから Cranelift の JIT / object / executable
  へ落とす形に寄せる。
- 最適化の中心は known continuation の direct jump 化、administrative
  continuation / thunk の除去、effect evidence による handler / delimiter
  frame の静的消去、非 escape closure / continuation / thunk の stack / SSA 化、
  pure な CPS continuation subgraph の direct-style / SSA island 化、
  call-site の型 / effect / handler evidence が具体化した高階制御 pattern の
  specialization とする。std の loop / fold / nondet helper / handler wrapper は
  代表的な hot path だが、optimizer は std module path や関数名に依存しない。
- pure-subset backend は effect-free speed-checking path と boxed `VmValue`
  helper の供給元として扱う。
- まず `notes/design/native-cps-mainline-plan.md` の milestone に沿って、
  backend selection 境界、CPS `RuntimeValuePtr` lane、汎用 thunk / closure /
  resumption value の順に進める。
- `select_native_backends` は runtime module から root ごとに
  `ValueFastPath` / `CpsMainline` / `Unsupported(reason)` を返す。
  これは pure-subset coverage と構造化された unsupported reason を見るための
  helper として残し、user-facing な native run は effects executable path を本線にする。
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
- CPS repr ABI lowering と Cranelift JIT/object codegen の間に
  `cps_optimize` entrypoint を挟んだ。現時点では explicit call site から空の
  forwarding continuation と `Return(param)` continuation を潰し、構造上 primitive
  wrapper と分かる direct call を `Primitive` stmt に戻し、literal bool branch を
  fold し、同じ continuation 内で
  作った partial-application closure の `ApplyClosure` を `DirectCall` に戻し、
  continuation parameter 経由で渡った known partial-application closure も、
  capture を target parameter に張り替えられる場合は `DirectCall` に戻し、
  known closure の `EffectfulApply` terminator は `EffectfulCall` か
  pure primitive + resume `Continue` に戻し、
  unused continuation parameter と対応する continuation-call argument を削り、
  small pure direct callee を caller に展開し、total primitive stmt /
  structural projection まで含めて dead pure value statement を削り、到達不能
  continuation を削る。
  `CpsOptimizationProfile` には最適化後の continuation / statement 数も出し、
  `bench/native_cps_opt_trace.sh` で interpreter / pure-subset exe / effects exe /
  default native の小さい比較と `YULANG_CPS_OPT_TRACE` をまとめて見られるようにした。
  small single-use one-shot continuation の tail inline と dead pure value statement
  の削除も入った。profile /
  `YULANG_CPS_OPT_TRACE` も出せる。inline 後に同じ reify をもう一度走らせるので、
  continuation 境界を挟んだ partial application も inline で局所化した後に潰せる。
  direct-style / SSA island 候補数も profile に出る。artifact kind ごとに pass が
  分岐しない入口を先に固定した。
- CPS repr Cranelift の effectful continuation function lowering で、pure successor
  continuation を同じ Cranelift 関数内の block として吸う最初の direct-style island
  codegen を入れた。`Continue` / `Branch` は block jump に戻し、island exit の
  `Return` は従来の `yulang_cps_return_i64` routing を保つ。
- 2026-05-16 round-7 prompt-1 で、handler install の prompt-exit return frame が
  effectful call の post frame を継承 frame 扱いしていた経路を修正した。
  `list.show/debug`、`for` body 内の `if` からの var write、`loop with` の
  `if` result、range `for` body の console effect は手元 regression / CLI で確認済み。
  続けて indexed ref update の `ScopeReturn` / resumption 経路も修正した。
  resumption に保存する handler stack の return-frame threshold を captured
  frame slice に合わせて rebase し、`ResumeWithHandler` で handler env を
  差し替えた inherited arm の plain result は古い prompt へ包み直さず normal
  value として返す。JIT では selected handler env が RWH sibling 由来の場合だけ
  inherited escaped finish を normal value として扱う。`runs_indexed_ref_update_through_cps_repr`
  で regression 化済み。`runs_junction_condition_without_once_through_cps_repr` と
  nested undet 系は HEAD でも同じ失敗を再現するため、今回の回帰ではなく既存の
  native CPS routing 未解決として扱う。
- 2026-05-16 round-8 で `runs_effect_handler_guard_through_cps_repr` の JIT
  root display を修正した。CPS repr ABI の scalar lane は `int` / `bool` /
  `unit` を同じ `i64` に載せるため、root の静的 runtime type が `unit` のときだけ
  display hint で `0` を `()` として表示する。これは実行値の routing ではなく
  root 表示境界の問題。
- 2026-05-16 round-9 で `runs_recursive_effect_handler_tuple_result_through_cps_repr`
  の JIT 経路を修正した。`EffectfulForce` terminator は resume frame を push した後、
  thunk 本体だけを `initial = return_frames.len()` の fresh eval で force し、force
  が値を返した後に `initial = pre_push_count` へ戻して post continuation を消費する。
  これで handler 内の `Perform` は post frame を capture できるが、thunk 本体の plain
  `Return(Thunk)` は outer frame を先に消費しない。さらに force loop は abort /
  ScopeReturn active で payload thunk を通常 thunk として剥き続けず、root abort
  payload は残った prompt-exit frame を捨ててから必要なら force する。
- effectful continuation function 内から pure callee function を `DirectCall` する
  場合は、eval context 切替 / abort-result routing / scope-return check を挟まず
  普通の Cranelift call として lower する。
- `EffectfulCall` terminator でも callee が pure function と分かる場合は、CPS
  optimizer で `DirectCall` stmt + resume continuation への `Continue` に戻す。
  これで return-frame push と callee eval-context switch の経路に入らない。
- CPS optimizer の簡約列を small bounded fixpoint にした。`EffectfulCall` の巻き戻しで
  露出した `DirectCall` を同じ entrypoint 内で pure callee inline し、その結果で
  露出した returner / forwarding continuation も後続 round で消せる。
- small pure direct callee inline は scalar primitive だけでなく、tuple / record /
  variant / select 系の structural value helper も展開できる。
- pure direct callee が引数をそのまま返す identity wrapper の場合でも、
  現時点では call を消さない。試験的に alias 化したところ finite `for` /
  `last` の native JIT が `5` ではなく `0` を返したため、scope-return
  boundary evidence なしの copy propagation は禁止する方針を
  `notes/design/native-direct-style-islands.md` に明記した。
- captured closure を tuple に入れ、tuple pattern で取り出して呼ぶ source
  regression を effects executable path に追加した。
- `ScopeReturn` routing の prompt-only 化は却下した。finite list `for` /
  `last` だけを見ると直ったように見えるが、nondet list / logic で外側
  handler を過捕捉して結果が一段余分に包まれる。current stack は
  `(prompt, current eval)`、return-frame walk は `(prompt, owner eval)` の
  ままにする。
- finite/open range `for` / `last` は native JIT でも後続 continuation へ戻れる。
  routed jump の consume は、保存済み return-frame prefix へ戻る必要がある場合だけ
  current native activation から返し、root/value-arm 境界の threshold 0 では通常値として
  後続へ渡す。これで open range の memory exhaustion と、guard block tail /
  finite undet list の値落ちを同時に避ける。

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
   - 現状: lazy operator / thunk 引数インラインの境界は
     `notes/design/native-cps-mainline-plan.md` と
     `notes/design/native-remaining-failure-matrix.md` へ切り出した。
     保存・選択・force される thunk value は CPS-level / 型変換後 runtime IR
     で通り始めている。
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

- native backend の残穴は `notes/design/native-remaining-failure-matrix.md` で追う。
  N1/N2/N3/N7/N8/N9/N10/N11 は source regression または structured
  unsupported として固まった。残りは N4/N6 の prototype / packaging 境界と、
  N2 周辺のより広い source-shaped effectful thunk coverage。
- mutable ref 以外の user-defined state/effect wrapper は、VM 比較へ足す候補として
  N2 の stored callback hygiene と一緒に扱う。
- std `undet.once` / `.list` / `.logic` は finite list の forced CPS repr
  executable path で VM と一致する。次は同じ handler / resumption 経路を
  named structural value や stored thunk path の回帰へ広げる。
- effectful callback の handler frame は関数境界をまたいで選択できるように
  なった。次は current-handler `ScopeReturn` を interpreter と同じ「eval loop
  jump」として扱うか、同等の scoped short-circuit を continuation boundary で
  消費する。
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
- N13 (`all/any` + finite `each` + record method + `.once`) は Cranelift JIT
  でも `:just 18` で VM / CPS eval / CPS repr eval と一致するようになった。
  原因は JIT の thread-local return frame stack が、thunk 内で未処理の
  `ScopeReturn` を外へ伝播する時に caller の frame snapshot を戻していなかった
  ことと、scoped abort が handler install threshold ちょうどでも即 return
  扱いになっていたこと。`force_thunk_i64` は routing 済み stack は残し、
  未処理の `ScopeReturn` / abort では caller snapshot を復元し、普通の値では
  thunk 内で作られた frame だけ落とす。scoped abort は `frame_len > threshold`
  の間だけ外へ伝播し、threshold に戻ったら解除して再開する。
- indexed ref update の N12 regression も同時に確認した。`ResumeWithHandler`
  で追加された sibling handler / env を restored return-frame snapshot に
  合流させ、`my $xs = [2, 3, 4]; &xs[1] = 6; $xs` が Cranelift JIT でも
  `[2, 6, 4]` を返す。
- callback-return hygiene の observable source regression を forced CPS repr
  executable path に追加した。inner `sub` 内の直呼び `f()` は inner handler に
  捕まり outer root が `2` まで進む一方、thunk callback 経由の `h()` は inner
  handler を越えて outer `sub` から `0` を返す。
- finite-list `for` の中で外側 `sub` へ `return` する経路は、CPS repr
  Cranelift でも VM と一致する。handler arm が installed escape に到達済みの
  経路では、`perform_finish_escaped` が skipped force/apply chain へ abort
  signal を残すようにした。
- open-range `for` の `last` は forced/default CPS repr executable path で VM と
  一致するようになった。local handler arm value の `0` は scoped abort として
  recursive range/fold chain 内では返し続け、return-frame threshold の外側で
  consume して後続 continuation (`5`) へ戻す。
  `runs_open_range_for_loop_last_through_cps_repr` で regression 化した。
- `examples/10_effect_handler.yu` は forced CPS repr executable path で
  `(9, "3\n6\n")` 相当を返すようになった。ScopeReturn の stale thunk payload
  を force 後の値に更新し、duplicate selected handler env は newest-first に読んだ。
  `runs_recursive_effect_handler_tuple_result_through_cps_repr` で regression 化した。
- closure value を record に保存し、field select で取り出してから呼ぶ source
  regression を forced CPS repr executable path に追加した。CPS repr の
  `RuntimeValuePtr` record と `ClosurePtr` call 境界が同じ observable path に
  乗る。scalar / string environment を capture した closure も同じ path で通る。
- CPS-level thunk pointer を record に保存し、field select で取り出してから
  `ForceThunk` する Cranelift regression を追加した。source-level first-class
  thunk はまだ型/lowering 境界が残るが、native value lane 側の保存・選択・force
  の入口はできた。
- CPS-level thunk pointer を list に保存し、`ListIndex` で取り出してから複数回
  `ForceThunk` する Cranelift regression を追加した。`ListIndex` の `Unknown`
  lane からでも force 側で thunk pointer として扱える。indexed thunk が string
  heap value を返す path も固定した。
- 型変換後 runtime IR の `ExprKind::Thunk` を list に保存し、`ListIndex` で
  取り出してから `BindHere` で force する Cranelift regression を追加した。
  source surface ではなく、`ValueToThunk` adapter 後の構文を native が読む path を
  固定する。
- boundary 付き thunk pointer を list に保存し、`ListIndex` 後に force しても
  active boundary が handler selection に残る Cranelift regression を追加した。
  hidden callback effect が blocked inner handler を越える native 側の衛生性を
  構造値越しに固定する。
- boundary 付き thunk pointer を record に保存し、field select 後に force しても
  active boundary が handler selection に残る Cranelift regression を追加した。
  source selection を巻き込まない CPS-level structural storage として N2 を一段
  狭める。
- CPS-level closure pointer を list に保存し、`ListIndex` で取り出してから
  `ApplyClosure` する Cranelift regression を追加した。indexed closure call の
  返り値は `Unknown` lane のまま root へ返せるようにした。CPS repr の
  `Unknown` は transitional opaque i64 として root でも扱う。
- source-level closure value を list に保存し、`std::list::index_raw` で取り出して
  から呼ぶ forced CPS repr executable regression を追加した。direct call chain が
  over-applied の時は、その式全体を direct-call lowering で処理せず、通常の
  `Apply` lowering に戻して callee 側を先に評価する。scalar environment を
  capture した closure も list index 後に呼べる。string capture も同じ path で
  通る。
- source-level callback value を list に保存し、`std::list::index_raw` で取り出して
  から呼んでも return hygiene が保たれる regression を追加した。local parameter
  boundary wrapper は、callback の返した thunk を先に force せず、境界付き thunk を
  作ってから force 側へ渡す。これで stored callback 経由の `return` は inner `sub`
  を越え、caller 側の `sub` へ届く。
- lazy operator の結果を tuple value position に置く source regression を
  forced CPS repr executable path に追加した。tuple 内部でも thunk が可視値として
  漏れず、native i64 表示 helper も tuple payload を再帰的に整形する。
- lazy operator の結果を list value position に置き、`std::list::index_raw` で
  取り出す source regression を forced CPS repr executable path に追加した。
  型変換後 thunk adapter が list payload に残っても、index 後の表示では
  plain bool value として VM と一致する。
- lazy operator の結果を record field / variant payload position に置く source
  regression も forced CPS repr executable path に追加した。N1 の structural
  coverage は tuple / list / record / variant までそろった。
- CPS repr lowering に source-shaped `case` の tuple / list / list-spread /
  record / record-spread / variant payload pattern test を追加した。arm-local bind
  も同じ構造パターンから直接落とすので、pure-subset backend だけに偏っていた
  structural pattern subset を CPS repr mainline 側にも寄せた。
- top-level `my {x, ..rest} = ...` も CPS repr path で通る。record rest は
  CPS IR の `RecordWithoutFields` として明示し、pure-subset backend の record-spread
  pattern 規則と同じ位置で処理する。
- record spread expression も CPS repr path へ入れた。CPS IR の `Record` は
  optional base record を持ち、base をコピーしてから明示 field を上書きする。
- record default pattern は CPS IR の `SelectWithDefault` で表し、field presence が
  必要な pattern test には `RecordHasField` を使う。match guard と list spread
  expression も source regression として固定した。
- examples sweep で `03_for_last.yu` / `04_sub_return.yu` の forced CPS repr が
  VM と合わないことを確認した。有限 list の再現は
  `notes/bugs/native_for_loop_escape_keeps_running.yu` に切り出し済み。外側
  `sub` handler は `return 2` を捕まえているが、その後の内側 fold/for chain が
  normal fallback `0` を返し続けて root を上書きする。
- top-level destructuring `my` は runtime IR が各名前ごとの `case` binding に
  分解され、native 側だけ再帰/クラッシュすることを
  `notes/bugs/native_top_level_destructure_binding_recurses.yu` に切り出した。
  direct `case` pattern は通るため、これは frontend/runtime IR の binding
  shadowing 形状と native global lookup の接続バグとして追う。
- CPS repr の direct-call reachability は value binding 展開に visited set を
  持つようにした。これで `x = case ... [x, y] -> x` の arm-local `x` を
  global `x` として無限展開しない。default `yulang native` は同じ形を
  structured `structural pattern binding` reason で CPS repr に回すので、forced
  value lane の nullary-binding crash を避けられる。さらに forced value lane は
  top-level structural pattern binding を unsupported として返し、crashing
  executable を生成しないようにした。
- native CLI の現状は `docs/native-backend.md` の Public CLI に集約済み。
  user-facing には `yulang run --native` を effects backend へ直接送り、
  `yulang native` は artifact generation / backend debugging 用として残す。
  `run-pure-exe` / `run-effects-exe` は debugging 用の強制 path として残す。
- pure-subset backend と effects backend の fallback policy を、握りつぶしではなく
  structured unsupported reason で選べる形へ寄せる。
- backend selection は closure value を `closure value` reason として effects
  backend へ回すようにした。direct closure root と record-contained closure root は
  pure-subset backend の失敗 fallback を待たずに、IR node ベースの selection で分岐する。
- list-construction primitive payload 内の closure value も同じ `closure value`
  reason で effects backend へ回す regression を追加した。
- boundary 付き thunk pointer を variant payload に保存し、payload projection 後に
  force しても active boundary が handler selection に残る Cranelift regression を
  追加した。
- playground は interpreter only として UI / native docs に明記した。
  native backend selection は今のところ CLI surface として扱う。

## 重要な制約

- VM は behavioral oracle のままにする。Native code は置き換えではなく、VM の横に追加する。
- 現 VM は nondet continuation の clone cost が大きい。playground/docs examples では
  無限選択を早めに絞り、VM 参照化は native backend / control IR 作業と一緒に扱う。

## Track 2: Parser Combinators

parser combinators を Yulang 側から使える capability として実装する。

設計参照:

- `notes/design/parser-dsl-desugar.md` — `rule { ... }` / `~"..."` の desugar 方針（lower3 で展開、`~"abc": () -> [parse] ()`）

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
- `notes/design/std-fs.md` — std::fs 最小設計（open/close を露出せず、path + byte range で毎回読み書き。path はバイト列）

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
