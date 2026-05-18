# 現在のタスク: post-core roadmap

Yulang は、"この言語は成立するか" から "実用的な scripting language になれるか" へ
進むだけの core language / runtime 機能を持ち始めた。

現在の作業は、主に 4 つの track と横断的な継続作業で整理する。

広い backlog:

- `notes/todo/index.md`

完了履歴:

- `tasks/done/2026-05-14-native-backend-history.md` — Track 1 のここまでのマイルストーン
- `tasks/done/2026-05-14-host-filesystem-history.md` — Track 3 の parser/lowering 特例削減

## Track 1: Native Backend

native backend は、experimental release に向けた gate を切る段階に入った。
ここでいう release は「interpreter を置き換える」ではなく、`yulang run --native`
を明示的な subset 付きの実験的実行系として外へ出せる状態を指す。

設計参照:

- `notes/design/native-backend-plan.md`
- `notes/design/cps-effect-lowering-plan.md`
- `notes/design/native-value-abi-plan.md`
- `notes/design/native-gc-runtime-plan.md`
- `notes/design/native-cps-mainline-plan.md`
- `notes/design/native-direct-style-islands.md`
- `notes/design/source-realm-band-plan.md`
- `docs/native-backend.md`

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
- `select_native_backends` は pure-subset coverage と structured unsupported reason
  のために残し、user-facing な native run は effects executable path を本線にする。
- VM / interpreter は behavioral oracle のままにする。native code は置き換えではなく、
  VM の横にある明示 opt-in backend。

現在の実装:

- `yulang run --native` と `yulang native` は effects backend へ入る。
- CPS repr Cranelift は `RuntimeValuePtr` / `ClosurePtr` / `ThunkPtr` /
  resumption pointer を ABI lane として持ち、handler / resumption payload に
  non-scalar value を通せる。
- tuple / record / variant / list / string / boxed scalar / closure / thunk /
  resumption の prototype heap handle は effects path で表示・選択・呼び出しの
  regression がある。
- source-defined algebraic effects、multi-shot resumption、`std::undet`、
  `std::junction`、mutable refs、finite/open range `for` + `last` / `next`、
  `sub` / `return` は covered source regression で native と VM を比較している。
- recursive handler / resumption chain が tuple を返す場合、handler arm の
  thunk result は `apply_closure` / direct-call reification 後にも force され、
  block tail の scoped abort は loop boundary で消費される。`5` だけが漏れる
  症状と pointer-looking integer leak は解消済み。
- native root pretty print は runtime-shaped roots の Debug projection へ寄せた。
  unit / bool / tuple 内 unit も covered path では interpreter 表示と揃う。
- CPS optimizer は bounded fixpoint で forwarding continuation、空 returner、
  literal bool branch、known closure apply、local direct-style closure apply、
  small pure direct callee、dead pure value statement、unreachable continuation を
  消す。pure successor continuation を Cranelift block に吸う direct-style island
  codegen の入口もある。
- pure-subset backend は effect-free speed check / boxed `VmValue` helper /
  backend debugging path として残る。

release gate:

- `RUSTC_WRAPPER= cargo test -q -p yulang-native`
- `RUSTC_WRAPPER= cargo test -q -p yulang --test native_cli`
- `RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_undet_once_open_range_guard_through_cps_repr`
- `RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_junction_method_undet_once_through_cps_repr`
- `RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/03_for_last.yu`
- `RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/04_sub_return.yu`
- `RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/06_undet_once.yu`
- `RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/07_junction.yu`
- `RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/10_effect_handler.yu`
- `RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/showcase.yu`

2026-05-18 時点の gate 状態:

- `yulang-native` と `yulang --test native_cli` は通る。
- `runs_undet_once_open_range_guard_through_cps_repr` は `:just 3` に届く。
- `runs_junction_method_undet_once_through_cps_repr` は `:just 18` に届く。
- CLI smoke でも `examples/06_undet_once.yu` は `just (3, 4, 5)`、
  `examples/showcase.yu` の final root は `just 18` で VM と一致する。
- native release gate は、documented experimental subset について通過。

release 後に残すもの:

- 一般的な returned/stored effectful thunk coverage。
- prototype heap handle から MMTk-backed な安定 native runtime layout への移行。
  `VmValue` GC 化ではなく、`YValue` word、native object header、precise root
  discipline、`i63` immediate + heap `BigInt` を中心にする。最初の isolated
  spike として `crates/yulang-native/src/gc_runtime.rs` に `YValue` tagging、
  heap object header、traceable payload、first-milestone object allocator、
  explicit root stack、allocation stress tracing、i63 overflow -> heap `BigInt`
  promotion を入れた。`YHeap` allocator boundary と root frame も入り、MMTk heap
  と JIT helper temporary roots の接続点が見える形になった。temporary-root helper
  scope も足して、helper が allocation を挟むときの root discipline をテストで固定
  した。allocated-heap stats と live root-trace report も入り、future MMTk heap と
  spike heap の比較面ができた。integer helper smoke は add/sub/mul/compare まで広げ、
  i63 overflow/underflow から heap `BigInt` へ promotion する境界を押さえた。
  monomorphic native layout descriptor、typed `NativeHeapBlock` storage、
  layout registry / shared handle、layout footprint / field offset、trace bitmap も
  追加し、type monomorphization 後の tuple / closure env / continuation env /
  stack frame では `i64`/`u64`/`f64`/bool field を unboxed のまま置き、`YValue`
  field だけ trace する方針を固定した。stack-frame layout は heap allocation から
  弾き、同一 monomorphic layout は object ごとに複製せず registry 経由で共有する。
  `NativeHeapBlock` の保存形式は `NativeFieldValue` 配列から raw payload buffer へ
  寄せ、field offset 経由で read/write する形にした。
  static path / atom identity 用に `YSymbolTable` / `YSymbolId` / stable fingerprint /
  symbolic variant / `Symbol` field lane も入れた。ADT tag や path-like payload は
  full path object を持ち回らず compact symbol id で扱う方向。Ruby-style なただの
  symbol 文字列も path symbol とは別 key として intern できる。closed symbol set は
  `YPerfectSymbolHash` へ freeze でき、hash collision は runtime dispatch 前に明示的に
  reject する。native variant layout は raw payload の先頭に `Symbol` tag field を置き、
  後続 payload field は monomorphic layout の lane に従って保存・trace する。
  `mmtk_runtime.rs` を追加し、MMTk crate を native crate の通常依存にした。
  最初の接続 plan は single-threaded `NoGC` spike。
  `mmtk_binding.rs` で Yulang VM binding skeleton も入り、
  native object header / `YValue` slot / memory slice / object-size callback /
  trace-slot scanner は MMTk trait に接続済み。`MmtkHeap` prototype で `YHeap`
  boundary から MMTk allocation へ入り、object header と trace slots は MMTk heap
  に置く。現時点の semantic `YObject` payload も MMTk raw payload area に置き、
  `MmtkHeap::object` は object reference から payload を投影する。compact raw payload
  object と compact `NativeHeapBlock` payload も MMTk heap 上に置けるようにし、
  native layout offset 経由で field を読める入口を作った。closure/thunk/resumption/
  continuation env / handler frame / return frame も compact native-block payload で
  header / trace slot / env slot を読める。string/list rope node metadata も raw
  payload に畳み、hot path は object table ではなく header/payload 直読みにした。
  tuple/variant は fixed raw-payload metadata + trace slot layout に移し、
  `list.view_raw` の node tuple/variant construction が native layout intern /
  native-block projection を通らないようにした。
  record も field-name metadata を raw payload、field values を trace slot に置く
  fixed compact layout に移した。
  compact list は `len`/index/view/debug で tree 全体を flatten せず、node view は
  既存 child をそのまま返し、trace slot も一時 `Vec` なしで読む。
  captured native CPS control-stack snapshot は MMTk lane で compact `ControlStack`
  heap object として materialize でき、reachable な MMTk `YValue` children を trace slot
  として持つ。MMTk heap の tracked address range で prototype pointer-shaped word を
  object-table lookup 前に落とし、MMTk child が増えない snapshot allocation は省く。
  この mirror は `YULANG_MMTK_CPS_CONTROL_STACK_SNAPSHOTS=1` の opt-in にした。
  現在の default `--mmtk` は NoGC benchmark lane なので、collection 未接続の間は
  control-stack の GC mirror cost を hot path に乗せない。
  `YHeap` の read surface は object header / trace children / full object projection
  に分けたので、tracing と stats は full semantic payload に依存しない。
  `MmtkNativeRuntimeContext`
  で raw `YValue` word helper boundary も作り、unit/bool/int arithmetic/compare/
  scalar string conversion、赤黒木 string index/range/slice/splice/concat/length/equality
  と compact bytes/path conversion helper、tuple/record/variant/list の小さい C ABI
  smoke まで通した。record default/has/without と list view/range/splice も MMTk
  helper surface に乗った。
  別名の `yulang_mmtk_cps_*` helper symbols も登録した。
  これは future all-`YValue` CPS lane 用で、現行 `yulang_cps_*` の plain scalar
  i64 / prototype handle ABI はまだ置き換えていない。最小 JIT smoke では
  Cranelift から `yulang_mmtk_cps_*` を直接呼び、MMTk `YValue` の
  string/bytes/tuple を JIT call 越しに渡せるところまで確認した。
  `CpsReprCraneliftOptions::mmtk_yvalue_primitives()` も追加し、通常 CPS repr
  lowering のうち string literal、current runtime primitive family、
  tuple/record/variant structural stmt を `yulang_mmtk_cps_*` へ opt-in で
  流せるようにした。この opt-in lane では Yulang の `int` / bool / unit は
  tagged `YValue` word として primitive call と branch condition を通る。float は
  unboxed `f64` input のまま扱い、比較結果だけ `YValue` bool へ戻す。固定幅
  `i64`/`u64` lane は native layout spike 側の機能で、まだ source-level Yulang
  type ではない。`yulang run --mmtk` はこの lane を benchmark 用に走らせる入口。
  string/list payload は runtime の `StringTree` / `ListTree` と同根の
  赤黒木 rope shape にしている。native CPS runtime の handler / guard /
  return-frame stack はまだ mutable Vec + cached snapshot で、mutation 後の最初の
  snapshot は active stack を clone する。`Rc<Vec>` COW と `im::Vector` 置換は
  `(each 1..20 + each 1..20).list.say` を遅くしたため採用しない。capture clone を
  消すには、hot push/pop は Vec 相当に保ち、snapshot だけ構造共有する専用 stack が
  必要。
  MMTk lane では env opt-in 時に同じ snapshot を GC heap 上の `ControlStack`
  mirror にも載せる。
  `mmtk_cps_control.rs` で closure/thunk/resumption body を compact fixed
  raw-payload MMTk object として作り、code/env を native layout projection なしで
  読む専用 helper も追加した。control payload は env length を自前で持ち、
  helper context は per-call の `RefCell<Option<_>>` borrow ではなく raw thread-local
  context pointer にした。この guarded compact control helper は stable `--mmtk` lane
  で closure/thunk control body に使う。`YULANG_MMTK_CPS_CONTROL_OBJECTS=0` で
  prototype native control helper path へ opt out できる。compact control object は
  まだ non-empty native handler/guard snapshot を直接保存しないため、compact thunk
  作成は native control capture context が空のときだけに絞った。compact thunk に
  effect boundary を足す
  ときは、boundary 時点の context を誤って捕まえず、明示的な empty snapshot から
  prototype thunk を作って boundary を足す。これで unsafe experiment の isolated
  `.once` tail と `showcase` は正しい出力を維持しつつ、thunk 作成を compact path へ
  戻せた。non-empty snapshot を持つ control object はまだ prototype helper path へ
  fallback する。さらに狭い helper-level 実験として
  `YULANG_MMTK_CPS_CONTROL_THUNK_SIDECARS=unsafe` を追加し、compact thunk surface と
  作成時 native thunk snapshot sidecar を結びつける入口を作った。direct helper test
  では force でき、mixed native path が compact thunk を受け取った場合は native
  force helper から MMTk force へ戻す橋も追加した。native CPS runtime は compact
  control が捕まえる必要のある状態を bitmask で公開し、MMTk control helper は
  abort / scope-return 中の thunk 作成を sidecar 実験でも prototype thunk path へ戻す。
  direct helper test は handler/guard、pending handler env、pending escape targets、
  active blocked thunk force、abort/scope-return の capture flag を固定する。
  full lowering では non-local flow が `compact apply/force` を
  またいだときに `0` payload を ordinary apply と誤認する形がまだ残るため、通常の
  unsafe control lane では無効のままにした。
  default MMTk は compact list metadata read、view/debug の再構築削減、
  tuple/variant raw-payload 化、control-stack mirror opt-in 化後、release executable
  で default native と同じ帯まで戻した。2026-05-18 の手元測定では
  `(each 1..20 + each 1..20).list.len` が outlier を除いて native/MMTk とも
  0.40-0.43s、`.list.say` は native 0.62-0.68s / default MMTk 0.65-0.71s /
  thunk-native unsafe control experiment 0.70s 前後。thunk 作成を compact path へ
  戻したあとの `examples/showcase.yu` は手元の release sequential 3 runs で
  native 1.63-1.71s / default MMTk 1.59-1.91s / unsafe compact-control 1.55-1.69s。
  compact control entry は allocation 時に code/env pointer を TLS cache へ登録し、
  hot force/apply で MMTk object table projection と raw payload decode を繰り返さない
  形にした。生成済み executable を直接 `hyperfine --warmup 2 --runs 10` で測った結果は
  `list.len` が native 372.1ms / MMTk opt-out 375.3ms / MMTk guarded 370.9ms、
  `list.say` が native 639.7ms / MMTk opt-out 688.3ms / MMTk guarded 678.7ms、
  `showcase` が native 5.3ms / MMTk opt-out 6.1ms / MMTk guarded 6.5ms。sidecar runtime
  env は `showcase` で既知の non-local-flow hole に当たり、
  `MMTk CPS control apply received a non-applicable control value: 0x0` で abort する。
  生成直後に同じ continuation 内で apply される小さい direct-style closure は
  CPS optimizer が本体を apply site へ展開し、closure construction は dead pure
  削除で落ちるようにした。これは wrapper 形に限らない captured closure にも効く
  closure 生成削減の入口。
  `YULANG_CPS_I64_STATS=1` で生成済み CPS executable が runtime control counter を
  root ごとに stderr へ出す計測入口を追加した。stack 操作は site 別にも出すので、
  clone/replace が make-resumption、thunk force、return-frame continue、route の
  どこから来ているかを見られる。20x20 の計測では `.list.len` が
  resumption 861、thunk 1346(native)/1345(MMTk)、closure 441、return-frame
  snapshot 861/861 miss、return-frame cloned items 15625、return-frame push 3048、
  pop 3782。`.list.say` は resumption 861、thunk 2947/2946、closure 441、
  return-frame snapshot は同じ 861/861 miss だが、表示側で guard snapshot clone が
  410671 items まで増える。native と MMTk の control counter はほぼ同形で、
  MMTk 側だけ force-thunk call が `.list.len` で 19004 vs 18164、`.list.say` で
  38609 vs 37769 と少し多い。
  site breakdown では `.list.len` の return-frame snapshot clone 15625 items は
  すべて make-resumption 由来。handler snapshot clone は push-return-frame 由来が
  26569/26822 items と支配的で、handler replace items は continue-return-frame
  87566 と force-thunk 131726 が大きい。`.list.say` の guard clone 410671 items は
  make-thunk 324545 と force-thunk 83940 がほぼ支配し、guard replace items は
  continue-return-frame 490622 と force-thunk 659695 が支配する。よって次に見るべき
  最適化は active stack の汎用永続化ではなく、snapshot を clone-only object として
  GC/compact object に置くこと、restore/replace を snapshot handle + mutable tail で
  遅延すること、make-thunk/force-thunk の guard capture を抑えること。
  その第一段として `force_thunk` は caller 側に active handler/guard stack がある場合、
  captured stack の `replace(to_vec())` を行わず、現在の stack をそのまま使うようにした。
  さらに return-frame continuation restore は frame が持つ snapshot と現在 stack の
  snapshot storage が同一なら no-op にし、復元が必要な場合も snapshot cache を保持して
  stack へ戻す `restore_snapshot` を使う。その後、snapshot 本体を flat `Rc<[T]>` だけでなく
  `base snapshot + appended item` も持てる形にし、guard stack は active 表現も
  `base snapshot + mutable tail` にした。これで guard push 後の thunk / closure /
  resumption capture は full guard stack clone ではなく append node 共有になる。
  20x20 の最終 stats では `.list.len` の handler replace items が 236264 -> 174540、
  guard snapshot clone が 6342 -> 0、guard replace items が 22475 -> 8060。
  `.list.say` は guard snapshot clone が 410671 -> 0、handler snapshot clone は
  28315 -> 16385、handler replace items は 283364 -> 175342。guard replace items は
  active guard stack の snapshot restore 表現へ移したため item traffic 指標としては
  比較しにくいが、復元時の full Vec clone は消えた。
  生成済み executable の `hyperfine --warmup 2 --runs 10` では、最新の run で
  `list.len` が native 425.9ms / MMTk 410.3ms、`list.say` が native 641.1ms /
  MMTk 692.3ms。旧 guarded MMTk binary との直接比較では `.list.say` が
  758.9ms -> 677.9ms で約 12% 改善。ただし native にはまだ届かない。
  その後のGC側追試では、direct-mapped compact-control entry cache は壁時計で悪化したため
  残さず、`YULANG_MMTK_CPS_CONTROL_THUNK_SIDECARS` の env 判定 cache だけを残した。
  thunk sidecar lane は `list.len` / `list.say` とも default MMTk より遅く、closure を
  pending handler env 付きでも compact 化する実験は native `make_closure` counter を
  441 -> 0、余分な MMTk `force_thunk` を native と同数まで落としたが、compact closure
  apply 側の lookup/payload 経路が勝って wall-clock は悪化したため採用しない。
  追加で `YULANG_MMTK_CPS_CONTROL_THUNK_CONTEXTS=unsafe` を作り、compact thunk body は
  MMTk object のまま、捕獲した native handler/guard context だけを小さい opaque side
  table に置く実験も行った。これは 20x20 stats では native `make_thunk` を 0 まで消し、
  `force_thunk` 由来の replace traffic も大きく下げるが、wall-clock では
  `list.len` default MMTk 409.5ms / context 418.8ms、`list.say` default MMTk
  705.8ms / context 710.6ms と負けたため default にはしない。
  抜本案の入口として、既存 stable CPS runtime とは別に GC-first control runtime の
  payload 最小核を追加した。`ControlState` は独立した `YObjectKind` になり、
  GC-control thunk payload は legacy compact-control tag とは別tagで
  `{ code, context, env }` を raw payload に持つ。trace edge は thunk -> control state
  と thunk -> heap env value、control state -> control stacks へ張る。まだ CPS lowering
  には接続せず、ctx-passing ABI へ移すための横置き runtime nucleus として扱う。
  その最初の helper surface として、明示的な control-state word を受け取る
  `gc_control_empty_state` / `gc_control_push_guard` / `gc_control_find_guard` /
  `gc_control_peek_guard` を追加した。これは native TLS guard stack を読まず、
  `ControlState.guard_stack` の GC guard stack node だけを見る。
  compact list の `len` / `get` / merge entry は同じ compact-list metadata を入口で
  読み直さない形へ寄せた。最新の生成済み executable `hyperfine --warmup 2 --runs 10`
  では `list.len` が native 402.7ms / MMTk 416.9ms、`list.say` が native 667.8ms /
  MMTk 731.1ms。MMTk がnativeを安定して越える状態にはまだ届いていない。
  関数型言語向け GC tuning の入口として、MMTk heap に allocation profile を足した。
  `YULANG_MMTK_CPS_HEAP_STATS=1` で generated executable harness が root 実行後に
  `[JIT-MMTK-STATS]` を出す。object kind 別の object 数 / trace slot 数 /
  raw payload bytes / total object bytes と、compact storage shape 別の object 数を
  見られる。20x20 の初回確認では `.list.len` は list 899 objects / 4,872 trace slots、
  `.list.say` は string 5,984 objects と list 4,748 objects が支配的。
  残りは list primitive 単体ではなく、control lane が handler/guard snapshot を
  compact object に持てていないため non-empty capture や boundary thunk が prototype
  helper path へ戻ること、sidecar bridge が full lowering ではまだ non-local flow safe
  でないこと、prototype interop/fallback を hot value が背負うこと、control capture
  が専用 snapshot-sharing stack ではないことが主因。通常 native を安定して
  越えるには、all-`YValue` control lane を完了し、残り metadata を header/raw payload
  に寄せ、hot runtime value を全て compact `YValue` layout に統一し、capture clone を
  専用 stack で消す必要がある。
  default native path はまだ prototype helper のまま。
- unsupported native root を VM へ戻す fallback policy。
- package/cache/build workflow と native artifact lifecycle。
- 型 surface / monomorphize strictness。これは native release blocker ではなく、
  Track 4 側の処理系健全性作業として進める。

近い形:

```text
runtime/core IR
  -> pure debug control IR / effect-aware CPS IR
  -> closure/environment layout
  -> Cranelift IR
```

現在の距離感:

- まだ Yulang 全体を実行する処理系ではない。
- `yulang run --native` は experimental subset として外へ出せる距離にいる。
- Go module/package よりの source identity として realm / band を採用する。
  realm は versioned distribution boundary、band は realm 内の import /
  namespace / build unit。band identity は resolved realm + band path で決まる。
- source から runtime IR / effect-aware CPS / CPS repr / ABI lane / Cranelift JIT
  まで通る実行可能パスはできている。
- 当面は VM を oracle にしたまま、native 対応 root と diagnostic を増やす。

直近 TODO:

- native に残す bug / scary note を `solved` / open に仕分ける。
- native experimental release を切る直前に
  `docs/native-experimental-release.md` の release gate を再実行する。
- tag / publish 手順が必要なら、native は `experimental` と明記して出す。
- release 後は、型 surface audit と monomorphize strictness を優先 track に戻す。

これまでの主なマイルストーン (CPS lowering / CPS repr Cranelift JIT / value-lane Cranelift /
dynamic handler frame / guard stack / finite nondet など) は
`tasks/done/2026-05-14-native-backend-history.md` に退避。

## Native Release Follow-Up

`docs/native-backend.md` を public status、`tasks/current.md` を次の作業 queue とする。
細かい履歴は `tasks/done/2026-05-14-native-backend-history.md` と
`notes/progress/daily/` に寄せ、ここには release 判断に必要な項目だけ残す。

直近の順番:

1. native scary notes / bugs を open と solved に仕分ける。
2. release 直前に `docs/native-experimental-release.md` の gate を再実行する。
3. tag / publish 手順では、native は `experimental` と明記して出す。
4. その後、型 surface / monomorphize strictness と native GC runtime layout の
   優先順を決める。

## 重要な制約

- VM は behavioral oracle のままにする。Native code は置き換えではなく、VM の横に追加する。
- 現 VM は nondet continuation の clone cost が大きい。playground/docs examples では
  無限選択を早めに絞り、VM 参照化は native backend / control IR 作業と一緒に扱う。
- native GC は `VmValue` の所有方式変更ではなく、MMTk-backed な native object
  model への移行として扱う。小さい continuation / env / thunk / handler frame を
  near bump-allocation cost で作り、普通の runtime payload は `i63` immediate +
  heap object reference の `YValue` word に寄せる。
- `gc_runtime` spike は MMTk 接続前の object model / root discipline 固定用。
  MMTk feature/config boundary、VM binding skeleton、`MmtkHeap` prototype、
  `MmtkNativeRuntimeContext` は入ったので、次は JIT へ急がず helper context を
  smoke harness として使い、残る semantic payload 依存と CPS helper symbol 面を
  compact raw/native-block + all-`YValue` lane へ寄せる。root stack scanning は
  その後 MMTk roots work factory に接続する。

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

## Track 4: Type Surface / Monomorphize Strictness

native release 後に戻る主作業。今の問題は「単一化そのもの」だけではなく、
runtime / monomorphize の出入口に残る型 surface を網羅的に置換・投影・監査できて
いないこととして扱う。

設計参照:

- `notes/bugs/type-substitute.md`
- `notes/bugs/type-monomorphize.md`
- `notes/bugs/type-monorphized-refactor.md`

方針:

- `Expr.ty` / pattern ty / binding scheme / evidence / handler residual /
  thunk effect / adapter / coercion など、runtime へ残る型 surface をまず列挙する。
- 置換、runtime projection、residual audit が同じ surface list を読む形へ寄せる。
- fallback-to-old-`expr.ty` は telemetry を通して理由付きにし、monomorphized 出口で
  strict に落とせるようにする。
- 型推論・monomorphize の途中に path / module / fixture 名依存の分岐は入れない。

直近 TODO:

- `type_surface.rs` 相当の collector / folder / audit entrypoint を足す。
- collector と substituter が同じ site set を覆う parity test を入れる。
- poison type test で `ApplyEvidence`、`HandleEffect`、`ThunkEffect`、
  `AddId.allowed`、nested pattern bind などの漏れを見つける。
- `YULANG_STRICT_MONO_RUNTIME_TYPES=1 RUSTC_WRAPPER= cargo test -q -p yulang-runtime`
  の失敗を surface site ごとに分類する。
- `substitute_type` の推移的置換、recursive binder capture、effect row matching は
  `Subst` / free-vars / row matcher の責務として切り出す。

## Ongoing: Static Analysis Speed

最近の performance work は、引き続き playground の目標と揃っている。

現在の参照:

- `notes/design/static-analysis-speed-plan.md`
- `notes/design/partial-compilation-cache-plan.md`
- `notes/bugs/type-substitute.md`
- `notes/bugs/type-monomorphize.md`
- `notes/bugs/type-monorphized-refactor.md`

現在の checkpoint:

- principal-unify は default monomorphize route。
- specialization body rewrite は queue 化され、target ごとに profile される。
- block rewrite は redundant pre-walk を避け、`showcase` の monomorphize time を大きく減らす。
- compiled-unit artifacts は syntax / namespace / typed / runtime surfaces を持つ。
- wasm は std compiled-unit artifacts を embed し、source std を fallback として使う。

次 TODO:

- Track 4 の type surface audit を先に通し、strict residual 型を見つける入口を作る。
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
