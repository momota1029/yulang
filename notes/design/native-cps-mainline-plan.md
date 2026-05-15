# Native CPS Mainline Plan

Yulang の native backend は、effect-free な値計算だけを速くする段階から、
effect / handler を含む普通の Yulang program を native で動かす段階へ進める。

結論として、native 実行の本線は CPS representation backend に寄せる。
value backend は捨てず、effect-free fast path と runtime value helper の供給元として使う。

## Why CPS Repr Is The Mainline

Yulang の中核は effect / handler / thunk hygiene / resumption を含む。
これらは direct-style value backend へ後付けするより、CPS repr の control frame と
continuation model に載せる方が自然。

既に CPS repr 側にあるもの:

- `Perform` / `Resume` / `ResumeWithHandler`
- shallow handler の resumption capture
- handler stack / guard stack snapshot
- thunk boundary hygiene の scalar prototype
- source-level `sub` / `return` と小さい algebraic effect regression

value backend 側にあるもの:

- boxed `VmValue` helper
- string / list / tuple / record / variant construction
- list range / splice / view
- closure handle と indirect closure call
- top-level partial application wrapper
- std `list.map` / `filter` / `fold` の effect-free executable path

次の native 完全化では、この 2 つを競合させない。
CPS repr は control semantics を担当し、value backend の helper は heap value ABI として再利用する。

## Optimization Policy

CPS optimization must be driven by IR shape, call-site type/effect evidence,
handler evidence, and escape information. It must not key correctness or
optimization eligibility on std module paths, function names, or today's std
implementation layout.

Standard-library programs such as list folds, loops, and nondeterminism helpers
are important hot paths and regression sources, but they should get faster
because they instantiate general higher-order control patterns. If std changes
shape, the optimizer should either still recognize the same IR/evidence pattern
or simply stop applying that optimization, not miscompile by following a stale
path name.

The implementation has an explicit `cps_optimize` boundary between CPS repr ABI
lowering and Cranelift codegen. It currently rewrites explicit calls through
empty forwarding continuations, folds empty return continuations, prunes
unreachable continuations, inlines small single-use one-shot continuations,
removes dead pure value statements, and records a profile, while both JIT and
object codegen go through the same entrypoint so future passes cannot
accidentally diverge by artifact kind.

## Execution Policy

`--native-run` の長期方針:

1. effectful root / thunk hygiene が関わる root は CPS repr backend を選ぶ。
2. effect-free で value backend が確実に扱える root は value backend を fast path として使ってよい。
3. unsupported は無言 fallback ではなく、structured reason を持つ。
4. VM は当面 oracle として残し、regression は `VM == native` を基本にする。

短期的には、既存 CLI の fallback 挙動を急に壊さない。
まず backend 選択の判定と理由を内部 API に切り出す。

## Target Architecture

```text
runtime/core IR
  -> effect-aware CPS IR
  -> CPS repr IR
  -> CPS repr ABI lanes
  -> Cranelift/native runtime

value backend helpers
  -> boxed VmValue construction
  -> list/string/record/variant helper symbols
  -> closure handle helpers
```

CPS repr ABI lane は、少なくとも次を明示的に扱う。

- scalar int / bool / unit
- native float
- runtime value pointer
- closure pointer
- thunk pointer
- resumption pointer
- opaque i64 for transitional internal values

最終的には scalar-only prototype を縮小し、`RuntimeValuePtr` を普通の lane として扱う。

## Invariants

- effectful control は direct-style value backend へ後付けしない。
- `handler_match` / hidden effect evidence は型表示に出さず、runtime では delimiter / guard / handler frame として扱う。
- shallow handler の resumption は handler frame 自身を含まない。
- thunk / resumption / closure の captured frame は native 側でも構造共有を基本にする。
- value backend helper は `VmValue` 互換の意味を保つ。CPS repr 専用の別 semantics を作らない。
- unsupported 判定は、関数名・module 名の文字列特例ではなく、IR node / lane / value kind から出す。

## Milestones

### 1. Backend Selection Boundary

- [x] backend selection を `native-run` CLI から分離する。
- [x] root ごとに `ValueFastPath` / `CpsMainline` / `Unsupported(reason)` を返す。
- [x] fallback message は選択理由を表示できるようにする。
- [x] effectful root は CPS repr を選ぶ regression を追加する。

### 2. CPS Runtime Value Lane

- [x] CPS repr ABI に `RuntimeValuePtr` を first-class lane として通す。
- [x] `Continue` / `Branch` / `DirectCall` / `ApplyClosure` が runtime value pointer を壊さず運べるようにする。
- [x] value backend 相当の boxed helper symbols を CPS repr Cranelift から呼ぶ。
- [x] string/list/record/variant root を CPS repr executable path で VM と比較する。

### 3. CPS Closure / Partial Application

- [x] CPS repr closure env slot limit を現在の small fixed helper から広げる。
- [x] closure pointer と runtime value pointer の境界を明示する。
- [x] top-level partial application wrapper と CPS closure creation を揃える。
- [x] higher-order std functions を CPS repr path で VM と比較する。
- [x] source-level closure value を record に保存し、select してから呼ぶ path を
      forced CPS repr executable regression に入れる。
  - [x] scalar / string environment を capture した closure も同じ record path で確認する。
- [x] CPS-level closure pointer を list に保存し、index してから呼ぶ Cranelift
      regression を入れる。
  - [x] Indexed / selected closure call の返り値を unknown lane のまま root へ返す
        path を通す。CPS repr の `Unknown` lane は root でも transitional opaque i64
        として扱う。
  - [x] source-level closure value を list に保存し、`std::list::index_raw` で
        取り出してから呼ぶ forced CPS repr executable regression を入れる。
  - [x] scalar / string environment を capture した closure も同じ list index path で確認する。
  - [x] lazy operator の結果を tuple value position に置く regression を入れる。
        tuple 内部でも short-circuit operand thunk が可視値として漏れないことを
        forced CPS repr executable path で確認する。

### 4. General Thunk Invocation

- [ ] thunk value を型変換後 IR / CPS repr lane として保存・返却・複数箇所で force できるようにする。
  - [x] CPS repr Cranelift の thunk capture env は 4 slot 固定 helper から外れ、
        larger env を `yulang_cps_make_thunk_i64_many(ptr, len)` で運べる。
  - [x] CPS-level thunk pointer を record に保存し、select してから force する
        Cranelift regression を入れる。
  - [x] CPS-level thunk pointer を list に保存し、index してから複数回 force する
        Cranelift regression を入れる。
  - [x] indexed thunk が string heap value を返す Cranelift regression を入れる。
  - [x] 型変換後 runtime IR の `ExprKind::Thunk` を list に保存し、index 後
        `BindHere` で force する Cranelift regression を入れる。
  - [x] source-level lazy operator の結果を tuple value position に置いても、
        型変換後 thunk adapter が可視値として漏れないことを forced CPS repr
        executable path で確認する。
  - [x] source-level lazy operator の結果を list value position に置き、
        `std::list::index_raw` 後も plain value として読めることを forced CPS repr
        executable path で確認する。
  - [x] source-level lazy operator の結果を record field / variant payload position
        に置いても plain value として読めることを forced CPS repr executable path
        で確認する。
  - [ ] source-level first-class thunk 構文を増やすのではなく、型変換後 IR で
        現れる thunk adapter の structural coverage を増やす。
- [ ] `AddId` / `BindHere` / hidden evidence boundary を thunk pointer に保持する。
  - [x] CPS-level list に保存した boundary 付き thunk を index して force しても、
        active boundary が handler selection に残る Cranelift regression を入れる。
  - [x] CPS-level record に保存した boundary 付き thunk を field select して
        force しても、active boundary が handler selection に残る Cranelift
        regression を入れる。
- [ ] force 時に handler / guard stack を正しく re-enter する。
- [ ] direct thunk callback inline の暫定経路を、汎用 thunk invocation に置き換える。
  - [x] Handler arm entry が installed escape continuation へ直接進む source
        lowering 形では、arm result を二度目の `ScopeReturn` として包まない。
        `sub` の結果を list へ埋める source regression で VM と揃えた。
  - [x] 再帰 handler wrapper は call site で inline しない。`branch().list`
        のような全解収集 wrapper は、CPS 関数として残して resumption 経路へ渡す。
  - [x] `each [1, 2, 3] .list` の false branch は、Return(Thunk) の
        pre-force で thunk body を先に実行し、その結果を retained return-frame
        chain へ戻す。CPS eval / CPS repr eval / Cranelift runtime が同じ形で通る。
  - [x] Handler arm entry が installed escape continuation へ到達済みの場合も、
        arm result を値だけで返さず、handler install 時点より内側の frame を
        切ってから retained return-frame chain を続行する。これで
        `(each [1, 2, 3] + each [10, 20]).list` が VM と一致する。

### 5. Handler / Resumption Heap Values

- [x] resumption pointer を closure-like callable value として扱う。
  - [x] CPS eval / CPS repr eval / Cranelift runtime の `ApplyClosure` が
        closure と resumption を動的 dispatch する。`std::undet.logic` の
        queue から取り出した continuation を `k false` として呼ぶ path が通る。
- [x] `EffectfulApply` の closure/resumption dynamic dispatch を runtime value lane と統合する。
- [x] multi-shot resumption capture が runtime value payload を含んでも VM と一致するようにする。
  - [x] `(each [1, 2, 3] + each [10, 20]).logic` が VM / CPS eval /
        CPS repr eval / Cranelift runtime で一致する。
  - [x] `(each [1, 2, 3] + each [10, 20]).once` が VM / CPS eval /
        CPS repr eval / Cranelift runtime で `just 11` を返す。
- [x] shallow handler + delimiter frame + guard stack の source regression を native executable path に増やす。
  - [x] Direct `f()` inside an inner `sub` returns through the inner handler and leaves the caller root at `2`.
  - [x] Callback `h()` crossing the thunk boundary skips the inner handler and returns from the caller root as `0`.

### 6. CLI And Release Surface

- [x] `--native-run` の backend 選択を docs に明記する。
- [x] `--native-run-value-exe` は debugging fast path として残す。
- [x] CPS repr executable path を primary native effect path として説明する。
- [ ] playground/deploy 側の native option も同じ選択規則に揃える。

## Near-Term Work Queue

詳細な残穴は `notes/design/native-remaining-failure-matrix.md` で追う。

1. N1/N2: closed for the current semantic pass. Add more cases only when a new
   source-shaped runtime IR form appears.
2. N3/N5: value backend unsupported reason から CPS repr fallback / playground
   surface までを同じ structured selection policy に揃える。
3. N4/N6: compact native heap layout と artifact cache は semantic completion 後の
   package/cache 作業として分離する。

## Done Definition

「native で動く」と呼ぶ最初の基準:

- effect-free std-heavy programs は value backend か CPS repr で動く。
- `sub` / `return` / simple algebraic effect / shallow handler は native executable path で動く。
- string/list/record/variant payload が effect boundary を越えても VM と一致する。
- unsupported は root ごとに理由を出し、VM fallback するか失敗するかが明示されている。

完全化の基準:

- direct-style VM と native CPS repr の observable result が、通常の source programs で一致する。
- handler hygiene regression が native path の通常 regression suite に入っている。
- generic thunk / closure / resumption value が tuple/list/record/variant payload として安全に運べる。
