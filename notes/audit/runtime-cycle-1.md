# Yulang2 実機記録 cycle 1

Y2 main d4c8bc8fc。出力は変更せず記録。各commandに`--no-prelude`があるものは標準ライブラリ依存を切り離した試験。ないものは指定の標準環境。`YULANG_CACHE_DIR=/workspace/scratch/1d0b4aaa3394/audit-y2-cache`。

## cast-branch-case

```yulang
struct user_id { raw: int }
cast(x: user_id): int = x.raw
our mixed(flag) = case flag:
    true -> 1
    false -> user_id { raw: 2 }
(mixed true, mixed false)
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-branch-case.yu`

開始: 2026-11-08T11:54:16.298519+00:00、所要 0.009 秒、exit 0。

```text
roots d0:user_id d4:mixed
d0:user_id: {raw: int} -> user_id = <missing>
d4:mixed: bool -> int | user_id = e10:(fn p1:d6:flag -> e9:case e3:r1:flag->d6:flag { p2:true -> e4:1; p3:false -> e8:(e5:r2:user_id->d0:user_id e7:{raw: e6:2}) })
root exprs e17:(e13:(e11:r3:mixed->d4:mixed e12:true), e16:(e14:r4:mixed->d4:mixed e15:false))
runtime roots e17:(e13:(e11:r3:mixed->d4:mixed e12:true), e16:(e14:r4:mixed->d4:mixed e15:false))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d5:x -> e1:(e0:r0:x->d5:x.s0.raw->d1))
  d5:x arg
  d6:flag arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-branch-case.yu`

開始: 2026-11-08T11:54:16.307844+00:00、所要 0.007 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-branch-case.yu`

開始: 2026-11-08T11:54:16.314974+00:00、所要 0.004 秒、exit 0。

```text
run roots [(1, 2)]
```

## cast-builtin-cardinality-0

```yulang
our f(x: bool): bool = x
f(42)
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-builtin-cardinality-0.yu`

開始: 2026-11-08T12:07:04.269825+00:00、所要 0.009 秒、exit 0。

```text
roots d0:f
d0:f: bool -> bool = e1:(fn p0:d1:x -> e0:r0:x->d1:x)
root exprs e4:(e2:r1:f->d0:f e3:42)
runtime roots e4:(e2:r1:f->d0:f e3:42)
detached {
  d1:x arg
}
error: cannot use `int` where `bool` is required: no implicit cast from `int` to `bool`
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-builtin-cardinality-0.yu`

開始: 2026-11-08T12:07:04.279010+00:00、所要 0.005 秒、exit 1。

```text
diagnostics:
  error [yulang.missing-implicit-cast]: cannot use `int` where `bool` is required: no implicit cast from `int` to `bool`
    --> line 2, column 1
    2 | f(42)
      | ^^^^^
    hint: declare a `cast` from `int` to `bool`, or check whether a different type was intended
    note: type `int` is inferred from this argument
    --> line 2, column 3
    2 | f(42)
      |   ^^
    note: this callee requires an argument compatible with `bool`
    --> line 2, column 1
    2 | f(42)
      | ^
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-builtin-cardinality-0.yu`

開始: 2026-11-08T12:07:04.284024+00:00、所要 0.005 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: cannot use `int` where `bool` is required: no implicit cast from `int` to `bool`
  hint: run `yulang check` to see source ranges before running
```

## cast-builtin-cardinality-1

```yulang
cast(x: int): bool = true
our f(x: bool): bool = x
f(42)
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-builtin-cardinality-1.yu`

開始: 2026-11-08T12:07:04.289305+00:00、所要 0.004 秒、exit 0。

```text
roots d1:f
d1:f: bool -> bool = e3:(fn p1:d3:x -> e2:r0:x->d3:x)
root exprs e6:(e4:r1:f->d1:f e5:42)
runtime roots e6:(e4:r1:f->d1:f e5:42)
detached {
  my d0:"#cast": int -> bool = e1:(fn p0:d2:x -> e0:true)
  d2:x arg
  d3:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-builtin-cardinality-1.yu`

開始: 2026-11-08T12:07:04.293777+00:00、所要 0.004 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-builtin-cardinality-1.yu`

開始: 2026-11-08T12:07:04.297777+00:00、所要 0.004 秒、exit 0。

```text
run roots [true]
```

## cast-builtin-cardinality-2

```yulang
cast(x: int): bool = true
cast(x: int): bool = false
our f(x: bool): bool = x
f(42)
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-builtin-cardinality-2.yu`

開始: 2026-11-08T12:07:04.301861+00:00、所要 0.005 秒、exit 0。

```text
roots d2:f
d2:f: bool -> bool = e5:(fn p2:d5:x -> e4:r0:x->d5:x)
root exprs e8:(e6:r1:f->d2:f e7:42)
runtime roots e8:(e6:r1:f->d2:f e7:42)
detached {
  my d0:"#cast": int -> bool = e1:(fn p0:d3:x -> e0:true)
  my d1:"#cast": int -> bool = e3:(fn p1:d4:x -> e2:false)
  d3:x arg
  d4:x arg
  d5:x arg
}
error: implicit cast from `int` to `bool` is ambiguous: 2 visible declarations match
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-builtin-cardinality-2.yu`

開始: 2026-11-08T12:07:04.306880+00:00、所要 0.005 秒、exit 1。

```text
diagnostics:
  error [yulang.ambiguous-implicit-cast]: implicit cast from `int` to `bool` is ambiguous: 2 visible declarations match
    hint: declare or import only one matching `cast` for this pair
    note: matching cast declaration: #cast
    --> line 1, column 1
    1 | cast(x: int): bool = true
      | ^^^^^^^^^^^^^^^^^^^^^^^^^
    note: matching cast declaration: #cast
    --> line 2, column 1
    2 | cast(x: int): bool = false
      | ^^^^^^^^^^^^^^^^^^^^^^^^^^
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-builtin-cardinality-2.yu`

開始: 2026-11-08T12:07:04.312338+00:00、所要 0.007 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: implicit cast from `int` to `bool` is ambiguous: 2 visible declarations match
  hint: run `yulang check` to see source ranges before running
```

## cast-ambiguous-call

```yulang
struct user_id { raw: int }
cast(x: user_id): int = x.raw
cast(x: user_id): int = 9
our use_int(x: int): int = x
use_int(user_id {raw: 1})
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-call.yu`

開始: 2026-11-08T11:35:26.598297+00:00、所要 0.016 秒、exit 0。

```text
roots d0:user_id d5:use_int
d0:user_id: {raw: int} -> user_id = <missing>
d5:use_int: int -> int = e6:(fn p2:d8:x -> e5:r1:x->d8:x)
root exprs e12:(e7:r2:use_int->d5:use_int e11:(e8:r3:user_id->d0:user_id e10:{raw: e9:1}))
runtime roots e12:(e7:r2:use_int->d5:use_int e11:(e8:r3:user_id->d0:user_id e10:{raw: e9:1}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d6:x -> e1:(e0:r0:x->d6:x.s0.raw->d1))
  my d4:"#cast": user_id -> int = e4:(fn p1:d7:x -> e3:9)
  d6:x arg
  d7:x arg
  d8:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-call.yu`

開始: 2026-11-08T11:35:26.614096+00:00、所要 0.008 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-call.yu`

開始: 2026-11-08T11:35:26.622511+00:00、所要 0.003 秒、exit 0。

```text
run roots [1]
```

## cast-explicit-call

```yulang
struct user_id { raw: int }
cast(x: user_id): int = x.raw
our use_int(x: int): int = x
use_int(user_id {raw: 1})
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-explicit-call.yu`

開始: 2026-11-08T11:35:26.625985+00:00、所要 0.04 秒、exit 0。

```text
roots d0:user_id d4:use_int
d0:user_id: {raw: int} -> user_id = <missing>
d4:use_int: int -> int = e4:(fn p1:d6:x -> e3:r1:x->d6:x)
root exprs e10:(e5:r2:use_int->d4:use_int e9:(e6:r3:user_id->d0:user_id e8:{raw: e7:1}))
runtime roots e10:(e5:r2:use_int->d4:use_int e9:(e6:r3:user_id->d0:user_id e8:{raw: e7:1}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d5:x -> e1:(e0:r0:x->d5:x.s0.raw->d1))
  d5:x arg
  d6:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-explicit-call.yu`

開始: 2026-11-08T11:35:26.665971+00:00、所要 0.007 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-explicit-call.yu`

開始: 2026-11-08T11:35:26.672730+00:00、所要 0.01 秒、exit 0。

```text
run roots [1]
```

## cast-missing-nominal

```yulang
struct source { raw: int }
struct target { left: int, right: int }
our use_target(x: target): target = x
use_target(source {raw: 9})
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-missing-nominal.yu`

開始: 2026-11-08T12:07:24.477018+00:00、所要 0.008 秒、exit 0。

```text
roots d0:source d3:target d8:use_target
d0:source: {raw: int} -> source = <missing>
d3:target: {left: int, right: int} -> target = <missing>
d8:use_target: target -> target = e1:(fn p0:d9:x -> e0:r0:x->d9:x)
root exprs e7:(e2:r1:use_target->d8:use_target e6:(e3:r2:source->d0:source e5:{raw: e4:9}))
runtime roots e7:(e2:r1:use_target->d8:use_target e6:(e3:r2:source->d0:source e5:{raw: e4:9}))
detached {
  d1: source -> int = <missing>
  d2: std::control::var::ref 'a source -> std::control::var::ref 'a int = <missing>
  d4: target -> int = <missing>
  d5: std::control::var::ref 'a target -> std::control::var::ref 'a int = <missing>
  d6: target -> int = <missing>
  d7: std::control::var::ref 'a target -> std::control::var::ref 'a int = <missing>
  d9:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-missing-nominal.yu`

開始: 2026-11-08T12:07:24.484808+00:00、所要 0.006 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-missing-nominal.yu`

開始: 2026-11-08T12:07:24.490966+00:00、所要 0.006 秒、exit 1。

```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: source <: target
  hint: check that the value provides the fields or shape required by this use
```

## cast-ambiguous-nominal-reverse

```yulang
struct source { raw: int }
struct target { left: int, right: int }
cast(x: source): target = target {left: 3, right: 4}
cast(x: source): target = target {left: 1, right: 2}
our use_target(x: target): target = x
use_target(source {raw: 9})
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-nominal-reverse.yu`

開始: 2026-11-08T12:07:24.497256+00:00、所要 0.01 秒、exit 0。

```text
roots d0:source d3:target d10:use_target
d0:source: {raw: int} -> source = <missing>
d3:target: {left: int, right: int} -> target = <missing>
d10:use_target: target -> target = e13:(fn p2:d13:x -> e12:r2:x->d13:x)
root exprs e19:(e14:r3:use_target->d10:use_target e18:(e15:r4:source->d0:source e17:{raw: e16:9}))
runtime roots e19:(e14:r3:use_target->d10:use_target e18:(e15:r4:source->d0:source e17:{raw: e16:9}))
detached {
  d1: source -> int = <missing>
  d2: std::control::var::ref 'a source -> std::control::var::ref 'a int = <missing>
  d4: target -> int = <missing>
  d5: std::control::var::ref 'a target -> std::control::var::ref 'a int = <missing>
  d6: target -> int = <missing>
  d7: std::control::var::ref 'a target -> std::control::var::ref 'a int = <missing>
  my d8:"#cast": source -> target = e5:(fn p0:d11:x -> e4:(e0:r0:target->d3:target e3:{left: e1:3, right: e2:4}))
  my d9:"#cast": source -> target = e11:(fn p1:d12:x -> e10:(e6:r1:target->d3:target e9:{left: e7:1, right: e8:2}))
  d11:x arg
  d12:x arg
  d13:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-nominal-reverse.yu`

開始: 2026-11-08T12:07:24.507245+00:00、所要 0.008 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-nominal-reverse.yu`

開始: 2026-11-08T12:07:24.515245+00:00、所要 0.003 秒、exit 0。

```text
run roots [target({left: 3, right: 4})]
```

## cast-ambiguous-nominal

```yulang
struct source { raw: int }
struct target { left: int, right: int }
cast(x: source): target = target {left: 1, right: 2}
cast(x: source): target = target {left: 3, right: 4}
our use_target(x: target): target = x
use_target(source {raw: 9})
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-nominal.yu`

開始: 2026-11-08T11:36:01.157030+00:00、所要 0.022 秒、exit 0。

```text
roots d0:source d3:target d10:use_target
d0:source: {raw: int} -> source = <missing>
d3:target: {left: int, right: int} -> target = <missing>
d10:use_target: target -> target = e13:(fn p2:d13:x -> e12:r2:x->d13:x)
root exprs e19:(e14:r3:use_target->d10:use_target e18:(e15:r4:source->d0:source e17:{raw: e16:9}))
runtime roots e19:(e14:r3:use_target->d10:use_target e18:(e15:r4:source->d0:source e17:{raw: e16:9}))
detached {
  d1: source -> int = <missing>
  d2: std::control::var::ref 'a source -> std::control::var::ref 'a int = <missing>
  d4: target -> int = <missing>
  d5: std::control::var::ref 'a target -> std::control::var::ref 'a int = <missing>
  d6: target -> int = <missing>
  d7: std::control::var::ref 'a target -> std::control::var::ref 'a int = <missing>
  my d8:"#cast": source -> target = e5:(fn p0:d11:x -> e4:(e0:r0:target->d3:target e3:{left: e1:1, right: e2:2}))
  my d9:"#cast": source -> target = e11:(fn p1:d12:x -> e10:(e6:r1:target->d3:target e9:{left: e7:3, right: e8:4}))
  d11:x arg
  d12:x arg
  d13:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-nominal.yu`

開始: 2026-11-08T11:36:01.179507+00:00、所要 0.01 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-nominal.yu`

開始: 2026-11-08T11:36:01.189314+00:00、所要 0.006 秒、exit 0。

```text
run roots [target({left: 1, right: 2})]
```

### check

Command: `./target/release/yulang --std-root lib check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-nominal.yu`

開始: 2026-11-08T11:52:59.344849+00:00、所要 158.476 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-nominal.yu`

開始: 2026-11-08T11:55:37.820818+00:00、所要 0.231 秒、exit 0。

```text
run roots [target({left: 1, right: 2})]
```

## cast-single-nominal

```yulang
struct source { raw: int }
struct target { left: int, right: int }
cast(x: source): target = target {left: 1, right: 2}
our use_target(x: target): target = x
use_target(source {raw: 9})
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-single-nominal.yu`

開始: 2026-11-08T11:36:01.195525+00:00、所要 0.021 秒、exit 0。

```text
roots d0:source d3:target d9:use_target
d0:source: {raw: int} -> source = <missing>
d3:target: {left: int, right: int} -> target = <missing>
d9:use_target: target -> target = e7:(fn p1:d11:x -> e6:r1:x->d11:x)
root exprs e13:(e8:r2:use_target->d9:use_target e12:(e9:r3:source->d0:source e11:{raw: e10:9}))
runtime roots e13:(e8:r2:use_target->d9:use_target e12:(e9:r3:source->d0:source e11:{raw: e10:9}))
detached {
  d1: source -> int = <missing>
  d2: std::control::var::ref 'a source -> std::control::var::ref 'a int = <missing>
  d4: target -> int = <missing>
  d5: std::control::var::ref 'a target -> std::control::var::ref 'a int = <missing>
  d6: target -> int = <missing>
  d7: std::control::var::ref 'a target -> std::control::var::ref 'a int = <missing>
  my d8:"#cast": source -> target = e5:(fn p0:d10:x -> e4:(e0:r0:target->d3:target e3:{left: e1:1, right: e2:2}))
  d10:x arg
  d11:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-single-nominal.yu`

開始: 2026-11-08T11:36:01.216222+00:00、所要 0.018 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-single-nominal.yu`

開始: 2026-11-08T11:36:01.234795+00:00、所要 0.023 秒、exit 0。

```text
run roots [target({left: 1, right: 2})]
```

## cast-explicit

```yulang
struct user_id { raw: int }
cast(x: user_id): int = x.raw
cast(x: int): user_id = user_id { raw: x }
our id: user_id = 1
our back: int = id
back
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-explicit.yu`

開始: 2026-11-08T11:35:04.479425+00:00、所要 0.017 秒、exit 0。

```text
roots d0:user_id d5:id d6:back
d0:user_id: {raw: int} -> user_id = <missing>
d5:id: int | user_id = e8:1
d6:back: int | user_id = e9:r3:id->d5:id
root exprs e10:r4:back->d6:back
runtime roots e10:r4:back->d6:back
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d7:x -> e1:(e0:r0:x->d7:x.s0.raw->d1))
  my d4:"#cast": int -> user_id = e7:(fn p1:d8:x -> e6:(e3:r1:user_id->d0:user_id e5:{raw: e4:r2:x->d8:x}))
  d7:x arg
  d8:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-explicit.yu`

開始: 2026-11-08T11:35:04.496001+00:00、所要 0.02 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-explicit.yu`

開始: 2026-11-08T11:35:04.515741+00:00、所要 0.013 秒、exit 0。

```text
run roots [1]
```

## cast-branch

```yulang
struct user_id { raw: int }
cast(x: user_id): int = x.raw
our mixed(flag) = if flag: 1 else: user_id { raw: 2 }
mixed
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-branch.yu`

開始: 2026-11-08T11:35:04.529167+00:00、所要 0.029 秒、exit 0。

```text
roots d0:user_id d4:mixed
d0:user_id: {raw: int} -> user_id = <missing>
d4:mixed: never = <missing>
root exprs e4:r2:mixed->d4:mixed
runtime roots e4:r2:mixed->d4:mixed
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d5:x -> e1:(e0:r0:x->d5:x.s0.raw->d1))
  d5:x arg
  d6:flag arg
}
error: unresolved value name: std::control::junction::junction::junction
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-branch.yu`

開始: 2026-11-08T11:35:04.557924+00:00、所要 0.007 秒、exit 1。

```text
diagnostics:
  error [yulang.unresolved-value]: mixed: unresolved value name: std::control::junction::junction::junction
    --> line 3, column 5
    3 | our mixed(flag) = if flag: 1 else: user_id { raw: 2 }
      |     ^^^^^
    hint: define `std::control::junction::junction::junction` before this use, or import the module that provides it
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-branch.yu`

開始: 2026-11-08T11:35:04.565233+00:00、所要 0.013 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: std::control::junction::junction::junction
  hint: run `yulang check` to see source ranges before running
```

### check

Command: `./target/release/yulang --std-root lib check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-branch.yu`

開始: 2026-11-08T11:50:26.924364+00:00、所要 152.218 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-branch.yu`

開始: 2026-11-08T11:52:59.142867+00:00、所要 0.202 秒、exit 0。

```text
run roots [<closure>]
```

## cast-missing

```yulang
our use_bool(x: bool) = x
use_bool 42
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-missing.yu`

開始: 2026-11-08T11:35:04.578782+00:00、所要 0.006 秒、exit 0。

```text
roots d0:use_bool
d0:use_bool: bool -> bool = e1:(fn p0:d1:x -> e0:r0:x->d1:x)
root exprs e4:(e2:r1:use_bool->d0:use_bool e3:42)
runtime roots e4:(e2:r1:use_bool->d0:use_bool e3:42)
detached {
  d1:x arg
}
error: cannot use `int` where `bool` is required: no implicit cast from `int` to `bool`
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-missing.yu`

開始: 2026-11-08T11:35:04.584412+00:00、所要 0.009 秒、exit 1。

```text
diagnostics:
  error [yulang.missing-implicit-cast]: cannot use `int` where `bool` is required: no implicit cast from `int` to `bool`
    --> line 2, column 1
    2 | use_bool 42
      | ^^^^^^^^^^^
    hint: declare a `cast` from `int` to `bool`, or check whether a different type was intended
    note: type `int` is inferred from this argument
    --> line 2, column 10
    2 | use_bool 42
      |          ^^
    note: this callee requires an argument compatible with `bool`
    --> line 2, column 1
    2 | use_bool 42
      | ^^^^^^^^
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-missing.yu`

開始: 2026-11-08T11:35:04.593312+00:00、所要 0.015 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: cannot use `int` where `bool` is required: no implicit cast from `int` to `bool`
  hint: run `yulang check` to see source ranges before running
```

## cast-ambiguous

```yulang
struct user_id { raw: int }
cast(x: user_id): int = x.raw
cast(x: user_id): int = 9
our back: int = user_id {raw: 1}
back
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous.yu`

開始: 2026-11-08T11:35:04.608080+00:00、所要 0.011 秒、exit 0。

```text
roots d0:user_id d5:back
d0:user_id: {raw: int} -> user_id = <missing>
d5:back: int | user_id = e8:(e5:r1:user_id->d0:user_id e7:{raw: e6:1})
root exprs e9:r2:back->d5:back
runtime roots d5:back e9:r2:back->d5:back
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d6:x -> e1:(e0:r0:x->d6:x.s0.raw->d1))
  my d4:"#cast": user_id -> int = e4:(fn p1:d7:x -> e3:9)
  d6:x arg
  d7:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous.yu`

開始: 2026-11-08T11:35:04.618997+00:00、所要 0.007 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous.yu`

開始: 2026-11-08T11:35:04.625630+00:00、所要 0.009 秒、exit 0。

```text
run roots [1]
```

## cast-bare

```yulang
struct user_id { raw: int }
cast(x: user_id): int = x.raw
our id = user_id {raw: 1}
id
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-bare.yu`

開始: 2026-11-08T11:35:04.634222+00:00、所要 0.039 秒、exit 0。

```text
roots d0:user_id d4:id
d0:user_id: {raw: int} -> user_id = <missing>
d4:id: user_id = e6:(e3:r1:user_id->d0:user_id e5:{raw: e4:1})
root exprs e7:r2:id->d4:id
runtime roots d4:id e7:r2:id->d4:id
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d5:x -> e1:(e0:r0:x->d5:x.s0.raw->d1))
  d5:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-bare.yu`

開始: 2026-11-08T11:35:04.673713+00:00、所要 0.019 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-bare.yu`

開始: 2026-11-08T11:35:04.692585+00:00、所要 0.014 秒、exit 0。

```text
run roots [user_id({raw: 1})]
```

## cast-ambiguous-str

```yulang
struct user_id { raw: int }
cast(x: user_id): str = "first"
cast(x: user_id): str = "second"
our use_str(x: str): str = x
use_str(user_id {raw: 1})
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-str.yu`

開始: 2026-11-08T11:35:38.879864+00:00、所要 0.006 秒、exit 0。

```text
roots d0:user_id d5:use_str
d0:user_id: {raw: int} -> user_id = <missing>
d5:use_str: never = <missing>
root exprs e5:(e0:r0:use_str->d5:use_str e4:(e1:r1:user_id->d0:user_id e3:{raw: e2:1}))
runtime roots e5:(e0:r0:use_str->d5:use_str e4:(e1:r1:user_id->d0:user_id e3:{raw: e2:1}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": never = <missing>
  my d4:"#cast": never = <missing>
}
error: unresolved type name: str
error: unresolved type name: str
error: unresolved type name: str
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-str.yu`

開始: 2026-11-08T11:35:38.885937+00:00、所要 0.008 秒、exit 1。

```text
diagnostics:
  error [yulang.unresolved-type]: #cast: unresolved type name: str
    --> line 2, column 19
    2 | cast(x: user_id): str = "first"
      |                   ^^^
    hint: define type `str` before this annotation, or import it
  error [yulang.unresolved-type]: #cast: unresolved type name: str
    --> line 3, column 19
    3 | cast(x: user_id): str = "second"
      |                   ^^^
    hint: define type `str` before this annotation, or import it
  error [yulang.unresolved-type]: use_str: unresolved type name: str
    --> line 4, column 16
    4 | our use_str(x: str): str = x
      |                ^^^
    hint: define type `str` before this annotation, or import it
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-ambiguous-str.yu`

開始: 2026-11-08T11:35:38.894018+00:00、所要 0.009 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved type name: str
  detail: unresolved type name: str
  detail: unresolved type name: str
  hint: run `yulang check` to see source ranges before running
```

## cast-single-str

```yulang
struct user_id { raw: int }
cast(x: user_id): str = "only"
our use_str(x: str): str = x
use_str(user_id {raw: 1})
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-single-str.yu`

開始: 2026-11-08T11:35:38.902978+00:00、所要 0.006 秒、exit 0。

```text
roots d0:user_id d4:use_str
d0:user_id: {raw: int} -> user_id = <missing>
d4:use_str: never = <missing>
root exprs e5:(e0:r0:use_str->d4:use_str e4:(e1:r1:user_id->d0:user_id e3:{raw: e2:1}))
runtime roots e5:(e0:r0:use_str->d4:use_str e4:(e1:r1:user_id->d0:user_id e3:{raw: e2:1}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": never = <missing>
}
error: unresolved type name: str
error: unresolved type name: str
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-single-str.yu`

開始: 2026-11-08T11:35:38.909490+00:00、所要 0.01 秒、exit 1。

```text
diagnostics:
  error [yulang.unresolved-type]: #cast: unresolved type name: str
    --> line 2, column 19
    2 | cast(x: user_id): str = "only"
      |                   ^^^
    hint: define type `str` before this annotation, or import it
  error [yulang.unresolved-type]: use_str: unresolved type name: str
    --> line 3, column 16
    3 | our use_str(x: str): str = x
      |                ^^^
    hint: define type `str` before this annotation, or import it
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-single-str.yu`

開始: 2026-11-08T11:35:38.919549+00:00、所要 0.031 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved type name: str
  detail: unresolved type name: str
  hint: run `yulang check` to see source ranges before running
```

### check

Command: `./target/release/yulang --std-root lib check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-single-str.yu`

開始: 2026-11-08T11:55:38.051678+00:00、所要 172.535 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-single-str.yu`

開始: 2026-11-08T11:58:30.587082+00:00、所要 0.291 秒、exit 0。

```text
run roots ["only"]
```

## if-no-else-true

```yulang
our x = if true: 42
x
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/if-no-else-true.yu`

開始: 2026-11-08T11:46:39.331303+00:00、所要 0.005 秒、exit 0。

```text
roots d0:x
d0:x: never = <missing>
root exprs e1:r0:x->d0:x
runtime roots e1:r0:x->d0:x
error: unresolved value name: std::control::junction::junction::junction
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/if-no-else-true.yu`

開始: 2026-11-08T11:46:39.336031+00:00、所要 0.004 秒、exit 1。

```text
diagnostics:
  error [yulang.unresolved-value]: x: unresolved value name: std::control::junction::junction::junction
    --> line 1, column 5
    1 | our x = if true: 42
      |     ^
    hint: define `std::control::junction::junction::junction` before this use, or import the module that provides it
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/if-no-else-true.yu`

開始: 2026-11-08T11:46:39.339668+00:00、所要 0.004 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: std::control::junction::junction::junction
  hint: run `yulang check` to see source ranges before running
```

## if-no-else-false

```yulang
our x = if false: 42
x
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/if-no-else-false.yu`

開始: 2026-11-08T11:46:39.343867+00:00、所要 0.003 秒、exit 0。

```text
roots d0:x
d0:x: never = <missing>
root exprs e1:r0:x->d0:x
runtime roots e1:r0:x->d0:x
error: unresolved value name: std::control::junction::junction::junction
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/if-no-else-false.yu`

開始: 2026-11-08T11:46:39.347255+00:00、所要 0.006 秒、exit 1。

```text
diagnostics:
  error [yulang.unresolved-value]: x: unresolved value name: std::control::junction::junction::junction
    --> line 1, column 5
    1 | our x = if false: 42
      |     ^
    hint: define `std::control::junction::junction::junction` before this use, or import the module that provides it
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/if-no-else-false.yu`

開始: 2026-11-08T11:46:39.352797+00:00、所要 0.004 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: std::control::junction::junction::junction
  hint: run `yulang check` to see source ranges before running
```

## guard-where

```yulang
our x = case 1:
    value where false -> 9
    value -> value
x
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/guard-where.yu`

開始: 2026-11-08T11:46:39.357164+00:00、所要 0.004 秒、exit 0。

```text
roots d0:x
d0:x: never = <missing>
root exprs e2:r0:x->d0:x
runtime roots e2:r0:x->d0:x
detached {
  d1:value arg
}
error: unresolved value name: std::control::junction::junction::junction
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/guard-where.yu`

開始: 2026-11-08T11:46:39.361201+00:00、所要 0.003 秒、exit 1。

```text
diagnostics:
  error [yulang.unresolved-value]: x: unresolved value name: std::control::junction::junction::junction
    --> line 1, column 5
    1 | our x = case 1:
      |     ^
    hint: define `std::control::junction::junction::junction` before this use, or import the module that provides it
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/guard-where.yu`

開始: 2026-11-08T11:46:39.364239+00:00、所要 0.003 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: std::control::junction::junction::junction
  hint: run `yulang check` to see source ranges before running
```

## guard-if

```yulang
our x = case 1:
    value if false -> 9
    value -> value
x
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/guard-if.yu`

開始: 2026-11-08T11:46:39.367484+00:00、所要 0.003 秒、exit 0。

```text
roots d0:x
d0:x: never = <missing>
root exprs e2:r0:x->d0:x
runtime roots e2:r0:x->d0:x
detached {
  d1:value arg
}
error: unresolved value name: std::control::junction::junction::junction
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/guard-if.yu`

開始: 2026-11-08T11:46:39.370268+00:00、所要 0.002 秒、exit 1。

```text
diagnostics:
  error [yulang.unresolved-value]: x: unresolved value name: std::control::junction::junction::junction
    --> line 1, column 5
    1 | our x = case 1:
      |     ^
    hint: define `std::control::junction::junction::junction` before this use, or import the module that provides it
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/guard-if.yu`

開始: 2026-11-08T11:46:39.372524+00:00、所要 0.004 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: std::control::junction::junction::junction
  hint: run `yulang check` to see source ranges before running
```

## error-record

```yulang
error problem:
    bad {code: int}
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/error-record.yu`

開始: 2026-11-08T11:46:39.376528+00:00、所要 0.003 秒、exit 0。

```text
roots d0:problem
d0:problem mod {
  d1:"problem.bad": {code: int} -> problem = <missing>
}
detached {
  my d2: never = <missing>
  d3:"problem.wrap" = <missing>
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/error-record.yu`

開始: 2026-11-08T11:46:39.379210+00:00、所要 0.002 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/error-record.yu`

開始: 2026-11-08T11:46:39.381293+00:00、所要 0.003 秒、exit 0。

```text
run roots []
```

## lazy-short-circuit

```yulang
pub lazy infix(and) 2.0.0 2.0.1 = \a -> \b ->
    if a():
        b()
    else:
        false
act ping:
    our get: () -> bool
our x = catch (false and ping::get()):
    ping::get(), k -> true
    value -> value
x
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/lazy-short-circuit.yu`

開始: 2026-11-08T11:46:39.384618+00:00、所要 0.005 秒、exit 0。

```text
roots d0:"#op:infix:and" d1:ping d3:x
pub d0:"#op:infix:and": never = <missing>
d1:ping mod {
}
d3:x: bool = e14:catch e11:(e10:(e4:r1:"#op:infix:and"->d0:"#op:infix:and" e8:(fn p2:() -> e3:false)) e9:(fn p3:() -> e7:(e5:r2:"ping::get"->d2:"ping.get" e6:()))) { ping::get p4:_, p5:d6:k -> e12:true; p6:d7:value -> e13:r3:value->d7:value }
root exprs e15:r4:x->d3:x
runtime roots d3:x e15:r4:x->d3:x
detached {
  d2:"ping.get": () -> [ping] bool = <missing>
  d4:a arg
  d5:b arg
  d6:k arg
  d7:value arg
}
error: unresolved value name: std::control::junction::junction::junction
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/lazy-short-circuit.yu`

開始: 2026-11-08T11:46:39.389686+00:00、所要 0.004 秒、exit 1。

```text
diagnostics:
  error [yulang.unresolved-value]: #op:infix:and: unresolved value name: std::control::junction::junction::junction
    --> line 1, column 16
    1 | pub lazy infix(and) 2.0.0 2.0.1 = \a -> \b ->
      |                ^^^
    hint: define `std::control::junction::junction::junction` before this use, or import the module that provides it
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/lazy-short-circuit.yu`

開始: 2026-11-08T11:46:39.393348+00:00、所要 0.005 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: std::control::junction::junction::junction
  hint: run `yulang check` to see source ranges before running
```

## lazy-force-right

```yulang
pub lazy infix(and) 2.0.0 2.0.1 = \a -> \b ->
    if a():
        b()
    else:
        false
act ping:
    our get: () -> bool
our x = catch (true and ping::get()):
    ping::get(), k -> true
    value -> value
x
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/lazy-force-right.yu`

開始: 2026-11-08T11:46:39.398228+00:00、所要 0.005 秒、exit 0。

```text
roots d0:"#op:infix:and" d1:ping d3:x
pub d0:"#op:infix:and": never = <missing>
d1:ping mod {
}
d3:x: bool = e14:catch e11:(e10:(e4:r1:"#op:infix:and"->d0:"#op:infix:and" e8:(fn p2:() -> e3:true)) e9:(fn p3:() -> e7:(e5:r2:"ping::get"->d2:"ping.get" e6:()))) { ping::get p4:_, p5:d6:k -> e12:true; p6:d7:value -> e13:r3:value->d7:value }
root exprs e15:r4:x->d3:x
runtime roots d3:x e15:r4:x->d3:x
detached {
  d2:"ping.get": () -> [ping] bool = <missing>
  d4:a arg
  d5:b arg
  d6:k arg
  d7:value arg
}
error: unresolved value name: std::control::junction::junction::junction
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/lazy-force-right.yu`

開始: 2026-11-08T11:46:39.403339+00:00、所要 0.004 秒、exit 1。

```text
diagnostics:
  error [yulang.unresolved-value]: #op:infix:and: unresolved value name: std::control::junction::junction::junction
    --> line 1, column 16
    1 | pub lazy infix(and) 2.0.0 2.0.1 = \a -> \b ->
      |                ^^^
    hint: define `std::control::junction::junction::junction` before this use, or import the module that provides it
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/lazy-force-right.yu`

開始: 2026-11-08T11:46:39.407053+00:00、所要 0.005 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: std::control::junction::junction::junction
  hint: run `yulang check` to see source ranges before running
```

## lazy-short-circuit-case

```yulang
pub lazy infix(and) 2.0.0 2.0.1 = \a -> \b ->
    case a():
        true -> b()
        false -> false
act ping:
    our get: () -> bool
our x = catch (false and ping::get()):
    ping::get(), k -> true
    value -> value
x
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/lazy-short-circuit-case.yu`

開始: 2026-11-08T11:47:27.269137+00:00、所要 0.012 秒、exit 0。

```text
roots d0:"#op:infix:and" d1:ping d3:x
pub d0:"#op:infix:and": (() -> ['a] bool) -> (() -> ['a] 'b) -> ['a] 'b | bool = e9:(fn p0:d4:a -> e8:(fn p1:d5:b -> e7:case e2:(e0:r0:a->d4:a e1:()) { p2:true -> e5:(e3:r1:b->d5:b e4:()); p3:false -> e6:false }))
d1:ping mod {
}
d3:x: bool = e21:catch e18:(e17:(e11:r2:"#op:infix:and"->d0:"#op:infix:and" e15:(fn p4:() -> e10:false)) e16:(fn p5:() -> e14:(e12:r3:"ping::get"->d2:"ping.get" e13:()))) { ping::get p6:_, p7:d6:k -> e19:true; p8:d7:value -> e20:r4:value->d7:value }
root exprs e22:r5:x->d3:x
runtime roots d3:x e22:r5:x->d3:x
detached {
  d2:"ping.get": () -> [ping] bool = <missing>
  d4:a arg
  d5:b arg
  d6:k arg
  d7:value arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/lazy-short-circuit-case.yu`

開始: 2026-11-08T11:47:27.281449+00:00、所要 0.007 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/lazy-short-circuit-case.yu`

開始: 2026-11-08T11:47:27.288829+00:00、所要 0.005 秒、exit 0。

```text
run roots [false]
```

## lazy-force-right-case

```yulang
pub lazy infix(and) 2.0.0 2.0.1 = \a -> \b ->
    case a():
        true -> b()
        false -> false
act ping:
    our get: () -> bool
our x = catch (true and ping::get()):
    ping::get(), k -> true
    value -> value
x
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/lazy-force-right-case.yu`

開始: 2026-11-08T11:47:27.293847+00:00、所要 0.008 秒、exit 0。

```text
roots d0:"#op:infix:and" d1:ping d3:x
pub d0:"#op:infix:and": (() -> ['a] bool) -> (() -> ['a] 'b) -> ['a] 'b | bool = e9:(fn p0:d4:a -> e8:(fn p1:d5:b -> e7:case e2:(e0:r0:a->d4:a e1:()) { p2:true -> e5:(e3:r1:b->d5:b e4:()); p3:false -> e6:false }))
d1:ping mod {
}
d3:x: bool = e21:catch e18:(e17:(e11:r2:"#op:infix:and"->d0:"#op:infix:and" e15:(fn p4:() -> e10:true)) e16:(fn p5:() -> e14:(e12:r3:"ping::get"->d2:"ping.get" e13:()))) { ping::get p6:_, p7:d6:k -> e19:true; p8:d7:value -> e20:r4:value->d7:value }
root exprs e22:r5:x->d3:x
runtime roots d3:x e22:r5:x->d3:x
detached {
  d2:"ping.get": () -> [ping] bool = <missing>
  d4:a arg
  d5:b arg
  d6:k arg
  d7:value arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/lazy-force-right-case.yu`

開始: 2026-11-08T11:47:27.301978+00:00、所要 0.007 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/lazy-force-right-case.yu`

開始: 2026-11-08T11:47:27.309204+00:00、所要 0.004 秒、exit 0。

```text
run roots [true]
```

## error-record-use

```yulang
error problem:
    bad {code: int}
problem::bad {code: 7}
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/error-record-use.yu`

開始: 2026-11-08T11:47:27.312930+00:00、所要 0.003 秒、exit 0。

```text
roots d0:problem
d0:problem mod {
  d1:"problem.bad": {code: int} -> problem = <missing>
}
root exprs e3:(e0:r0:"problem::bad"->d1:"problem.bad" e2:{code: e1:7})
runtime roots e3:(e0:r0:"problem::bad"->d1:"problem.bad" e2:{code: e1:7})
detached {
  my d2: never = <missing>
  d3:"problem.wrap" = <missing>
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/error-record-use.yu`

開始: 2026-11-08T11:47:27.315905+00:00、所要 0.003 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/error-record-use.yu`

開始: 2026-11-08T11:47:27.318545+00:00、所要 0.002 秒、exit 0。

```text
run roots [problem::bad({code: 7})]
```

### check

Command: `./target/release/yulang --std-root lib check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/error-record-use.yu`

開始: 2026-11-08T11:49:50.105062+00:00、所要 139.547 秒、exit -9。

```text
```

### run

Command: `./target/release/yulang --std-root lib run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/error-record-use.yu`

開始: 2026-11-08T11:52:09.651727+00:00、所要 0.304 秒、exit 0。

```text
run roots [problem::bad({code: 7})]
```

### check

Command: `./target/release/yulang --std-root lib check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/error-record-use.yu`

開始: 2026-11-08T12:01:22.341548+00:00、所要 150.092 秒、exit 0。

```text
```

## record-default-effects-absent

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get(), b = a} = (a,b)
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default-effects-absent.yu`

開始: 2026-11-08T11:56:24.088007+00:00、所要 0.011 秒、exit 0。

```text
roots d0:ping d2:pick d3:handle
d0:ping mod {
}
d2:pick: {a?: 'a & 'b, b?: 'b} -> ('a | int, 'b | 'a | int) = e7:(fn p2:{a: p0:d4:a = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()), b: p1:d5:b = e3:r1:a->d4:a} -> e6:(e4:r2:a->d4:a, e5:r3:b->d5:b))
d3:handle: 'a ['b & [ping; 'b]] -> ['b] 'a = e14:(fn p3:d6:action -> e13:catch e8:r4:action->d6:action { ping::get p4:_, p5:d7:k -> e11:(e9:r5:k->d7:k e10:7); p6:d8:value -> e12:r6:value->d8:value })
root exprs e19:(e15:r7:handle->d3:handle e18:(e16:r8:pick->d2:pick e17:{}))
runtime roots e19:(e15:r7:handle->d3:handle e18:(e16:r8:pick->d2:pick e17:{}))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:a arg
  d5:b arg
  d6:action arg
  d7:k arg
  d8:value arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default-effects-absent.yu`

開始: 2026-11-08T11:56:24.098822+00:00、所要 0.009 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default-effects-absent.yu`

開始: 2026-11-08T11:56:24.107994+00:00、所要 0.004 秒、exit 1。

```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
    --> line 3, column 15
    3 | our pick {a = ping::get(), b = a} = (a,b)
      |               ^^^^^^^^^
  hint: handle this computation with a matching effect handler before running it
  note: application occurs here
    --> line 3, column 15
    3 | our pick {a = ping::get(), b = a} = (a,b)
      |               ^^^^^^^^^^^
```

## record-default-effects-present

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get(), b = a} = (a,b)
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {a: 9})
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default-effects-present.yu`

開始: 2026-11-08T11:56:24.112641+00:00、所要 0.009 秒、exit 0。

```text
roots d0:ping d2:pick d3:handle
d0:ping mod {
}
d2:pick: {a?: 'a & 'b, b?: 'b} -> ('a | int, 'b | 'a | int) = e7:(fn p2:{a: p0:d4:a = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()), b: p1:d5:b = e3:r1:a->d4:a} -> e6:(e4:r2:a->d4:a, e5:r3:b->d5:b))
d3:handle: 'a ['b & [ping; 'b]] -> ['b] 'a = e14:(fn p3:d6:action -> e13:catch e8:r4:action->d6:action { ping::get p4:_, p5:d7:k -> e11:(e9:r5:k->d7:k e10:7); p6:d8:value -> e12:r6:value->d8:value })
root exprs e20:(e15:r7:handle->d3:handle e19:(e16:r8:pick->d2:pick e18:{a: e17:9}))
runtime roots e20:(e15:r7:handle->d3:handle e19:(e16:r8:pick->d2:pick e18:{a: e17:9}))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:a arg
  d5:b arg
  d6:action arg
  d7:k arg
  d8:value arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default-effects-present.yu`

開始: 2026-11-08T11:56:24.121812+00:00、所要 0.008 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default-effects-present.yu`

開始: 2026-11-08T11:56:24.129604+00:00、所要 0.004 秒、exit 0。

```text
run roots [(9, 9)]
```

## record-default-effects-both

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get(), b = a} = (a,b)
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {a: 9, b: 8})
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default-effects-both.yu`

開始: 2026-11-08T11:56:24.133443+00:00、所要 0.01 秒、exit 0。

```text
roots d0:ping d2:pick d3:handle
d0:ping mod {
}
d2:pick: {a?: 'a & 'b, b?: 'b} -> ('a | int, 'b | 'a | int) = e7:(fn p2:{a: p0:d4:a = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()), b: p1:d5:b = e3:r1:a->d4:a} -> e6:(e4:r2:a->d4:a, e5:r3:b->d5:b))
d3:handle: 'a ['b & [ping; 'b]] -> ['b] 'a = e14:(fn p3:d6:action -> e13:catch e8:r4:action->d6:action { ping::get p4:_, p5:d7:k -> e11:(e9:r5:k->d7:k e10:7); p6:d8:value -> e12:r6:value->d8:value })
root exprs e21:(e15:r7:handle->d3:handle e20:(e16:r8:pick->d2:pick e19:{a: e17:9, b: e18:8}))
runtime roots e21:(e15:r7:handle->d3:handle e20:(e16:r8:pick->d2:pick e19:{a: e17:9, b: e18:8}))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:a arg
  d5:b arg
  d6:action arg
  d7:k arg
  d8:value arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default-effects-both.yu`

開始: 2026-11-08T11:56:24.143310+00:00、所要 0.009 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default-effects-both.yu`

開始: 2026-11-08T11:56:24.152278+00:00、所要 0.005 秒、exit 0。

```text
run roots [(9, 8)]
```

## error-from-wrap

```yulang
error small:
    bad
error big:
    nested from small
big::wrap: fail small::bad
```

### run

Command: `./target/release/yulang --std-root lib run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/error-from-wrap.yu`

開始: 2026-11-08T12:09:18.661292+00:00、所要 0.244 秒、exit 1。

```text
runtime error [yulang.unhandled-effect]: unhandled effect request small::bad
  hint: handle this computation with a matching effect handler before running it
```

## error-from-up

```yulang
error small:
    bad
error big:
    nested from small
big::wrap: big::up: fail small::bad
```

### run

Command: `./target/release/yulang --std-root lib run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/error-from-up.yu`

開始: 2026-11-08T12:09:18.905647+00:00、所要 0.232 秒、exit 0。

```text
run roots [result::err(big::nested(small::bad))]
```

## enum-from-cast

```yulang
enum small:
    bad
enum big:
    nested from small
our use_big(x: big): big = x
use_big(small::bad)
```

### run

Command: `./target/release/yulang --std-root lib run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/enum-from-cast.yu`

開始: 2026-11-08T12:09:19.137653+00:00、所要 308.048 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: cannot use `small` where `big` is required: no implicit cast from `small` to `big`
  hint: run `yulang check` to see source ranges before running
```

## handler-multishot-sequence

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my first = k 3
        k 7
    v -> v
handle(ping::get())
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/handler-multishot-sequence.yu`

開始: 2026-11-08T11:33:32.168840+00:00、所要 0.028 秒、exit 0。

```text
roots d0:ping d2:handle
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e10:(fn p0:d3:action -> e9:catch e0:r0:action->d3:action { ping::get p1:_, p2:d4:k -> e7:block { let my p3:d5:first = e3:(e1:r1:k->d4:k e2:3); e6:(e4:r2:k->d4:k e5:7) }; p4:d6:v -> e8:r3:v->d6:v })
root exprs e15:(e11:r4:handle->d2:handle e14:(e12:r5:"ping::get"->d1:"ping.get" e13:()))
runtime roots e15:(e11:r4:handle->d2:handle e14:(e12:r5:"ping::get"->d1:"ping.get" e13:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:action arg
  d4:k arg
  my d5:first: 'a | 'b | int = e3:(e1:r1:k->d4:k e2:3)
  d6:v arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/handler-multishot-sequence.yu`

開始: 2026-11-08T11:33:32.197461+00:00、所要 0.033 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/handler-multishot-sequence.yu`

開始: 2026-11-08T11:33:32.230677+00:00、所要 0.02 秒、exit 0。

```text
run roots [7]
```

## ascription-simple

```yulang
our one = 1 as int
one
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/ascription-simple.yu`

開始: 2026-11-08T11:33:32.250742+00:00、所要 0.017 秒、exit 0。

```text
roots d0:one
d0:one: int = e0:1
root exprs e1:r0:one->d0:one
runtime roots e1:r0:one->d0:one
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/ascription-simple.yu`

開始: 2026-11-08T11:33:32.267939+00:00、所要 0.009 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/ascription-simple.yu`

開始: 2026-11-08T11:33:32.276897+00:00、所要 0.011 秒、exit 0。

```text
run roots [1]
```

## argument-forcing

```yulang
act ping:
    our get: () -> int
our ignore(x: int): int = 99
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 7
    v -> v
handle(ignore(ping::get()))
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/argument-forcing.yu`

開始: 2026-11-08T11:33:32.287830+00:00、所要 0.008 秒、exit 0。

```text
roots d0:ping d2:ignore d3:handle
d0:ping mod {
}
d2:ignore: int -> int = e1:(fn p0:d4:x -> e0:99)
d3:handle: int [ping; 'a] -> ['a] int = e6:(fn p1:d5:action -> e5:catch e2:r0:action->d5:action { ping::get p2:_, p3:d6:k -> e3:7; p4:d7:v -> e4:r1:v->d7:v })
root exprs e13:(e7:r2:handle->d3:handle e12:(e8:r3:ignore->d2:ignore e11:(e9:r4:"ping::get"->d1:"ping.get" e10:())))
runtime roots e13:(e7:r2:handle->d3:handle e12:(e8:r3:ignore->d2:ignore e11:(e9:r4:"ping::get"->d1:"ping.get" e10:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:x arg
  d5:action arg
  d6:k arg
  d7:v arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/argument-forcing.yu`

開始: 2026-11-08T11:33:32.295919+00:00、所要 0.018 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/argument-forcing.yu`

開始: 2026-11-08T11:33:32.313732+00:00、所要 0.013 秒、exit 0。

```text
run roots [7]
```

## return-filter

```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
our bad(): [ping] int = pong::get()
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/return-filter.yu`

開始: 2026-11-08T11:33:32.327280+00:00、所要 0.01 秒、exit 0。

```text
roots d0:ping d2:pong d4:bad
d0:ping mod {
}
d2:pong mod {
}
d4:bad: () -> [pong] int = e3:(fn p0:() -> e2:(e0:r0:"pong::get"->d3:"pong.get" e1:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
}
error: effect filter mismatch: pong is not allowed by [ping]
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/return-filter.yu`

開始: 2026-11-08T11:33:32.336946+00:00、所要 0.033 秒、exit 1。

```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/return-filter.yu`

開始: 2026-11-08T11:33:32.369938+00:00、所要 0.02 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: effect filter mismatch: pong is not allowed by [ping]
  hint: run `yulang check` to see source ranges before running
```

## record-default-effects

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get(), b = a} = (a,b)
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
(handle(pick {}), handle(pick {a: 9}), handle(pick {a: 9, b: 8}))
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default-effects.yu`

開始: 2026-11-08T11:56:09.599518+00:00、所要 0.015 秒、exit 0。

```text
roots d0:ping d2:pick d3:handle
d0:ping mod {
}
d2:pick: {a?: 'a & 'b, b?: 'b} -> ('a | int, 'b | 'a | int) = e7:(fn p2:{a: p0:d4:a = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()), b: p1:d5:b = e3:r1:a->d4:a} -> e6:(e4:r2:a->d4:a, e5:r3:b->d5:b))
d3:handle: 'a ['b & [ping; 'b]] -> ['b] 'a = e14:(fn p3:d6:action -> e13:catch e8:r4:action->d6:action { ping::get p4:_, p5:d7:k -> e11:(e9:r5:k->d7:k e10:7); p6:d8:value -> e12:r6:value->d8:value })
root exprs e33:(e19:(e15:r7:handle->d3:handle e18:(e16:r8:pick->d2:pick e17:{})), e25:(e20:r9:handle->d3:handle e24:(e21:r10:pick->d2:pick e23:{a: e22:9})), e32:(e26:r11:handle->d3:handle e31:(e27:r12:pick->d2:pick e30:{a: e28:9, b: e29:8})))
runtime roots e33:(e19:(e15:r7:handle->d3:handle e18:(e16:r8:pick->d2:pick e17:{})), e25:(e20:r9:handle->d3:handle e24:(e21:r10:pick->d2:pick e23:{a: e22:9})), e32:(e26:r11:handle->d3:handle e31:(e27:r12:pick->d2:pick e30:{a: e28:9, b: e29:8})))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:a arg
  d5:b arg
  d6:action arg
  d7:k arg
  d8:value arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default-effects.yu`

開始: 2026-11-08T11:56:09.614925+00:00、所要 0.013 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default-effects.yu`

開始: 2026-11-08T11:56:09.627772+00:00、所要 0.006 秒、exit 1。

```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
    --> line 3, column 15
    3 | our pick {a = ping::get(), b = a} = (a,b)
      |               ^^^^^^^^^
  hint: handle this computation with a matching effect handler before running it
  note: application occurs here
    --> line 3, column 15
    3 | our pick {a = ping::get(), b = a} = (a,b)
      |               ^^^^^^^^^^^
```

## row-method-single

```yulang
act ping:
    our get: () -> int
    our x.answer = catch x:
        get(), k -> k 7
        value -> value
ping::get().answer
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/row-method-single.yu`

開始: 2026-11-08T11:56:09.633587+00:00、所要 0.006 秒、exit 0。

```text
roots d0:ping
d0:ping mod {
  d2:"ping.#act-method:answer:2": 'a ['b & [ping; 'b]] -> ['b] 'a = e6:(fn p0:d3:x -> e5:catch e0:r0:x->d3:x { ping::get p1:_, p2:d4:k -> e3:(e1:r1:k->d4:k e2:7); p3:d5:value -> e4:r2:value->d5:value })
}
root exprs e10:(e9:(e7:r3:"ping::get"->d1:"ping.get" e8:()).s0.answer->d2:"ping.#act-method:answer:2")
runtime roots e10:(e9:(e7:r3:"ping::get"->d1:"ping.get" e8:()).s0.answer->d2:"ping.#act-method:answer:2")
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:x arg
  d4:k arg
  d5:value arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/row-method-single.yu`

開始: 2026-11-08T11:56:09.640173+00:00、所要 0.005 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/row-method-single.yu`

開始: 2026-11-08T11:56:09.645498+00:00、所要 0.003 秒、exit 0。

```text
run roots [7]
```

## row-method-ambiguous

```yulang
act ping:
    our get: () -> int
    our x.answer = catch x:
        get(), k -> k 7
        value -> value
act pong:
    our get: () -> int
    our x.answer = catch x:
        get(), k -> k 8
        value -> value
our both() =
    ping::get()
    pong::get()
both().answer
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/row-method-ambiguous.yu`

開始: 2026-11-08T11:56:09.649025+00:00、所要 0.008 秒、exit 0。

```text
roots d0:ping d3:pong d6:both
d0:ping mod {
  d2:"ping.#act-method:answer:2": 'a ['b & [ping; 'b]] -> ['b] 'a = e6:(fn p0:d7:x -> e5:catch e0:r0:x->d7:x { ping::get p1:_, p2:d8:k -> e3:(e1:r1:k->d8:k e2:7); p3:d9:value -> e4:r2:value->d9:value })
}
d3:pong mod {
  d5:"pong.#act-method:answer:5": 'a ['b & [pong; 'b]] -> ['b] 'a = e13:(fn p4:d10:x -> e12:catch e7:r3:x->d10:x { pong::get p5:_, p6:d11:k -> e10:(e8:r4:k->d11:k e9:8); p7:d12:value -> e11:r5:value->d12:value })
}
d6:both: () -> [ping, pong] int = e21:(fn p8:() -> e20:block { e16:(e14:r6:"ping::get"->d1:"ping.get" e15:()); e19:(e17:r7:"pong::get"->d4:"pong.get" e18:()) })
root exprs e25:(e24:(e22:r8:both->d6:both e23:()).s0.answer#field)
runtime roots e25:(e24:(e22:r8:both->d6:both e23:()).s0.answer#field)
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:"pong.get": () -> [pong] int = <missing>
  d7:x arg
  d8:k arg
  d9:value arg
  d10:x arg
  d11:k arg
  d12:value arg
}
error: type shape `int` is not compatible with required shape `record {answer}`
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/row-method-ambiguous.yu`

開始: 2026-11-08T11:56:09.657406+00:00、所要 0.007 秒、exit 1。

```text
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `int` is not compatible with required shape `record {answer}`
    hint: check that the value provides the fields or shape required by this use
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/row-method-ambiguous.yu`

開始: 2026-11-08T11:56:09.664989+00:00、所要 0.01 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `int` is not compatible with required shape `record {answer}`
  hint: run `yulang check` to see source ranges before running
```

## type-variable-explicit

```yulang
our id(x: 'a): 'a = x
(id 7,id true)
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/type-variable-explicit.yu`

開始: 2026-11-08T11:56:09.674542+00:00、所要 0.006 秒、exit 0。

```text
roots d0:id
d0:id: 'a -> 'a = e1:(fn p0:d1:x -> e0:r0:x->d1:x)
root exprs e8:(e4:(e2:r1:id->d0:id e3:7), e7:(e5:r2:id->d0:id e6:true))
runtime roots e8:(e4:(e2:r1:id->d0:id e3:7), e7:(e5:r2:id->d0:id e6:true))
detached {
  d1:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/type-variable-explicit.yu`

開始: 2026-11-08T11:56:09.680770+00:00、所要 0.005 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/type-variable-explicit.yu`

開始: 2026-11-08T11:56:09.685897+00:00、所要 0.004 秒、exit 0。

```text
run roots [(7, true)]
```

## hygiene-callback-plain

```yulang
act ping:
    our get: () -> int
our inner(f) = catch f():
    ping::get(), k -> k 1
    value -> value
our outer(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
outer(inner(\() -> ping::get()))
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/hygiene-callback-plain.yu`

開始: 2026-11-08T11:52:25.564683+00:00、所要 0.013 秒、exit 0。

```text
roots d0:ping d2:inner d3:outer
d0:ping mod {
}
d2:inner: (() -> ['a] 'b) -> ['a] 'b = e8:(fn p0:d4:f -> e7:catch e2:(e0:r0:f->d4:f e1:()) { ping::get p1:_, p2:d5:k -> e5:(e3:r1:k->d5:k e4:1); p3:d6:value -> e6:r2:value->d6:value })
d3:outer: int ['a & [ping; 'a]] -> ['a] int = e15:(fn p4:d7:action -> e14:catch e9:r3:action->d7:action { ping::get p5:_, p6:d8:k -> e12:(e10:r4:k->d8:k e11:7); p7:d9:value -> e13:r5:value->d9:value })
root exprs e23:(e16:r6:outer->d3:outer e22:(e17:r7:inner->d2:inner e21:(fn p8:() -> e20:(e18:r8:"ping::get"->d1:"ping.get" e19:()))))
runtime roots e23:(e16:r6:outer->d3:outer e22:(e17:r7:inner->d2:inner e21:(fn p8:() -> e20:(e18:r8:"ping::get"->d1:"ping.get" e19:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:f arg
  d5:k arg
  d6:value arg
  d7:action arg
  d8:k arg
  d9:value arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/hygiene-callback-plain.yu`

開始: 2026-11-08T11:52:25.577819+00:00、所要 0.011 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/hygiene-callback-plain.yu`

開始: 2026-11-08T11:52:25.589540+00:00、所要 0.004 秒、exit 0。

```text
run roots [1]
```

## hygiene-callback-surface

```yulang
act ping:
    our get: () -> int
our inner(f: () -> [_] int) = catch f():
    ping::get(), k -> k 1
    value -> value
our outer(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
outer(inner(\() -> ping::get()))
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/hygiene-callback-surface.yu`

開始: 2026-11-08T11:52:25.593791+00:00、所要 0.013 秒、exit 0。

```text
roots d0:ping d2:inner d3:outer
d0:ping mod {
}
d2:inner: (() -> ['a] int) -> ['a] int = e8:(fn p0:d4:f -> e7:catch e2:(e0:r0:f->d4:f e1:()) { ping::get p1:_, p2:d5:k -> e5:(e3:r1:k->d5:k e4:1); p3:d6:value -> e6:r2:value->d6:value })
d3:outer: int ['a & [ping; 'a]] -> ['a] int = e15:(fn p4:d7:action -> e14:catch e9:r3:action->d7:action { ping::get p5:_, p6:d8:k -> e12:(e10:r4:k->d8:k e11:7); p7:d9:value -> e13:r5:value->d9:value })
root exprs e23:(e16:r6:outer->d3:outer e22:(e17:r7:inner->d2:inner e21:(fn p8:() -> e20:(e18:r8:"ping::get"->d1:"ping.get" e19:()))))
runtime roots e23:(e16:r6:outer->d3:outer e22:(e17:r7:inner->d2:inner e21:(fn p8:() -> e20:(e18:r8:"ping::get"->d1:"ping.get" e19:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:f arg
  d5:k arg
  d6:value arg
  d7:action arg
  d8:k arg
  d9:value arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/hygiene-callback-surface.yu`

開始: 2026-11-08T11:52:25.607184+00:00、所要 0.017 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/hygiene-callback-surface.yu`

開始: 2026-11-08T11:52:25.624701+00:00、所要 0.005 秒、exit 0。

```text
run roots [1]
```

## hygiene-callback-filter

```yulang
act ping:
    our get: () -> int
our inner(f: () -> [ping] int) = catch f():
    ping::get(), k -> k 1
    value -> value
our outer(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
outer(inner(\() -> ping::get()))
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/hygiene-callback-filter.yu`

開始: 2026-11-08T11:52:25.629403+00:00、所要 0.013 秒、exit 0。

```text
roots d0:ping d2:inner d3:outer
d0:ping mod {
}
d2:inner: (() -> [ping] int) -> int = e8:(fn p0:d4:f -> e7:catch e2:(e0:r0:f->d4:f e1:()) { ping::get p1:_, p2:d5:k -> e5:(e3:r1:k->d5:k e4:1); p3:d6:value -> e6:r2:value->d6:value })
d3:outer: int ['a & [ping; 'a]] -> ['a] int = e15:(fn p4:d7:action -> e14:catch e9:r3:action->d7:action { ping::get p5:_, p6:d8:k -> e12:(e10:r4:k->d8:k e11:7); p7:d9:value -> e13:r5:value->d9:value })
root exprs e23:(e16:r6:outer->d3:outer e22:(e17:r7:inner->d2:inner e21:(fn p8:() -> e20:(e18:r8:"ping::get"->d1:"ping.get" e19:()))))
runtime roots e23:(e16:r6:outer->d3:outer e22:(e17:r7:inner->d2:inner e21:(fn p8:() -> e20:(e18:r8:"ping::get"->d1:"ping.get" e19:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:f arg
  d5:k arg
  d6:value arg
  d7:action arg
  d8:k arg
  d9:value arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/hygiene-callback-filter.yu`

開始: 2026-11-08T11:52:25.642654+00:00、所要 0.012 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/hygiene-callback-filter.yu`

開始: 2026-11-08T11:52:25.655251+00:00、所要 0.005 秒、exit 0。

```text
run roots [7]
```

## hygiene-doc

```yulang
pub act sub 'a:
    pub return: 'a -> never
    pub sub(x: [_] 'a): 'a = catch x:
        return a, _ -> a
        a -> a
our g h = sub::sub:
    h 0
    sub::return 1
sub::sub:
    g \i -> sub::return i
    sub::return 2
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/hygiene-doc.yu`

開始: 2026-11-08T11:52:44.273728+00:00、所要 0.032 秒、exit 0。

```text
roots d0:sub d3:g
pub d0:sub mod {
  pub d2:"sub.sub": 'a [sub('b & 'a); 'c] -> ['c] 'a | 'b = e4:(fn p0:d4:x -> e3:catch e0:r0:x->d4:x { sub::return p1:d5:a, p2:_ -> e1:r1:a->d5:a; p3:d6:a -> e2:r2:a->d6:a })
}
d3:g: (int -> ['a] any) -> ['a] int = e14:(fn p4:d7:h -> e13:(e5:r3:"sub::sub"->d2:"sub.sub" e12:block { e8:(e6:r4:h->d7:h e7:0); e11:(e9:r5:"sub::return"->d1:"sub.return" e10:1) }))
root exprs e26:(e15:r6:"sub::sub"->d2:"sub.sub" e25:block { e21:(e16:r7:g->d3:g e20:(fn p5:d9:i -> e19:(e17:r8:"sub::return"->d1:"sub.return" e18:r9:i->d9:i))); e24:(e22:r10:"sub::return"->d1:"sub.return" e23:2) })
runtime roots e26:(e15:r6:"sub::sub"->d2:"sub.sub" e25:block { e21:(e16:r7:g->d3:g e20:(fn p5:d9:i -> e19:(e17:r8:"sub::return"->d1:"sub.return" e18:r9:i->d9:i))); e24:(e22:r10:"sub::return"->d1:"sub.return" e23:2) })
detached {
  pub d1:"sub.return": 'a -> [sub 'a] never = <missing>
  d4:x arg
  d5:a arg
  d6:a arg
  d7:h arg
  d9:i arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/hygiene-doc.yu`

開始: 2026-11-08T11:52:44.305493+00:00、所要 0.028 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/hygiene-doc.yu`

開始: 2026-11-08T11:52:44.333509+00:00、所要 0.005 秒、exit 0。

```text
run roots [0]
```

## pattern-or-bindings-left

```yulang
case (0, 2):
    (0, x) | (x, 2) -> x
    _ -> 99
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-or-bindings-left.yu`

開始: 2026-11-08T11:40:56.137506+00:00、所要 0.006 秒、exit 0。

```text
roots
root exprs e5:case e2:(e0:0, e1:2) { p6:(p2:(p0:0, p1:d1:x) | p5:(p3:d2:x, p4:2)) -> e3:r0:x->d2:x; p7:_ -> e4:99 }
runtime roots e5:case e2:(e0:0, e1:2) { p6:(p2:(p0:0, p1:d1:x) | p5:(p3:d2:x, p4:2)) -> e3:r0:x->d2:x; p7:_ -> e4:99 }
detached {
  d1:x arg
  d2:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-or-bindings-left.yu`

開始: 2026-11-08T11:40:56.143222+00:00、所要 0.005 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-or-bindings-left.yu`

開始: 2026-11-08T11:40:56.148462+00:00、所要 0.003 秒、exit 1。

```text
runtime error [yulang.runtime-internal]: runtime-evidence-run unbound local d2
  hint: report this with the source program if it came from normal `yulang run`
```

## pattern-or-different-names-left

```yulang
case (0, 2):
    (0, x) | (y, 2) -> y
    _ -> 99
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-or-different-names-left.yu`

開始: 2026-11-08T11:40:56.151531+00:00、所要 0.005 秒、exit 0。

```text
roots
root exprs e5:case e2:(e0:0, e1:2) { p6:(p2:(p0:0, p1:d1:x) | p5:(p3:d2:y, p4:2)) -> e3:r0:y->d2:y; p7:_ -> e4:99 }
runtime roots e5:case e2:(e0:0, e1:2) { p6:(p2:(p0:0, p1:d1:x) | p5:(p3:d2:y, p4:2)) -> e3:r0:y->d2:y; p7:_ -> e4:99 }
detached {
  d1:x arg
  d2:y arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-or-different-names-left.yu`

開始: 2026-11-08T11:40:56.156191+00:00、所要 0.004 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-or-different-names-left.yu`

開始: 2026-11-08T11:40:56.160296+00:00、所要 0.003 秒、exit 1。

```text
runtime error [yulang.runtime-internal]: runtime-evidence-run unbound local d2
  hint: report this with the source program if it came from normal `yulang run`
```

## pattern-alias-precedence-left

```yulang
case 0:
    0 | 1 as matched -> matched
    _ -> 99
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-alias-precedence-left.yu`

開始: 2026-11-08T11:40:56.163408+00:00、所要 0.003 秒、exit 0。

```text
roots
root exprs e3:case e0:0 { p3:(p0:0 | p2:(p1:1 as d1:matched)) -> e1:r0:matched->d1:matched; p4:_ -> e2:99 }
runtime roots e3:case e0:0 { p3:(p0:0 | p2:(p1:1 as d1:matched)) -> e1:r0:matched->d1:matched; p4:_ -> e2:99 }
detached {
  d1:matched arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-alias-precedence-left.yu`

開始: 2026-11-08T11:40:56.166718+00:00、所要 0.003 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-alias-precedence-left.yu`

開始: 2026-11-08T11:40:56.169785+00:00、所要 0.002 秒、exit 1。

```text
runtime error [yulang.runtime-internal]: runtime-evidence-run unbound local d1
  hint: report this with the source program if it came from normal `yulang run`
```

## pipe-position

```yulang
our pair(a)(b) = (a, b)
1 | pair 2
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pipe-position.yu`

開始: 2026-11-08T11:40:31.612255+00:00、所要 0.005 秒、exit 0。

```text
roots d0:pair
d0:pair: 'a -> 'b -> ('a, 'b) = e4:(fn p0:d1:a -> e3:(fn p1:d2:b -> e2:(e0:r0:a->d1:a, e1:r1:b->d2:b)))
root exprs e9:(e7:(e6:r2:pair->d0:pair e5:1) e8:2)
runtime roots e9:(e7:(e6:r2:pair->d0:pair e5:1) e8:2)
detached {
  d1:a arg
  d2:b arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pipe-position.yu`

開始: 2026-11-08T11:40:31.617312+00:00、所要 0.004 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pipe-position.yu`

開始: 2026-11-08T11:40:31.620915+00:00、所要 0.003 秒、exit 0。

```text
run roots [(1, 2)]
```

## pattern-type-ignored

```yulang
case 41:
    value: bool -> value
    _ -> 0
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-type-ignored.yu`

開始: 2026-11-08T11:40:31.624431+00:00、所要 0.003 秒、exit 0。

```text
roots
root exprs e3:case e0:41 { p0:d1:value -> e1:r0:value->d1:value; p1:_ -> e2:0 }
runtime roots e3:case e0:41 { p0:d1:value -> e1:r0:value->d1:value; p1:_ -> e2:0 }
detached {
  d1:value arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-type-ignored.yu`

開始: 2026-11-08T11:40:31.627701+00:00、所要 0.003 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-type-ignored.yu`

開始: 2026-11-08T11:40:31.630506+00:00、所要 0.002 秒、exit 0。

```text
run roots [41]
```

## pattern-or-bindings

```yulang
case (1, 2):
    (0, x) | (x, 2) -> x
    _ -> 99
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-or-bindings.yu`

開始: 2026-11-08T11:40:31.632809+00:00、所要 0.004 秒、exit 0。

```text
roots
root exprs e5:case e2:(e0:1, e1:2) { p6:(p2:(p0:0, p1:d1:x) | p5:(p3:d2:x, p4:2)) -> e3:r0:x->d2:x; p7:_ -> e4:99 }
runtime roots e5:case e2:(e0:1, e1:2) { p6:(p2:(p0:0, p1:d1:x) | p5:(p3:d2:x, p4:2)) -> e3:r0:x->d2:x; p7:_ -> e4:99 }
detached {
  d1:x arg
  d2:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-or-bindings.yu`

開始: 2026-11-08T11:40:31.636953+00:00、所要 0.004 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-or-bindings.yu`

開始: 2026-11-08T11:40:31.641067+00:00、所要 0.003 秒、exit 0。

```text
run roots [1]
```

## pattern-or-different-names

```yulang
case (1, 2):
    (0, x) | (y, 2) -> y
    _ -> 99
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-or-different-names.yu`

開始: 2026-11-08T11:40:31.643697+00:00、所要 0.004 秒、exit 0。

```text
roots
root exprs e5:case e2:(e0:1, e1:2) { p6:(p2:(p0:0, p1:d1:x) | p5:(p3:d2:y, p4:2)) -> e3:r0:y->d2:y; p7:_ -> e4:99 }
runtime roots e5:case e2:(e0:1, e1:2) { p6:(p2:(p0:0, p1:d1:x) | p5:(p3:d2:y, p4:2)) -> e3:r0:y->d2:y; p7:_ -> e4:99 }
detached {
  d1:x arg
  d2:y arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-or-different-names.yu`

開始: 2026-11-08T11:40:31.647937+00:00、所要 0.005 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-or-different-names.yu`

開始: 2026-11-08T11:40:31.652856+00:00、所要 0.003 秒、exit 0。

```text
run roots [1]
```

## pattern-refutable-let

```yulang
my 0 = 1
42
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-refutable-let.yu`

開始: 2026-11-08T11:40:31.655906+00:00、所要 0.003 秒、exit 0。

```text
roots
root exprs e0:42
runtime roots e0:42
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-refutable-let.yu`

開始: 2026-11-08T11:40:31.658742+00:00、所要 0.002 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-refutable-let.yu`

開始: 2026-11-08T11:40:31.660845+00:00、所要 0.002 秒、exit 0。

```text
run roots [42]
```

## pattern-alias-precedence

```yulang
case 1:
    0 | 1 as matched -> matched
    _ -> 99
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-alias-precedence.yu`

開始: 2026-11-08T11:40:31.663293+00:00、所要 0.004 秒、exit 0。

```text
roots
root exprs e3:case e0:1 { p3:(p0:0 | p2:(p1:1 as d1:matched)) -> e1:r0:matched->d1:matched; p4:_ -> e2:99 }
runtime roots e3:case e0:1 { p3:(p0:0 | p2:(p1:1 as d1:matched)) -> e1:r0:matched->d1:matched; p4:_ -> e2:99 }
detached {
  d1:matched arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-alias-precedence.yu`

開始: 2026-11-08T11:40:31.666873+00:00、所要 0.003 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/pattern-alias-precedence.yu`

開始: 2026-11-08T11:40:31.669669+00:00、所要 0.003 秒、exit 0。

```text
run roots [1]
```

## f1-higher-run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our higher(f: [ping] int -> [ping] int) = f(ping::get())
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(higher plain)
```

### check

Command: `./target/release/yulang --std-root lib check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher-run.yu`

開始: 2026-11-08T11:39:43.668803+00:00、所要 152.603 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher-run.yu`

開始: 2026-11-08T11:42:16.271770+00:00、所要 157.347 秒、exit 1。

```text
conflicting type candidates: [ping] vs []
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher-run.yu`

開始: 2026-11-08T11:32:55.215762+00:00、所要 0.037 秒、exit 0。

```text
roots d0:ping d2:plain d3:higher d4:handle
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:higher: (int -> [ping] int) -> int = e7:(fn p1:d6:f -> e6:(e2:r1:f->d6:f e5:(e3:r2:"ping::get"->d1:"ping.get" e4:())))
d4:handle: int ['a & [ping; 'a]] -> ['a] int = e14:(fn p2:d7:action -> e13:catch e8:r3:action->d7:action { ping::get p3:_, p4:d8:k -> e11:(e9:r4:k->d8:k e10:7); p5:d9:v -> e12:r5:v->d9:v })
root exprs e19:(e15:r6:handle->d4:handle e18:(e16:r7:higher->d3:higher e17:r8:plain->d2:plain))
runtime roots e19:(e15:r6:handle->d4:handle e18:(e16:r7:higher->d3:higher e17:r8:plain->d2:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:f arg
  d7:action arg
  d8:k arg
  d9:v arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher-run.yu`

開始: 2026-11-08T11:32:55.252858+00:00、所要 0.032 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher-run.yu`

開始: 2026-11-08T11:32:55.284559+00:00、所要 0.039 秒、exit 1。

```text
conflicting type candidates: [ping] vs []
```

## f1-pipe-run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(ping::get() | plain)
```

### check

Command: `./target/release/yulang --std-root lib check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-pipe-run.yu`

開始: 2026-11-08T11:44:53.618665+00:00、所要 154.847 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-pipe-run.yu`

開始: 2026-11-08T11:47:28.466107+00:00、所要 0.208 秒、exit 0。

```text
run roots [7]
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-pipe-run.yu`

開始: 2026-11-08T11:32:55.129804+00:00、所要 0.04 秒、exit 0。

```text
roots d0:ping d2:plain d3:handle
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d4:x -> e0:r0:x->d4:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d5:action -> e7:catch e2:r1:action->d5:action { ping::get p2:_, p3:d6:k -> e5:(e3:r2:k->d6:k e4:7); p4:d7:v -> e6:r3:v->d7:v })
root exprs e15:(e9:r4:handle->d3:handle e14:(e13:r6:plain->d2:plain e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
runtime roots e15:(e9:r4:handle->d3:handle e14:(e13:r6:plain->d2:plain e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:x arg
  d5:action arg
  d6:k arg
  d7:v arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-pipe-run.yu`

開始: 2026-11-08T11:32:55.169671+00:00、所要 0.035 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-pipe-run.yu`

開始: 2026-11-08T11:32:55.204549+00:00、所要 0.011 秒、exit 0。

```text
run roots [7]
```

## f1-higher-inferred-run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our higher(f) = f(ping::get())
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(higher plain)
```

### check

Command: `./target/release/yulang --std-root lib check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher-inferred-run.yu`

開始: 2026-11-08T11:47:28.674294+00:00、所要 178.002 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher-inferred-run.yu`

開始: 2026-11-08T11:50:26.676586+00:00、所要 0.248 秒、exit 0。

```text
run roots [7]
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher-inferred-run.yu`

開始: 2026-11-08T11:32:55.323299+00:00、所要 0.046 秒、exit 0。

```text
roots d0:ping d2:plain d3:higher d4:handle
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:higher: (int [ping] -> ['a] 'b) -> ['a] 'b = e7:(fn p1:d6:f -> e6:(e2:r1:f->d6:f e5:(e3:r2:"ping::get"->d1:"ping.get" e4:())))
d4:handle: int ['a & [ping; 'a]] -> ['a] int = e14:(fn p2:d7:action -> e13:catch e8:r3:action->d7:action { ping::get p3:_, p4:d8:k -> e11:(e9:r4:k->d8:k e10:7); p5:d9:v -> e12:r5:v->d9:v })
root exprs e19:(e15:r6:handle->d4:handle e18:(e16:r7:higher->d3:higher e17:r8:plain->d2:plain))
runtime roots e19:(e15:r6:handle->d4:handle e18:(e16:r7:higher->d3:higher e17:r8:plain->d2:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:f arg
  d7:action arg
  d8:k arg
  d9:v arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher-inferred-run.yu`

開始: 2026-11-08T11:32:55.369806+00:00、所要 0.032 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher-inferred-run.yu`

開始: 2026-11-08T11:32:55.401808+00:00、所要 0.024 秒、exit 0。

```text
run roots [7]
```

## cast-branch-if-run

```yulang
struct user_id { raw: int }
cast(x: user_id): int = x.raw
our mixed(flag) = if flag: 1 else: user_id { raw: 2 }
(mixed true, mixed false)
```

### dump

Command: `./target/release/yulang --std-root lib dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-branch-if-run.yu`

開始: 2026-11-08T11:54:16.351697+00:00、所要 0.135 秒、exit 0。

```text
roots d0:std d2285:user_id d2289:mixed
d0:std mod {
}
d2285:user_id: {raw: int} -> user_id = <missing>
d2289:mixed: bool -> int | user_id = e8406:(fn p1938:d2291:flag -> e8405:case e8399:(e8398:r3454:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e8397:r3453:flag->d2291:flag) { p1939:true -> e8400:1; p1940:false -> e8404:(e8401:r3455:user_id->d2285:user_id e8403:{raw: e8402:2}) })
root exprs e8413:(e8409:(e8407:r3456:mixed->d2289:mixed e8408:true), e8412:(e8410:r3457:mixed->d2289:mixed e8411:false))
runtime roots d179:"std.control.flow.label_sub.control_label" d209:"std.control.flow.label_loop.control_label" e8413:(e8409:(e8407:r3456:mixed->d2289:mixed e8408:true), e8412:(e8410:r3457:mixed->d2289:mixed e8411:false))
detached {
  pub d1:"std.core" mod {
    pub d21:"std.core.cmp" mod {
      pub d247:"std.core.cmp.Eq" mod {
        pub d248:"std.core.cmp.Eq.eq": 'a -> 'a -> bool where 'a: std::core::cmp::Eq = <missing>
      }
      pub d249:"std.core.cmp.Ord" mod {
        pub d250:"std.core.cmp.Ord.lt": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = <missing>
        pub d251:"std.core.cmp.Ord.le": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = <missing>
        pub d252:"std.core.cmp.Ord.gt": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = <missing>
        pub d253:"std.core.cmp.Ord.ge": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = <missing>
      }
      my d254 mod {
        d255: int -> int -> bool = e1441:(fn p333:d1209:x -> e1440:(fn p334:d1210:y -> e1439:(e1437:(e1435:r520:"std::int::eq"->d45:"std.int.eq" e1436:r521:x->d1209:x) e1438:r522:y->d1210:y)))
      }
      my d256 mod {
        d257: int -> int -> bool = e1448:(fn p335:d1211:x -> e1447:(fn p336:d1212:y -> e1446:(e1444:(e1442:r523:"std::int::lt"->d46:"std.int.lt" e1443:r524:x->d1211:x) e1445:r525:y->d1212:y)))
        d258: int -> int -> bool = e1455:(fn p337:d1213:x -> e1454:(fn p338:d1214:y -> e1453:(e1451:(e1449:r526:"std::int::le"->d47:"std.int.le" e1450:r527:x->d1213:x) e1452:r528:y->d1214:y)))
        d259: int -> int -> bool = e1462:(fn p339:d1215:x -> e1461:(fn p340:d1216:y -> e1460:(e1458:(e1456:r529:"std::int::gt"->d48:"std.int.gt" e1457:r530:x->d1215:x) e1459:r531:y->d1216:y)))
        d260: int -> int -> bool = e1469:(fn p341:d1217:x -> e1468:(fn p342:d1218:y -> e1467:(e1465:(e1463:r532:"std::int::ge"->d49:"std.int.ge" e1464:r533:x->d1217:x) e1466:r534:y->d1218:y)))
      }
      my d261 mod {
        d262: float -> float -> bool = e1476:(fn p343:d1219:x -> e1475:(fn p344:d1220:y -> e1474:(e1472:(e1470:r535:"std::float::eq"->d34:"std.float.eq" e1471:r536:x->d1219:x) e1473:r537:y->d1220:y)))
      }
      my d263 mod {
        d264: float -> float -> bool = e1483:(fn p345:d1221:x -> e1482:(fn p346:d1222:y -> e1481:(e1479:(e1477:r538:"std::float::lt"->d35:"std.float.lt" e1478:r539:x->d1221:x) e1480:r540:y->d1222:y)))
        d265: float -> float -> bool = e1490:(fn p347:d1223:x -> e1489:(fn p348:d1224:y -> e1488:(e1486:(e1484:r541:"std::float::le"->d36:"std.float.le" e1485:r542:x->d1223:x) e1487:r543:y->d1224:y)))
        d266: float -> float -> bool = e1497:(fn p349:d1225:x -> e1496:(fn p350:d1226:y -> e1495:(e1493:(e1491:r544:"std::float::gt"->d37:"std.float.gt" e1492:r545:x->d1225:x) e1494:r546:y->d1226:y)))
        d267: float -> float -> bool = e1504:(fn p351:d1227:x -> e1503:(fn p352:d1228:y -> e1502:(e1500:(e1498:r547:"std::float::ge"->d38:"std.float.ge" e1499:r548:x->d1227:x) e1501:r549:y->d1228:y)))
      }
      my d268 mod {
        d269: std::num::frac::frac -> std::num::frac::frac -> bool = e1511:(fn p353:d1229:x -> e1510:(fn p354:d1230:y -> e1509:(e1507:(e1505:r550:"std::num::frac::eq"->d646:"std.num.frac.eq" e1506:r551:x->d1229:x) e1508:r552:y->d1230:y)))
      }
      my d270 mod {
        d271: std::num::frac::frac -> std::num::frac::frac -> bool = e1518:(fn p355:d1231:x -> e1517:(fn p356:d1232:y -> e1516:(e1514:(e1512:r553:"std::num::frac::lt"->d647:"std.num.frac.lt" e1513:r554:x->d1231:x) e1515:r555:y->d1232:y)))
        d272: std::num::frac::frac -> std::num::frac::frac -> bool = e1525:(fn p357:d1233:x -> e1524:(fn p358:d1234:y -> e1523:(e1521:(e1519:r556:"std::num::frac::le"->d648:"std.num.frac.le" e1520:r557:x->d1233:x) e1522:r558:y->d1234:y)))
        d273: std::num::frac::frac -> std::num::frac::frac -> bool = e1532:(fn p359:d1235:x -> e1531:(fn p360:d1236:y -> e1530:(e1528:(e1526:r559:"std::num::frac::gt"->d649:"std.num.frac.gt" e1527:r560:x->d1235:x) e1529:r561:y->d1236:y)))
        d274: std::num::frac::frac -> std::num::frac::frac -> bool = e1539:(fn p361:d1237:x -> e1538:(fn p362:d1238:y -> e1537:(e1535:(e1533:r562:"std::num::frac::ge"->d650:"std.num.frac.ge" e1534:r563:x->d1237:x) e1536:r564:y->d1238:y)))
      }
      my d275 mod {
        d276: bool -> bool -> bool = e1546:(fn p363:d1239:x -> e1545:(fn p364:d1240:y -> e1544:(e1542:(e1540:r565:"std::bool::eq"->d13:"std.bool.eq" e1541:r566:x->d1239:x) e1543:r567:y->d1240:y)))
      }
      my d277 mod {
        d278: std::text::str::str -> std::text::str::str -> bool = e1553:(fn p365:d1241:x -> e1552:(fn p366:d1242:y -> e1551:(e1549:(e1547:r568:"std::text::str::eq"->d785:"std.text.str.eq" e1548:r569:x->d1241:x) e1550:r570:y->d1242:y)))
      }
      my d279 mod {
        d280: std::text::char::char -> std::text::char::char -> bool = e1560:(fn p367:d1243:x -> e1559:(fn p368:d1244:y -> e1558:(e1556:(e1554:r571:"std::text::char::eq"->d671:"std.text.char.eq" e1555:r572:x->d1243:x) e1557:r573:y->d1244:y)))
      }
      my d281 mod {
        d282: std::data::list::list int -> std::data::list::list int -> bool = e1589:(fn p369:d1245:xs -> e1588:(fn p370:d1246:ys -> e1587:case e1567:(e1563:(e1561:r574:"std::data::list::view_raw"->d477:"std.data.list.view_raw" e1562:r575:xs->d1245:xs), e1566:(e1564:r576:"std::data::list::view_raw"->d477:"std.data.list.view_raw" e1565:r577:ys->d1246:ys)) { p373:(p371:r578:"std::data::list::list_view::empty"->d456:"std.data.list.list_view.empty", p372:r579:"std::data::list::list_view::empty"->d456:"std.data.list.list_view.empty") -> e1568:true; p378:(p375:r580:"std::data::list::list_view::leaf"->d457:"std.data.list.list_view.leaf"(p374:d1247:x), p377:r581:"std::data::list::list_view::leaf"->d457:"std.data.list.list_view.leaf"(p376:d1248:y)) -> e1573:(e1571:(e1569:r582:"std::int::eq"->d45:"std.int.eq" e1570:r583:x->d1247:x) e1572:r584:y->d1248:y); p385:(p381:r585:"std::data::list::list_view::node"->d458:"std.data.list.list_view.node"(p379:d1249:xl, p380:d1250:xr), p384:r586:"std::data::list::list_view::node"->d458:"std.data.list.list_view.node"(p382:d1251:yl, p383:d1252:yr)) -> e1585:case e1579:(e1578:r589:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1577:(e1575:(e1574:r587:xl->d1249:xl.s44.eq=>d248:"std.core.cmp.Eq.eq") e1576:r588:yl->d1251:yl)) { p386:true -> e1583:(e1581:(e1580:r590:xr->d1250:xr.s45.eq=>d248:"std.core.cmp.Eq.eq") e1582:r591:yr->d1252:yr); p387:false -> e1584:false }; p388:_ -> e1586:false }))
      }
    }
    pub d22:"std.core.convert" mod {
      pub d283:"std.core.convert.Cast" mod {
        pub d284:"std.core.convert.Cast.cast": 'a -> 'b where 'a: std::core::convert::Cast(to = 'b) = <missing>
      }
    }
    pub d23:"std.core.fmt" mod {
      pub d289:"std.core.fmt.format_kind" mod {
        pub d290:"std.core.fmt.format_kind.display": std::core::fmt::format_kind = <missing>
        pub d291:"std.core.fmt.format_kind.debug": std::core::fmt::format_kind = <missing>
        pub d292:"std.core.fmt.format_kind.lower_hex": std::core::fmt::format_kind = <missing>
        pub d293:"std.core.fmt.format_kind.upper_hex": std::core::fmt::format_kind = <missing>
      }
      pub d294:"std.core.fmt.format_align" mod {
        pub d295:"std.core.fmt.format_align.left": std::core::fmt::format_align = <missing>
        pub d296:"std.core.fmt.format_align.right": std::core::fmt::format_align = <missing>
        pub d297:"std.core.fmt.format_align.center": std::core::fmt::format_align = <missing>
      }
      pub d298:"std.core.fmt.format_sign" mod {
        pub d299:"std.core.fmt.format_sign.plus": std::core::fmt::format_sign = <missing>
        pub d300:"std.core.fmt.format_sign.minus": std::core::fmt::format_sign = <missing>
      }
      pub d301:"std.core.fmt.format_spec": {kind: std::core::fmt::format_kind, align: std::data::opt::opt std::core::fmt::format_align, sign: std::data::opt::opt std::core::fmt::format_sign, fill: std::data::opt::opt std::text::str::str, width: std::data::opt::opt int, precision: std::data::opt::opt int, alternate: bool, zero_pad: bool} -> std::core::fmt::format_spec = <missing>
      pub d318:"std.core.fmt.Display" mod {
        pub d319:"std.core.fmt.Display.show": 'a -> std::text::str::str where 'a: std::core::fmt::Display = <missing>
        pub d320:"std.core.fmt.Display.say": 'a -> [std::io::console::out] () where 'a: std::core::fmt::Display = e1616:(fn p393:d1257:a -> e1615:(e1608:r599:"std::io::out::write"->d538:"std.io.console.out.write" e1614:(e1613:(e1611:r601:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1610:(e1609:r600:a->d1257:a.s46.show=>d319:"std.core.fmt.Display.show")) e1612:"\n")))
        pub d321:"std.core.fmt.Display.note": 'a -> [std::io::console::err] () where 'a: std::core::fmt::Display = e1625:(fn p394:d1258:a -> e1624:(e1617:r602:"std::io::err::write"->d543:"std.io.console.err.write" e1623:(e1622:(e1620:r604:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1619:(e1618:r603:a->d1258:a.s47.show=>d319:"std.core.fmt.Display.show")) e1621:"\n")))
      }
      pub d322:"std.core.fmt.Debug" mod {
        pub d323:"std.core.fmt.Debug.debug": 'a -> std::text::str::str where 'a: std::core::fmt::Debug = <missing>
        pub d324:"std.core.fmt.Debug.dd": 'a -> [std::io::console::err] () where 'a: std::core::fmt::Debug = e1634:(fn p395:d1259:a -> e1633:(e1626:r605:"std::io::err::write"->d543:"std.io.console.err.write" e1632:(e1631:(e1629:r607:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1628:(e1627:r606:a->d1259:a.s48.debug=>d323:"std.core.fmt.Debug.debug")) e1630:"\n")))
      }
      my d325:"std.core.fmt.repeat": std::text::str::str -> int -> std::text::str::str = e1658:(fn p396:d1260:text -> e1657:(fn p397:d1261:count -> e1656:case e1641:(e1640:r610:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1639:(e1638:(e1636:r609:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e1635:r608:count->d1261:count) e1637:0)) { p398:true -> e1642:""; p399:false -> e1655:(e1654:(e1644:r612:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1643:r611:text->d1260:text) e1653:(e1647:(e1645:r613:repeat->d325:"std.core.fmt.repeat" e1646:r614:text->d1260:text) e1652:(e1651:(e1649:r616:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e1648:r615:count->d1261:count) e1650:1))) }))
      my d326:"std.core.fmt.format_fill": std::core::fmt::format_spec -> std::text::str::str = e1670:(fn p400:d1262:spec -> e1669:case e1660:(e1659:r617:spec->d1262:spec.s49.fill->d308) { p402:r618:"opt::just"->d504:"std.data.opt.opt.just"(p401:d1263:fill) -> e1661:r619:fill->d1263:fill; p403:r620:"opt::nil"->d503:"std.data.opt.opt.nil" -> e1668:case e1665:(e1664:r622:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1663:(e1662:r621:spec->d1262:spec.s50.zero_pad->d316)) { p404:true -> e1666:"0"; p405:false -> e1667:" " } })
      my d327:"std.core.fmt.format_body": std::core::fmt::format_spec -> std::text::str::str -> std::text::str::str = e1693:(fn p406:d1264:spec -> e1692:(fn p407:d1265:body -> e1691:case e1672:(e1671:r623:spec->d1264:spec.s51.precision->d312) { p409:r624:"opt::just"->d504:"std.data.opt.opt.just"(p408:d1266:limit) -> e1689:case e1680:(e1679:r628:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1678:(e1677:(e1675:r626:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e1674:(e1673:r625:body->d1265:body.s52.len->d838:"std.text.str.str.len")) e1676:r627:limit->d1266:limit)) { p410:true -> e1681:r629:body->d1265:body; p411:false -> e1688:(e1686:(e1684:(e1682:r630:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e1683:r631:body->d1265:body) e1685:0) e1687:r632:limit->d1266:limit) }; p412:r633:"opt::nil"->d503:"std.data.opt.opt.nil" -> e1690:r634:body->d1265:body }))
      my d328:"std.core.fmt.starts_with_minus": std::text::str::str -> bool = e1715:(fn p413:d1267:body -> e1714:case e1701:(e1700:r637:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1699:(e1698:(e1696:r636:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e1695:(e1694:r635:body->d1267:body.s53.len->d838:"std.text.str.str.len")) e1697:0)) { p414:true -> e1702:false; p415:false -> e1713:(e1712:(e1710:r640:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e1709:(e1707:(e1705:(e1703:r638:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e1704:r639:body->d1267:body) e1706:0) e1708:1)) e1711:"-") })
      my d329:"std.core.fmt.format_sign_prefix": std::core::fmt::format_spec -> std::text::str::str -> std::text::str::str -> std::text::str::str = e1735:(fn p416:d1268:spec -> e1734:(fn p417:d1269:head -> e1733:(fn p418:d1270:body -> e1732:case e1717:(e1716:r641:spec->d1268:spec.s54.sign->d306) { p420:r642:"opt::just"->d504:"std.data.opt.opt.just"(p419:r643:"format_sign::plus"->d299:"std.core.fmt.format_sign.plus") -> e1729:case e1722:(e1721:r646:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1720:(e1718:r644:starts_with_minus->d328:"std.core.fmt.starts_with_minus" e1719:r645:body->d1270:body)) { p421:true -> e1723:r647:head->d1269:head; p422:false -> e1728:(e1727:(e1725:r648:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1724:"+") e1726:r649:head->d1269:head) }; p424:r650:"opt::just"->d504:"std.data.opt.opt.just"(p423:r651:"format_sign::minus"->d300:"std.core.fmt.format_sign.minus") -> e1730:r652:head->d1269:head; p425:r653:"opt::nil"->d503:"std.data.opt.opt.nil" -> e1731:r654:head->d1269:head })))
      my d330:"std.core.fmt.format_with_padding": std::core::fmt::format_spec -> std::text::str::str -> std::text::str::str -> std::text::str::str = e1872:(fn p426:d1271:spec -> e1871:(fn p427:d1272:head -> e1870:(fn p428:d1273:body -> e1869:case e1737:(e1736:r655:spec->d1271:spec.s55.width->d310) { p429:r656:"opt::nil"->d503:"std.data.opt.opt.nil" -> e1756:block { let my p430:d1274:clipped = e1742:(e1740:(e1738:r657:format_body->d327:"std.core.fmt.format_body" e1739:r658:spec->d1271:spec) e1741:r659:body->d1273:body); e1755:block { let my p431:d1275:body_prefix = e1749:(e1747:(e1745:(e1743:r660:format_sign_prefix->d329:"std.core.fmt.format_sign_prefix" e1744:r661:spec->d1271:spec) e1746:r662:head->d1272:head) e1748:r663:clipped->d1274:clipped); e1754:(e1753:(e1751:r665:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1750:r664:body_prefix->d1275:body_prefix) e1752:r666:clipped->d1274:clipped) } }; p433:r667:"opt::just"->d504:"std.data.opt.opt.just"(p432:d1276:width) -> e1868:block { let my p434:d1277:clipped = e1761:(e1759:(e1757:r668:format_body->d327:"std.core.fmt.format_body" e1758:r669:spec->d1271:spec) e1760:r670:body->d1273:body); e1867:block { let my p435:d1278:body_prefix = e1768:(e1766:(e1764:(e1762:r671:format_sign_prefix->d329:"std.core.fmt.format_sign_prefix" e1763:r672:spec->d1271:spec) e1765:r673:head->d1272:head) e1767:r674:clipped->d1277:clipped); e1866:block { let my p436:d1279:text = e1773:(e1772:(e1770:r676:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1769:r675:body_prefix->d1278:body_prefix) e1771:r677:clipped->d1277:clipped); e1865:block { let my p437:d1280:missing = e1779:(e1778:(e1775:r679:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e1774:r678:width->d1276:width) e1777:(e1776:r680:text->d1279:text.s56.len->d838:"std.text.str.str.len")); e1864:case e1786:(e1785:r683:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1784:(e1783:(e1781:r682:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e1780:r681:missing->d1280:missing) e1782:0)) { p450:true -> e1787:r684:text->d1279:text; p451:false -> e1863:block { let my p438:d1281:fill = e1790:(e1788:r685:format_fill->d326:"std.core.fmt.format_fill" e1789:r686:spec->d1271:spec); e1862:case e1792:(e1791:r687:spec->d1271:spec.s57.align->d304) { p440:r688:"opt::just"->d504:"std.data.opt.opt.just"(p439:r689:"format_align::left"->d295:"std.core.fmt.format_align.left") -> e1801:(e1800:(e1794:r691:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1793:r690:text->d1279:text) e1799:(e1797:(e1795:r692:repeat->d325:"std.core.fmt.repeat" e1796:r693:fill->d1281:fill) e1798:r694:missing->d1280:missing)); p442:r695:"opt::just"->d504:"std.data.opt.opt.just"(p441:r696:"format_align::center"->d297:"std.core.fmt.format_align.center") -> e1830:block { let my p443:d1282:left = e1806:(e1805:(e1803:r698:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e1802:r697:missing->d1280:missing) e1804:2); e1829:block { let my p444:d1283:right = e1811:(e1810:(e1808:r700:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e1807:r699:missing->d1280:missing) e1809:r701:left->d1282:left); e1828:(e1827:(e1821:r707:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1820:(e1819:(e1817:r705:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1816:(e1814:(e1812:r702:repeat->d325:"std.core.fmt.repeat" e1813:r703:fill->d1281:fill) e1815:r704:left->d1282:left)) e1818:r706:text->d1279:text)) e1826:(e1824:(e1822:r708:repeat->d325:"std.core.fmt.repeat" e1823:r709:fill->d1281:fill) e1825:r710:right->d1283:right)) } }; p445:_ -> e1861:case e1834:(e1833:r712:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1832:(e1831:r711:spec->d1271:spec.s58.zero_pad->d316)) { p448:true -> e1851:block { let my p446:d1284:padding = e1839:(e1837:(e1835:r713:repeat->d325:"std.core.fmt.repeat" e1836:r714:fill->d1281:fill) e1838:r715:missing->d1280:missing); e1850:block { let my p447:d1285:padded_prefix = e1844:(e1843:(e1841:r717:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1840:r716:body_prefix->d1278:body_prefix) e1842:r718:padding->d1284:padding); e1849:(e1848:(e1846:r720:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1845:r719:padded_prefix->d1285:padded_prefix) e1847:r721:clipped->d1277:clipped) } }; p449:false -> e1860:(e1859:(e1857:r725:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1856:(e1854:(e1852:r722:repeat->d325:"std.core.fmt.repeat" e1853:r723:fill->d1281:fill) e1855:r724:missing->d1280:missing)) e1858:r726:text->d1279:text) } } } } } } } } })))
      pub d331:"std.core.fmt.format_display": std::core::fmt::format_spec -> 'a -> std::text::str::str where 'a: std::core::fmt::Display = e1882:(fn p452:d1286:spec -> e1881:(fn p453:d1287:value -> e1880:(e1877:(e1875:(e1873:r727:format_with_padding->d330:"std.core.fmt.format_with_padding" e1874:r728:spec->d1286:spec) e1876:"") e1879:(e1878:r729:value->d1287:value.s59.show=>d319:"std.core.fmt.Display.show"))))
      pub d332:"std.core.fmt.format_debug": std::core::fmt::format_spec -> 'a -> std::text::str::str where 'a: std::core::fmt::Debug = e1892:(fn p454:d1288:spec -> e1891:(fn p455:d1289:value -> e1890:(e1887:(e1885:(e1883:r730:format_with_padding->d330:"std.core.fmt.format_with_padding" e1884:r731:spec->d1288:spec) e1886:"") e1889:(e1888:r732:value->d1289:value.s60.debug=>d323:"std.core.fmt.Debug.debug"))))
      pub d333:"std.core.fmt.format_lower_hex": std::core::fmt::format_spec -> 'a -> std::text::str::str where 'a: std::num::LowerHex = e1910:(fn p456:d1290:spec -> e1909:(fn p457:d1291:value -> e1908:block { let my p458:d1292:head = e1899:case e1896:(e1895:r734:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1894:(e1893:r733:spec->d1290:spec.s61.alternate->d314)) { p459:true -> e1897:"0x"; p460:false -> e1898:"" }; e1907:(e1904:(e1902:(e1900:r735:format_with_padding->d330:"std.core.fmt.format_with_padding" e1901:r736:spec->d1290:spec) e1903:r737:head->d1292:head) e1906:(e1905:r738:value->d1291:value.s62.lower_hex=>d70:"std.num.LowerHex.lower_hex")) }))
      pub d334:"std.core.fmt.format_upper_hex": std::core::fmt::format_spec -> 'a -> std::text::str::str where 'a: std::num::UpperHex = e1928:(fn p461:d1293:spec -> e1927:(fn p462:d1294:value -> e1926:block { let my p463:d1295:head = e1917:case e1914:(e1913:r740:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1912:(e1911:r739:spec->d1293:spec.s63.alternate->d314)) { p464:true -> e1915:"0X"; p465:false -> e1916:"" }; e1925:(e1922:(e1920:(e1918:r741:format_with_padding->d330:"std.core.fmt.format_with_padding" e1919:r742:spec->d1293:spec) e1921:r743:head->d1295:head) e1924:(e1923:r744:value->d1294:value.s64.upper_hex=>d72:"std.num.UpperHex.upper_hex")) }))
      my d335 mod {
        d336: int -> std::text::str::str = e1932:(fn p466:d1296:x -> e1931:(e1929:r745:"std::int::to_string"->d54:"std.int.to_string" e1930:r746:x->d1296:x))
      }
      my d337 mod {
        d338: int -> std::text::str::str = e1935:(fn p467:d1297:x -> e1934:(e1933:r747:x->d1297:x.s65.show=>d319:"std.core.fmt.Display.show"))
      }
      my d339 mod {
        d340: float -> std::text::str::str = e1939:(fn p468:d1298:x -> e1938:(e1936:r748:"std::float::to_string"->d43:"std.float.to_string" e1937:r749:x->d1298:x))
      }
      my d341 mod {
        d342: float -> std::text::str::str = e1942:(fn p469:d1299:x -> e1941:(e1940:r750:x->d1299:x.s66.show=>d319:"std.core.fmt.Display.show"))
      }
      my d343 mod {
        d344: std::num::frac::frac -> std::text::str::str = e1946:(fn p470:d1300:x -> e1945:(e1943:r751:"std::num::frac::to_string"->d652:"std.num.frac.to_string" e1944:r752:x->d1300:x))
      }
      my d345 mod {
        d346: std::num::frac::frac -> std::text::str::str = e1949:(fn p471:d1301:x -> e1948:(e1947:r753:x->d1301:x.s67.show=>d319:"std.core.fmt.Display.show"))
      }
      my d347 mod {
        d348: bool -> std::text::str::str = e1953:(fn p472:d1302:x -> e1952:(e1950:r754:"std::bool::to_string"->d15:"std.bool.to_string" e1951:r755:x->d1302:x))
      }
      my d349 mod {
        d350: bool -> std::text::str::str = e1956:(fn p473:d1303:x -> e1955:(e1954:r756:x->d1303:x.s68.show=>d319:"std.core.fmt.Display.show"))
      }
      my d351 mod {
        d352: std::text::str::str -> std::text::str::str = e1958:(fn p474:d1304:x -> e1957:r757:x->d1304:x)
      }
      my d353 mod {
        d354: std::text::char::char -> std::text::str::str = e1962:(fn p475:d1305:x -> e1961:(e1959:r758:"std::text::char::to_string"->d672:"std.text.char.to_string" e1960:r759:x->d1305:x))
      }
      my d355 mod {
        d356: () -> std::text::str::str = e1964:(fn p476:d1306:x -> e1963:"()")
      }
      my d357:"std.core.fmt.show_list_items": std::data::list::list 'a -> std::text::str::str where 'a: std::core::fmt::Display = e1989:(fn p477:d1307:xs -> e1988:case e1967:(e1965:r760:"std::data::list::view_raw"->d477:"std.data.list.view_raw" e1966:r761:xs->d1307:xs) { p478:r762:"std::data::list::list_view::empty"->d456:"std.data.list.list_view.empty" -> e1968:""; p480:r763:"std::data::list::list_view::leaf"->d457:"std.data.list.list_view.leaf"(p479:d1308:item) -> e1970:(e1969:r764:item->d1308:item.s69.show=>d319:"std.core.fmt.Display.show"); p483:r765:"std::data::list::list_view::node"->d458:"std.data.list.list_view.node"(p481:d1309:left, p482:d1310:right) -> e1987:block { let my p484:d1311:left_text = e1973:(e1971:r766:show_list_items->d357:"std.core.fmt.show_list_items" e1972:r767:left->d1309:left); e1986:block { let my p485:d1312:right_text = e1976:(e1974:r768:show_list_items->d357:"std.core.fmt.show_list_items" e1975:r769:right->d1310:right); e1985:(e1984:(e1982:r772:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1981:(e1980:(e1978:r771:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1977:r770:left_text->d1311:left_text) e1979:", ")) e1983:r773:right_text->d1312:right_text) } } })
      my d358 mod {
        d359: std::data::list::list 'a -> std::text::str::str where 'a: std::core::fmt::Display = e2001:(fn p486:d1313:xs -> e2000:(e1999:(e1997:r777:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1996:(e1995:(e1991:r774:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1990:"[") e1994:(e1992:r775:show_list_items->d357:"std.core.fmt.show_list_items" e1993:r776:xs->d1313:xs))) e1998:"]"))
      }
      my d360 mod {
        d361: std::data::opt::opt 'a -> std::text::str::str where 'a: std::core::fmt::Display = e2011:(fn p487:d1314:value -> e2010:case e2002:r778:value->d1314:value { p488:r779:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil" -> e2003:"nil"; p490:r780:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just"(p489:d1315:inner) -> e2009:(e2008:(e2005:r781:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2004:"just ") e2007:(e2006:r782:inner->d1315:inner.s70.show=>d319:"std.core.fmt.Display.show")) })
      }
      my d362 mod {
        d363: std::data::result::result 'a 'b -> std::text::str::str where 'a: std::core::fmt::Display, 'b: std::core::fmt::Display = e2026:(fn p491:d1316:value -> e2025:case e2012:r783:value->d1316:value { p493:r784:"std::data::result::result::ok"->d529:"std.data.result.result.ok"(p492:d1317:inner) -> e2018:(e2017:(e2014:r785:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2013:"ok ") e2016:(e2015:r786:inner->d1317:inner.s71.show=>d319:"std.core.fmt.Display.show")); p495:r787:"std::data::result::result::err"->d530:"std.data.result.result.err"(p494:d1318:inner) -> e2024:(e2023:(e2020:r788:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2019:"err ") e2022:(e2021:r789:inner->d1318:inner.s72.show=>d319:"std.core.fmt.Display.show")) })
      }
      my d364 mod {
        d365: ('a, 'b) -> std::text::str::str where 'a: std::core::fmt::Display, 'b: std::core::fmt::Display = e2048:(fn p496:d1319:value -> e2047:case e2027:r790:value->d1319:value { p499:(p497:d1320:a, p498:d1321:b) -> e2046:(e2045:(e2043:r796:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2042:(e2041:(e2038:r794:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2037:(e2036:(e2034:r793:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2033:(e2032:(e2029:r791:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2028:"(") e2031:(e2030:r792:a->d1320:a.s73.show=>d319:"std.core.fmt.Display.show"))) e2035:", ")) e2040:(e2039:r795:b->d1321:b.s74.show=>d319:"std.core.fmt.Display.show"))) e2044:")") })
      }
      my d366 mod {
        d367: ('a, 'b, 'c) -> std::text::str::str where 'a: std::core::fmt::Display, 'b: std::core::fmt::Display, 'c: std::core::fmt::Display = e2079:(fn p500:d1322:value -> e2078:case e2049:r797:value->d1322:value { p504:(p501:d1323:a, p502:d1324:b, p503:d1325:c) -> e2077:(e2076:(e2074:r806:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2073:(e2072:(e2069:r804:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2068:(e2067:(e2065:r803:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2064:(e2063:(e2060:r801:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2059:(e2058:(e2056:r800:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2055:(e2054:(e2051:r798:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2050:"(") e2053:(e2052:r799:a->d1323:a.s75.show=>d319:"std.core.fmt.Display.show"))) e2057:", ")) e2062:(e2061:r802:b->d1324:b.s76.show=>d319:"std.core.fmt.Display.show"))) e2066:", ")) e2071:(e2070:r805:c->d1325:c.s77.show=>d319:"std.core.fmt.Display.show"))) e2075:")") })
      }
      my d368 mod {
        d369: ('a, 'b, 'c, 'd) -> std::text::str::str where 'a: std::core::fmt::Display, 'b: std::core::fmt::Display, 'c: std::core::fmt::Display, 'd: std::core::fmt::Display = e2119:(fn p505:d1326:value -> e2118:case e2080:r807:value->d1326:value { p510:(p506:d1327:a, p507:d1328:b, p508:d1329:c, p509:d1330:d) -> e2117:(e2116:(e2114:r819:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2113:(e2112:(e2109:r817:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2108:(e2107:(e2105:r816:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2104:(e2103:(e2100:r814:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2099:(e2098:(e2096:r813:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2095:(e2094:(e2091:r811:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2090:(e2089:(e2087:r810:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2086:(e2085:(e2082:r808:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2081:"(") e2084:(e2083:r809:a->d1327:a.s78.show=>d319:"std.core.fmt.Display.show"))) e2088:", ")) e2093:(e2092:r812:b->d1328:b.s79.show=>d319:"std.core.fmt.Display.show"))) e2097:", ")) e2102:(e2101:r815:c->d1329:c.s80.show=>d319:"std.core.fmt.Display.show"))) e2106:", ")) e2111:(e2110:r818:d->d1330:d.s81.show=>d319:"std.core.fmt.Display.show"))) e2115:")") })
      }
      my d370 mod {
        d371: ('a, 'b, 'c, 'd, 'e) -> std::text::str::str where 'a: std::core::fmt::Display, 'b: std::core::fmt::Display, 'c: std::core::fmt::Display, 'd: std::core::fmt::Display, 'e: std::core::fmt::Display = e2168:(fn p511:d1331:value -> e2167:case e2120:r820:value->d1331:value { p517:(p512:d1332:a, p513:d1333:b, p514:d1334:c, p515:d1335:d, p516:d1336:e) -> e2166:(e2165:(e2163:r835:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2162:(e2161:(e2158:r833:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2157:(e2156:(e2154:r832:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2153:(e2152:(e2149:r830:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2148:(e2147:(e2145:r829:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2144:(e2143:(e2140:r827:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2139:(e2138:(e2136:r826:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2135:(e2134:(e2131:r824:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2130:(e2129:(e2127:r823:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2126:(e2125:(e2122:r821:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2121:"(") e2124:(e2123:r822:a->d1332:a.s82.show=>d319:"std.core.fmt.Display.show"))) e2128:", ")) e2133:(e2132:r825:b->d1333:b.s83.show=>d319:"std.core.fmt.Display.show"))) e2137:", ")) e2142:(e2141:r828:c->d1334:c.s84.show=>d319:"std.core.fmt.Display.show"))) e2146:", ")) e2151:(e2150:r831:d->d1335:d.s85.show=>d319:"std.core.fmt.Display.show"))) e2155:", ")) e2160:(e2159:r834:e->d1336:e.s86.show=>d319:"std.core.fmt.Display.show"))) e2164:")") })
      }
      my d372 mod {
        d373: std::text::str::str -> std::text::str::str = e2178:(fn p518:d1337:x -> e2177:(e2176:(e2174:r838:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2173:(e2172:(e2170:r836:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2169:"\"") e2171:r837:x->d1337:x)) e2175:"\""))
      }
      my d374 mod {
        d375: std::text::char::char -> std::text::str::str = e2190:(fn p519:d1338:x -> e2189:(e2188:(e2186:r842:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2185:(e2184:(e2180:r839:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2179:"'") e2183:(e2181:r840:"std::text::char::to_string"->d672:"std.text.char.to_string" e2182:r841:x->d1338:x))) e2187:"'"))
      }
      my d376 mod {
        d377: () -> std::text::str::str = e2192:(fn p520:d1339:x -> e2191:"()")
      }
      my d378:"std.core.fmt.debug_list_items": std::data::list::list 'a -> std::text::str::str where 'a: std::core::fmt::Debug = e2217:(fn p521:d1340:xs -> e2216:case e2195:(e2193:r843:"std::data::list::view_raw"->d477:"std.data.list.view_raw" e2194:r844:xs->d1340:xs) { p522:r845:"std::data::list::list_view::empty"->d456:"std.data.list.list_view.empty" -> e2196:""; p524:r846:"std::data::list::list_view::leaf"->d457:"std.data.list.list_view.leaf"(p523:d1341:item) -> e2198:(e2197:r847:item->d1341:item.s87.debug=>d323:"std.core.fmt.Debug.debug"); p527:r848:"std::data::list::list_view::node"->d458:"std.data.list.list_view.node"(p525:d1342:left, p526:d1343:right) -> e2215:block { let my p528:d1344:left_text = e2201:(e2199:r849:debug_list_items->d378:"std.core.fmt.debug_list_items" e2200:r850:left->d1342:left); e2214:block { let my p529:d1345:right_text = e2204:(e2202:r851:debug_list_items->d378:"std.core.fmt.debug_list_items" e2203:r852:right->d1343:right); e2213:(e2212:(e2210:r855:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2209:(e2208:(e2206:r854:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2205:r853:left_text->d1344:left_text) e2207:", ")) e2211:r856:right_text->d1345:right_text) } } })
      my d379 mod {
        d380: std::data::list::list 'a -> std::text::str::str where 'a: std::core::fmt::Debug = e2229:(fn p530:d1346:xs -> e2228:(e2227:(e2225:r860:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2224:(e2223:(e2219:r857:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2218:"[") e2222:(e2220:r858:debug_list_items->d378:"std.core.fmt.debug_list_items" e2221:r859:xs->d1346:xs))) e2226:"]"))
      }
      my d381 mod {
        d382: std::data::opt::opt 'a -> std::text::str::str where 'a: std::core::fmt::Debug = e2239:(fn p531:d1347:value -> e2238:case e2230:r861:value->d1347:value { p532:r862:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil" -> e2231:"nil"; p534:r863:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just"(p533:d1348:inner) -> e2237:(e2236:(e2233:r864:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2232:"just ") e2235:(e2234:r865:inner->d1348:inner.s88.debug=>d323:"std.core.fmt.Debug.debug")) })
      }
      my d383 mod {
        d384: std::data::result::result 'a 'b -> std::text::str::str where 'a: std::core::fmt::Debug, 'b: std::core::fmt::Debug = e2254:(fn p535:d1349:value -> e2253:case e2240:r866:value->d1349:value { p537:r867:"std::data::result::result::ok"->d529:"std.data.result.result.ok"(p536:d1350:inner) -> e2246:(e2245:(e2242:r868:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2241:"ok ") e2244:(e2243:r869:inner->d1350:inner.s89.debug=>d323:"std.core.fmt.Debug.debug")); p539:r870:"std::data::result::result::err"->d530:"std.data.result.result.err"(p538:d1351:inner) -> e2252:(e2251:(e2248:r871:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2247:"err ") e2250:(e2249:r872:inner->d1351:inner.s90.debug=>d323:"std.core.fmt.Debug.debug")) })
      }
      my d385 mod {
        d386: ('a, 'b) -> std::text::str::str where 'a: std::core::fmt::Debug, 'b: std::core::fmt::Debug = e2276:(fn p540:d1352:value -> e2275:case e2255:r873:value->d1352:value { p543:(p541:d1353:a, p542:d1354:b) -> e2274:(e2273:(e2271:r879:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2270:(e2269:(e2266:r877:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2265:(e2264:(e2262:r876:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2261:(e2260:(e2257:r874:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2256:"(") e2259:(e2258:r875:a->d1353:a.s91.debug=>d323:"std.core.fmt.Debug.debug"))) e2263:", ")) e2268:(e2267:r878:b->d1354:b.s92.debug=>d323:"std.core.fmt.Debug.debug"))) e2272:")") })
      }
      my d387 mod {
        d388: ('a, 'b, 'c) -> std::text::str::str where 'a: std::core::fmt::Debug, 'b: std::core::fmt::Debug, 'c: std::core::fmt::Debug = e2307:(fn p544:d1355:value -> e2306:case e2277:r880:value->d1355:value { p548:(p545:d1356:a, p546:d1357:b, p547:d1358:c) -> e2305:(e2304:(e2302:r889:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2301:(e2300:(e2297:r887:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2296:(e2295:(e2293:r886:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2292:(e2291:(e2288:r884:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2287:(e2286:(e2284:r883:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2283:(e2282:(e2279:r881:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2278:"(") e2281:(e2280:r882:a->d1356:a.s93.debug=>d323:"std.core.fmt.Debug.debug"))) e2285:", ")) e2290:(e2289:r885:b->d1357:b.s94.debug=>d323:"std.core.fmt.Debug.debug"))) e2294:", ")) e2299:(e2298:r888:c->d1358:c.s95.debug=>d323:"std.core.fmt.Debug.debug"))) e2303:")") })
      }
      my d389 mod {
        d390: ('a, 'b, 'c, 'd) -> std::text::str::str where 'a: std::core::fmt::Debug, 'b: std::core::fmt::Debug, 'c: std::core::fmt::Debug, 'd: std::core::fmt::Debug = e2347:(fn p549:d1359:value -> e2346:case e2308:r890:value->d1359:value { p554:(p550:d1360:a, p551:d1361:b, p552:d1362:c, p553:d1363:d) -> e2345:(e2344:(e2342:r902:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2341:(e2340:(e2337:r900:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2336:(e2335:(e2333:r899:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2332:(e2331:(e2328:r897:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2327:(e2326:(e2324:r896:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2323:(e2322:(e2319:r894:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2318:(e2317:(e2315:r893:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2314:(e2313:(e2310:r891:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2309:"(") e2312:(e2311:r892:a->d1360:a.s96.debug=>d323:"std.core.fmt.Debug.debug"))) e2316:", ")) e2321:(e2320:r895:b->d1361:b.s97.debug=>d323:"std.core.fmt.Debug.debug"))) e2325:", ")) e2330:(e2329:r898:c->d1362:c.s98.debug=>d323:"std.core.fmt.Debug.debug"))) e2334:", ")) e2339:(e2338:r901:d->d1363:d.s99.debug=>d323:"std.core.fmt.Debug.debug"))) e2343:")") })
      }
      my d391 mod {
        d392: ('a, 'b, 'c, 'd, 'e) -> std::text::str::str where 'a: std::core::fmt::Debug, 'b: std::core::fmt::Debug, 'c: std::core::fmt::Debug, 'd: std::core::fmt::Debug, 'e: std::core::fmt::Debug = e2396:(fn p555:d1364:value -> e2395:case e2348:r903:value->d1364:value { p561:(p556:d1365:a, p557:d1366:b, p558:d1367:c, p559:d1368:d, p560:d1369:e) -> e2394:(e2393:(e2391:r918:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2390:(e2389:(e2386:r916:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2385:(e2384:(e2382:r915:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2381:(e2380:(e2377:r913:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2376:(e2375:(e2373:r912:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2372:(e2371:(e2368:r910:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2367:(e2366:(e2364:r909:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2363:(e2362:(e2359:r907:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2358:(e2357:(e2355:r906:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2354:(e2353:(e2350:r904:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2349:"(") e2352:(e2351:r905:a->d1365:a.s100.debug=>d323:"std.core.fmt.Debug.debug"))) e2356:", ")) e2361:(e2360:r908:b->d1366:b.s101.debug=>d323:"std.core.fmt.Debug.debug"))) e2365:", ")) e2370:(e2369:r911:c->d1367:c.s102.debug=>d323:"std.core.fmt.Debug.debug"))) e2374:", ")) e2379:(e2378:r914:d->d1368:d.s103.debug=>d323:"std.core.fmt.Debug.debug"))) e2383:", ")) e2388:(e2387:r917:e->d1369:e.s104.debug=>d323:"std.core.fmt.Debug.debug"))) e2392:")") })
      }
    }
    pub d24:"std.core.ops" mod {
      pub d393:"std.core.ops.#op:nullfix:return": () -> [std::control::flow::sub('a | ())] never = e2400:(fn p562:() -> e2399:(e2397:r919:"std::control::flow::sub::return"->d172:"std.control.flow.sub.return" e2398:()))
      pub d394:"std.core.ops.#op:prefix:return": 'a -> [std::control::flow::sub 'a] never = e2401:r920:"std::control::flow::sub::return"->d172:"std.control.flow.sub.return"
      pub d395:"std.core.ops.#op:prefix:fail": 'a -> ['b] never where 'a: std::control::throw::Throw(throws = 'b) = e2404:(fn p563:d1370:e -> e2403:(e2402:r921:e->d1370:e.s105.throw=>d232:"std.control.throw.Throw.throw"))
      pub d396:"std.core.ops.#op:nullfix:last": () -> [std::control::flow::loop] never = e2408:(fn p564:() -> e2407:(e2405:r922:loop_last->d427:"std.core.ops.loop_last" e2406:()))
      pub d397:"std.core.ops.#op:nullfix:next": () -> [std::control::flow::loop] never = e2412:(fn p565:() -> e2411:(e2409:r923:loop_next->d428:"std.core.ops.loop_next" e2410:()))
      pub d398:"std.core.ops.#op:nullfix:redo": () -> [std::control::flow::loop] never = e2416:(fn p566:() -> e2415:(e2413:r924:loop_redo->d429:"std.core.ops.loop_redo" e2414:()))
      pub d399:"std.core.ops.#op:prefix:last": 'a -> never where 'a: std::control::flow::LoopLabel = e2417:r925:label_last->d430:"std.core.ops.label_last"
      pub d400:"std.core.ops.#op:prefix:next": 'a -> never where 'a: std::control::flow::LoopLabel = e2418:r926:label_next->d431:"std.core.ops.label_next"
      pub d401:"std.core.ops.#op:prefix:redo": 'a -> never where 'a: std::control::flow::LoopLabel = e2419:r927:label_redo->d432:"std.core.ops.label_redo"
      pub d402:"std.core.ops.#op:nullfix:..": () -> std::data::range::range = e2423:(fn p567:() -> e2422:(e2420:r928:"std::data::range::full"->d519:"std.data.range.full" e2421:()))
      pub d403:"std.core.ops.#op:prefix:..": int -> std::data::range::range = e2424:r929:"std::data::range::to_included"->d517:"std.data.range.to_included"
      pub d404:"std.core.ops.#op:prefix:..<": int -> std::data::range::range = e2425:r930:"std::data::range::to_excluded"->d518:"std.data.range.to_excluded"
      pub d405:"std.core.ops.#op:suffix:..": int -> std::data::range::range = e2426:r931:"std::data::range::from_included"->d515:"std.data.range.from_included"
      pub d406:"std.core.ops.#op:suffix:<..": int -> std::data::range::range = e2427:r932:"std::data::range::from_excluded"->d516:"std.data.range.from_excluded"
      pub d407:"std.core.ops.#op:infix:..": int -> int -> std::data::range::range = e2428:r933:"std::data::range::inclusive"->d512:"std.data.range.inclusive"
      pub d408:"std.core.ops.#op:infix:..<": int -> int -> std::data::range::range = e2429:r934:"std::data::range::range"->d511:"std.data.range.range"
      pub d409:"std.core.ops.#op:infix:<..": int -> int -> std::data::range::range = e2430:r935:"std::data::range::from_exclusive_to_inclusive"->d514:"std.data.range.from_exclusive_to_inclusive"
      pub d410:"std.core.ops.#op:infix:<..<": int -> int -> std::data::range::range = e2431:r936:"std::data::range::exclusive"->d513:"std.data.range.exclusive"
      pub d411:"std.core.ops.#op:prefix:not": bool -> bool = e2432:r937:"std::bool::not"->d14:"std.bool.not"
      pub d412:"std.core.ops.#op:prefix:-": int -> int = e2438:(fn p568:d1371:x -> e2437:(e2435:(e2433:r938:"std::int::sub"->d51:"std.int.sub" e2434:0) e2436:r939:x->d1371:x))
      pub d413:"std.core.ops.#op:infix:+": 'a -> 'a -> 'a where 'a: std::num::Add = e2444:(fn p569:d1372:x -> e2443:(fn p570:d1373:y -> e2442:(e2440:(e2439:r940:x->d1372:x.s106.add=>d62:"std.num.Add.add") e2441:r941:y->d1373:y)))
      pub d414:"std.core.ops.#op:infix:-": 'a -> 'a -> 'a where 'a: std::num::Sub = e2450:(fn p571:d1374:x -> e2449:(fn p572:d1375:y -> e2448:(e2446:(e2445:r942:x->d1374:x.s107.sub=>d64:"std.num.Sub.sub") e2447:r943:y->d1375:y)))
      pub d415:"std.core.ops.#op:infix:*": 'a -> 'a -> 'a where 'a: std::num::Mul = e2456:(fn p573:d1376:x -> e2455:(fn p574:d1377:y -> e2454:(e2452:(e2451:r944:x->d1376:x.s108.mul=>d66:"std.num.Mul.mul") e2453:r945:y->d1377:y)))
      pub d416:"std.core.ops.#op:infix:/": 'a -> 'a -> 'b where 'a: std::num::Div(out = 'b) = e2462:(fn p575:d1378:x -> e2461:(fn p576:d1379:y -> e2460:(e2458:(e2457:r946:x->d1378:x.s109.div=>d68:"std.num.Div.div") e2459:r947:y->d1379:y)))
      pub d417:"std.core.ops.#op:infix:div": int -> int -> int = e2463:r948:"std::int::div"->d53:"std.int.div"
      pub d418:"std.core.ops.#op:infix:mod": int -> int -> int = e2464:r949:"std::int::mod"->d44:"std.int.mod"
      pub d419:"std.core.ops.#op:infix:==": 'a -> 'a -> bool where 'a: std::core::cmp::Eq = e2470:(fn p577:d1380:x -> e2469:(fn p578:d1381:y -> e2468:(e2466:(e2465:r950:x->d1380:x.s110.eq=>d248:"std.core.cmp.Eq.eq") e2467:r951:y->d1381:y)))
      pub d420:"std.core.ops.#op:infix:!=": 'a -> 'a -> bool where 'a: std::core::cmp::Eq = e2478:(fn p579:d1382:x -> e2477:(fn p580:d1383:y -> e2476:(e2471:r952:"std::bool::not"->d14:"std.bool.not" e2475:(e2473:(e2472:r953:x->d1382:x.s111.eq=>d248:"std.core.cmp.Eq.eq") e2474:r954:y->d1383:y))))
      pub d421:"std.core.ops.#op:infix:<": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = e2484:(fn p581:d1384:x -> e2483:(fn p582:d1385:y -> e2482:(e2480:(e2479:r955:x->d1384:x.s112.lt=>d250:"std.core.cmp.Ord.lt") e2481:r956:y->d1385:y)))
      pub d422:"std.core.ops.#op:infix:<=": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = e2490:(fn p583:d1386:x -> e2489:(fn p584:d1387:y -> e2488:(e2486:(e2485:r957:x->d1386:x.s113.le=>d251:"std.core.cmp.Ord.le") e2487:r958:y->d1387:y)))
      pub d423:"std.core.ops.#op:infix:>": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = e2496:(fn p585:d1388:x -> e2495:(fn p586:d1389:y -> e2494:(e2492:(e2491:r959:x->d1388:x.s114.gt=>d252:"std.core.cmp.Ord.gt") e2493:r960:y->d1389:y)))
      pub d424:"std.core.ops.#op:infix:>=": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = e2502:(fn p587:d1390:x -> e2501:(fn p588:d1391:y -> e2500:(e2498:(e2497:r961:x->d1390:x.s115.ge=>d253:"std.core.cmp.Ord.ge") e2499:r962:y->d1391:y)))
      pub d425:"std.core.ops.#op:infix:and": (() -> ['a & [std::control::junction::junction; 'a]] bool) -> (() -> ['a] 'b) -> ['a] 'b | bool = e2514:(fn p589:d1392:a -> e2513:(fn p590:d1393:b -> e2512:case e2507:(e2506:r964:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e2505:(e2503:r963:a->d1392:a e2504:())) { p591:true -> e2510:(e2508:r965:b->d1393:b e2509:()); p592:false -> e2511:false }))
      pub d426:"std.core.ops.#op:infix:or": (() -> ['a & [std::control::junction::junction; 'a]] bool) -> (() -> ['a] 'b) -> ['a] 'b | bool = e2526:(fn p593:d1394:a -> e2525:(fn p594:d1395:b -> e2524:case e2519:(e2518:r967:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e2517:(e2515:r966:a->d1394:a e2516:())) { p595:true -> e2520:true; p596:false -> e2523:(e2521:r968:b->d1395:b e2522:()) }))
      my d427:"std.core.ops.loop_last": () -> [std::control::flow::loop] never = e2530:(fn p597:() -> e2529:(e2527:r969:"std::control::flow::loop::last"->d182:"std.control.flow.loop.last" e2528:()))
      my d428:"std.core.ops.loop_next": () -> [std::control::flow::loop] never = e2534:(fn p598:() -> e2533:(e2531:r970:"std::control::flow::loop::next"->d183:"std.control.flow.loop.next" e2532:()))
      my d429:"std.core.ops.loop_redo": () -> [std::control::flow::loop] never = e2538:(fn p599:() -> e2537:(e2535:r971:"std::control::flow::loop::redo"->d184:"std.control.flow.loop.redo" e2536:()))
      my d430:"std.core.ops.label_last": 'a -> never where 'a: std::control::flow::LoopLabel = e2543:(fn p600:d1396:label -> e2542:(e2540:(e2539:r972:label->d1396:label.s116.last=>d191:"std.control.flow.LoopLabel.last") e2541:()))
      my d431:"std.core.ops.label_next": 'a -> never where 'a: std::control::flow::LoopLabel = e2548:(fn p601:d1397:label -> e2547:(e2545:(e2544:r973:label->d1397:label.s117.next=>d192:"std.control.flow.LoopLabel.next") e2546:()))
      my d432:"std.core.ops.label_redo": 'a -> never where 'a: std::control::flow::LoopLabel = e2553:(fn p602:d1398:label -> e2552:(e2550:(e2549:r974:label->d1398:label.s118.redo=>d193:"std.control.flow.LoopLabel.redo") e2551:()))
    }
    pub d25:"std.core.seq" mod {
      pub d433:"std.core.seq.Len" mod {
        pub d434:"std.core.seq.Len.len": 'a -> int where 'a: std::core::seq::Len = <missing>
      }
      pub d435:"std.core.seq.IsEmpty" mod {
        pub d436:"std.core.seq.IsEmpty.is_empty": 'a -> bool where 'a: std::core::seq::IsEmpty = <missing>
      }
      my d437 mod {
        d438: std::text::str::str -> int = e2557:(fn p603:d1399:s -> e2556:(e2554:r975:"std::text::str::len"->d786:"std.text.str.len" e2555:r976:s->d1399:s))
      }
      my d439 mod {
        d440: std::data::list::list 'a -> int = e2561:(fn p604:d1400:xs -> e2560:(e2558:r977:"std::data::list::len"->d479:"std.data.list.len" e2559:r978:xs->d1400:xs))
      }
      my d441 mod {
        d442: std::text::str::str -> bool = e2569:(fn p605:d1401:s -> e2568:(e2566:(e2562:r979:"std::int::eq"->d45:"std.int.eq" e2565:(e2563:r980:"std::text::str::len"->d786:"std.text.str.len" e2564:r981:s->d1401:s)) e2567:0))
      }
      my d443 mod {
        d444: std::data::list::list 'a -> bool = e2577:(fn p606:d1402:xs -> e2576:(e2574:(e2570:r982:"std::int::eq"->d45:"std.int.eq" e2573:(e2571:r983:"std::data::list::len"->d479:"std.data.list.len" e2572:r984:xs->d1402:xs)) e2575:0))
      }
      my d445 mod {
        d446: std::text::bytes::bytes -> bool = e2585:(fn p607:d1403:b -> e2584:(e2582:(e2578:r985:"std::int::eq"->d45:"std.int.eq" e2581:(e2579:r986:"std::text::bytes::len"->d653:"std.text.bytes.len" e2580:r987:b->d1403:b)) e2583:0))
      }
      pub d447:"std.core.seq.len": 'a -> int where 'a: std::core::seq::Len = e2588:(fn p608:d1404:x -> e2587:(e2586:r988:x->d1404:x.s119.len=>d434:"std.core.seq.Len.len"))
    }
    pub d26:"std.core.id": 'a -> 'a = e4:(fn p0:d1010:x -> e3:r0:x->d1010:x)
    pub d27:"std.core.compose": ('a ['b#0[Empty]] -> ['c] 'd) -> ('e -> ['b#0[Empty]] 'a) -> 'e -> ['c#0] 'd#0 = e12:(fn p1:d1011:f -> e11:(fn p2:d1012:g -> e10:(fn p3:d1013:x -> e9:(e5:r1:f->d1011:f e8:(e6:r2:g->d1012:g e7:r3:x->d1013:x)))))
  }
  pub d2:"std.int" mod {
    pub d44:"std.int.mod": int -> int -> int = e23:builtin_op::int_mod
    pub d45:"std.int.eq": int -> int -> bool = e24:builtin_op::int_eq
    pub d46:"std.int.lt": int -> int -> bool = e25:builtin_op::int_lt
    pub d47:"std.int.le": int -> int -> bool = e26:builtin_op::int_le
    pub d48:"std.int.gt": int -> int -> bool = e27:builtin_op::int_gt
    pub d49:"std.int.ge": int -> int -> bool = e28:builtin_op::int_ge
    pub d50:"std.int.add": int -> int -> int = e29:builtin_op::int_add
    pub d51:"std.int.sub": int -> int -> int = e30:builtin_op::int_sub
    pub d52:"std.int.mul": int -> int -> int = e31:builtin_op::int_mul
    pub d53:"std.int.div": int -> int -> int = e32:builtin_op::int_div
    pub d54:"std.int.to_string": int -> std::text::str::str = e33:builtin_op::int_to_string
    pub d55:"std.int.to_hex": int -> std::text::str::str = e34:builtin_op::int_to_hex
    pub d56:"std.int.to_upper_hex": int -> std::text::str::str = e35:builtin_op::int_to_upper_hex
  }
  pub d3:"std.float" mod {
    pub d34:"std.float.eq": float -> float -> bool = e13:builtin_op::float_eq
    pub d35:"std.float.lt": float -> float -> bool = e14:builtin_op::float_lt
    pub d36:"std.float.le": float -> float -> bool = e15:builtin_op::float_le
    pub d37:"std.float.gt": float -> float -> bool = e16:builtin_op::float_gt
    pub d38:"std.float.ge": float -> float -> bool = e17:builtin_op::float_ge
    pub d39:"std.float.add": float -> float -> float = e18:builtin_op::float_add
    pub d40:"std.float.sub": float -> float -> float = e19:builtin_op::float_sub
    pub d41:"std.float.mul": float -> float -> float = e20:builtin_op::float_mul
    pub d42:"std.float.div": float -> float -> float = e21:builtin_op::float_div
    pub d43:"std.float.to_string": float -> std::text::str::str = e22:builtin_op::float_to_string
  }
  pub d4:"std.bool" mod {
    pub d13:"std.bool.eq": bool -> bool -> bool = e0:builtin_op::bool_eq
    pub d14:"std.bool.not": bool -> bool = e1:builtin_op::bool_not
    pub d15:"std.bool.to_string": bool -> std::text::str::str = e2:builtin_op::bool_to_string
  }
  pub d5:"std.num" mod {
    pub d60:"std.num.frac" mod {
      pub d633:"std.num.frac.frac": {num: int, den: int} -> std::num::frac::frac = <missing>
      my d638:"std.num.frac.abs": int -> int = e3703:(fn p943:d1630:x -> e3702:case e3695:(e3694:r1529:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e3693:(e3691:(e3689:r1527:"std::int::lt"->d46:"std.int.lt" e3690:r1528:x->d1630:x) e3692:0)) { p944:true -> e3700:(e3698:(e3696:r1530:"std::int::sub"->d51:"std.int.sub" e3697:0) e3699:r1531:x->d1630:x); p945:false -> e3701:r1532:x->d1630:x })
      my d639:"std.num.frac.gcd_positive": int -> int -> int = e3723:(fn p946:d1631:a -> e3722:(fn p947:d1632:b -> e3721:case e3710:(e3709:r1535:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e3708:(e3706:(e3704:r1533:"std::int::eq"->d45:"std.int.eq" e3705:r1534:b->d1632:b) e3707:0)) { p948:true -> e3711:r1536:a->d1631:a; p949:false -> e3720:(e3714:(e3712:r1537:gcd_positive->d639:"std.num.frac.gcd_positive" e3713:r1538:b->d1632:b) e3719:(e3717:(e3715:r1539:"std::int::mod"->d44:"std.int.mod" e3716:r1540:a->d1631:a) e3718:r1541:b->d1632:b)) }))
      my d640:"std.num.frac.gcd": int -> int -> int = e3734:(fn p950:d1633:a -> e3733:(fn p951:d1634:b -> e3732:(e3728:(e3724:r1542:gcd_positive->d639:"std.num.frac.gcd_positive" e3727:(e3725:r1543:abs->d638:"std.num.frac.abs" e3726:r1544:a->d1633:a)) e3731:(e3729:r1545:abs->d638:"std.num.frac.abs" e3730:r1546:b->d1634:b))))
      pub d641:"std.num.frac.new": int -> int -> std::num::frac::frac = e3780:(fn p952:d1635:n -> e3779:(fn p953:d1636:d -> e3778:block { let my p954:d1637:divisor = e3739:(e3737:(e3735:r1547:gcd->d640:"std.num.frac.gcd" e3736:r1548:n->d1635:n) e3738:r1549:d->d1636:d); e3777:block { let my p955:d1638:normalized_num = e3744:(e3742:(e3740:r1550:"std::int::div"->d53:"std.int.div" e3741:r1551:n->d1635:n) e3743:r1552:divisor->d1637:divisor); e3776:block { let my p956:d1639:normalized_den = e3749:(e3747:(e3745:r1553:"std::int::div"->d53:"std.int.div" e3746:r1554:d->d1636:d) e3748:r1555:divisor->d1637:divisor); e3775:case e3756:(e3755:r1558:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e3754:(e3752:(e3750:r1556:"std::int::lt"->d46:"std.int.lt" e3751:r1557:normalized_den->d1639:normalized_den) e3753:0)) { p957:true -> e3769:(e3757:r1559:frac->d633:"std.num.frac.frac" e3768:{num: e3762:(e3760:(e3758:r1560:"std::int::sub"->d51:"std.int.sub" e3759:0) e3761:r1561:normalized_num->d1638:normalized_num), den: e3767:(e3765:(e3763:r1562:"std::int::sub"->d51:"std.int.sub" e3764:0) e3766:r1563:normalized_den->d1639:normalized_den)}); p958:false -> e3774:(e3770:r1564:frac->d633:"std.num.frac.frac" e3773:{num: e3771:r1565:normalized_num->d1638:normalized_num, den: e3772:r1566:normalized_den->d1639:normalized_den}) } } } }))
      pub d642:"std.num.frac.add": std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e3809:(fn p959:d1640:x -> e3808:(fn p960:d1641:y -> e3807:(e3799:(e3781:r1567:new->d641:"std.num.frac.new" e3798:(e3790:(e3782:r1568:"std::int::add"->d50:"std.int.add" e3789:(e3786:(e3783:r1569:"std::int::mul"->d52:"std.int.mul" e3785:(e3784:r1570:x->d1640:x.s144.num->d634)) e3788:(e3787:r1571:y->d1641:y.s145.den->d636))) e3797:(e3794:(e3791:r1572:"std::int::mul"->d52:"std.int.mul" e3793:(e3792:r1573:y->d1641:y.s146.num->d634)) e3796:(e3795:r1574:x->d1640:x.s147.den->d636)))) e3806:(e3803:(e3800:r1575:"std::int::mul"->d52:"std.int.mul" e3802:(e3801:r1576:x->d1640:x.s148.den->d636)) e3805:(e3804:r1577:y->d1641:y.s149.den->d636)))))
      pub d643:"std.num.frac.sub": std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e3838:(fn p961:d1642:x -> e3837:(fn p962:d1643:y -> e3836:(e3828:(e3810:r1578:new->d641:"std.num.frac.new" e3827:(e3819:(e3811:r1579:"std::int::sub"->d51:"std.int.sub" e3818:(e3815:(e3812:r1580:"std::int::mul"->d52:"std.int.mul" e3814:(e3813:r1581:x->d1642:x.s150.num->d634)) e3817:(e3816:r1582:y->d1643:y.s151.den->d636))) e3826:(e3823:(e3820:r1583:"std::int::mul"->d52:"std.int.mul" e3822:(e3821:r1584:y->d1643:y.s152.num->d634)) e3825:(e3824:r1585:x->d1642:x.s153.den->d636)))) e3835:(e3832:(e3829:r1586:"std::int::mul"->d52:"std.int.mul" e3831:(e3830:r1587:x->d1642:x.s154.den->d636)) e3834:(e3833:r1588:y->d1643:y.s155.den->d636)))))
      pub d644:"std.num.frac.mul": std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e3857:(fn p963:d1644:x -> e3856:(fn p964:d1645:y -> e3855:(e3847:(e3839:r1589:new->d641:"std.num.frac.new" e3846:(e3843:(e3840:r1590:"std::int::mul"->d52:"std.int.mul" e3842:(e3841:r1591:x->d1644:x.s156.num->d634)) e3845:(e3844:r1592:y->d1645:y.s157.num->d634))) e3854:(e3851:(e3848:r1593:"std::int::mul"->d52:"std.int.mul" e3850:(e3849:r1594:x->d1644:x.s158.den->d636)) e3853:(e3852:r1595:y->d1645:y.s159.den->d636)))))
      pub d645:"std.num.frac.div": std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e3876:(fn p965:d1646:x -> e3875:(fn p966:d1647:y -> e3874:(e3866:(e3858:r1596:new->d641:"std.num.frac.new" e3865:(e3862:(e3859:r1597:"std::int::mul"->d52:"std.int.mul" e3861:(e3860:r1598:x->d1646:x.s160.num->d634)) e3864:(e3863:r1599:y->d1647:y.s161.den->d636))) e3873:(e3870:(e3867:r1600:"std::int::mul"->d52:"std.int.mul" e3869:(e3868:r1601:x->d1646:x.s162.den->d636)) e3872:(e3871:r1602:y->d1647:y.s163.num->d634)))))
      pub d646:"std.num.frac.eq": std::num::frac::frac -> std::num::frac::frac -> bool = e3896:(fn p967:d1648:x -> e3895:(fn p968:d1649:y -> e3894:case e3885:(e3884:r1606:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e3883:(e3880:(e3877:r1603:"std::int::eq"->d45:"std.int.eq" e3879:(e3878:r1604:x->d1648:x.s164.num->d634)) e3882:(e3881:r1605:y->d1649:y.s165.num->d634))) { p969:true -> e3892:(e3889:(e3886:r1607:"std::int::eq"->d45:"std.int.eq" e3888:(e3887:r1608:x->d1648:x.s166.den->d636)) e3891:(e3890:r1609:y->d1649:y.s167.den->d636)); p970:false -> e3893:false }))
      pub d647:"std.num.frac.lt": std::num::frac::frac -> std::num::frac::frac -> bool = e3915:(fn p971:d1650:x -> e3914:(fn p972:d1651:y -> e3913:(e3905:(e3897:r1610:"std::int::lt"->d46:"std.int.lt" e3904:(e3901:(e3898:r1611:"std::int::mul"->d52:"std.int.mul" e3900:(e3899:r1612:x->d1650:x.s168.num->d634)) e3903:(e3902:r1613:y->d1651:y.s169.den->d636))) e3912:(e3909:(e3906:r1614:"std::int::mul"->d52:"std.int.mul" e3908:(e3907:r1615:y->d1651:y.s170.num->d634)) e3911:(e3910:r1616:x->d1650:x.s171.den->d636)))))
      pub d648:"std.num.frac.le": std::num::frac::frac -> std::num::frac::frac -> bool = e3931:(fn p973:d1652:x -> e3930:(fn p974:d1653:y -> e3929:case e3922:(e3921:r1620:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e3920:(e3918:(e3916:r1617:lt->d647:"std.num.frac.lt" e3917:r1618:x->d1652:x) e3919:r1619:y->d1653:y)) { p975:true -> e3923:true; p976:false -> e3928:(e3926:(e3924:r1621:eq->d646:"std.num.frac.eq" e3925:r1622:x->d1652:x) e3927:r1623:y->d1653:y) }))
      pub d649:"std.num.frac.gt": std::num::frac::frac -> std::num::frac::frac -> bool = e3938:(fn p977:d1654:x -> e3937:(fn p978:d1655:y -> e3936:(e3934:(e3932:r1624:lt->d647:"std.num.frac.lt" e3933:r1625:y->d1655:y) e3935:r1626:x->d1654:x)))
      pub d650:"std.num.frac.ge": std::num::frac::frac -> std::num::frac::frac -> bool = e3954:(fn p979:d1656:x -> e3953:(fn p980:d1657:y -> e3952:case e3945:(e3944:r1630:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e3943:(e3941:(e3939:r1627:gt->d649:"std.num.frac.gt" e3940:r1628:x->d1656:x) e3942:r1629:y->d1657:y)) { p981:true -> e3946:true; p982:false -> e3951:(e3949:(e3947:r1631:eq->d646:"std.num.frac.eq" e3948:r1632:x->d1656:x) e3950:r1633:y->d1657:y) }))
      pub d651:"std.num.frac.to_float": std::num::frac::frac -> float = e3962:(fn p983:d1658:x -> e3961:(e3958:(e3955:r1634:"std::float::div"->d42:"std.float.div" e3957:(e3956:r1635:x->d1658:x.s172.num->d634)) e3960:(e3959:r1636:x->d1658:x.s173.den->d636)))
      pub d652:"std.num.frac.to_string": std::num::frac::frac -> std::text::str::str = e3991:(fn p984:d1659:x -> e3990:case e3970:(e3969:r1639:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e3968:(e3966:(e3963:r1637:"std::int::eq"->d45:"std.int.eq" e3965:(e3964:r1638:x->d1659:x.s174.den->d636)) e3967:1)) { p985:true -> e3974:(e3971:r1640:"std::int::to_string"->d54:"std.int.to_string" e3973:(e3972:r1641:x->d1659:x.s175.num->d634)); p986:false -> e3989:(e3984:(e3975:r1642:"std::text::str::concat"->d784:"std.text.str.concat" e3983:(e3981:(e3976:r1643:"std::text::str::concat"->d784:"std.text.str.concat" e3980:(e3977:r1644:"std::int::to_string"->d54:"std.int.to_string" e3979:(e3978:r1645:x->d1659:x.s176.num->d634))) e3982:"/")) e3988:(e3985:r1646:"std::int::to_string"->d54:"std.int.to_string" e3987:(e3986:r1647:x->d1659:x.s177.den->d636))) })
    }
    pub d61:"std.num.Add" mod {
      pub d62:"std.num.Add.add": 'a -> 'a -> 'a where 'a: std::num::Add = <missing>
    }
    pub d63:"std.num.Sub" mod {
      pub d64:"std.num.Sub.sub": 'a -> 'a -> 'a where 'a: std::num::Sub = <missing>
    }
    pub d65:"std.num.Mul" mod {
      pub d66:"std.num.Mul.mul": 'a -> 'a -> 'a where 'a: std::num::Mul = <missing>
    }
    pub d67:"std.num.Div" mod {
      pub d68:"std.num.Div.div": 'a -> 'a -> 'b where 'a: std::num::Div(out = 'b) = <missing>
    }
    pub d69:"std.num.LowerHex" mod {
      pub d70:"std.num.LowerHex.lower_hex": 'a -> std::text::str::str where 'a: std::num::LowerHex = <missing>
    }
    pub d71:"std.num.UpperHex" mod {
      pub d72:"std.num.UpperHex.upper_hex": 'a -> std::text::str::str where 'a: std::num::UpperHex = <missing>
    }
    my d73 mod {
      d74: int -> int -> int = e42:(fn p4:d1014:x -> e41:(fn p5:d1015:y -> e40:(e38:(e36:r4:"std::int::add"->d50:"std.int.add" e37:r5:x->d1014:x) e39:r6:y->d1015:y)))
    }
    my d75 mod {
      d76: int -> int -> int = e49:(fn p6:d1016:x -> e48:(fn p7:d1017:y -> e47:(e45:(e43:r7:"std::int::sub"->d51:"std.int.sub" e44:r8:x->d1016:x) e46:r9:y->d1017:y)))
    }
    my d77 mod {
      d78: int -> int -> int = e56:(fn p8:d1018:x -> e55:(fn p9:d1019:y -> e54:(e52:(e50:r10:"std::int::mul"->d52:"std.int.mul" e51:r11:x->d1018:x) e53:r12:y->d1019:y)))
    }
    my d79 mod {
      d80: int -> int -> std::num::frac::frac = e63:(fn p10:d1020:x -> e62:(fn p11:d1021:y -> e61:(e59:(e57:r13:"std::num::frac::new"->d641:"std.num.frac.new" e58:r14:x->d1020:x) e60:r15:y->d1021:y)))
    }
    my d81 mod {
      d82: int -> std::text::str::str = e67:(fn p12:d1022:x -> e66:(e64:r16:"std::int::to_hex"->d55:"std.int.to_hex" e65:r17:x->d1022:x))
    }
    my d83 mod {
      d84: int -> std::text::str::str = e71:(fn p13:d1023:x -> e70:(e68:r18:"std::int::to_upper_hex"->d56:"std.int.to_upper_hex" e69:r19:x->d1023:x))
    }
    my d85 mod {
      d86: float -> float -> float = e78:(fn p14:d1024:x -> e77:(fn p15:d1025:y -> e76:(e74:(e72:r20:"std::float::add"->d39:"std.float.add" e73:r21:x->d1024:x) e75:r22:y->d1025:y)))
    }
    my d87 mod {
      d88: float -> float -> float = e85:(fn p16:d1026:x -> e84:(fn p17:d1027:y -> e83:(e81:(e79:r23:"std::float::sub"->d40:"std.float.sub" e80:r24:x->d1026:x) e82:r25:y->d1027:y)))
    }
    my d89 mod {
      d90: float -> float -> float = e92:(fn p18:d1028:x -> e91:(fn p19:d1029:y -> e90:(e88:(e86:r26:"std::float::mul"->d41:"std.float.mul" e87:r27:x->d1028:x) e89:r28:y->d1029:y)))
    }
    my d91 mod {
      d92: float -> float -> float = e99:(fn p20:d1030:x -> e98:(fn p21:d1031:y -> e97:(e95:(e93:r29:"std::float::div"->d42:"std.float.div" e94:r30:x->d1030:x) e96:r31:y->d1031:y)))
    }
    my d93 mod {
      d94: std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e106:(fn p22:d1032:x -> e105:(fn p23:d1033:y -> e104:(e102:(e100:r32:"std::num::frac::add"->d642:"std.num.frac.add" e101:r33:x->d1032:x) e103:r34:y->d1033:y)))
    }
    my d95 mod {
      d96: std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e113:(fn p24:d1034:x -> e112:(fn p25:d1035:y -> e111:(e109:(e107:r35:"std::num::frac::sub"->d643:"std.num.frac.sub" e108:r36:x->d1034:x) e110:r37:y->d1035:y)))
    }
    my d97 mod {
      d98: std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e120:(fn p26:d1036:x -> e119:(fn p27:d1037:y -> e118:(e116:(e114:r38:"std::num::frac::mul"->d644:"std.num.frac.mul" e115:r39:x->d1036:x) e117:r40:y->d1037:y)))
    }
    my d99 mod {
      d100: std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e127:(fn p28:d1038:x -> e126:(fn p29:d1039:y -> e125:(e123:(e121:r41:"std::num::frac::div"->d645:"std.num.frac.div" e122:r42:x->d1038:x) e124:r43:y->d1039:y)))
    }
    my d101 mod {
      d102: std::text::str::str -> std::text::str::str -> std::text::str::str = e134:(fn p30:d1040:x -> e133:(fn p31:d1041:y -> e132:(e130:(e128:r44:"std::text::str::concat"->d784:"std.text.str.concat" e129:r45:x->d1040:x) e131:r46:y->d1041:y)))
    }
    my d103 mod {
      d104: std::data::list::list 'a -> std::data::list::list 'a -> std::data::list::list 'a = e141:(fn p32:d1042:xs -> e140:(fn p33:d1043:ys -> e139:(e137:(e135:r47:"std::data::list::merge"->d478:"std.data.list.merge" e136:r48:xs->d1042:xs) e138:r49:ys->d1043:ys)))
    }
  }
  pub d6:"std.data" mod {
    pub d28:"std.data.fold" mod {
      pub d448:"std.data.fold.Fold" mod {
        pub d449:"std.data.fold.Fold.fold": 'a -> 'b -> ('b -> 'c -> ['d] 'b) -> ['d] 'b where 'a: std::data::fold::Fold(item = 'c) = <missing>
        pub d450:"std.data.fold.Fold.find": 'a -> ('b -> ['c & [std::control::junction::junction; 'c]] bool) -> ['c] std::data::opt::opt 'b where 'a: std::data::fold::Fold(item = 'b) = e2613:(fn p609:d1405:container -> e2612:(fn p610:d1406:f -> e2611:(e2589:r989:"std::control::flow::sub::sub"->d173:"std.control.flow.sub.sub" e2610:block { let my p611:d1407:nil = e2590:r990:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil"; e2609:(e2594:(e2592:(e2591:r991:container->d1405:container.s120.fold=>d449:"std.data.fold.Fold.fold") e2593:r992:nil->d1407:nil) e2608:(fn p612:_ -> e2607:(fn p613:d1408:x -> e2606:case e2599:(e2598:r995:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e2597:(e2595:r993:f->d1406:f e2596:r994:x->d1408:x)) { p614:true -> e2604:(e2600:r996:"std::control::flow::sub::return"->d172:"std.control.flow.sub.return" e2603:(e2601:r997:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just" e2602:r998:x->d1408:x)); p615:false -> e2605:r999:nil->d1407:nil }))) })))
        pub d451:"std.data.fold.Fold.contains": 'a -> 'b -> bool where 'a: std::data::fold::Fold(item = 'b), 'b: std::core::cmp::Eq = e2629:(fn p616:d1409:container -> e2628:(fn p617:d1410:target -> e2627:block { let my p618:d1411:found = e2622:(e2615:(e2614:r1000:container->d1409:container.s121.find=>d450:"std.data.fold.Fold.find") e2621:(fn p619:d1412:x -> e2620:(e2619:(e2617:r1002:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e2616:r1001:x->d1412:x) e2618:r1003:target->d1410:target))); e2626:case e2623:r1004:found->d1411:found { p620:r1005:"opt::nil"->d503:"std.data.opt.opt.nil" -> e2624:false; p622:r1006:"opt::just"->d504:"std.data.opt.opt.just"(p621:_) -> e2625:true } }))
        pub d452:"std.data.fold.Fold.each": 'a -> [std::control::nondet::nondet] 'b where 'a: std::data::fold::Fold(item = 'b) = e2633:(fn p623:d1413:container -> e2632:(e2630:r1007:"std::control::nondet::each"->d224:"std.control.nondet.nondet.each" e2631:r1008:container->d1413:container))
      }
    }
    pub d29:"std.data.index" mod {
      pub d453:"std.data.index.Index" mod {
        pub d454:"std.data.index.Index.index": 'a -> 'b -> 'c where 'a: std::data::index::Index('b, value = 'c) = <missing>
      }
    }
    pub d30:"std.data.list" mod {
      pub d455:"std.data.list.list_view" mod {
        pub d456:"std.data.list.list_view.empty": std::data::list::list_view 'a = <missing>
        pub d457:"std.data.list.list_view.leaf": 'a -> std::data::list::list_view 'a = <missing>
        pub d458:"std.data.list.list_view.node": std::data::list::list 'a -> std::data::list::list 'a -> std::data::list::list_view 'a = <missing>
      }
      pub d459:"std.data.list.list" mod {
        pub d460:"std.data.list.list.append": std::data::list::list 'a -> std::data::list::list 'a -> std::data::list::list 'a = e2640:(fn p624:d1414:xs -> e2639:(fn p625:d1415:ys -> e2638:(e2636:(e2634:r1009:"std::data::list::append"->d497:"std.data.list.append" e2635:r1010:xs->d1414:xs) e2637:r1011:ys->d1415:ys)))
        pub d461:"std.data.list.list.map": std::data::list::list 'a -> ('a -> ['b] 'c) -> ['b] std::data::list::list 'c = e2647:(fn p626:d1416:xs -> e2646:(fn p627:d1417:f -> e2645:(e2643:(e2641:r1012:"std::data::list::map"->d495:"std.data.list.map" e2642:r1013:xs->d1416:xs) e2644:r1014:f->d1417:f)))
        pub d462:"std.data.list.list.filter": std::data::list::list 'a -> ('a -> ['b & 'b] bool) -> ['b] std::data::list::list 'a = e2654:(fn p628:d1418:xs -> e2653:(fn p629:d1419:pred -> e2652:(e2650:(e2648:r1015:"std::data::list::filter"->d496:"std.data.list.filter" e2649:r1016:xs->d1418:xs) e2651:r1017:pred->d1419:pred)))
        pub d463:"std.data.list.list.splice": std::data::list::list 'a -> std::data::range::range -> std::data::list::list 'a -> std::data::list::list 'a = e2664:(fn p630:d1420:xs -> e2663:(fn p631:d1421:r -> e2662:(fn p632:d1422:ys -> e2661:(e2659:(e2657:(e2655:r1018:"std::data::list::splice"->d483:"std.data.list.splice" e2656:r1019:xs->d1420:xs) e2658:r1020:r->d1421:r) e2660:r1021:ys->d1422:ys))))
        pub d464:"std.data.list.list.join": std::data::list::list std::text::str::str -> std::text::str::str -> std::text::str::str = e2671:(fn p633:d1423:xs -> e2670:(fn p634:d1424:separator -> e2669:(e2667:(e2665:r1022:"std::text::str::join"->d865:"std.text.str.join" e2666:r1023:xs->d1423:xs) e2668:r1024:separator->d1424:separator)))
        pub d465:"std.data.list.list.is_empty": std::data::list::list 'a -> bool = e2675:(fn p635:d1425:xs -> e2674:(e2672:r1025:"std::data::list::is_empty"->d490:"std.data.list.is_empty" e2673:r1026:xs->d1425:xs))
        pub d466:"std.data.list.list.first": std::data::list::list 'a -> std::data::opt::opt 'a = e2679:(fn p636:d1426:xs -> e2678:(e2676:r1027:"std::data::list::first"->d498:"std.data.list.first" e2677:r1028:xs->d1426:xs))
        pub d467:"std.data.list.list.last": std::data::list::list 'a -> std::data::opt::opt 'a = e2683:(fn p637:d1427:xs -> e2682:(e2680:r1029:"std::data::list::last"->d499:"std.data.list.last" e2681:r1030:xs->d1427:xs))
        pub d468:"std.data.list.list.rev": std::data::list::list 'a -> std::data::list::list 'a = e2687:(fn p638:d1428:xs -> e2686:(e2684:r1031:"std::data::list::rev"->d494:"std.data.list.rev" e2685:r1032:xs->d1428:xs))
        pub d469:"std.data.list.list.sort": std::data::list::list 'a -> std::data::list::list 'a where std::num::Add('b & std::data::list::list 'a), 'a: std::core::cmp::Ord = e2691:(fn p639:d1429:xs -> e2690:(e2688:r1033:"std::data::list::sort"->d501:"std.data.list.sort" e2689:r1034:xs->d1429:xs))
        pub d470:"std.data.list.list.push!": std::control::var::ref('a, std::data::list::list 'b) -> 'b -> ['a] () = e2704:(fn p640:d1430:"&xs" -> e2703:(fn p641:d1431:x -> e2702:(e2692:r1035:"&xs"->d1430:"&xs" := e2701:(e2697:(e2696:(e2694:(e2693:r1036:"&xs"->d1430:"&xs".s122.get->d236) e2695:()).s123.append->d460:"std.data.list.list.append") e2700:(e2699:builtin_op::list_singleton e2698:r1037:x->d1431:x)))))
      }
      my d471 mod {
        d472: std::data::list::list('a & 'b) -> int -> 'a = e2711:(fn p642:d1432:xs -> e2710:(fn p643:d1433:i -> e2709:(e2707:(e2705:r1038:"std::data::list::index_raw"->d480:"std.data.list.index_raw" e2706:r1039:xs->d1432:xs) e2708:r1040:i->d1433:i)))
      }
      my d473 mod {
        d474: std::data::list::list 'a -> std::data::range::range -> std::data::list::list 'a = e2718:(fn p644:d1434:xs -> e2717:(fn p645:d1435:r -> e2716:(e2714:(e2712:r1041:"std::data::list::index_range"->d481:"std.data.list.index_range" e2713:r1042:xs->d1434:xs) e2715:r1043:r->d1435:r)))
      }
      my d475 mod {
        d476: std::control::var::ref('a & 'b, std::data::list::list('c & 'd)) -> int -> std::control::var::ref('b | 'a, 'd | 'c) = e2770:(fn p646:d1436:r -> e2769:(fn p647:d1437:i -> e2768:(e2719:r1044:ref->d235:"std.control.var.ref" e2767:{get: e2728:(fn p648:() -> e2727:(e2725:(e2720:r1045:"std::data::list::index_raw"->d480:"std.data.list.index_raw" e2724:(e2722:(e2721:r1046:r->d1436:r.s124.get->d236) e2723:())) e2726:r1047:i->d1437:i)), update_effect: e2766:(fn p649:() -> e2765:block { let my p650:d1438:loop = e2758:(fn p651:d1439:x -> e2757:catch e2729:r1048:x->d1439:x { std::control::var::ref_update::update p652:d1440:old, p653:d1441:k -> e2756:block { let my p654:d1442:new_item = e2736:(e2730:r1049:"ref_update::update"->d234:"std.control.var.ref_update.update" e2735:(e2733:(e2731:r1050:"std::data::list::index_raw"->d480:"std.data.list.index_raw" e2732:r1051:old->d1440:old) e2734:r1052:i->d1437:i)); e2755:(e2737:r1053:loop->d1438:loop e2754:(e2738:r1054:k->d1441:k e2753:(e2749:(e2743:(e2741:(e2739:r1055:"std::data::list::splice_raw"->d484:"std.data.list.splice_raw" e2740:r1056:old->d1440:old) e2742:r1057:i->d1437:i) e2748:(e2747:(e2745:r1059:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2744:r1058:i->d1437:i) e2746:1)) e2752:(e2751:builtin_op::list_singleton e2750:r1060:new_item->d1442:new_item)))) } }); e2764:(e2759:r1061:loop->d1438:loop e2763:(e2761:(e2760:r1062:r->d1436:r.s125.update_effect->d238) e2762:())) })})))
      }
      pub d477:"std.data.list.view_raw": std::data::list::list 'a -> std::data::list::list_view 'a = e2771:builtin_op::list_view_raw
      pub d478:"std.data.list.merge": std::data::list::list 'a -> std::data::list::list 'a -> std::data::list::list 'a = e2772:builtin_op::list_merge
      pub d479:"std.data.list.len": std::data::list::list 'a -> int = e2773:builtin_op::list_len
      pub d480:"std.data.list.index_raw": std::data::list::list 'a -> int -> 'a = e2774:builtin_op::list_index
      pub d481:"std.data.list.index_range": std::data::list::list 'a -> std::data::range::range -> std::data::list::list 'a = e2775:builtin_op::list_index_range
      pub d482:"std.data.list.index_range_raw": std::data::list::list 'a -> int -> int -> std::data::list::list 'a = e2776:builtin_op::list_index_range_raw
      pub d483:"std.data.list.splice": std::data::list::list 'a -> std::data::range::range -> std::data::list::list 'a -> std::data::list::list 'a = e2777:builtin_op::list_splice
      pub d484:"std.data.list.splice_raw": std::data::list::list 'a -> int -> int -> std::data::list::list 'a -> std::data::list::list 'a = e2778:builtin_op::list_splice_raw
      my d485:"std.data.list.fold_impl": std::data::list::list 'a -> ('b & 'c) -> ('b -> ['d] 'a -> ['e] 'c) -> ['e, 'd] 'c | 'b = e2804:(fn p655:d1443:xs -> e2803:(fn p656:d1444:z -> e2802:(fn p657:d1445:f -> e2801:case e2781:(e2779:r1063:"std::data::list::view_raw"->d477:"std.data.list.view_raw" e2780:r1064:xs->d1443:xs) { p658:r1065:"list_view::empty"->d456:"std.data.list.list_view.empty" -> e2782:r1066:z->d1444:z; p660:r1067:"list_view::leaf"->d457:"std.data.list.list_view.leaf"(p659:d1446:x) -> e2787:(e2785:(e2783:r1068:f->d1445:f e2784:r1069:z->d1444:z) e2786:r1070:x->d1446:x); p663:r1071:"list_view::node"->d458:"std.data.list.list_view.node"(p661:d1447:left, p662:d1448:right) -> e2800:(e2798:(e2790:(e2788:r1072:fold_impl->d485:"std.data.list.fold_impl" e2789:r1073:right->d1448:right) e2797:(e2795:(e2793:(e2791:r1074:fold_impl->d485:"std.data.list.fold_impl" e2792:r1075:left->d1447:left) e2794:r1076:z->d1444:z) e2796:r1077:f->d1445:f)) e2799:r1078:f->d1445:f) })))
      my d486 mod {
        d487: std::data::list::list 'a -> 'b -> ('b -> ['c] ('d | 'a) -> ['c] 'b) -> ['c] 'b = e2814:(fn p664:d1449:xs -> e2813:(fn p665:d1450:z -> e2812:(fn p666:d1451:f -> e2811:(e2809:(e2807:(e2805:r1079:fold_impl->d485:"std.data.list.fold_impl" e2806:r1080:xs->d1449:xs) e2808:r1081:z->d1450:z) e2810:r1082:f->d1451:f))))
      }
      pub d488:"std.data.list.empty": () -> std::data::list::list 'a = e2818:(fn p667:() -> e2817:(e2815:builtin_op::list_empty e2816:()))
      pub d489:"std.data.list.singleton": 'a -> std::data::list::list 'a = e2822:(fn p668:d1452:x -> e2821:(e2820:builtin_op::list_singleton e2819:r1083:x->d1452:x))
      pub d490:"std.data.list.is_empty": std::data::list::list 'a -> bool = e2830:(fn p669:d1453:xs -> e2829:(e2827:(e2823:r1084:"std::int::eq"->d45:"std.int.eq" e2826:(e2824:r1085:"std::data::list::len"->d479:"std.data.list.len" e2825:r1086:xs->d1453:xs)) e2828:0))
      pub d491:"std.data.list.cons": 'a -> std::data::list::list 'a -> std::data::list::list 'a = e2839:(fn p670:d1454:x -> e2838:(fn p671:d1455:xs -> e2837:(e2835:(e2831:r1087:"std::data::list::merge"->d478:"std.data.list.merge" e2834:(e2832:r1088:singleton->d489:"std.data.list.singleton" e2833:r1089:x->d1454:x)) e2836:r1090:xs->d1455:xs)))
      pub d492:"std.data.list.uncons": std::data::list::list 'a -> std::data::opt::opt ('a, std::data::list::list 'a) = e2868:(fn p672:d1456:xs -> e2867:block { let my p673:d1457:n = e2842:(e2840:r1091:"std::data::list::len"->d479:"std.data.list.len" e2841:r1092:xs->d1456:xs); e2866:case e2849:(e2848:r1095:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e2847:(e2845:(e2843:r1093:"std::int::eq"->d45:"std.int.eq" e2844:r1094:n->d1457:n) e2846:0)) { p674:true -> e2850:r1096:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil"; p675:false -> e2865:(e2851:r1097:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just" e2864:(e2856:(e2854:(e2852:r1098:"std::data::list::index_raw"->d480:"std.data.list.index_raw" e2853:r1099:xs->d1456:xs) e2855:0), e2863:(e2861:(e2859:(e2857:r1100:"std::data::list::index_range_raw"->d482:"std.data.list.index_range_raw" e2858:r1101:xs->d1456:xs) e2860:1) e2862:r1102:n->d1457:n))) } })
      pub d493:"std.data.list.fold": std::data::list::list 'a -> ('b & 'c) -> ('b -> ['d] 'a -> ['d] 'c) -> ['d] 'c | 'b = e2878:(fn p676:d1458:xs -> e2877:(fn p677:d1459:z -> e2876:(fn p678:d1460:f -> e2875:(e2873:(e2871:(e2869:r1103:fold_impl->d485:"std.data.list.fold_impl" e2870:r1104:xs->d1458:xs) e2872:r1105:z->d1459:z) e2874:r1106:f->d1460:f))))
      pub d494:"std.data.list.rev": std::data::list::list 'a -> std::data::list::list 'a = e2898:(fn p679:d1461:xs -> e2897:case e2881:(e2879:r1107:"std::data::list::view_raw"->d477:"std.data.list.view_raw" e2880:r1108:xs->d1461:xs) { p680:r1109:"list_view::empty"->d456:"std.data.list.list_view.empty" -> e2884:(e2882:r1110:empty->d488:"std.data.list.empty" e2883:()); p682:r1111:"list_view::leaf"->d457:"std.data.list.list_view.leaf"(p681:d1462:x) -> e2887:(e2885:r1112:singleton->d489:"std.data.list.singleton" e2886:r1113:x->d1462:x); p685:r1114:"list_view::node"->d458:"std.data.list.list_view.node"(p683:d1463:left, p684:d1464:right) -> e2896:(e2892:(e2888:r1115:append->d497:"std.data.list.append" e2891:(e2889:r1116:rev->d494:"std.data.list.rev" e2890:r1117:right->d1464:right)) e2895:(e2893:r1118:rev->d494:"std.data.list.rev" e2894:r1119:left->d1463:left)) })
      pub d495:"std.data.list.map": std::data::list::list 'a -> ('a -> ['b] 'c) -> ['b] std::data::list::list 'c = e2925:(fn p686:d1465:xs -> e2924:(fn p687:d1466:f -> e2923:case e2901:(e2899:r1120:"std::data::list::view_raw"->d477:"std.data.list.view_raw" e2900:r1121:xs->d1465:xs) { p688:r1122:"list_view::empty"->d456:"std.data.list.list_view.empty" -> e2904:(e2902:r1123:empty->d488:"std.data.list.empty" e2903:()); p690:r1124:"list_view::leaf"->d457:"std.data.list.list_view.leaf"(p689:d1467:x) -> e2909:(e2905:r1125:singleton->d489:"std.data.list.singleton" e2908:(e2906:r1126:f->d1466:f e2907:r1127:x->d1467:x)); p693:r1128:"list_view::node"->d458:"std.data.list.list_view.node"(p691:d1468:left, p692:d1469:right) -> e2922:(e2916:(e2910:r1129:append->d497:"std.data.list.append" e2915:(e2913:(e2911:r1130:map->d495:"std.data.list.map" e2912:r1131:left->d1468:left) e2914:r1132:f->d1466:f)) e2921:(e2919:(e2917:r1133:map->d495:"std.data.list.map" e2918:r1134:right->d1469:right) e2920:r1135:f->d1466:f)) }))
      pub d496:"std.data.list.filter": std::data::list::list 'a -> ('a -> ['b & 'b] bool) -> ['b] std::data::list::list 'a = e2959:(fn p694:d1470:xs -> e2958:(fn p695:d1471:pred -> e2957:case e2928:(e2926:r1136:"std::data::list::view_raw"->d477:"std.data.list.view_raw" e2927:r1137:xs->d1470:xs) { p696:r1138:"list_view::empty"->d456:"std.data.list.list_view.empty" -> e2931:(e2929:r1139:empty->d488:"std.data.list.empty" e2930:()); p698:r1140:"list_view::leaf"->d457:"std.data.list.list_view.leaf"(p697:d1472:x) -> e2943:case e2936:(e2935:r1143:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e2934:(e2932:r1141:pred->d1471:pred e2933:r1142:x->d1472:x)) { p699:true -> e2939:(e2937:r1144:singleton->d489:"std.data.list.singleton" e2938:r1145:x->d1472:x); p700:false -> e2942:(e2940:r1146:empty->d488:"std.data.list.empty" e2941:()) }; p703:r1147:"list_view::node"->d458:"std.data.list.list_view.node"(p701:d1473:left, p702:d1474:right) -> e2956:(e2950:(e2944:r1148:append->d497:"std.data.list.append" e2949:(e2947:(e2945:r1149:filter->d496:"std.data.list.filter" e2946:r1150:left->d1473:left) e2948:r1151:pred->d1471:pred)) e2955:(e2953:(e2951:r1152:filter->d496:"std.data.list.filter" e2952:r1153:right->d1474:right) e2954:r1154:pred->d1471:pred)) }))
      pub d497:"std.data.list.append": std::data::list::list 'a -> std::data::list::list 'a -> std::data::list::list 'a = e2966:(fn p704:d1475:xs -> e2965:(fn p705:d1476:ys -> e2964:(e2962:(e2960:r1155:"std::data::list::merge"->d478:"std.data.list.merge" e2961:r1156:xs->d1475:xs) e2963:r1157:ys->d1476:ys)))
      pub d498:"std.data.list.first": std::data::list::list 'a -> std::data::opt::opt 'a = e2975:(fn p706:d1477:xs -> e2974:case e2969:(e2967:r1158:uncons->d492:"std.data.list.uncons" e2968:r1159:xs->d1477:xs) { p707:r1160:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil" -> e2970:r1161:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil"; p711:r1162:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just"(p710:(p708:d1478:head, p709:_)) -> e2973:(e2971:r1163:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just" e2972:r1164:head->d1478:head) })
      pub d499:"std.data.list.last": std::data::list::list 'a -> std::data::opt::opt 'a = e2993:(fn p712:d1479:xs -> e2992:case e2978:(e2976:r1165:uncons->d492:"std.data.list.uncons" e2977:r1166:xs->d1479:xs) { p713:r1167:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil" -> e2979:r1168:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil"; p717:r1169:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just"(p716:(p714:d1480:head, p715:d1481:tail)) -> e2991:case e2984:(e2983:r1172:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e2982:(e2980:r1170:is_empty->d490:"std.data.list.is_empty" e2981:r1171:tail->d1481:tail)) { p718:true -> e2987:(e2985:r1173:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just" e2986:r1174:head->d1480:head); p719:false -> e2990:(e2988:r1175:"std::data::list::last"->d499:"std.data.list.last" e2989:r1176:tail->d1481:tail) } })
      my d500:"std.data.list.sort_split": std::data::list::list('a & 'b) -> 'b -> ('c | std::data::list::list('a & 'b), 'd | std::data::list::list('a & 'b)) where 'c: std::num::Add, 'd: std::num::Add, std::core::cmp::Ord('b | 'a) = e3050:(fn p720:d1482:xs -> e3049:(fn p721:d1483:x -> e3048:case e2996:(e2994:r1177:"std::data::list::view_raw"->d477:"std.data.list.view_raw" e2995:r1178:xs->d1482:xs) { p722:r1179:"list_view::empty"->d456:"std.data.list.list_view.empty" -> e3003:(e2999:(e2997:builtin_op::list_empty e2998:()), e3002:(e3000:builtin_op::list_empty e3001:())); p724:r1180:"list_view::leaf"->d457:"std.data.list.list_view.leaf"(p723:d1484:y) if e3010:(e3009:r1184:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e3008:(e3007:(e3005:r1182:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e3004:r1181:y->d1484:y) e3006:r1183:x->d1483:x)) -> e3017:(e3013:(e3012:builtin_op::list_singleton e3011:r1185:y->d1484:y), e3016:(e3014:builtin_op::list_empty e3015:())); p726:r1186:"list_view::leaf"->d457:"std.data.list.list_view.leaf"(p725:d1485:y) -> e3024:(e3020:(e3018:builtin_op::list_empty e3019:()), e3023:(e3022:builtin_op::list_singleton e3021:r1187:y->d1485:y)); p729:r1188:"list_view::node"->d458:"std.data.list.list_view.node"(p727:d1486:l, p728:d1487:r) -> e3047:block { let my p736:(p732:(p730:d1488:ll, p731:d1489:lr), p735:(p733:d1490:rl, p734:d1491:rr)) = e3035:(e3029:(e3027:(e3025:r1189:sort_split->d500:"std.data.list.sort_split" e3026:r1190:l->d1486:l) e3028:r1191:x->d1483:x), e3034:(e3032:(e3030:r1192:sort_split->d500:"std.data.list.sort_split" e3031:r1193:r->d1487:r) e3033:r1194:x->d1483:x)); e3046:(e3040:(e3039:(e3037:r1196:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3036:r1195:ll->d1488:ll) e3038:r1197:rl->d1490:rl), e3045:(e3044:(e3042:r1199:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3041:r1198:lr->d1489:lr) e3043:r1200:rr->d1491:rr)) } }))
      pub d501:"std.data.list.sort": std::data::list::list 'a -> std::data::list::list 'a where std::num::Add('b & std::data::list::list 'a), 'a: std::core::cmp::Ord = e3077:(fn p737:d1492:xs -> e3076:case e3051:r1201:xs->d1492:xs { p738:[] -> e3054:(e3052:builtin_op::list_empty e3053:()); p741:[p739:d1493:x, ..p740:d1494:xs] -> e3075:block { let my p744:(p742:d1495:l, p743:d1496:r) = e3059:(e3057:(e3055:r1202:sort_split->d500:"std.data.list.sort_split" e3056:r1203:xs->d1494:xs) e3058:r1204:x->d1493:x); e3074:(e3073:(e3072:builtin_op::list_merge e3062:(e3060:r1205:sort->d501:"std.data.list.sort" e3061:r1206:l->d1495:l)) e3071:(e3070:(e3069:builtin_op::list_merge e3065:(e3064:builtin_op::list_singleton e3063:r1207:x->d1493:x)) e3068:(e3066:r1208:sort->d501:"std.data.list.sort" e3067:r1209:r->d1496:r))) } })
    }
    pub d31:"std.data.opt" mod {
      pub d502:"std.data.opt.opt" mod {
        pub d503:"std.data.opt.opt.nil": std::data::opt::opt 'a = <missing>
        pub d504:"std.data.opt.opt.just": 'a -> std::data::opt::opt 'a = <missing>
      }
    }
    pub d32:"std.data.range" mod {
      pub d505:"std.data.range.bound" mod {
        pub d506:"std.data.range.bound.unbounded": std::data::range::bound = <missing>
        pub d507:"std.data.range.bound.included": int -> std::data::range::bound = <missing>
        pub d508:"std.data.range.bound.excluded": int -> std::data::range::bound = <missing>
      }
      pub d509:"std.data.range.range" mod {
        pub d510:"std.data.range.range.within": std::data::range::bound -> std::data::range::bound -> std::data::range::range = <missing>
      }
      pub d511:"std.data.range.range": int -> int -> std::data::range::range = e3088:(fn p745:d1497:start -> e3087:(fn p746:d1498:end -> e3086:(e3082:(e3078:r1210:"range::within"->d510:"std.data.range.range.within" e3081:(e3079:r1211:"bound::included"->d507:"std.data.range.bound.included" e3080:r1212:start->d1497:start)) e3085:(e3083:r1213:"bound::excluded"->d508:"std.data.range.bound.excluded" e3084:r1214:end->d1498:end))))
      pub d512:"std.data.range.inclusive": int -> int -> std::data::range::range = e3099:(fn p747:d1499:start -> e3098:(fn p748:d1500:end -> e3097:(e3093:(e3089:r1215:"range::within"->d510:"std.data.range.range.within" e3092:(e3090:r1216:"bound::included"->d507:"std.data.range.bound.included" e3091:r1217:start->d1499:start)) e3096:(e3094:r1218:"bound::included"->d507:"std.data.range.bound.included" e3095:r1219:end->d1500:end))))
      pub d513:"std.data.range.exclusive": int -> int -> std::data::range::range = e3110:(fn p749:d1501:start -> e3109:(fn p750:d1502:end -> e3108:(e3104:(e3100:r1220:"range::within"->d510:"std.data.range.range.within" e3103:(e3101:r1221:"bound::excluded"->d508:"std.data.range.bound.excluded" e3102:r1222:start->d1501:start)) e3107:(e3105:r1223:"bound::excluded"->d508:"std.data.range.bound.excluded" e3106:r1224:end->d1502:end))))
      pub d514:"std.data.range.from_exclusive_to_inclusive": int -> int -> std::data::range::range = e3121:(fn p751:d1503:start -> e3120:(fn p752:d1504:end -> e3119:(e3115:(e3111:r1225:"range::within"->d510:"std.data.range.range.within" e3114:(e3112:r1226:"bound::excluded"->d508:"std.data.range.bound.excluded" e3113:r1227:start->d1503:start)) e3118:(e3116:r1228:"bound::included"->d507:"std.data.range.bound.included" e3117:r1229:end->d1504:end))))
      pub d515:"std.data.range.from_included": int -> std::data::range::range = e3129:(fn p753:d1505:start -> e3128:(e3126:(e3122:r1230:"range::within"->d510:"std.data.range.range.within" e3125:(e3123:r1231:"bound::included"->d507:"std.data.range.bound.included" e3124:r1232:start->d1505:start)) e3127:r1233:"bound::unbounded"->d506:"std.data.range.bound.unbounded"))
      pub d516:"std.data.range.from_excluded": int -> std::data::range::range = e3137:(fn p754:d1506:start -> e3136:(e3134:(e3130:r1234:"range::within"->d510:"std.data.range.range.within" e3133:(e3131:r1235:"bound::excluded"->d508:"std.data.range.bound.excluded" e3132:r1236:start->d1506:start)) e3135:r1237:"bound::unbounded"->d506:"std.data.range.bound.unbounded"))
      pub d517:"std.data.range.to_included": int -> std::data::range::range = e3145:(fn p755:d1507:end -> e3144:(e3140:(e3138:r1238:"range::within"->d510:"std.data.range.range.within" e3139:r1239:"bound::unbounded"->d506:"std.data.range.bound.unbounded") e3143:(e3141:r1240:"bound::included"->d507:"std.data.range.bound.included" e3142:r1241:end->d1507:end)))
      pub d518:"std.data.range.to_excluded": int -> std::data::range::range = e3153:(fn p756:d1508:end -> e3152:(e3148:(e3146:r1242:"range::within"->d510:"std.data.range.range.within" e3147:r1243:"bound::unbounded"->d506:"std.data.range.bound.unbounded") e3151:(e3149:r1244:"bound::excluded"->d508:"std.data.range.bound.excluded" e3150:r1245:end->d1508:end)))
      pub d519:"std.data.range.full": () -> std::data::range::range = e3159:(fn p757:() -> e3158:(e3156:(e3154:r1246:"range::within"->d510:"std.data.range.range.within" e3155:r1247:"bound::unbounded"->d506:"std.data.range.bound.unbounded") e3157:r1248:"bound::unbounded"->d506:"std.data.range.bound.unbounded"))
      pub d520:"std.data.range.start": std::data::range::range -> std::data::range::bound = e3163:(fn p758:d1509:r -> e3162:case e3160:r1249:r->d1509:r { p761:r1250:"range::within"->d510:"std.data.range.range.within"(p759:d1510:start, p760:_) -> e3161:r1251:start->d1510:start })
      pub d521:"std.data.range.end": std::data::range::range -> std::data::range::bound = e3167:(fn p762:d1511:r -> e3166:case e3164:r1252:r->d1511:r { p765:r1253:"range::within"->d510:"std.data.range.range.within"(p763:_, p764:d1512:end) -> e3165:r1254:end->d1512:end })
      my d522:"std.data.range.first_int": std::data::range::bound -> int = e3177:(fn p766:d1513:b -> e3176:case e3168:r1255:b->d1513:b { p767:r1256:"bound::unbounded"->d506:"std.data.range.bound.unbounded" -> e3169:0; p769:r1257:"bound::included"->d507:"std.data.range.bound.included"(p768:d1514:x) -> e3170:r1258:x->d1514:x; p771:r1259:"bound::excluded"->d508:"std.data.range.bound.excluded"(p770:d1515:x) -> e3175:(e3174:(e3172:r1261:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3171:r1260:x->d1515:x) e3173:1) })
      my d523:"std.data.range.last_exclusive_int": std::data::range::bound -> int = e3187:(fn p772:d1516:b -> e3186:case e3178:r1262:b->d1516:b { p773:r1263:"bound::unbounded"->d506:"std.data.range.bound.unbounded" -> e3179:0; p775:r1264:"bound::included"->d507:"std.data.range.bound.included"(p774:d1517:x) -> e3184:(e3183:(e3181:r1266:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3180:r1265:x->d1517:x) e3182:1); p777:r1267:"bound::excluded"->d508:"std.data.range.bound.excluded"(p776:d1518:x) -> e3185:r1268:x->d1518:x })
      my d524:"std.data.range.fold_ints": ('a -> ['b] int -> ['b] 'a) -> int -> int -> 'a -> ['b] 'a = e3217:(fn p778:d1519:f -> e3216:(fn p779:d1520:i -> e3215:(fn p780:d1521:end -> e3214:(fn p781:d1522:acc -> e3213:case e3194:(e3193:r1272:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e3192:(e3191:(e3189:r1270:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e3188:r1269:i->d1520:i) e3190:r1271:end->d1521:end)) { p782:true -> e3211:(e3205:(e3203:(e3197:(e3195:r1273:fold_ints->d524:"std.data.range.fold_ints" e3196:r1274:f->d1519:f) e3202:(e3201:(e3199:r1276:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3198:r1275:i->d1520:i) e3200:1)) e3204:r1277:end->d1521:end) e3210:(e3208:(e3206:r1278:f->d1519:f e3207:r1279:acc->d1522:acc) e3209:r1280:i->d1520:i)); p783:false -> e3212:r1281:acc->d1522:acc }))))
      my d525:"std.data.range.fold_from": ('a -> ['b] int -> ['b] 'a) -> int -> 'a -> ['b] 'a = e3240:(fn p784:d1523:f -> e3239:(fn p785:d1524:i -> e3238:(fn p786:d1525:acc -> e3237:case e3220:(e3219:r1282:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e3218:true) { p787:true -> e3235:(e3229:(e3223:(e3221:r1283:fold_from->d525:"std.data.range.fold_from" e3222:r1284:f->d1523:f) e3228:(e3227:(e3225:r1286:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3224:r1285:i->d1524:i) e3226:1)) e3234:(e3232:(e3230:r1287:f->d1523:f e3231:r1288:acc->d1525:acc) e3233:r1289:i->d1524:i)); p788:false -> e3236:r1290:acc->d1525:acc })))
      my d526 mod {
        d527: std::data::range::range -> 'a -> ('a -> ['b] int -> ['b] 'a) -> ['b] 'a = e3267:(fn p789:d1526:r -> e3266:(fn p790:d1527:z -> e3265:(fn p791:d1528:f -> e3264:case e3241:r1291:r->d1526:r { p794:r1292:"range::within"->d510:"std.data.range.range.within"(p792:d1529:start, p793:r1293:"bound::unbounded"->d506:"std.data.range.bound.unbounded") -> e3250:(e3248:(e3244:(e3242:r1294:fold_from->d525:"std.data.range.fold_from" e3243:r1295:f->d1528:f) e3247:(e3245:r1296:first_int->d522:"std.data.range.first_int" e3246:r1297:start->d1529:start)) e3249:r1298:z->d1527:z); p797:r1299:"range::within"->d510:"std.data.range.range.within"(p795:d1530:start, p796:d1531:end) -> e3263:(e3261:(e3257:(e3253:(e3251:r1300:fold_ints->d524:"std.data.range.fold_ints" e3252:r1301:f->d1528:f) e3256:(e3254:r1302:first_int->d522:"std.data.range.first_int" e3255:r1303:start->d1530:start)) e3260:(e3258:r1304:last_exclusive_int->d523:"std.data.range.last_exclusive_int" e3259:r1305:end->d1531:end)) e3262:r1306:z->d1527:z) })))
      }
    }
    pub d33:"std.data.result" mod {
      pub d528:"std.data.result.result" mod {
        pub d529:"std.data.result.result.ok": 'a -> std::data::result::result 'a 'b = <missing>
        pub d530:"std.data.result.result.err": 'a -> std::data::result::result 'b 'a = <missing>
        pub d531:"std.data.result.result.map": std::data::result::result 'a 'b -> ('a -> ['c] 'd) -> ['c] std::data::result::result 'd 'b = e3274:(fn p798:d1532:r -> e3273:(fn p799:d1533:f -> e3272:(e3270:(e3268:r1307:"std::data::result::map"->d534:"std.data.result.map" e3269:r1308:r->d1532:r) e3271:r1309:f->d1533:f)))
        pub d532:"std.data.result.result.and_then": std::data::result::result 'a 'b -> ('a -> ['c] std::data::result::result 'd 'b) -> ['c] std::data::result::result 'd 'b = e3281:(fn p800:d1534:r -> e3280:(fn p801:d1535:f -> e3279:(e3277:(e3275:r1310:"std::data::result::and_then"->d535:"std.data.result.and_then" e3276:r1311:r->d1534:r) e3278:r1312:f->d1535:f)))
        pub d533:"std.data.result.result.unwrap_or": std::data::result::result 'a 'b -> 'a -> 'a = e3288:(fn p802:d1536:r -> e3287:(fn p803:d1537:fallback -> e3286:(e3284:(e3282:r1313:"std::data::result::unwrap_or"->d536:"std.data.result.unwrap_or" e3283:r1314:r->d1536:r) e3285:r1315:fallback->d1537:fallback)))
      }
      pub d534:"std.data.result.map": std::data::result::result 'a 'b -> ('a -> ['c] 'd) -> ['c] std::data::result::result 'd 'b = e3300:(fn p804:d1538:r -> e3299:(fn p805:d1539:f -> e3298:case e3289:r1316:r->d1538:r { p807:r1317:"result::ok"->d529:"std.data.result.result.ok"(p806:d1540:value) -> e3294:(e3290:r1318:"result::ok"->d529:"std.data.result.result.ok" e3293:(e3291:r1319:f->d1539:f e3292:r1320:value->d1540:value)); p809:r1321:"result::err"->d530:"std.data.result.result.err"(p808:d1541:err) -> e3297:(e3295:r1322:"result::err"->d530:"std.data.result.result.err" e3296:r1323:err->d1541:err) }))
      pub d535:"std.data.result.and_then": std::data::result::result 'a 'b -> ('a -> ['c] std::data::result::result 'd 'b) -> ['c] std::data::result::result 'd 'b = e3310:(fn p810:d1542:r -> e3309:(fn p811:d1543:f -> e3308:case e3301:r1324:r->d1542:r { p813:r1325:"result::ok"->d529:"std.data.result.result.ok"(p812:d1544:value) -> e3304:(e3302:r1326:f->d1543:f e3303:r1327:value->d1544:value); p815:r1328:"result::err"->d530:"std.data.result.result.err"(p814:d1545:err) -> e3307:(e3305:r1329:"result::err"->d530:"std.data.result.result.err" e3306:r1330:err->d1545:err) }))
      pub d536:"std.data.result.unwrap_or": std::data::result::result 'a 'b -> 'a -> 'a = e3316:(fn p816:d1546:r -> e3315:(fn p817:d1547:fallback -> e3314:case e3311:r1331:r->d1546:r { p819:r1332:"result::ok"->d529:"std.data.result.result.ok"(p818:d1548:value) -> e3312:r1333:value->d1548:value; p821:r1334:"result::err"->d530:"std.data.result.result.err"(p820:_) -> e3313:r1335:fallback->d1547:fallback }))
    }
  }
  pub d7:"std.text" mod {
    pub d110:"std.text.bytes" mod {
      pub d653:"std.text.bytes.len": std::text::bytes::bytes -> int = e3992:builtin_op::bytes_len
      pub d654:"std.text.bytes.eq": std::text::bytes::bytes -> std::text::bytes::bytes -> bool = e3993:builtin_op::bytes_eq
      pub d655:"std.text.bytes.concat": std::text::bytes::bytes -> std::text::bytes::bytes -> std::text::bytes::bytes = e3994:builtin_op::bytes_concat
      pub d656:"std.text.bytes.index_raw": std::text::bytes::bytes -> int -> int = e3995:builtin_op::bytes_index
      pub d657:"std.text.bytes.index_range": std::text::bytes::bytes -> std::data::range::range -> std::text::bytes::bytes = e3996:builtin_op::bytes_index_range
      pub d658:"std.text.bytes.to_utf8_raw": std::text::bytes::bytes -> (std::text::str::str, int) = e3997:builtin_op::bytes_to_utf8_raw
      pub d659:"std.text.bytes.bytes" mod {
        pub d660:"std.text.bytes.bytes.len": std::text::bytes::bytes -> int = e4001:(fn p987:d1660:b -> e4000:(e3998:r1648:"std::text::bytes::len"->d653:"std.text.bytes.len" e3999:r1649:b->d1660:b))
        pub d661:"std.text.bytes.bytes.is_empty": std::text::bytes::bytes -> bool = e4005:(fn p988:d1661:b -> e4004:(e4002:r1650:"std::text::bytes::is_empty"->d665:"std.text.bytes.is_empty" e4003:r1651:b->d1661:b))
        pub d662:"std.text.bytes.bytes.concat": std::text::bytes::bytes -> std::text::bytes::bytes -> std::text::bytes::bytes = e4012:(fn p989:d1662:b -> e4011:(fn p990:d1663:other -> e4010:(e4008:(e4006:r1652:"std::text::bytes::concat"->d655:"std.text.bytes.concat" e4007:r1653:b->d1662:b) e4009:r1654:other->d1663:other)))
        pub d663:"std.text.bytes.bytes.to_utf8_raw": std::text::bytes::bytes -> (std::text::str::str, int) = e4016:(fn p991:d1664:b -> e4015:(e4013:r1655:"std::text::bytes::to_utf8_raw"->d658:"std.text.bytes.to_utf8_raw" e4014:r1656:b->d1664:b))
        pub d664:"std.text.bytes.bytes.to_utf8_lossy": std::text::bytes::bytes -> std::text::str::str = e4020:(fn p992:d1665:b -> e4019:(e4017:r1657:"std::text::bytes::to_utf8_lossy"->d666:"std.text.bytes.to_utf8_lossy" e4018:r1658:b->d1665:b))
      }
      pub d665:"std.text.bytes.is_empty": std::text::bytes::bytes -> bool = e4028:(fn p993:d1666:b -> e4027:(e4025:(e4021:r1659:"std::int::eq"->d45:"std.int.eq" e4024:(e4022:r1660:"std::text::bytes::len"->d653:"std.text.bytes.len" e4023:r1661:b->d1666:b)) e4026:0))
      pub d666:"std.text.bytes.to_utf8_lossy": std::text::bytes::bytes -> std::text::str::str = e4034:(fn p994:d1667:b -> e4033:case e4031:(e4029:r1662:"std::text::bytes::to_utf8_raw"->d658:"std.text.bytes.to_utf8_raw" e4030:r1663:b->d1667:b) { p997:(p995:d1668:text, p996:_) -> e4032:r1664:text->d1668:text })
      my d667 mod {
        d668: std::text::bytes::bytes -> int -> int = e4041:(fn p998:d1669:b -> e4040:(fn p999:d1670:i -> e4039:(e4037:(e4035:r1665:"std::text::bytes::index_raw"->d656:"std.text.bytes.index_raw" e4036:r1666:b->d1669:b) e4038:r1667:i->d1670:i)))
      }
      my d669 mod {
        d670: std::text::bytes::bytes -> std::data::range::range -> std::text::bytes::bytes = e4048:(fn p1000:d1671:b -> e4047:(fn p1001:d1672:r -> e4046:(e4044:(e4042:r1668:"std::text::bytes::index_range"->d657:"std.text.bytes.index_range" e4043:r1669:b->d1671:b) e4045:r1670:r->d1672:r)))
      }
    }
    pub d111:"std.text.char" mod {
      pub d671:"std.text.char.eq": std::text::char::char -> std::text::char::char -> bool = e4049:builtin_op::char_eq
      pub d672:"std.text.char.to_string": std::text::char::char -> std::text::str::str = e4050:builtin_op::char_to_string
      pub d673:"std.text.char.is_whitespace": std::text::char::char -> bool = e4051:builtin_op::char_is_whitespace
      pub d674:"std.text.char.is_punctuation": std::text::char::char -> bool = e4052:builtin_op::char_is_punctuation
      pub d675:"std.text.char.is_word": std::text::char::char -> bool = e4053:builtin_op::char_is_word
      pub d676:"std.text.char.char" mod {
        pub d677:"std.text.char.char.to_string": std::text::char::char -> std::text::str::str = e4057:(fn p1002:d1673:c -> e4056:(e4054:r1671:"std::text::char::to_string"->d672:"std.text.char.to_string" e4055:r1672:c->d1673:c))
        pub d678:"std.text.char.char.is_whitespace": std::text::char::char -> bool = e4061:(fn p1003:d1674:c -> e4060:(e4058:r1673:"std::text::char::is_whitespace"->d673:"std.text.char.is_whitespace" e4059:r1674:c->d1674:c))
        pub d679:"std.text.char.char.is_punctuation": std::text::char::char -> bool = e4065:(fn p1004:d1675:c -> e4064:(e4062:r1675:"std::text::char::is_punctuation"->d674:"std.text.char.is_punctuation" e4063:r1676:c->d1675:c))
        pub d680:"std.text.char.char.is_word": std::text::char::char -> bool = e4069:(fn p1005:d1676:c -> e4068:(e4066:r1677:"std::text::char::is_word"->d675:"std.text.char.is_word" e4067:r1678:c->d1676:c))
      }
    }
    pub d112:"std.text.config" mod {
      pub d681:"std.text.config.section": {name: std::text::str::str, entries: std::data::list::list (std::text::str::str, std::text::str::str)} -> std::text::config::section = <missing>
      pub d686:"std.text.config.config": {sections_: std::data::list::list std::text::config::section} -> std::text::config::config = <missing>
      pub d689:"std.text.config.config" mod {
        pub d690:"std.text.config.config.get": std::text::config::config -> std::text::str::str -> std::text::str::str -> std::data::opt::opt std::text::str::str = e4079:(fn p1006:d1677:c -> e4078:(fn p1007:d1678:section_name -> e4077:(fn p1008:d1679:key -> e4076:(e4074:(e4072:(e4070:r1679:"std::text::config::get"->d706:"std.text.config.get" e4071:r1680:c->d1677:c) e4073:r1681:section_name->d1678:section_name) e4075:r1682:key->d1679:key))))
        pub d691:"std.text.config.config.sections": std::text::config::config -> std::data::list::list std::text::config::section = e4083:(fn p1009:d1680:c -> e4082:(e4080:r1683:"std::text::config::sections"->d694:"std.text.config.sections" e4081:r1684:c->d1680:c))
      }
      my d692:"std.text.config.empty_section": std::text::str::str -> std::text::config::section = e4091:(fn p1010:d1681:name -> e4090:(e4084:r1685:section->d681:"std.text.config.section" e4089:{name: e4085:r1686:name->d1681:name, entries: e4088:(e4086:builtin_op::list_empty e4087:())}))
      my d693:"std.text.config.empty": () -> std::text::config::config = e4100:(fn p1011:() -> e4099:(e4092:r1687:config->d686:"std.text.config.config" e4098:{sections_: e4097:(e4096:builtin_op::list_singleton e4095:(e4093:r1688:empty_section->d692:"std.text.config.empty_section" e4094:""))}))
      pub d694:"std.text.config.sections": std::text::config::config -> std::data::list::list std::text::config::section = e4103:(fn p1012:d1682:c -> e4102:(e4101:r1689:c->d1682:c.s178.sections_->d687))
      my d695:"std.text.config.ensure_section_list": std::data::list::list std::text::config::section -> std::text::str::str -> std::data::list::list std::text::config::section = e4132:(fn p1013:d1683:sections -> e4131:(fn p1014:d1684:name -> e4130:case e4104:r1690:sections->d1683:sections { p1015:[] -> e4109:(e4108:builtin_op::list_singleton e4107:(e4105:r1691:empty_section->d692:"std.text.config.empty_section" e4106:r1692:name->d1684:name)); p1018:[p1016:d1685:head, ..p1017:d1686:tail] if e4117:(e4116:r1696:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4115:(e4114:(e4112:r1694:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e4111:(e4110:r1693:head->d1685:head.s179.name->d682)) e4113:r1695:name->d1684:name)) -> e4118:r1697:sections->d1683:sections; p1021:[p1019:d1687:head, ..p1020:d1688:tail] -> e4129:(e4128:(e4127:builtin_op::list_merge e4121:(e4120:builtin_op::list_singleton e4119:r1698:head->d1687:head)) e4126:(e4124:(e4122:r1699:ensure_section_list->d695:"std.text.config.ensure_section_list" e4123:r1700:tail->d1688:tail) e4125:r1701:name->d1684:name)) }))
      my d696:"std.text.config.ensure_section": std::text::config::config -> std::text::str::str -> std::text::config::config = e4143:(fn p1022:d1689:c -> e4142:(fn p1023:d1690:name -> e4141:(e4133:r1702:config->d686:"std.text.config.config" e4140:{sections_: e4139:(e4137:(e4134:r1703:ensure_section_list->d695:"std.text.config.ensure_section_list" e4136:(e4135:r1704:c->d1689:c.s180.sections_->d687)) e4138:r1705:name->d1690:name)})))
      my d697:"std.text.config.put_entry_list": std::data::list::list std::text::config::section -> std::text::str::str -> (std::text::str::str, std::text::str::str) -> std::data::list::list std::text::config::section = e4197:(fn p1024:d1691:sections -> e4196:(fn p1025:d1692:section_name -> e4195:(fn p1026:d1693:entry -> e4194:case e4144:r1706:sections->d1691:sections { p1027:[] -> e4153:(e4152:builtin_op::list_singleton e4151:(e4145:r1707:section->d681:"std.text.config.section" e4150:{name: e4146:r1708:section_name->d1692:section_name, entries: e4149:(e4148:builtin_op::list_singleton e4147:r1709:entry->d1693:entry)})); p1030:[p1028:d1694:head, ..p1029:d1695:tail] if e4161:(e4160:r1713:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4159:(e4158:(e4156:r1711:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e4155:(e4154:r1710:head->d1694:head.s181.name->d682)) e4157:r1712:section_name->d1692:section_name)) -> e4180:(e4179:(e4178:builtin_op::list_merge e4176:(e4175:builtin_op::list_singleton e4174:(e4162:r1714:section->d681:"std.text.config.section" e4173:{name: e4164:(e4163:r1715:head->d1694:head.s182.name->d682), entries: e4172:(e4171:(e4167:r1717:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4166:(e4165:r1716:head->d1694:head.s183.entries->d684)) e4170:(e4169:builtin_op::list_singleton e4168:r1718:entry->d1693:entry))}))) e4177:r1719:tail->d1695:tail); p1033:[p1031:d1696:head, ..p1032:d1697:tail] -> e4193:(e4192:(e4191:builtin_op::list_merge e4183:(e4182:builtin_op::list_singleton e4181:r1720:head->d1696:head)) e4190:(e4188:(e4186:(e4184:r1721:put_entry_list->d697:"std.text.config.put_entry_list" e4185:r1722:tail->d1697:tail) e4187:r1723:section_name->d1692:section_name) e4189:r1724:entry->d1693:entry)) })))
      my d698:"std.text.config.put_entry": std::text::config::config -> std::text::str::str -> (std::text::str::str, std::text::str::str) -> std::text::config::config = e4211:(fn p1034:d1698:c -> e4210:(fn p1035:d1699:section_name -> e4209:(fn p1036:d1700:entry -> e4208:(e4198:r1725:config->d686:"std.text.config.config" e4207:{sections_: e4206:(e4204:(e4202:(e4199:r1726:put_entry_list->d697:"std.text.config.put_entry_list" e4201:(e4200:r1727:c->d1698:c.s184.sections_->d687)) e4203:r1728:section_name->d1699:section_name) e4205:r1729:entry->d1700:entry)}))))
      my d699:"std.text.config.header_name": std::text::str::str -> std::data::opt::opt std::text::str::str = e4244:(fn p1037:d1701:clean -> e4243:case e4226:(e4225:r1733:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4224:(e4223:(e4216:r1731:"#op:infix:and"->d425:"std.core.ops.#op:infix:and" e4221:(fn p1038:() -> e4215:(e4213:(e4212:r1730:clean->d1701:clean.s185.starts_with->d820:"std.text.str.str.starts_with") e4214:"["))) e4222:(fn p1039:() -> e4220:(e4218:(e4217:r1732:clean->d1701:clean.s186.ends_with->d821:"std.text.str.str.ends_with") e4219:"]")))) { p1040:true -> e4241:(e4227:r1734:just->d504:"std.data.opt.opt.just" e4240:(e4239:(e4232:(e4230:(e4228:r1735:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e4229:r1736:clean->d1701:clean) e4231:1) e4238:(e4237:(e4235:r1738:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e4234:(e4233:r1737:clean->d1701:clean.s187.len->d838:"std.text.str.str.len")) e4236:1)).s188.trim->d826:"std.text.str.str.trim")); p1041:false -> e4242:r1739:nil->d503:"std.data.opt.opt.nil" })
      my d700:"std.text.config.trim_entry": (std::text::str::str, std::text::str::str) -> (std::text::str::str, std::text::str::str) = e4252:(fn p1042:d1702:pair -> e4251:case e4245:r1740:pair->d1702:pair { p1045:(p1043:d1703:key, p1044:d1704:value) -> e4250:(e4247:(e4246:r1741:key->d1703:key.s189.trim->d826:"std.text.str.str.trim"), e4249:(e4248:r1742:value->d1704:value.s190.trim->d826:"std.text.str.str.trim")) })
      my d701:"std.text.config.parse_line": (std::text::config::config, std::text::str::str) -> std::text::str::str -> (std::text::config::config, std::text::str::str) = e4304:(fn p1046:d1705:state -> e4303:(fn p1047:d1706:line -> e4302:case e4253:r1743:state->d1705:state { p1050:(p1048:d1707:cfg, p1049:d1708:current_section) -> e4301:block { let my p1051:d1709:clean = e4255:(e4254:r1744:line->d1706:line.s191.trim->d826:"std.text.str.str.trim"); e4300:case e4262:(e4261:r1747:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4260:(e4259:(e4257:r1746:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e4256:r1745:clean->d1709:clean) e4258:"")) { p1060:true -> e4263:r1748:state->d1705:state; p1061:false -> e4299:case e4269:(e4268:r1750:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4267:(e4265:(e4264:r1749:clean->d1709:clean.s192.starts_with->d820:"std.text.str.str.starts_with") e4266:"#")) { p1058:true -> e4270:r1751:state->d1705:state; p1059:false -> e4298:case e4273:(e4271:r1752:header_name->d699:"std.text.config.header_name" e4272:r1753:clean->d1709:clean) { p1053:r1754:just->d504:"std.data.opt.opt.just"(p1052:d1710:name) -> e4280:(e4278:(e4276:(e4274:r1755:ensure_section->d696:"std.text.config.ensure_section" e4275:r1756:cfg->d1707:cfg) e4277:r1757:name->d1710:name), e4279:r1758:name->d1710:name); p1054:r1759:nil->d503:"std.data.opt.opt.nil" -> e4297:case e4284:(e4282:(e4281:r1760:clean->d1709:clean.s193.split_once->d823:"std.text.str.str.split_once") e4283:"=") { p1056:r1761:just->d504:"std.data.opt.opt.just"(p1055:d1711:pair) -> e4295:(e4293:(e4289:(e4287:(e4285:r1762:put_entry->d698:"std.text.config.put_entry" e4286:r1763:cfg->d1707:cfg) e4288:r1764:current_section->d1708:current_section) e4292:(e4290:r1765:trim_entry->d700:"std.text.config.trim_entry" e4291:r1766:pair->d1711:pair)), e4294:r1767:current_section->d1708:current_section); p1057:r1768:nil->d503:"std.data.opt.opt.nil" -> e4296:r1769:state->d1705:state } } } } } }))
      pub d702:"std.text.config.parse": std::text::str::str -> std::text::config::config = e4320:(fn p1062:d1712:source -> e4319:block { let my p1065:(p1063:d1713:cfg, p1064:_) = e4317:(e4315:(e4309:(e4308:(e4306:(e4305:r1770:source->d1712:source.s194.split->d822:"std.text.str.str.split") e4307:"\n").s195.fold=>d449:"std.data.fold.Fold.fold") e4314:(e4312:(e4310:r1771:empty->d693:"std.text.config.empty" e4311:()), e4313:"")) e4316:r1772:parse_line->d701:"std.text.config.parse_line"); e4318:r1773:cfg->d1713:cfg })
      my d703:"std.text.config.get_entry_rev": std::data::list::list (std::text::str::str, std::text::str::str) -> std::text::str::str -> std::data::opt::opt std::text::str::str = e4340:(fn p1066:d1714:entries -> e4339:(fn p1067:d1715:key -> e4338:case e4321:r1774:entries->d1714:entries { p1068:[] -> e4322:r1775:nil->d503:"std.data.opt.opt.nil"; p1073:[p1071:(p1069:d1716:candidate, p1070:d1717:value), ..p1072:d1718:rest] if e4329:(e4328:r1779:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4327:(e4326:(e4324:r1777:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e4323:r1776:candidate->d1716:candidate) e4325:r1778:key->d1715:key)) -> e4332:(e4330:r1780:just->d504:"std.data.opt.opt.just" e4331:r1781:value->d1717:value); p1076:[p1074:_, ..p1075:d1719:rest] -> e4337:(e4335:(e4333:r1782:get_entry_rev->d703:"std.text.config.get_entry_rev" e4334:r1783:rest->d1719:rest) e4336:r1784:key->d1715:key) }))
      my d704:"std.text.config.get_entry": std::data::list::list (std::text::str::str, std::text::str::str) -> std::text::str::str -> std::data::opt::opt std::text::str::str = e4349:(fn p1077:d1720:entries -> e4348:(fn p1078:d1721:key -> e4347:(e4345:(e4341:r1785:get_entry_rev->d703:"std.text.config.get_entry_rev" e4344:(e4342:r1786:"std::data::list::rev"->d494:"std.data.list.rev" e4343:r1787:entries->d1720:entries)) e4346:r1788:key->d1721:key)))
      my d705:"std.text.config.get_section_rev": std::data::list::list std::text::config::section -> std::text::str::str -> std::text::str::str -> std::data::opt::opt std::text::str::str = e4376:(fn p1079:d1722:sections -> e4375:(fn p1080:d1723:section_name -> e4374:(fn p1081:d1724:key -> e4373:case e4350:r1789:sections->d1722:sections { p1082:[] -> e4351:r1790:nil->d503:"std.data.opt.opt.nil"; p1085:[p1083:d1725:head, ..p1084:d1726:rest] if e4359:(e4358:r1794:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4357:(e4356:(e4354:r1792:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e4353:(e4352:r1791:head->d1725:head.s196.name->d682)) e4355:r1793:section_name->d1723:section_name)) -> e4365:(e4363:(e4360:r1795:get_entry->d704:"std.text.config.get_entry" e4362:(e4361:r1796:head->d1725:head.s197.entries->d684)) e4364:r1797:key->d1724:key); p1088:[p1086:_, ..p1087:d1727:rest] -> e4372:(e4370:(e4368:(e4366:r1798:get_section_rev->d705:"std.text.config.get_section_rev" e4367:r1799:rest->d1727:rest) e4369:r1800:section_name->d1723:section_name) e4371:r1801:key->d1724:key) })))
      pub d706:"std.text.config.get": std::text::config::config -> std::text::str::str -> std::text::str::str -> std::data::opt::opt std::text::str::str = e4389:(fn p1089:d1728:c -> e4388:(fn p1090:d1729:section_name -> e4387:(fn p1091:d1730:key -> e4386:(e4384:(e4382:(e4377:r1802:get_section_rev->d705:"std.text.config.get_section_rev" e4381:(e4378:r1803:"std::data::list::rev"->d494:"std.data.list.rev" e4380:(e4379:r1804:c->d1728:c.s198.sections_->d687))) e4383:r1805:section_name->d1729:section_name) e4385:r1806:key->d1730:key))))
      pub d707:"std.text.config.load": std::text::str::str -> [std::io::file::file, std::io::file::io_err] std::text::config::config = e4399:(fn p1092:d1731:path -> e4398:(e4390:r1807:parse->d702:"std.text.config.parse" e4397:(e4391:r1808:"std::io::file::read_text"->d594:"std.io.file.read_text" e4396:(e4392:r1809:"std::text::path::of_bytes"->d781:"std.text.path.of_bytes" e4395:(e4393:r1810:"std::text::str::to_bytes"->d794:"std.text.str.to_bytes" e4394:r1811:path->d1731:path)))))
    }
    pub d113:"std.text.parse" mod {
      pub d708:"std.text.parse.parse" mod {
      }
      pub d717:"std.text.parse.ParseError" mod {
        pub d718:"std.text.parse.ParseError.merge": 'a -> 'a -> 'a where 'a: std::text::parse::ParseError(item = 'b, pos = 'c) = <missing>
        pub d719:"std.text.parse.ParseError.unexpected": std::data::opt::opt 'a -> 'b -> 'c where 'c: std::text::parse::ParseError(item = 'a, pos = 'b) = <missing>
        pub d720:"std.text.parse.ParseError.expected": std::text::str::str -> 'a -> 'b where 'b: std::text::parse::ParseError(item = 'c, pos = 'a) = <missing>
        pub d721:"std.text.parse.ParseError.label": 'a -> std::text::str::str -> 'a where 'a: std::text::parse::ParseError(item = 'b, pos = 'c) = <missing>
      }
      pub d722:"std.text.parse.str_error": {line: int, column: int, unexpected: std::data::opt::opt std::text::char::char, expected: std::data::list::list std::text::str::str, message: std::data::list::list std::text::str::str} -> std::text::parse::str_error = <missing>
      pub d733:"std.text.parse.str_error" mod {
        my d734 mod {
          d735: std::text::parse::str_error -> std::text::parse::str_error -> std::text::parse::str_error = e4468:(fn p1093:d1732:e -> e4467:(fn p1094:d1733:f -> e4466:case e4408:(e4407:r1815:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4406:(e4405:(e4402:r1813:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e4401:(e4400:r1812:e->d1732:e.s199.line->d723)) e4404:(e4403:r1814:f->d1733:f.s200.line->d723))) { p1101:true -> e4409:r1816:f->d1733:f; p1102:false -> e4465:case e4418:(e4417:r1820:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4416:(e4415:(e4412:r1818:"#op:infix:>"->d423:"std.core.ops.#op:infix:>" e4411:(e4410:r1817:e->d1732:e.s201.line->d723)) e4414:(e4413:r1819:f->d1733:f.s202.line->d723))) { p1099:true -> e4419:r1821:e->d1732:e; p1100:false -> e4464:case e4428:(e4427:r1825:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4426:(e4425:(e4422:r1823:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e4421:(e4420:r1822:e->d1732:e.s203.column->d725)) e4424:(e4423:r1824:f->d1733:f.s204.column->d725))) { p1097:true -> e4429:r1826:f->d1733:f; p1098:false -> e4463:case e4438:(e4437:r1830:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4436:(e4435:(e4432:r1828:"#op:infix:>"->d423:"std.core.ops.#op:infix:>" e4431:(e4430:r1827:e->d1732:e.s205.column->d725)) e4434:(e4433:r1829:f->d1733:f.s206.column->d725))) { p1095:true -> e4439:r1831:e->d1732:e; p1096:false -> e4462:(e4440:r1832:str_error->d722:"std.text.parse.str_error" e4461:{line: e4442:(e4441:r1833:e->d1732:e.s207.line->d723), column: e4444:(e4443:r1834:e->d1732:e.s208.column->d725), unexpected: e4446:(e4445:r1835:e->d1732:e.s209.unexpected->d727), expected: e4453:(e4452:(e4449:r1837:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4448:(e4447:r1836:e->d1732:e.s210.expected->d729)) e4451:(e4450:r1838:f->d1733:f.s211.expected->d729)), message: e4460:(e4459:(e4456:r1840:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4455:(e4454:r1839:e->d1732:e.s212.message->d731)) e4458:(e4457:r1841:f->d1733:f.s213.message->d731))}) } } } }))
          d736: std::data::opt::opt std::text::char::char -> (int, int) -> std::text::parse::str_error = e4482:(fn p1103:d1734:u -> e4481:(fn p1106:(p1104:d1735:l, p1105:d1736:c) -> e4480:(e4469:r1842:str_error->d722:"std.text.parse.str_error" e4479:{line: e4470:r1843:l->d1735:l, column: e4471:r1844:c->d1736:c, unexpected: e4472:r1845:u->d1734:u, expected: e4475:(e4473:builtin_op::list_empty e4474:()), message: e4478:(e4476:builtin_op::list_empty e4477:())})))
          d737: std::text::str::str -> (int, int) -> std::text::parse::str_error = e4496:(fn p1107:d1737:label -> e4495:(fn p1110:(p1108:d1738:l, p1109:d1739:c) -> e4494:(e4483:r1846:str_error->d722:"std.text.parse.str_error" e4493:{line: e4484:r1847:l->d1738:l, column: e4485:r1848:c->d1739:c, unexpected: e4486:r1849:nil->d503:"std.data.opt.opt.nil", expected: e4489:(e4488:builtin_op::list_singleton e4487:r1850:label->d1737:label), message: e4492:(e4490:builtin_op::list_empty e4491:())})))
          d738: std::text::parse::str_error -> std::text::str::str -> std::text::parse::str_error = e4512:(fn p1111:d1740:e -> e4511:(fn p1112:d1741:label -> e4510:(e4497:r1851:str_error->d722:"std.text.parse.str_error" e4509:{line: e4499:(e4498:r1852:e->d1740:e.s214.line->d723), column: e4501:(e4500:r1853:e->d1740:e.s215.column->d725), unexpected: e4503:(e4502:r1854:e->d1740:e.s216.unexpected->d727), expected: e4506:(e4505:builtin_op::list_singleton e4504:r1855:label->d1741:label), message: e4508:(e4507:r1856:e->d1740:e.s217.message->d731)})))
        }
      }
      pub d739:"std.text.parse.prefix_result": {value: 'a, rest: std::text::str::str} -> std::text::parse::prefix_result 'a = <missing>
      pub d744:"std.text.parse.match_result": {value: 'a, start: int, end: int, text: std::text::str::str} -> std::text::parse::match_result 'a = <missing>
      my d753:"std.text.parse.advance_position": std::text::str::str -> int -> int -> int -> (int, int) = e4553:(fn p1113:d1742:input -> e4552:(fn p1114:d1743:count -> e4551:(fn p1115:d1744:line -> e4550:(fn p1116:d1745:column -> e4549:block { let my p1117:d1746:data = e4515:(e4513:r1857:"std::text::str::to_bytes"->d794:"std.text.str.to_bytes" e4514:r1858:input->d1742:input); e4548:case e4525:(e4524:r1863:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4523:(e4522:(e4519:r1861:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e4518:(e4516:r1859:"std::text::bytes::len"->d653:"std.text.bytes.len" e4517:r1860:data->d1746:data)) e4521:(e4520:r1862:input->d1742:input.s218.len->d838:"std.text.str.str.len"))) { p1118:true -> e4536:(e4534:(e4532:(e4530:(e4528:(e4526:r1864:advance_position_ascii_chunks->d754:"std.text.parse.advance_position_ascii_chunks" e4527:r1865:data->d1746:data) e4529:r1866:count->d1743:count) e4531:0) e4533:r1867:line->d1744:line) e4535:r1868:column->d1745:column); p1119:false -> e4547:(e4545:(e4543:(e4541:(e4539:(e4537:r1869:advance_position_slow_chunks->d756:"std.text.parse.advance_position_slow_chunks" e4538:r1870:input->d1742:input) e4540:r1871:count->d1743:count) e4542:0) e4544:r1872:line->d1744:line) e4546:r1873:column->d1745:column) } }))))
      my d754:"std.text.parse.advance_position_ascii_chunks": std::text::bytes::bytes -> int -> int -> int -> int -> (int, int) = e4611:(fn p1120:d1747:data -> e4610:(fn p1121:d1748:count -> e4609:(fn p1122:d1749:i -> e4608:(fn p1123:d1750:line -> e4607:(fn p1124:d1751:column -> e4606:case e4560:(e4559:r1877:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4558:(e4557:(e4555:r1875:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e4554:r1874:i->d1749:i) e4556:r1876:count->d1748:count)) { p1131:true -> e4602:block { let my p1125:d1752:chunk_end = e4578:case e4571:(e4570:r1882:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4569:(e4568:(e4566:r1880:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e4565:(e4564:(e4562:r1879:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4561:r1878:i->d1749:i) e4563:1024)) e4567:r1881:count->d1748:count)) { p1126:true -> e4576:(e4575:(e4573:r1884:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4572:r1883:i->d1749:i) e4574:1024); p1127:false -> e4577:r1885:count->d1748:count }; e4601:case e4589:(e4587:(e4585:(e4583:(e4581:(e4579:r1886:advance_position_ascii_loop->d755:"std.text.parse.advance_position_ascii_loop" e4580:r1887:data->d1747:data) e4582:r1888:chunk_end->d1752:chunk_end) e4584:r1889:i->d1749:i) e4586:r1890:line->d1750:line) e4588:r1891:column->d1751:column) { p1130:(p1128:d1753:line, p1129:d1754:column) -> e4600:(e4598:(e4596:(e4594:(e4592:(e4590:r1892:advance_position_ascii_chunks->d754:"std.text.parse.advance_position_ascii_chunks" e4591:r1893:data->d1747:data) e4593:r1894:count->d1748:count) e4595:r1895:chunk_end->d1752:chunk_end) e4597:r1896:line->d1753:line) e4599:r1897:column->d1754:column) } }; p1132:false -> e4605:(e4603:r1898:line->d1750:line, e4604:r1899:column->d1751:column) })))))
      my d755:"std.text.parse.advance_position_ascii_loop": std::text::bytes::bytes -> int -> int -> int -> int -> (int, int) = e4671:(fn p1133:d1755:data -> e4670:(fn p1134:d1756:count -> e4669:(fn p1135:d1757:i -> e4668:(fn p1136:d1758:line -> e4667:(fn p1137:d1759:column -> e4666:case e4618:(e4617:r1903:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4616:(e4615:(e4613:r1901:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e4612:r1900:i->d1757:i) e4614:r1902:count->d1756:count)) { p1142:true -> e4662:case e4623:(e4621:(e4619:r1904:"std::text::bytes::index_raw"->d656:"std.text.bytes.index_raw" e4620:r1905:data->d1755:data) e4622:r1906:i->d1757:i) { p1140:(p1138:10 | p1139:13) -> e4642:(e4640:(e4634:(e4628:(e4626:(e4624:r1907:advance_position_ascii_loop->d755:"std.text.parse.advance_position_ascii_loop" e4625:r1908:data->d1755:data) e4627:r1909:count->d1756:count) e4633:(e4632:(e4630:r1911:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4629:r1910:i->d1757:i) e4631:1)) e4639:(e4638:(e4636:r1913:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4635:r1912:line->d1758:line) e4637:1)) e4641:1); p1141:_ -> e4661:(e4655:(e4653:(e4647:(e4645:(e4643:r1914:advance_position_ascii_loop->d755:"std.text.parse.advance_position_ascii_loop" e4644:r1915:data->d1755:data) e4646:r1916:count->d1756:count) e4652:(e4651:(e4649:r1918:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4648:r1917:i->d1757:i) e4650:1)) e4654:r1919:line->d1758:line) e4660:(e4659:(e4657:r1921:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4656:r1920:column->d1759:column) e4658:1)) }; p1143:false -> e4665:(e4663:r1922:line->d1758:line, e4664:r1923:column->d1759:column) })))))
      my d756:"std.text.parse.advance_position_slow_chunks": std::text::str::str -> int -> int -> int -> int -> (int, int) = e4729:(fn p1144:d1760:input -> e4728:(fn p1145:d1761:count -> e4727:(fn p1146:d1762:i -> e4726:(fn p1147:d1763:line -> e4725:(fn p1148:d1764:column -> e4724:case e4678:(e4677:r1927:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4676:(e4675:(e4673:r1925:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e4672:r1924:i->d1762:i) e4674:r1926:count->d1761:count)) { p1155:true -> e4720:block { let my p1149:d1765:chunk_end = e4696:case e4689:(e4688:r1932:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4687:(e4686:(e4684:r1930:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e4683:(e4682:(e4680:r1929:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4679:r1928:i->d1762:i) e4681:1024)) e4685:r1931:count->d1761:count)) { p1150:true -> e4694:(e4693:(e4691:r1934:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4690:r1933:i->d1762:i) e4692:1024); p1151:false -> e4695:r1935:count->d1761:count }; e4719:case e4707:(e4705:(e4703:(e4701:(e4699:(e4697:r1936:advance_position_slow_loop->d757:"std.text.parse.advance_position_slow_loop" e4698:r1937:input->d1760:input) e4700:r1938:chunk_end->d1765:chunk_end) e4702:r1939:i->d1762:i) e4704:r1940:line->d1763:line) e4706:r1941:column->d1764:column) { p1154:(p1152:d1766:line, p1153:d1767:column) -> e4718:(e4716:(e4714:(e4712:(e4710:(e4708:r1942:advance_position_slow_chunks->d756:"std.text.parse.advance_position_slow_chunks" e4709:r1943:input->d1760:input) e4711:r1944:count->d1761:count) e4713:r1945:chunk_end->d1765:chunk_end) e4715:r1946:line->d1766:line) e4717:r1947:column->d1767:column) } }; p1156:false -> e4723:(e4721:r1948:line->d1763:line, e4722:r1949:column->d1764:column) })))))
      my d757:"std.text.parse.advance_position_slow_loop": std::text::str::str -> int -> int -> int -> int -> (int, int) = e4792:(fn p1157:d1768:input -> e4791:(fn p1158:d1769:count -> e4790:(fn p1159:d1770:i -> e4789:(fn p1160:d1771:line -> e4788:(fn p1161:d1772:column -> e4787:case e4736:(e4735:r1953:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4734:(e4733:(e4731:r1951:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e4730:r1950:i->d1770:i) e4732:r1952:count->d1769:count)) { p1169:true -> e4783:block { let my p1162:d1773:item = e4741:(e4739:(e4737:r1954:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e4738:r1955:input->d1768:input) e4740:r1956:i->d1770:i); e4782:case e4743:(e4742:r1957:item->d1773:item.s219.to_string->d677:"std.text.char.char.to_string") { p1167:(p1163:"\\r" | p1166:(p1164:"\\r\\n" | p1165:"\\n")) -> e4762:(e4760:(e4754:(e4748:(e4746:(e4744:r1958:advance_position_slow_loop->d757:"std.text.parse.advance_position_slow_loop" e4745:r1959:input->d1768:input) e4747:r1960:count->d1769:count) e4753:(e4752:(e4750:r1962:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4749:r1961:i->d1770:i) e4751:1)) e4759:(e4758:(e4756:r1964:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4755:r1963:line->d1771:line) e4757:1)) e4761:1); p1168:_ -> e4781:(e4775:(e4773:(e4767:(e4765:(e4763:r1965:advance_position_slow_loop->d757:"std.text.parse.advance_position_slow_loop" e4764:r1966:input->d1768:input) e4766:r1967:count->d1769:count) e4772:(e4771:(e4769:r1969:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4768:r1968:i->d1770:i) e4770:1)) e4774:r1970:line->d1771:line) e4780:(e4779:(e4777:r1972:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4776:r1971:column->d1772:column) e4778:1)) } }; p1170:false -> e4786:(e4784:r1973:line->d1771:line, e4785:r1974:column->d1772:column) })))))
      pub d758:"std.text.parse.run_str": std::text::str::str -> int -> int -> 'a [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int); 'b] -> ['b] std::data::result::result 'a std::text::parse::str_error = e4981:(fn p1171:d1774:input -> e4980:(fn p1172:d1775:line -> e4979:(fn p1173:d1776:column -> e4978:(fn p1174:d1777:parser -> e4977:catch e4793:r1975:parser->d1777:parser { std::text::parse::parse::item p1175:_, p1176:d1778:k if e4801:(e4800:r1978:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4799:(e4798:(e4796:r1977:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e4795:(e4794:r1976:input->d1774:input.s220.len->d838:"std.text.str.str.len")) e4797:0)) -> e4815:(e4802:r1979:"result::err"->d530:"std.data.result.result.err" e4814:(e4803:r1980:str_error->d722:"std.text.parse.str_error" e4813:{line: e4804:r1981:line->d1775:line, column: e4805:r1982:column->d1776:column, unexpected: e4806:r1983:nil->d503:"std.data.opt.opt.nil", expected: e4809:(e4807:builtin_op::list_empty e4808:()), message: e4812:(e4810:builtin_op::list_empty e4811:())})); std::text::parse::parse::item p1177:_, p1178:d1779:k -> e4862:block { let my p1179:d1780:item = e4820:(e4818:(e4816:r1984:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e4817:r1985:input->d1774:input) e4819:0); e4861:block { let my p1180:d1781:rest = e4827:(e4823:(e4821:r1986:"std::text::str::index_range"->d790:"std.text.str.index_range" e4822:r1987:input->d1774:input) e4826:(e4824:r1988:"std::data::range::from_excluded"->d516:"std.data.range.from_excluded" e4825:0)); e4860:case e4829:(e4828:r1989:item->d1780:item.s221.to_string->d677:"std.text.char.char.to_string") { p1185:(p1181:"\\r" | p1184:(p1182:"\\r\\n" | p1183:"\\n")) -> e4844:(e4840:(e4838:(e4832:(e4830:r1990:run_str->d758:"std.text.parse.run_str" e4831:r1991:rest->d1781:rest) e4837:(e4836:(e4834:r1993:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4833:r1992:line->d1775:line) e4835:1)) e4839:1) e4843:(e4841:r1994:k->d1779:k e4842:r1995:item->d1780:item)); p1186:_ -> e4859:(e4855:(e4849:(e4847:(e4845:r1996:run_str->d758:"std.text.parse.run_str" e4846:r1997:rest->d1781:rest) e4848:r1998:line->d1775:line) e4854:(e4853:(e4851:r2000:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4850:r1999:column->d1776:column) e4852:1)) e4858:(e4856:r2001:k->d1779:k e4857:r2002:item->d1780:item)) } } }; std::text::parse::parse::fail p1187:d1782:e, p1188:_ -> e4865:(e4863:r2003:"result::err"->d530:"std.data.result.result.err" e4864:r2004:e->d1782:e); std::text::parse::parse::eof p1189:_, p1190:d1783:k -> e4881:(e4872:(e4870:(e4868:(e4866:r2005:run_str->d758:"std.text.parse.run_str" e4867:r2006:input->d1774:input) e4869:r2007:line->d1775:line) e4871:r2008:column->d1776:column) e4880:(e4873:r2009:k->d1783:k e4879:(e4878:(e4876:r2011:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e4875:(e4874:r2010:input->d1774:input.s222.len->d838:"std.text.str.str.len")) e4877:0))); std::text::parse::parse::pos p1191:_, p1192:d1784:k -> e4894:(e4888:(e4886:(e4884:(e4882:r2012:run_str->d758:"std.text.parse.run_str" e4883:r2013:input->d1774:input) e4885:r2014:line->d1775:line) e4887:r2015:column->d1776:column) e4893:(e4889:r2016:k->d1784:k e4892:(e4890:r2017:line->d1775:line, e4891:r2018:column->d1776:column))); std::text::parse::parse::cut p1193:_, p1194:d1785:k -> e4905:(e4901:(e4899:(e4897:(e4895:r2019:run_str->d758:"std.text.parse.run_str" e4896:r2020:input->d1774:input) e4898:r2021:line->d1775:line) e4900:r2022:column->d1776:column) e4904:(e4902:r2023:k->d1785:k e4903:())); std::text::parse::parse::snapshot p1195:_, p1196:d1786:k -> e4919:(e4912:(e4910:(e4908:(e4906:r2024:run_str->d758:"std.text.parse.run_str" e4907:r2025:input->d1774:input) e4909:r2026:line->d1775:line) e4911:r2027:column->d1776:column) e4918:(e4913:r2028:k->d1786:k e4917:(e4914:r2029:input->d1774:input, e4915:r2030:line->d1775:line, e4916:r2031:column->d1776:column))); std::text::parse::parse::restore p1200:(p1197:d1787:input, p1198:d1788:line, p1199:d1789:column), p1201:d1790:k -> e4930:(e4926:(e4924:(e4922:(e4920:r2032:run_str->d758:"std.text.parse.run_str" e4921:r2033:input->d1787:input) e4923:r2034:line->d1788:line) e4925:r2035:column->d1789:column) e4929:(e4927:r2036:k->d1790:k e4928:())); std::text::parse::parse::advance p1202:d1791:count, p1203:d1792:k -> e4973:block { let my p1204:d1793:input_len = e4932:(e4931:r2037:input->d1774:input.s223.len->d838:"std.text.str.str.len"); e4972:block { let my p1205:d1794:end = e4942:case e4939:(e4938:r2041:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4937:(e4936:(e4934:r2039:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e4933:r2038:count->d1791:count) e4935:r2040:input_len->d1793:input_len)) { p1206:true -> e4940:r2042:count->d1791:count; p1207:false -> e4941:r2043:input_len->d1793:input_len }; e4971:block { let my p1208:d1795:rest = e4949:(e4947:(e4945:(e4943:r2044:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e4944:r2045:input->d1774:input) e4946:r2046:end->d1794:end) e4948:r2047:input_len->d1793:input_len); e4970:block { let my p1211:(p1209:d1796:line, p1210:d1797:column) = e4958:(e4956:(e4954:(e4952:(e4950:r2048:advance_position->d753:"std.text.parse.advance_position" e4951:r2049:input->d1774:input) e4953:r2050:end->d1794:end) e4955:r2051:line->d1775:line) e4957:r2052:column->d1776:column); e4969:(e4965:(e4963:(e4961:(e4959:r2053:run_str->d758:"std.text.parse.run_str" e4960:r2054:rest->d1795:rest) e4962:r2055:line->d1796:line) e4964:r2056:column->d1797:column) e4968:(e4966:r2057:k->d1792:k e4967:())) } } } }; p1212:d1798:v -> e4976:(e4974:r2058:"result::ok"->d529:"std.data.result.result.ok" e4975:r2059:v->d1798:v) }))))
      pub d759:"std.text.parse.run_prefix_str": std::text::str::str -> int -> int -> 'a [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int); 'b] -> ['b] std::data::result::result(std::text::parse::prefix_result 'a, std::text::parse::str_error) = e5174:(fn p1213:d1799:input -> e5173:(fn p1214:d1800:line -> e5172:(fn p1215:d1801:column -> e5171:(fn p1216:d1802:parser -> e5170:catch e4982:r2060:parser->d1802:parser { std::text::parse::parse::item p1217:_, p1218:d1803:k if e4990:(e4989:r2063:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4988:(e4987:(e4985:r2062:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e4984:(e4983:r2061:input->d1799:input.s224.len->d838:"std.text.str.str.len")) e4986:0)) -> e5004:(e4991:r2064:"result::err"->d530:"std.data.result.result.err" e5003:(e4992:r2065:str_error->d722:"std.text.parse.str_error" e5002:{line: e4993:r2066:line->d1800:line, column: e4994:r2067:column->d1801:column, unexpected: e4995:r2068:nil->d503:"std.data.opt.opt.nil", expected: e4998:(e4996:builtin_op::list_empty e4997:()), message: e5001:(e4999:builtin_op::list_empty e5000:())})); std::text::parse::parse::item p1219:_, p1220:d1804:k -> e5051:block { let my p1221:d1805:item = e5009:(e5007:(e5005:r2069:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e5006:r2070:input->d1799:input) e5008:0); e5050:block { let my p1222:d1806:rest = e5016:(e5012:(e5010:r2071:"std::text::str::index_range"->d790:"std.text.str.index_range" e5011:r2072:input->d1799:input) e5015:(e5013:r2073:"std::data::range::from_excluded"->d516:"std.data.range.from_excluded" e5014:0)); e5049:case e5018:(e5017:r2074:item->d1805:item.s225.to_string->d677:"std.text.char.char.to_string") { p1227:(p1223:"\\r" | p1226:(p1224:"\\r\\n" | p1225:"\\n")) -> e5033:(e5029:(e5027:(e5021:(e5019:r2075:run_prefix_str->d759:"std.text.parse.run_prefix_str" e5020:r2076:rest->d1806:rest) e5026:(e5025:(e5023:r2078:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e5022:r2077:line->d1800:line) e5024:1)) e5028:1) e5032:(e5030:r2079:k->d1804:k e5031:r2080:item->d1805:item)); p1228:_ -> e5048:(e5044:(e5038:(e5036:(e5034:r2081:run_prefix_str->d759:"std.text.parse.run_prefix_str" e5035:r2082:rest->d1806:rest) e5037:r2083:line->d1800:line) e5043:(e5042:(e5040:r2085:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e5039:r2084:column->d1801:column) e5041:1)) e5047:(e5045:r2086:k->d1804:k e5046:r2087:item->d1805:item)) } } }; std::text::parse::parse::fail p1229:d1807:e, p1230:_ -> e5054:(e5052:r2088:"result::err"->d530:"std.data.result.result.err" e5053:r2089:e->d1807:e); std::text::parse::parse::eof p1231:_, p1232:d1808:k -> e5070:(e5061:(e5059:(e5057:(e5055:r2090:run_prefix_str->d759:"std.text.parse.run_prefix_str" e5056:r2091:input->d1799:input) e5058:r2092:line->d1800:line) e5060:r2093:column->d1801:column) e5069:(e5062:r2094:k->d1808:k e5068:(e5067:(e5065:r2096:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e5064:(e5063:r2095:input->d1799:input.s226.len->d838:"std.text.str.str.len")) e5066:0))); std::text::parse::parse::pos p1233:_, p1234:d1809:k -> e5083:(e5077:(e5075:(e5073:(e5071:r2097:run_prefix_str->d759:"std.text.parse.run_prefix_str" e5072:r2098:input->d1799:input) e5074:r2099:line->d1800:line) e5076:r2100:column->d1801:column) e5082:(e5078:r2101:k->d1809:k e5081:(e5079:r2102:line->d1800:line, e5080:r2103:column->d1801:column))); std::text::parse::parse::cut p1235:_, p1236:d1810:k -> e5094:(e5090:(e5088:(e5086:(e5084:r2104:run_prefix_str->d759:"std.text.parse.run_prefix_str" e5085:r2105:input->d1799:input) e5087:r2106:line->d1800:line) e5089:r2107:column->d1801:column) e5093:(e5091:r2108:k->d1810:k e5092:())); std::text::parse::parse::snapshot p1237:_, p1238:d1811:k -> e5108:(e5101:(e5099:(e5097:(e5095:r2109:run_prefix_str->d759:"std.text.parse.run_prefix_str" e5096:r2110:input->d1799:input) e5098:r2111:line->d1800:line) e5100:r2112:column->d1801:column) e5107:(e5102:r2113:k->d1811:k e5106:(e5103:r2114:input->d1799:input, e5104:r2115:line->d1800:line, e5105:r2116:column->d1801:column))); std::text::parse::parse::restore p1242:(p1239:d1812:input, p1240:d1813:line, p1241:d1814:column), p1243:d1815:k -> e5119:(e5115:(e5113:(e5111:(e5109:r2117:run_prefix_str->d759:"std.text.parse.run_prefix_str" e5110:r2118:input->d1812:input) e5112:r2119:line->d1813:line) e5114:r2120:column->d1814:column) e5118:(e5116:r2121:k->d1815:k e5117:())); std::text::parse::parse::advance p1244:d1816:count, p1245:d1817:k -> e5162:block { let my p1246:d1818:input_len = e5121:(e5120:r2122:input->d1799:input.s227.len->d838:"std.text.str.str.len"); e5161:block { let my p1247:d1819:end = e5131:case e5128:(e5127:r2126:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e5126:(e5125:(e5123:r2124:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e5122:r2123:count->d1816:count) e5124:r2125:input_len->d1818:input_len)) { p1248:true -> e5129:r2127:count->d1816:count; p1249:false -> e5130:r2128:input_len->d1818:input_len }; e5160:block { let my p1250:d1820:rest = e5138:(e5136:(e5134:(e5132:r2129:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5133:r2130:input->d1799:input) e5135:r2131:end->d1819:end) e5137:r2132:input_len->d1818:input_len); e5159:block { let my p1253:(p1251:d1821:line, p1252:d1822:column) = e5147:(e5145:(e5143:(e5141:(e5139:r2133:advance_position->d753:"std.text.parse.advance_position" e5140:r2134:input->d1799:input) e5142:r2135:end->d1819:end) e5144:r2136:line->d1800:line) e5146:r2137:column->d1801:column); e5158:(e5154:(e5152:(e5150:(e5148:r2138:run_prefix_str->d759:"std.text.parse.run_prefix_str" e5149:r2139:rest->d1820:rest) e5151:r2140:line->d1821:line) e5153:r2141:column->d1822:column) e5157:(e5155:r2142:k->d1817:k e5156:())) } } } }; p1254:d1823:v -> e5169:(e5163:r2143:"result::ok"->d529:"std.data.result.result.ok" e5168:(e5164:r2144:prefix_result->d739:"std.text.parse.prefix_result" e5167:{value: e5165:r2145:v->d1823:v, rest: e5166:r2146:input->d1799:input})) }))))
      pub d760:"std.text.parse.read_prefix": std::text::str::str -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] 'a) -> std::data::result::result(std::text::parse::prefix_result 'a, std::text::parse::str_error) = e5187:(fn p1255:d1824:source -> e5186:(fn p1256:d1825:parser -> e5185:(e5181:(e5179:(e5177:(e5175:r2147:run_prefix_str->d759:"std.text.parse.run_prefix_str" e5176:r2148:source->d1824:source) e5178:1) e5180:1) e5184:(e5182:r2149:parser->d1825:parser e5183:()))))
      my d761:"std.text.parse.find_from": std::text::str::str -> int -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] 'a) -> std::data::opt::opt(std::text::parse::match_result 'a) = e5288:(fn p1257:d1826:source -> e5287:(fn p1258:d1827:start -> e5286:(fn p1259:d1828:parser -> e5285:case e5195:(e5194:r2153:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e5193:(e5192:(e5189:r2151:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e5188:r2150:start->d1827:start) e5191:(e5190:r2152:source->d1826:source.s228.len->d838:"std.text.str.str.len"))) { p1268:true -> e5283:block { let my p1260:d1829:rest = e5203:(e5200:(e5198:(e5196:r2154:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5197:r2155:source->d1826:source) e5199:r2156:start->d1827:start) e5202:(e5201:r2157:source->d1826:source.s229.len->d838:"std.text.str.str.len")); e5282:case e5218:(e5214:(e5208:(e5206:(e5204:r2158:run_prefix_str->d759:"std.text.parse.run_prefix_str" e5205:r2159:rest->d1829:rest) e5207:1) e5213:(e5212:(e5210:r2161:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e5209:r2160:start->d1827:start) e5211:1)) e5217:(e5215:r2162:parser->d1828:parser e5216:())) { p1262:r2163:"result::ok"->d529:"std.data.result.result.ok"(p1261:d1830:found) -> e5270:block { let my p1263:d1831:consumed = e5226:(e5225:(e5221:r2165:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e5220:(e5219:r2164:rest->d1829:rest.s230.len->d838:"std.text.str.str.len")) e5224:(e5223:(e5222:r2166:found->d1830:found.s231.rest->d742).s232.len->d838:"std.text.str.str.len")); e5269:case e5233:(e5232:r2169:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e5231:(e5230:(e5228:r2168:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e5227:r2167:consumed->d1831:consumed) e5229:0)) { p1264:true -> e5244:(e5242:(e5236:(e5234:r2170:find_from->d761:"std.text.parse.find_from" e5235:r2171:source->d1826:source) e5241:(e5240:(e5238:r2173:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e5237:r2172:start->d1827:start) e5239:1)) e5243:r2174:parser->d1828:parser); p1265:false -> e5268:(e5245:r2175:just->d504:"std.data.opt.opt.just" e5267:(e5246:r2176:match_result->d744:"std.text.parse.match_result" e5266:{value: e5248:(e5247:r2177:found->d1830:found.s233.value->d740), start: e5249:r2178:start->d1827:start, end: e5254:(e5253:(e5251:r2180:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e5250:r2179:start->d1827:start) e5252:r2181:consumed->d1831:consumed), text: e5265:(e5259:(e5257:(e5255:r2182:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5256:r2183:source->d1826:source) e5258:r2184:start->d1827:start) e5264:(e5263:(e5261:r2186:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e5260:r2185:start->d1827:start) e5262:r2187:consumed->d1831:consumed))})) } }; p1267:r2188:"result::err"->d530:"std.data.result.result.err"(p1266:_) -> e5281:(e5279:(e5273:(e5271:r2189:find_from->d761:"std.text.parse.find_from" e5272:r2190:source->d1826:source) e5278:(e5277:(e5275:r2192:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e5274:r2191:start->d1827:start) e5276:1)) e5280:r2193:parser->d1828:parser) } }; p1269:false -> e5284:r2194:nil->d503:"std.data.opt.opt.nil" })))
      pub d762:"std.text.parse.find": std::text::str::str -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] 'a) -> std::data::opt::opt(std::text::parse::match_result 'a) = e5297:(fn p1270:d1832:source -> e5296:(fn p1271:d1833:parser -> e5295:(e5293:(e5291:(e5289:r2195:find_from->d761:"std.text.parse.find_from" e5290:r2196:source->d1832:source) e5292:0) e5294:r2197:parser->d1833:parser)))
      pub d763:"std.text.parse.edit_once": std::text::str::str -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] 'a) -> ('a -> ['b] std::text::str::str) -> ['b] std::text::str::str = e5336:(fn p1272:d1834:source -> e5335:(fn p1273:d1835:parser -> e5334:(fn p1274:d1836:replacement -> e5333:case e5304:(e5302:(e5300:(e5298:r2198:find_from->d761:"std.text.parse.find_from" e5299:r2199:source->d1834:source) e5301:0) e5303:r2200:parser->d1835:parser) { p1276:r2201:just->d504:"std.data.opt.opt.just"(p1275:d1837:found) -> e5331:(e5321:(e5305:r2202:"std::text::str::concat"->d784:"std.text.str.concat" e5320:(e5315:(e5306:r2203:"std::text::str::concat"->d784:"std.text.str.concat" e5314:(e5311:(e5309:(e5307:r2204:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5308:r2205:source->d1834:source) e5310:0) e5313:(e5312:r2206:found->d1837:found.s234.start->d747))) e5319:(e5316:r2207:replacement->d1836:replacement e5318:(e5317:r2208:found->d1837:found.s235.value->d745)))) e5330:(e5327:(e5324:(e5322:r2209:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5323:r2210:source->d1834:source) e5326:(e5325:r2211:found->d1837:found.s236.end->d749)) e5329:(e5328:r2212:source->d1834:source.s237.len->d838:"std.text.str.str.len"))); p1277:r2213:nil->d503:"std.data.opt.opt.nil" -> e5332:r2214:source->d1834:source })))
      pub d764:"std.text.parse.edit": std::text::str::str -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] 'a) -> ('a -> ['b] std::text::str::str) -> ['b] std::text::str::str = e5391:(fn p1278:d1838:source -> e5390:(fn p1279:d1839:parser -> e5389:(fn p1280:d1840:replacement -> e5388:block { let my p1281:d1841:loop = e5382:(fn p1282:d1842:start -> e5381:(fn p1283:d1843:out -> e5380:case e5343:(e5341:(e5339:(e5337:r2215:find_from->d761:"std.text.parse.find_from" e5338:r2216:source->d1838:source) e5340:r2217:start->d1842:start) e5342:r2218:parser->d1839:parser) { p1285:r2219:just->d504:"std.data.opt.opt.just"(p1284:d1844:found) -> e5367:(e5347:(e5344:r2220:loop->d1841:loop e5346:(e5345:r2221:found->d1844:found.s238.end->d749)) e5366:(e5361:(e5348:r2222:"std::text::str::concat"->d784:"std.text.str.concat" e5360:(e5351:(e5349:r2223:"std::text::str::concat"->d784:"std.text.str.concat" e5350:r2224:out->d1843:out) e5359:(e5356:(e5354:(e5352:r2225:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5353:r2226:source->d1838:source) e5355:r2227:start->d1842:start) e5358:(e5357:r2228:found->d1844:found.s239.start->d747)))) e5365:(e5362:r2229:replacement->d1840:replacement e5364:(e5363:r2230:found->d1844:found.s240.value->d745)))); p1286:r2231:nil->d503:"std.data.opt.opt.nil" -> e5379:(e5370:(e5368:r2232:"std::text::str::concat"->d784:"std.text.str.concat" e5369:r2233:out->d1843:out) e5378:(e5375:(e5373:(e5371:r2234:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5372:r2235:source->d1838:source) e5374:r2236:start->d1842:start) e5377:(e5376:r2237:source->d1838:source.s241.len->d838:"std.text.str.str.len"))) })); e5387:(e5385:(e5383:r2238:loop->d1841:loop e5384:0) e5386:"") })))
      pub d765:"std.text.parse.replace_once": std::text::str::str -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] any) -> std::text::str::str -> std::text::str::str = e5427:(fn p1287:d1845:source -> e5426:(fn p1288:d1846:parser -> e5425:(fn p1289:d1847:replacement -> e5424:case e5398:(e5396:(e5394:(e5392:r2239:find_from->d761:"std.text.parse.find_from" e5393:r2240:source->d1845:source) e5395:0) e5397:r2241:parser->d1846:parser) { p1291:r2242:just->d504:"std.data.opt.opt.just"(p1290:d1848:found) -> e5422:(e5412:(e5399:r2243:"std::text::str::concat"->d784:"std.text.str.concat" e5411:(e5409:(e5400:r2244:"std::text::str::concat"->d784:"std.text.str.concat" e5408:(e5405:(e5403:(e5401:r2245:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5402:r2246:source->d1845:source) e5404:0) e5407:(e5406:r2247:found->d1848:found.s242.start->d747))) e5410:r2248:replacement->d1847:replacement)) e5421:(e5418:(e5415:(e5413:r2249:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5414:r2250:source->d1845:source) e5417:(e5416:r2251:found->d1848:found.s243.end->d749)) e5420:(e5419:r2252:source->d1845:source.s244.len->d838:"std.text.str.str.len"))); p1292:r2253:nil->d503:"std.data.opt.opt.nil" -> e5423:r2254:source->d1845:source })))
      pub d766:"std.text.parse.replace": std::text::str::str -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] any) -> std::text::str::str -> std::text::str::str = e5479:(fn p1293:d1849:source -> e5478:(fn p1294:d1850:parser -> e5477:(fn p1295:d1851:replacement -> e5476:block { let my p1296:d1852:loop = e5470:(fn p1297:d1853:start -> e5469:(fn p1298:d1854:out -> e5468:case e5434:(e5432:(e5430:(e5428:r2255:find_from->d761:"std.text.parse.find_from" e5429:r2256:source->d1849:source) e5431:r2257:start->d1853:start) e5433:r2258:parser->d1850:parser) { p1300:r2259:just->d504:"std.data.opt.opt.just"(p1299:d1855:found) -> e5455:(e5438:(e5435:r2260:loop->d1852:loop e5437:(e5436:r2261:found->d1855:found.s245.end->d749)) e5454:(e5452:(e5439:r2262:"std::text::str::concat"->d784:"std.text.str.concat" e5451:(e5442:(e5440:r2263:"std::text::str::concat"->d784:"std.text.str.concat" e5441:r2264:out->d1854:out) e5450:(e5447:(e5445:(e5443:r2265:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5444:r2266:source->d1849:source) e5446:r2267:start->d1853:start) e5449:(e5448:r2268:found->d1855:found.s246.start->d747)))) e5453:r2269:replacement->d1851:replacement)); p1301:r2270:nil->d503:"std.data.opt.opt.nil" -> e5467:(e5458:(e5456:r2271:"std::text::str::concat"->d784:"std.text.str.concat" e5457:r2272:out->d1854:out) e5466:(e5463:(e5461:(e5459:r2273:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5460:r2274:source->d1849:source) e5462:r2275:start->d1853:start) e5465:(e5464:r2276:source->d1849:source.s247.len->d838:"std.text.str.str.len"))) })); e5475:(e5473:(e5471:r2277:loop->d1852:loop e5472:0) e5474:"") })))
      pub d767:"std.text.parse.translate": (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] 'a) -> ('a -> ['b] std::text::str::str) -> std::text::str::str -> ['b] std::text::str::str = e5489:(fn p1302:d1856:parser -> e5488:(fn p1303:d1857:replacement -> e5487:(fn p1304:d1858:source -> e5486:(e5484:(e5482:(e5480:r2278:edit->d764:"std.text.parse.edit" e5481:r2279:source->d1858:source) e5483:r2280:parser->d1856:parser) e5485:r2281:replacement->d1857:replacement))))
      pub d768:"std.text.parse.choice": (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> () -> [std::text::parse::parse 'a 'b 'c 'd] 'e where 'b: std::text::parse::ParseError(item = 'f, pos = 'g) = e5525:(fn p1305:d1859:p -> e5524:(fn p1306:d1860:q -> e5523:(fn p1307:() -> e5522:block { let my p1308:d1861:snap = e5492:(e5490:r2282:"parse::snapshot"->d714:"std.text.parse.parse.snapshot" e5491:()); e5521:catch e5495:(e5493:r2283:p->d1859:p e5494:()) { std::text::parse::parse::cut p1309:_, p1310:d1862:k -> e5506:block { e5498:(e5496:r2284:"parse::cut"->d713:"std.text.parse.parse.cut" e5497:()); e5505:catch e5501:(e5499:r2285:k->d1862:k e5500:()) { std::text::parse::parse::fail p1311:d1863:e, p1312:_ -> e5504:(e5502:r2286:"parse::fail"->d710:"std.text.parse.parse.fail" e5503:r2287:e->d1863:e) } }; std::text::parse::parse::fail p1313:d1864:e1, p1314:_ -> e5520:block { e5509:(e5507:r2288:"parse::restore"->d715:"std.text.parse.parse.restore" e5508:r2289:snap->d1861:snap); e5519:catch e5512:(e5510:r2290:q->d1860:q e5511:()) { std::text::parse::parse::fail p1315:d1865:e2, p1316:_ -> e5518:(e5513:r2291:"parse::fail"->d710:"std.text.parse.parse.fail" e5517:(e5515:(e5514:r2292:e1->d1864:e1.s248.merge=>d718:"std.text.parse.ParseError.merge") e5516:r2293:e2->d1865:e2)) } } } })))
      pub d769:"std.text.parse.satisfy": ('a -> ['b & 'b] bool) -> () -> [std::text::parse::parse('a & 'c, 'd | 'e, 'g & 'f, 'h), 'b] 'a where std::text::parse::ParseError('e & 'd, item = 'a | 'c, pos = 'g | 'f) = e5564:(fn p1317:d1866:p -> e5563:(fn p1318:() -> e5562:block { let my p1319:d1867:pos = e5528:(e5526:r2294:"parse::pos"->d712:"std.text.parse.parse.pos" e5527:()); e5561:case e5533:(e5532:r2296:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e5531:(e5529:r2295:"parse::eof"->d711:"std.text.parse.parse.eof" e5530:())) { p1323:true -> e5540:(e5534:r2297:"parse::fail"->d710:"std.text.parse.parse.fail" e5539:(e5537:(e5535:r2298:"ParseError::unexpected"->d719:"std.text.parse.ParseError.unexpected" e5536:r2299:nil->d503:"std.data.opt.opt.nil") e5538:r2300:pos->d1867:pos)); p1324:false -> e5560:block { let my p1320:d1868:item = e5543:(e5541:r2301:"parse::item"->d709:"std.text.parse.parse.item" e5542:()); e5559:case e5548:(e5547:r2304:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e5546:(e5544:r2302:p->d1866:p e5545:r2303:item->d1868:item)) { p1321:true -> e5549:r2305:item->d1868:item; p1322:false -> e5558:(e5550:r2306:"parse::fail"->d710:"std.text.parse.parse.fail" e5557:(e5555:(e5551:r2307:"ParseError::unexpected"->d719:"std.text.parse.ParseError.unexpected" e5554:(e5552:r2308:just->d504:"std.data.opt.opt.just" e5553:r2309:item->d1868:item)) e5556:r2310:pos->d1867:pos)) } } } }))
      pub d770:"std.text.parse.token": std::text::str::str -> () -> [std::text::parse::parse(std::text::char::char, 'a | 'b, 'c, 'd & (std::text::str::str, any, any))] () where std::text::parse::ParseError('b & 'a, item = 'e, pos = 'f) = e5617:(fn p1325:d1869:expected -> e5616:(fn p1326:() -> e5615:block { let my p1330:(p1327:d1870:input, p1328:_, p1329:_) = e5567:(e5565:r2311:"parse::snapshot"->d714:"std.text.parse.parse.snapshot" e5566:()); e5614:case e5576:(e5575:r2315:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e5574:(e5573:(e5570:r2313:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e5569:(e5568:r2312:expected->d1869:expected.s249.len->d838:"std.text.str.str.len")) e5572:(e5571:r2314:input->d1870:input.s250.len->d838:"std.text.str.str.len"))) { p1333:true -> e5604:case e5590:(e5589:r2321:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e5588:(e5587:(e5585:r2319:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e5584:(e5581:(e5579:(e5577:r2316:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5578:r2317:input->d1870:input) e5580:0) e5583:(e5582:r2318:expected->d1869:expected.s251.len->d838:"std.text.str.str.len"))) e5586:r2320:expected->d1869:expected)) { p1331:true -> e5594:(e5591:r2322:"parse::advance"->d716:"std.text.parse.parse.advance" e5593:(e5592:r2323:expected->d1869:expected.s252.len->d838:"std.text.str.str.len")); p1332:false -> e5603:(e5595:r2324:"parse::fail"->d710:"std.text.parse.parse.fail" e5602:(e5598:(e5596:r2325:"ParseError::expected"->d720:"std.text.parse.ParseError.expected" e5597:r2326:expected->d1869:expected) e5601:(e5599:r2327:"parse::pos"->d712:"std.text.parse.parse.pos" e5600:()))) }; p1334:false -> e5613:(e5605:r2328:"parse::fail"->d710:"std.text.parse.parse.fail" e5612:(e5608:(e5606:r2329:"ParseError::expected"->d720:"std.text.parse.ParseError.expected" e5607:r2330:expected->d1869:expected) e5611:(e5609:r2331:"parse::pos"->d712:"std.text.parse.parse.pos" e5610:()))) } }))
      pub d771:"std.text.parse.rest": () -> [std::text::parse::parse std::text::char::char 'a (int, int) (std::text::str::str, int, int)] std::text::str::str = e5628:(fn p1335:() -> e5627:block { let my p1339:(p1336:d1871:input, p1337:_, p1338:_) = e5620:(e5618:r2332:"parse::snapshot"->d714:"std.text.parse.parse.snapshot" e5619:()); e5626:block { e5624:(e5621:r2333:"parse::advance"->d716:"std.text.parse.parse.advance" e5623:(e5622:r2334:input->d1871:input.s253.len->d838:"std.text.str.str.len")); e5625:r2335:input->d1871:input } })
      pub d772:"std.text.parse.optional": (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> () -> [std::text::parse::parse 'a 'b 'c 'd] std::data::opt::opt 'e where 'b: std::text::parse::ParseError(item = 'f, pos = 'g) = e5643:(fn p1340:d1872:p -> e5642:(fn p1341:() -> e5641:(e5639:(e5636:(e5629:r2336:choice->d768:"std.text.parse.choice" e5635:(fn p1342:() -> e5634:(e5630:r2337:just->d504:"std.data.opt.opt.just" e5633:(e5631:r2338:p->d1872:p e5632:())))) e5638:(fn p1343:() -> e5637:r2339:nil->d503:"std.data.opt.opt.nil")) e5640:())))
      pub d773:"std.text.parse.many": (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> () -> [std::text::parse::parse 'a 'b 'c 'd] std::data::list::list 'e where 'b: std::text::parse::ParseError(item = 'f, pos = 'g) = e5668:(fn p1344:d1873:p -> e5667:(fn p1345:() -> e5666:(e5664:(e5659:(e5644:r2340:choice->d768:"std.text.parse.choice" e5658:(fn p1346:() -> e5657:(e5656:(e5655:builtin_op::list_merge e5649:(e5648:builtin_op::list_singleton e5647:(e5645:r2341:p->d1873:p e5646:()))) e5654:(e5652:(e5650:r2342:many->d773:"std.text.parse.many" e5651:r2343:p->d1873:p) e5653:())))) e5663:(fn p1347:() -> e5662:(e5660:builtin_op::list_empty e5661:()))) e5665:())))
      pub d774:"std.text.parse.some": (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> () -> [std::text::parse::parse 'a 'b 'c 'd] std::data::list::list 'e where 'b: std::text::parse::ParseError(item = 'f, pos = 'g) = e5683:(fn p1348:d1874:p -> e5682:(fn p1349:() -> e5681:(e5680:(e5679:builtin_op::list_merge e5673:(e5672:builtin_op::list_singleton e5671:(e5669:r2344:p->d1874:p e5670:()))) e5678:(e5676:(e5674:r2345:many->d773:"std.text.parse.many" e5675:r2346:p->d1874:p) e5677:()))))
      pub d775:"std.text.parse.label": (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> std::text::str::str -> () -> [std::text::parse::parse 'a 'b 'c 'd] 'e where 'b: std::text::parse::ParseError(item = 'f, pos = 'g) = e5696:(fn p1350:d1875:p -> e5695:(fn p1351:d1876:label_text -> e5694:(fn p1352:() -> e5693:catch e5686:(e5684:r2347:p->d1875:p e5685:()) { std::text::parse::parse::fail p1353:d1877:e, p1354:_ -> e5692:(e5687:r2348:"parse::fail"->d710:"std.text.parse.parse.fail" e5691:(e5689:(e5688:r2349:e->d1877:e.s254.label=>d721:"std.text.parse.ParseError.label") e5690:r2350:label_text->d1876:label_text)) })))
      pub d776:"std.text.parse.word": () -> [std::text::parse::parse(std::text::char::char, 'a | 'b, (int, int), (std::text::str::str, int, int))] std::text::str::str where std::text::parse::ParseError('b & 'a, item = 'c, pos = 'd) = e5731:(fn p1355:() -> e5730:block { let my p1359:(p1356:d1878:input, p1357:_, p1358:_) = e5699:(e5697:r2351:"parse::snapshot"->d714:"std.text.parse.parse.snapshot" e5698:()); e5729:block { let my p1360:d1879:found = e5704:(e5702:(e5700:r2352:"std::text::str::word_prefix_at"->d879:"std.text.str.word_prefix_at" e5701:r2353:input->d1878:input) e5703:0); e5728:case e5712:(e5711:r2356:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e5710:(e5709:(e5707:r2355:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e5706:(e5705:r2354:found->d1879:found.s255.len->d838:"std.text.str.str.len")) e5708:0)) { p1361:true -> e5721:(e5713:r2357:"parse::fail"->d710:"std.text.parse.parse.fail" e5720:(e5716:(e5714:r2358:"ParseError::expected"->d720:"std.text.parse.ParseError.expected" e5715:"word") e5719:(e5717:r2359:"parse::pos"->d712:"std.text.parse.parse.pos" e5718:()))); p1362:false -> e5727:block { e5725:(e5722:r2360:"parse::advance"->d716:"std.text.parse.parse.advance" e5724:(e5723:r2361:found->d1879:found.s256.len->d838:"std.text.str.str.len")); e5726:r2362:found->d1879:found } } } })
    }
    pub d114:"std.text.path" mod {
      pub d777:"std.text.path.of_bytes_raw": std::text::bytes::bytes -> std::text::path::path = e5732:builtin_op::bytes_to_path
      pub d778:"std.text.path.to_bytes": std::text::path::path -> std::text::bytes::bytes = e5733:builtin_op::path_to_bytes
      pub d779:"std.text.path.path" mod {
        pub d780:"std.text.path.path.to_bytes": std::text::path::path -> std::text::bytes::bytes = e5737:(fn p1363:d1880:p -> e5736:(e5734:r2363:"std::text::path::to_bytes"->d778:"std.text.path.to_bytes" e5735:r2364:p->d1880:p))
      }
      pub d781:"std.text.path.of_bytes": std::text::bytes::bytes -> std::text::path::path = e5741:(fn p1364:d1881:b -> e5740:(e5738:r2365:"std::text::path::of_bytes_raw"->d777:"std.text.path.of_bytes_raw" e5739:r2366:b->d1881:b))
      my d782 mod {
        d783: std::text::path::path -> std::text::str::str = e5747:(fn p1365:d1882:p -> e5746:(e5742:r2367:"std::text::bytes::to_utf8_lossy"->d666:"std.text.bytes.to_utf8_lossy" e5745:(e5743:r2368:"std::text::path::to_bytes"->d778:"std.text.path.to_bytes" e5744:r2369:p->d1882:p)))
      }
    }
    pub d115:"std.text.str" mod {
      pub d784:"std.text.str.concat": std::text::str::str -> std::text::str::str -> std::text::str::str = e5748:builtin_op::string_concat
      pub d785:"std.text.str.eq": std::text::str::str -> std::text::str::str -> bool = e5749:builtin_op::string_eq
      pub d786:"std.text.str.len": std::text::str::str -> int = e5750:builtin_op::string_len
      pub d787:"std.text.str.line_count": std::text::str::str -> int = e5751:builtin_op::string_line_count
      pub d788:"std.text.str.line_range": std::text::str::str -> int -> std::data::range::range = e5752:builtin_op::string_line_range
      pub d789:"std.text.str.index_raw": std::text::str::str -> int -> std::text::char::char = e5753:builtin_op::string_index
      pub d790:"std.text.str.index_range": std::text::str::str -> std::data::range::range -> std::text::str::str = e5754:builtin_op::string_index_range
      pub d791:"std.text.str.index_range_raw": std::text::str::str -> int -> int -> std::text::str::str = e5755:builtin_op::string_index_range_raw
      pub d792:"std.text.str.splice": std::text::str::str -> std::data::range::range -> std::text::str::str -> std::text::str::str = e5756:builtin_op::string_splice
      pub d793:"std.text.str.splice_raw": std::text::str::str -> int -> int -> std::text::str::str -> std::text::str::str = e5757:builtin_op::string_splice_raw
      pub d794:"std.text.str.to_bytes": std::text::str::str -> std::text::bytes::bytes = e5758:builtin_op::string_to_bytes
      pub d795:"std.text.str.lines": {source: std::text::str::str} -> std::text::str::lines = <missing>
      pub d798:"std.text.str.lines" mod {
      }
      pub d799:"std.text.str.ref_lines": {source: std::control::var::ref 'a std::text::str::str} -> std::text::str::ref_lines 'a = <missing>
      pub d802:"std.text.str.ref_lines" mod {
        pub d803:"std.text.str.ref_lines.index": std::text::str::ref_lines('a & 'b) -> int -> std::control::var::ref('b | 'a, 'c | std::text::str::str) = e5820:(fn p1366:d1883:ls -> e5819:(fn p1367:d1884:i -> e5818:(e5759:r2370:ref->d235:"std.control.var.ref" e5817:{get: e5779:(fn p1368:() -> e5778:block { let my p1369:d1885:line_range = e5768:(e5766:(e5760:r2371:"std::text::str::line_range"->d788:"std.text.str.line_range" e5765:(e5763:(e5762:(e5761:r2372:ls->d1883:ls.s257.source->d800).s258.get->d236) e5764:())) e5767:r2373:i->d1884:i); e5777:(e5775:(e5769:r2374:"std::text::str::index_range"->d790:"std.text.str.index_range" e5774:(e5772:(e5771:(e5770:r2375:ls->d1883:ls.s259.source->d800).s260.get->d236) e5773:())) e5776:r2376:line_range->d1885:line_range) }), update_effect: e5816:(fn p1370:() -> e5815:block { let my p1371:d1886:loop = e5807:(fn p1372:d1887:x -> e5806:catch e5780:r2377:x->d1887:x { std::control::var::ref_update::update p1373:d1888:old, p1374:d1889:k -> e5805:block { let my p1375:d1890:line_range = e5785:(e5783:(e5781:r2378:"std::text::str::line_range"->d788:"std.text.str.line_range" e5782:r2379:old->d1888:old) e5784:r2380:i->d1884:i); e5804:block { let my p1376:d1891:new_item = e5792:(e5786:r2381:"ref_update::update"->d234:"std.control.var.ref_update.update" e5791:(e5789:(e5787:r2382:"std::text::str::index_range"->d790:"std.text.str.index_range" e5788:r2383:old->d1888:old) e5790:r2384:line_range->d1890:line_range)); e5803:(e5793:r2385:loop->d1886:loop e5802:(e5794:r2386:k->d1889:k e5801:(e5799:(e5797:(e5795:r2387:"std::text::str::splice"->d792:"std.text.str.splice" e5796:r2388:old->d1888:old) e5798:r2389:line_range->d1890:line_range) e5800:r2390:new_item->d1891:new_item))) } } }); e5814:(e5808:r2391:loop->d1886:loop e5813:(e5811:(e5810:(e5809:r2392:ls->d1883:ls.s261.source->d800).s262.update_effect->d238) e5812:())) })})))
      }
      pub d804:"std.text.str.str_line_view": std::text::str::str -> std::text::str::lines = e5825:(fn p1377:d1892:source -> e5824:(e5821:r2393:lines->d795:"std.text.str.lines" e5823:{source: e5822:r2394:source->d1892:source}))
      pub d805:"std.text.str.line_view": std::control::var::ref 'a std::text::str::str -> std::text::str::ref_lines 'a = e5830:(fn p1378:d1893:source -> e5829:(e5826:r2395:ref_lines->d799:"std.text.str.ref_lines" e5828:{source: e5827:r2396:source->d1893:source}))
      my d806 mod {
        d807: std::text::str::lines -> int -> std::text::str::str = e5845:(fn p1379:d1894:ls -> e5844:(fn p1380:d1895:i -> e5843:block { let my p1381:d1896:line_range = e5836:(e5834:(e5831:r2397:"std::text::str::line_range"->d788:"std.text.str.line_range" e5833:(e5832:r2398:ls->d1894:ls.s263.source->d796)) e5835:r2399:i->d1895:i); e5842:(e5840:(e5837:r2400:"std::text::str::index_range"->d790:"std.text.str.index_range" e5839:(e5838:r2401:ls->d1894:ls.s264.source->d796)) e5841:r2402:line_range->d1896:line_range) }))
      }
      my d808 mod {
        d809: std::text::str::ref_lines('a & 'b) -> int -> std::control::var::ref('b | 'a, 'c | std::text::str::str) = e5907:(fn p1382:d1897:ls -> e5906:(fn p1383:d1898:i -> e5905:(e5846:r2403:ref->d235:"std.control.var.ref" e5904:{get: e5866:(fn p1384:() -> e5865:block { let my p1385:d1899:line_range = e5855:(e5853:(e5847:r2404:"std::text::str::line_range"->d788:"std.text.str.line_range" e5852:(e5850:(e5849:(e5848:r2405:ls->d1897:ls.s265.source->d800).s266.get->d236) e5851:())) e5854:r2406:i->d1898:i); e5864:(e5862:(e5856:r2407:"std::text::str::index_range"->d790:"std.text.str.index_range" e5861:(e5859:(e5858:(e5857:r2408:ls->d1897:ls.s267.source->d800).s268.get->d236) e5860:())) e5863:r2409:line_range->d1899:line_range) }), update_effect: e5903:(fn p1386:() -> e5902:block { let my p1387:d1900:loop = e5894:(fn p1388:d1901:x -> e5893:catch e5867:r2410:x->d1901:x { std::control::var::ref_update::update p1389:d1902:old, p1390:d1903:k -> e5892:block { let my p1391:d1904:line_range = e5872:(e5870:(e5868:r2411:"std::text::str::line_range"->d788:"std.text.str.line_range" e5869:r2412:old->d1902:old) e5871:r2413:i->d1898:i); e5891:block { let my p1392:d1905:new_item = e5879:(e5873:r2414:"ref_update::update"->d234:"std.control.var.ref_update.update" e5878:(e5876:(e5874:r2415:"std::text::str::index_range"->d790:"std.text.str.index_range" e5875:r2416:old->d1902:old) e5877:r2417:line_range->d1904:line_range)); e5890:(e5880:r2418:loop->d1900:loop e5889:(e5881:r2419:k->d1903:k e5888:(e5886:(e5884:(e5882:r2420:"std::text::str::splice"->d792:"std.text.str.splice" e5883:r2421:old->d1902:old) e5885:r2422:line_range->d1904:line_range) e5887:r2423:new_item->d1905:new_item))) } } }); e5901:(e5895:r2424:loop->d1900:loop e5900:(e5898:(e5897:(e5896:r2425:ls->d1897:ls.s269.source->d800).s270.update_effect->d238) e5899:())) })})))
      }
      my d810:"std.text.str.fold_lines": std::text::str::lines -> int -> int -> 'a -> ('a -> ['b] std::text::str::str -> ['c] 'a) -> ['c, 'b] 'a = e5943:(fn p1393:d1906:ls -> e5942:(fn p1394:d1907:i -> e5941:(fn p1395:d1908:end -> e5940:(fn p1396:d1909:acc -> e5939:(fn p1397:d1910:f -> e5938:case e5914:(e5913:r2429:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e5912:(e5911:(e5909:r2427:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e5908:r2426:i->d1907:i) e5910:r2428:end->d1908:end)) { p1398:true -> e5936:(e5934:(e5925:(e5923:(e5917:(e5915:r2430:fold_lines->d810:"std.text.str.fold_lines" e5916:r2431:ls->d1906:ls) e5922:(e5921:(e5919:r2433:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e5918:r2432:i->d1907:i) e5920:1)) e5924:r2434:end->d1908:end) e5933:(e5928:(e5926:r2435:f->d1910:f e5927:r2436:acc->d1909:acc) e5932:(e5930:(e5929:r2437:ls->d1906:ls.s271.index=>d454:"std.data.index.Index.index") e5931:r2438:i->d1907:i))) e5935:r2439:f->d1910:f); p1399:false -> e5937:r2440:acc->d1909:acc })))))
      my d811:"std.text.str.fold_ref_lines": std::text::str::ref_lines('a & 'b) -> int -> int -> 'c -> ('c -> ['d] std::control::var::ref('b | 'a, 'e | std::text::str::str) -> ['f] 'c) -> ['f, 'd] 'c = e5979:(fn p1400:d1911:ls -> e5978:(fn p1401:d1912:i -> e5977:(fn p1402:d1913:end -> e5976:(fn p1403:d1914:acc -> e5975:(fn p1404:d1915:f -> e5974:case e5950:(e5949:r2444:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e5948:(e5947:(e5945:r2442:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e5944:r2441:i->d1912:i) e5946:r2443:end->d1913:end)) { p1405:true -> e5972:(e5970:(e5961:(e5959:(e5953:(e5951:r2445:fold_ref_lines->d811:"std.text.str.fold_ref_lines" e5952:r2446:ls->d1911:ls) e5958:(e5957:(e5955:r2448:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e5954:r2447:i->d1912:i) e5956:1)) e5960:r2449:end->d1913:end) e5969:(e5964:(e5962:r2450:f->d1915:f e5963:r2451:acc->d1914:acc) e5968:(e5966:(e5965:r2452:ls->d1911:ls.s272.index->d803:"std.text.str.ref_lines.index") e5967:r2453:i->d1912:i))) e5971:r2454:f->d1915:f); p1406:false -> e5973:r2455:acc->d1914:acc })))))
      my d812 mod {
        d813: std::text::str::lines -> 'a -> ('a -> ['b] std::text::str::str -> ['b] 'a) -> ['b] 'a = e5996:(fn p1407:d1916:ls -> e5995:(fn p1408:d1917:z -> e5994:(fn p1409:d1918:f -> e5993:(e5991:(e5989:(e5984:(e5982:(e5980:r2456:fold_lines->d810:"std.text.str.fold_lines" e5981:r2457:ls->d1916:ls) e5983:0) e5988:(e5985:r2458:"std::text::str::line_count"->d787:"std.text.str.line_count" e5987:(e5986:r2459:ls->d1916:ls.s273.source->d796))) e5990:r2460:z->d1917:z) e5992:r2461:f->d1918:f))))
      }
      my d814 mod {
        d815: std::text::str::ref_lines('a & 'b) -> 'c -> ('c -> ['a & 'b] std::control::var::ref('b | 'a, 'd | std::text::str::str) -> ['a & 'b] 'c) -> ['a] 'c = e6016:(fn p1410:d1919:ls -> e6015:(fn p1411:d1920:z -> e6014:(fn p1412:d1921:f -> e6013:(e6011:(e6009:(e6001:(e5999:(e5997:r2462:fold_ref_lines->d811:"std.text.str.fold_ref_lines" e5998:r2463:ls->d1919:ls) e6000:0) e6008:(e6002:r2464:"std::text::str::line_count"->d787:"std.text.str.line_count" e6007:(e6005:(e6004:(e6003:r2465:ls->d1919:ls.s274.source->d800).s275.get->d236) e6006:()))) e6010:r2466:z->d1920:z) e6012:r2467:f->d1921:f))))
      }
      pub d816:"std.text.str.str" mod {
        pub d817:"std.text.str.str.splice": std::text::str::str -> std::data::range::range -> std::text::str::str -> std::text::str::str = e6026:(fn p1413:d1922:s -> e6025:(fn p1414:d1923:r -> e6024:(fn p1415:d1924:insert -> e6023:(e6021:(e6019:(e6017:r2468:"std::text::str::splice"->d792:"std.text.str.splice" e6018:r2469:s->d1922:s) e6020:r2470:r->d1923:r) e6022:r2471:insert->d1924:insert))))
        pub d818:"std.text.str.str.find": std::text::str::str -> std::text::str::str -> std::data::opt::opt std::data::range::range = e6033:(fn p1416:d1925:s -> e6032:(fn p1417:d1926:needle -> e6031:(e6029:(e6027:r2472:"std::text::str::find"->d852:"std.text.str.find" e6028:r2473:s->d1925:s) e6030:r2474:needle->d1926:needle)))
        pub d819:"std.text.str.str.contains": std::text::str::str -> std::text::str::str -> bool = e6040:(fn p1418:d1927:s -> e6039:(fn p1419:d1928:needle -> e6038:(e6036:(e6034:r2475:"std::text::str::contains"->d853:"std.text.str.contains" e6035:r2476:s->d1927:s) e6037:r2477:needle->d1928:needle)))
        pub d820:"std.text.str.str.starts_with": std::text::str::str -> std::text::str::str -> bool = e6047:(fn p1420:d1929:s -> e6046:(fn p1421:d1930:prefix -> e6045:(e6043:(e6041:r2478:"std::text::str::starts_with"->d854:"std.text.str.starts_with" e6042:r2479:s->d1929:s) e6044:r2480:prefix->d1930:prefix)))
        pub d821:"std.text.str.str.ends_with": std::text::str::str -> std::text::str::str -> bool = e6054:(fn p1422:d1931:s -> e6053:(fn p1423:d1932:suffix -> e6052:(e6050:(e6048:r2481:"std::text::str::ends_with"->d855:"std.text.str.ends_with" e6049:r2482:s->d1931:s) e6051:r2483:suffix->d1932:suffix)))
        pub d822:"std.text.str.str.split": std::text::str::str -> std::text::str::str -> std::data::list::list std::text::str::str = e6061:(fn p1424:d1933:s -> e6060:(fn p1425:d1934:separator -> e6059:(e6057:(e6055:r2484:"std::text::str::split"->d857:"std.text.str.split" e6056:r2485:s->d1933:s) e6058:r2486:separator->d1934:separator)))
        pub d823:"std.text.str.str.split_once": std::text::str::str -> std::text::str::str -> std::data::opt::opt (std::text::str::str, std::text::str::str) = e6068:(fn p1426:d1935:s -> e6067:(fn p1427:d1936:separator -> e6066:(e6064:(e6062:r2487:"std::text::str::split_once"->d863:"std.text.str.split_once" e6063:r2488:s->d1935:s) e6065:r2489:separator->d1936:separator)))
        pub d824:"std.text.str.str.replace_once": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e6078:(fn p1428:d1937:s -> e6077:(fn p1429:d1938:from -> e6076:(fn p1430:d1939:to -> e6075:(e6073:(e6071:(e6069:r2490:"std::text::str::replace_once"->d875:"std.text.str.replace_once" e6070:r2491:s->d1937:s) e6072:r2492:from->d1938:from) e6074:r2493:to->d1939:to))))
        pub d825:"std.text.str.str.replace": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e6088:(fn p1431:d1940:s -> e6087:(fn p1432:d1941:from -> e6086:(fn p1433:d1942:to -> e6085:(e6083:(e6081:(e6079:r2494:"std::text::str::replace_all"->d877:"std.text.str.replace_all" e6080:r2495:s->d1940:s) e6082:r2496:from->d1941:from) e6084:r2497:to->d1942:to))))
        pub d826:"std.text.str.str.trim": std::text::str::str -> std::text::str::str = e6092:(fn p1434:d1943:s -> e6091:(e6089:r2498:"std::text::str::trim"->d870:"std.text.str.trim" e6090:r2499:s->d1943:s))
        pub d827:"std.text.str.str.trim_start": std::text::str::str -> std::text::str::str = e6096:(fn p1435:d1944:s -> e6095:(e6093:r2500:"std::text::str::trim_start"->d868:"std.text.str.trim_start" e6094:r2501:s->d1944:s))
        pub d828:"std.text.str.str.trim_end": std::text::str::str -> std::text::str::str = e6100:(fn p1436:d1945:s -> e6099:(e6097:r2502:"std::text::str::trim_end"->d869:"std.text.str.trim_end" e6098:r2503:s->d1945:s))
        pub d829:"std.text.str.str.replace_once!": std::control::var::ref 'a std::text::str::str -> std::text::str::str -> std::text::str::str -> ['a] () = e6114:(fn p1437:d1946:"&r" -> e6113:(fn p1438:d1947:pattern -> e6112:(fn p1439:d1948:replacement -> e6111:(e6102:(e6101:r2504:"&r"->d1946:"&r".s276.update->d241:"std.control.var.ref.update") e6110:(fn p1440:d1949:s -> e6109:(e6107:(e6105:(e6103:r2505:"std::text::str::replace_once"->d875:"std.text.str.replace_once" e6104:r2506:s->d1949:s) e6106:r2507:pattern->d1947:pattern) e6108:r2508:replacement->d1948:replacement))))))
        pub d830:"std.text.str.str.replace!": std::control::var::ref 'a std::text::str::str -> std::text::str::str -> std::text::str::str -> ['a] () = e6128:(fn p1441:d1950:"&r" -> e6127:(fn p1442:d1951:pattern -> e6126:(fn p1443:d1952:replacement -> e6125:(e6116:(e6115:r2509:"&r"->d1950:"&r".s277.update->d241:"std.control.var.ref.update") e6124:(fn p1444:d1953:s -> e6123:(e6121:(e6119:(e6117:r2510:"std::text::str::replace"->d876:"std.text.str.replace" e6118:r2511:s->d1953:s) e6120:r2512:pattern->d1951:pattern) e6122:r2513:replacement->d1952:replacement))))))
        pub d831:"std.text.str.str.replace_all!": std::control::var::ref 'a std::text::str::str -> std::text::str::str -> std::text::str::str -> ['a] () = e6142:(fn p1445:d1954:"&r" -> e6141:(fn p1446:d1955:pattern -> e6140:(fn p1447:d1956:replacement -> e6139:(e6130:(e6129:r2514:"&r"->d1954:"&r".s278.update->d241:"std.control.var.ref.update") e6138:(fn p1448:d1957:s -> e6137:(e6135:(e6133:(e6131:r2515:"std::text::str::replace_all"->d877:"std.text.str.replace_all" e6132:r2516:s->d1957:s) e6134:r2517:pattern->d1955:pattern) e6136:r2518:replacement->d1956:replacement))))))
        pub d832:"std.text.str.str.splice!": std::control::var::ref 'a std::text::str::str -> std::data::range::range -> std::text::str::str -> ['a] () = e6156:(fn p1449:d1958:"&r" -> e6155:(fn p1450:d1959:range -> e6154:(fn p1451:d1960:replacement -> e6153:(e6144:(e6143:r2519:"&r"->d1958:"&r".s279.update->d241:"std.control.var.ref.update") e6152:(fn p1452:d1961:s -> e6151:(e6149:(e6147:(e6145:r2520:"std::text::str::splice"->d792:"std.text.str.splice" e6146:r2521:s->d1961:s) e6148:r2522:range->d1959:range) e6150:r2523:replacement->d1960:replacement))))))
        pub d833:"std.text.str.str.trim!": std::control::var::ref 'a std::text::str::str -> ['a] () = e6164:(fn p1453:d1962:"&r" -> e6163:(e6158:(e6157:r2524:"&r"->d1962:"&r".s280.update->d241:"std.control.var.ref.update") e6162:(fn p1454:d1963:s -> e6161:(e6159:r2525:"std::text::str::trim"->d870:"std.text.str.trim" e6160:r2526:s->d1963:s))))
        pub d834:"std.text.str.str.trim_start!": std::control::var::ref 'a std::text::str::str -> ['a] () = e6172:(fn p1455:d1964:"&r" -> e6171:(e6166:(e6165:r2527:"&r"->d1964:"&r".s281.update->d241:"std.control.var.ref.update") e6170:(fn p1456:d1965:s -> e6169:(e6167:r2528:"std::text::str::trim_start"->d868:"std.text.str.trim_start" e6168:r2529:s->d1965:s))))
        pub d835:"std.text.str.str.trim_end!": std::control::var::ref 'a std::text::str::str -> ['a] () = e6180:(fn p1457:d1966:"&r" -> e6179:(e6174:(e6173:r2530:"&r"->d1966:"&r".s282.update->d241:"std.control.var.ref.update") e6178:(fn p1458:d1967:s -> e6177:(e6175:r2531:"std::text::str::trim_end"->d869:"std.text.str.trim_end" e6176:r2532:s->d1967:s))))
        pub d836:"std.text.str.str.repeat": std::text::str::str -> int -> std::text::str::str = e6187:(fn p1459:d1968:s -> e6186:(fn p1460:d1969:count -> e6185:(e6183:(e6181:r2533:"std::text::str::repeat"->d871:"std.text.str.repeat" e6182:r2534:s->d1968:s) e6184:r2535:count->d1969:count)))
        pub d837:"std.text.str.str.to_int": std::text::str::str -> std::data::opt::opt int = e6191:(fn p1461:d1970:s -> e6190:(e6188:r2536:"std::text::str::to_int"->d874:"std.text.str.to_int" e6189:r2537:s->d1970:s))
        pub d838:"std.text.str.str.len": std::text::str::str -> int = e6195:(fn p1462:d1971:s -> e6194:(e6192:r2538:"std::text::str::len"->d786:"std.text.str.len" e6193:r2539:s->d1971:s))
        pub d839:"std.text.str.str.is_empty": std::text::str::str -> bool = e6199:(fn p1463:d1972:s -> e6198:(e6196:r2540:"std::text::str::is_empty"->d846:"std.text.str.is_empty" e6197:r2541:s->d1972:s))
        pub d840:"std.text.str.str.lines": std::text::str::str -> std::text::str::lines = e6203:(fn p1464:d1973:s -> e6202:(e6200:r2542:str_line_view->d804:"std.text.str.str_line_view" e6201:r2543:s->d1973:s))
        pub d841:"std.text.str.str.lines!": std::control::var::ref 'a std::text::str::str -> std::text::str::ref_lines 'a = e6207:(fn p1465:d1974:"&s" -> e6206:(e6204:r2544:line_view->d805:"std.text.str.line_view" e6205:r2545:"&s"->d1974:"&s"))
        pub d842:"std.text.str.str.print": std::text::str::str -> [std::io::console::out] () = e6211:(fn p1466:d1975:s -> e6210:(e6208:r2546:"std::io::print"->d539:"std.io.console.print" e6209:r2547:s->d1975:s))
        pub d843:"std.text.str.str.println": std::text::str::str -> [std::io::console::out] () = e6215:(fn p1467:d1976:s -> e6214:(e6212:r2548:"std::io::println"->d541:"std.io.console.println" e6213:r2549:s->d1976:s))
        pub d844:"std.text.str.str.eprint": std::text::str::str -> [std::io::console::err] () = e6219:(fn p1468:d1977:s -> e6218:(e6216:r2550:"std::io::eprint"->d545:"std.io.console.eprint" e6217:r2551:s->d1977:s))
        pub d845:"std.text.str.str.eprintln": std::text::str::str -> [std::io::console::err] () = e6223:(fn p1469:d1978:s -> e6222:(e6220:r2552:"std::io::eprintln"->d546:"std.io.console.eprintln" e6221:r2553:s->d1978:s))
      }
      pub d846:"std.text.str.is_empty": std::text::str::str -> bool = e6231:(fn p1470:d1979:s -> e6230:(e6228:(e6224:r2554:"std::int::eq"->d45:"std.int.eq" e6227:(e6225:r2555:"std::text::str::len"->d786:"std.text.str.len" e6226:r2556:s->d1979:s)) e6229:0))
      my d847:"std.text.str.starts_with_at_len": std::text::str::str -> int -> std::text::str::str -> int -> int -> bool = e6262:(fn p1471:d1980:source -> e6261:(fn p1472:d1981:source_len -> e6260:(fn p1473:d1982:needle -> e6259:(fn p1474:d1983:needle_len -> e6258:(fn p1475:d1984:start -> e6257:block { let my p1476:d1985:end = e6236:(e6234:(e6232:r2557:"std::int::add"->d50:"std.int.add" e6233:r2558:start->d1984:start) e6235:r2559:needle_len->d1983:needle_len); e6256:case e6243:(e6242:r2563:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6241:(e6239:(e6237:r2560:"std::int::le"->d47:"std.int.le" e6238:r2561:end->d1985:end) e6240:r2562:source_len->d1981:source_len)) { p1477:true -> e6254:(e6253:(e6251:r2568:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e6250:(e6248:(e6246:(e6244:r2564:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e6245:r2565:source->d1980:source) e6247:r2566:start->d1984:start) e6249:r2567:end->d1985:end)) e6252:r2569:needle->d1982:needle); p1478:false -> e6255:false } })))))
      my d848:"std.text.str.starts_with_at": std::text::str::str -> std::text::str::str -> int -> bool = e6280:(fn p1479:d1986:source -> e6279:(fn p1480:d1987:needle -> e6278:(fn p1481:d1988:start -> e6277:(e6275:(e6271:(e6269:(e6265:(e6263:r2570:starts_with_at_len->d847:"std.text.str.starts_with_at_len" e6264:r2571:source->d1986:source) e6268:(e6266:r2572:"std::text::str::len"->d786:"std.text.str.len" e6267:r2573:source->d1986:source)) e6270:r2574:needle->d1987:needle) e6274:(e6272:r2575:"std::text::str::len"->d786:"std.text.str.len" e6273:r2576:needle->d1987:needle)) e6276:r2577:start->d1988:start))))
      my d849:"std.text.str.find_at_len": std::text::str::str -> int -> std::text::str::str -> int -> int -> std::data::opt::opt int = e6313:(fn p1482:d1989:source -> e6312:(fn p1483:d1990:source_len -> e6311:(fn p1484:d1991:needle -> e6310:(fn p1485:d1992:needle_len -> e6309:(fn p1486:d1993:start -> e6308:case e6287:(e6286:r2580:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6285:(e6283:(e6281:r2578:"std::int::eq"->d45:"std.int.eq" e6282:r2579:needle_len->d1992:needle_len) e6284:0)) { p1487:true -> e6290:(e6288:r2581:just->d504:"std.data.opt.opt.just" e6289:r2582:start->d1993:start); p1488:false -> e6307:(e6305:(e6299:(e6297:(e6295:(e6293:(e6291:r2583:find_at_loop->d850:"std.text.str.find_at_loop" e6292:r2584:source->d1989:source) e6294:r2585:source_len->d1990:source_len) e6296:r2586:needle->d1991:needle) e6298:r2587:needle_len->d1992:needle_len) e6304:(e6302:(e6300:r2588:"std::int::sub"->d51:"std.int.sub" e6301:r2589:source_len->d1990:source_len) e6303:r2590:needle_len->d1992:needle_len)) e6306:r2591:start->d1993:start) })))))
      my d850:"std.text.str.find_at_loop": std::text::str::str -> int -> std::text::str::str -> int -> int -> int -> std::data::opt::opt int = e6362:(fn p1489:d1994:source -> e6361:(fn p1490:d1995:source_len -> e6360:(fn p1491:d1996:needle -> e6359:(fn p1492:d1997:needle_len -> e6358:(fn p1493:d1998:limit -> e6357:(fn p1494:d1999:i -> e6356:case e6320:(e6319:r2595:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6318:(e6316:(e6314:r2592:"std::int::le"->d47:"std.int.le" e6315:r2593:i->d1999:i) e6317:r2594:limit->d1998:limit)) { p1497:true -> e6354:case e6333:(e6332:r2602:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6331:(e6329:(e6327:(e6325:(e6323:(e6321:r2596:starts_with_at_len->d847:"std.text.str.starts_with_at_len" e6322:r2597:source->d1994:source) e6324:r2598:source_len->d1995:source_len) e6326:r2599:needle->d1996:needle) e6328:r2600:needle_len->d1997:needle_len) e6330:r2601:i->d1999:i)) { p1495:true -> e6336:(e6334:r2603:just->d504:"std.data.opt.opt.just" e6335:r2604:i->d1999:i); p1496:false -> e6353:(e6347:(e6345:(e6343:(e6341:(e6339:(e6337:r2605:find_at_loop->d850:"std.text.str.find_at_loop" e6338:r2606:source->d1994:source) e6340:r2607:source_len->d1995:source_len) e6342:r2608:needle->d1996:needle) e6344:r2609:needle_len->d1997:needle_len) e6346:r2610:limit->d1998:limit) e6352:(e6350:(e6348:r2611:"std::int::add"->d50:"std.int.add" e6349:r2612:i->d1999:i) e6351:1)) }; p1498:false -> e6355:r2613:nil->d503:"std.data.opt.opt.nil" }))))))
      my d851:"std.text.str.find_at": std::text::str::str -> std::text::str::str -> int -> std::data::opt::opt int = e6380:(fn p1499:d2000:source -> e6379:(fn p1500:d2001:needle -> e6378:(fn p1501:d2002:start -> e6377:(e6375:(e6371:(e6369:(e6365:(e6363:r2614:find_at_len->d849:"std.text.str.find_at_len" e6364:r2615:source->d2000:source) e6368:(e6366:r2616:"std::text::str::len"->d786:"std.text.str.len" e6367:r2617:source->d2000:source)) e6370:r2618:needle->d2001:needle) e6374:(e6372:r2619:"std::text::str::len"->d786:"std.text.str.len" e6373:r2620:needle->d2001:needle)) e6376:r2621:start->d2002:start))))
      pub d852:"std.text.str.find": std::text::str::str -> std::text::str::str -> std::data::opt::opt std::data::range::range = e6404:(fn p1502:d2003:source -> e6403:(fn p1503:d2004:needle -> e6402:case e6387:(e6385:(e6383:(e6381:r2622:find_at->d851:"std.text.str.find_at" e6382:r2623:source->d2003:source) e6384:r2624:needle->d2004:needle) e6386:0) { p1505:r2625:just->d504:"std.data.opt.opt.just"(p1504:d2005:i) -> e6400:(e6388:r2626:just->d504:"std.data.opt.opt.just" e6399:(e6391:(e6389:r2627:range->d511:"std.data.range.range" e6390:r2628:i->d2005:i) e6398:(e6394:(e6392:r2629:"std::int::add"->d50:"std.int.add" e6393:r2630:i->d2005:i) e6397:(e6395:r2631:"std::text::str::len"->d786:"std.text.str.len" e6396:r2632:needle->d2004:needle)))); p1506:r2633:nil->d503:"std.data.opt.opt.nil" -> e6401:r2634:nil->d503:"std.data.opt.opt.nil" }))
      pub d853:"std.text.str.contains": std::text::str::str -> std::text::str::str -> bool = e6416:(fn p1507:d2006:source -> e6415:(fn p1508:d2007:needle -> e6414:case e6411:(e6409:(e6407:(e6405:r2635:find_at->d851:"std.text.str.find_at" e6406:r2636:source->d2006:source) e6408:r2637:needle->d2007:needle) e6410:0) { p1510:r2638:just->d504:"std.data.opt.opt.just"(p1509:_) -> e6412:true; p1511:r2639:nil->d503:"std.data.opt.opt.nil" -> e6413:false }))
      pub d854:"std.text.str.starts_with": std::text::str::str -> std::text::str::str -> bool = e6425:(fn p1512:d2008:source -> e6424:(fn p1513:d2009:prefix -> e6423:(e6421:(e6419:(e6417:r2640:starts_with_at->d848:"std.text.str.starts_with_at" e6418:r2641:source->d2008:source) e6420:r2642:prefix->d2009:prefix) e6422:0)))
      pub d855:"std.text.str.ends_with": std::text::str::str -> std::text::str::str -> bool = e6455:(fn p1514:d2010:source -> e6454:(fn p1515:d2011:suffix -> e6453:block { let my p1516:d2012:source_len = e6428:(e6426:r2643:"std::text::str::len"->d786:"std.text.str.len" e6427:r2644:source->d2010:source); e6452:block { let my p1517:d2013:suffix_len = e6431:(e6429:r2645:"std::text::str::len"->d786:"std.text.str.len" e6430:r2646:suffix->d2011:suffix); e6451:case e6438:(e6437:r2650:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6436:(e6434:(e6432:r2647:"std::int::le"->d47:"std.int.le" e6433:r2648:suffix_len->d2013:suffix_len) e6435:r2649:source_len->d2012:source_len)) { p1518:true -> e6449:(e6443:(e6441:(e6439:r2651:starts_with_at->d848:"std.text.str.starts_with_at" e6440:r2652:source->d2010:source) e6442:r2653:suffix->d2011:suffix) e6448:(e6446:(e6444:r2654:"std::int::sub"->d51:"std.int.sub" e6445:r2655:source_len->d2012:source_len) e6447:r2656:suffix_len->d2013:suffix_len)); p1519:false -> e6450:false } } }))
      my d856:"std.text.str.split_newline_byte_scan_min": int = e6456:2
      pub d857:"std.text.str.split": std::text::str::str -> std::text::str::str -> std::data::list::list std::text::str::str = e6525:(fn p1520:d2014:source -> e6524:(fn p1521:d2015:separator -> e6523:block { let my p1522:d2016:source_len = e6459:(e6457:r2657:"std::text::str::len"->d786:"std.text.str.len" e6458:r2658:source->d2014:source); e6522:block { let my p1523:d2017:separator_len = e6462:(e6460:r2659:"std::text::str::len"->d786:"std.text.str.len" e6461:r2660:separator->d2015:separator); e6521:case e6469:(e6468:r2663:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6467:(e6465:(e6463:r2661:"std::int::eq"->d45:"std.int.eq" e6464:r2662:separator_len->d2017:separator_len) e6466:0)) { p1531:true -> e6472:(e6471:builtin_op::list_singleton e6470:r2664:source->d2014:source); p1532:false -> e6520:case e6479:(e6478:r2667:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6477:(e6476:(e6474:r2666:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e6473:r2665:separator->d2015:separator) e6475:"\n")) { p1529:true -> e6510:case e6486:(e6485:r2671:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6484:(e6483:(e6481:r2669:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e6480:r2668:source_len->d2016:source_len) e6482:r2670:split_newline_byte_scan_min->d856:"std.text.str.split_newline_byte_scan_min")) { p1527:true -> e6495:(e6493:(e6491:(e6489:(e6487:r2672:split_generic->d858:"std.text.str.split_generic" e6488:r2673:source->d2014:source) e6490:r2674:source_len->d2016:source_len) e6492:r2675:separator->d2015:separator) e6494:r2676:separator_len->d2017:separator_len); p1528:false -> e6509:case e6498:(e6496:r2677:split_newline_bytes->d860:"std.text.str.split_newline_bytes" e6497:r2678:source->d2014:source) { p1525:r2679:just->d504:"std.data.opt.opt.just"(p1524:d2018:parts) -> e6499:r2680:parts->d2018:parts; p1526:r2681:nil->d503:"std.data.opt.opt.nil" -> e6508:(e6506:(e6504:(e6502:(e6500:r2682:split_generic->d858:"std.text.str.split_generic" e6501:r2683:source->d2014:source) e6503:r2684:source_len->d2016:source_len) e6505:r2685:separator->d2015:separator) e6507:r2686:separator_len->d2017:separator_len) } }; p1530:false -> e6519:(e6517:(e6515:(e6513:(e6511:r2687:split_generic->d858:"std.text.str.split_generic" e6512:r2688:source->d2014:source) e6514:r2689:source_len->d2016:source_len) e6516:r2690:separator->d2015:separator) e6518:r2691:separator_len->d2017:separator_len) } } } }))
      my d858:"std.text.str.split_generic": std::text::str::str -> int -> std::text::str::str -> int -> std::data::list::list std::text::str::str = e6544:(fn p1533:d2019:source -> e6543:(fn p1534:d2020:source_len -> e6542:(fn p1535:d2021:separator -> e6541:(fn p1536:d2022:separator_len -> e6540:(e6536:(e6534:(e6532:(e6530:(e6528:(e6526:r2692:split_generic_loop->d859:"std.text.str.split_generic_loop" e6527:r2693:source->d2019:source) e6529:r2694:source_len->d2020:source_len) e6531:r2695:separator->d2021:separator) e6533:r2696:separator_len->d2022:separator_len) e6535:0) e6539:(e6537:builtin_op::list_empty e6538:()))))))
      my d859:"std.text.str.split_generic_loop": std::text::str::str -> int -> std::text::str::str -> int -> int -> std::data::list::list std::text::str::str -> std::data::list::list std::text::str::str = e6604:(fn p1537:d2023:source -> e6603:(fn p1538:d2024:source_len -> e6602:(fn p1539:d2025:separator -> e6601:(fn p1540:d2026:separator_len -> e6600:(fn p1541:d2027:start -> e6599:(fn p1542:d2028:out -> e6598:case e6555:(e6553:(e6551:(e6549:(e6547:(e6545:r2697:find_at_len->d849:"std.text.str.find_at_len" e6546:r2698:source->d2023:source) e6548:r2699:source_len->d2024:source_len) e6550:r2700:separator->d2025:separator) e6552:r2701:separator_len->d2026:separator_len) e6554:r2702:start->d2027:start) { p1544:r2703:just->d504:"std.data.opt.opt.just"(p1543:d2029:i) -> e6584:block { let my p1545:d2030:piece = e6562:(e6560:(e6558:(e6556:r2704:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e6557:r2705:source->d2023:source) e6559:r2706:start->d2027:start) e6561:r2707:i->d2029:i); e6583:(e6577:(e6571:(e6569:(e6567:(e6565:(e6563:r2708:split_generic_loop->d859:"std.text.str.split_generic_loop" e6564:r2709:source->d2023:source) e6566:r2710:source_len->d2024:source_len) e6568:r2711:separator->d2025:separator) e6570:r2712:separator_len->d2026:separator_len) e6576:(e6574:(e6572:r2713:"std::int::add"->d50:"std.int.add" e6573:r2714:i->d2029:i) e6575:r2715:separator_len->d2026:separator_len)) e6582:(e6580:(e6578:r2716:"std::data::list::cons"->d491:"std.data.list.cons" e6579:r2717:piece->d2030:piece) e6581:r2718:out->d2028:out)) }; p1546:r2719:nil->d503:"std.data.opt.opt.nil" -> e6597:(e6585:r2720:"std::data::list::rev"->d494:"std.data.list.rev" e6596:(e6594:(e6586:r2721:"std::data::list::cons"->d491:"std.data.list.cons" e6593:(e6591:(e6589:(e6587:r2722:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e6588:r2723:source->d2023:source) e6590:r2724:start->d2027:start) e6592:r2725:source_len->d2024:source_len)) e6595:r2726:out->d2028:out)) }))))))
      my d860:"std.text.str.split_newline_bytes": std::text::str::str -> std::data::opt::opt(std::data::list::list std::text::str::str) = e6671:(fn p1547:d2031:source -> e6670:block { let my p1548:d2032:data = e6607:(e6605:r2727:"std::text::str::to_bytes"->d794:"std.text.str.to_bytes" e6606:r2728:source->d2031:source); e6669:block { let my p1549:d2033:end = e6610:(e6608:r2729:"std::text::bytes::len"->d653:"std.text.bytes.len" e6609:r2730:data->d2032:data); e6668:block { let my p1550:d2034:chunk_count = e6619:(e6617:(e6611:r2731:"std::int::div"->d53:"std.int.div" e6616:(e6615:(e6613:r2733:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e6612:r2732:end->d2033:end) e6614:1023)) e6618:1024); e6667:block { let my p1551:d2035:scan = e6644:(e6632:(e6625:(e6624:(e6623:(e6621:r2734:"#op:infix:..<"->d408:"std.core.ops.#op:infix:..<" e6620:0) e6622:r2735:chunk_count->d2034:chunk_count).s283.fold=>d449:"std.data.fold.Fold.fold") e6631:(e6626:0, e6629:(e6627:builtin_op::list_empty e6628:()), e6630:true)) e6643:(fn p1552:d2036:state -> e6642:(fn p1553:d2037:chunk -> e6641:(e6639:(e6637:(e6635:(e6633:r2736:split_newline_bytes_chunk->d861:"std.text.str.split_newline_bytes_chunk" e6634:r2737:data->d2032:data) e6636:r2738:end->d2033:end) e6638:r2739:state->d2036:state) e6640:r2740:chunk->d2037:chunk)))); e6666:case e6645:r2741:scan->d2035:scan { p1557:(p1554:d2038:start, p1555:d2039:out, p1556:true) -> e6664:(e6646:r2742:just->d504:"std.data.opt.opt.just" e6663:(e6647:r2743:"std::data::list::rev"->d494:"std.data.list.rev" e6662:(e6660:(e6648:r2744:"std::data::list::cons"->d491:"std.data.list.cons" e6659:(e6649:r2745:"std::text::bytes::to_utf8_lossy"->d666:"std.text.bytes.to_utf8_lossy" e6658:(e6652:(e6650:r2746:"std::text::bytes::index_range"->d657:"std.text.bytes.index_range" e6651:r2747:data->d2032:data) e6657:(e6655:(e6653:r2748:"std::data::range::range"->d511:"std.data.range.range" e6654:r2749:start->d2038:start) e6656:r2750:end->d2033:end)))) e6661:r2751:out->d2039:out))); p1558:_ -> e6665:r2752:nil->d503:"std.data.opt.opt.nil" } } } } })
      my d861:"std.text.str.split_newline_bytes_chunk": std::text::bytes::bytes -> int -> (int, std::data::list::list std::text::str::str, bool) -> int -> (int, std::data::list::list std::text::str::str, bool) = e6721:(fn p1559:d2040:data -> e6720:(fn p1560:d2041:end -> e6719:(fn p1561:d2042:state -> e6718:(fn p1562:d2043:chunk -> e6717:case e6672:r2753:state->d2042:state { p1566:(p1563:_, p1564:_, p1565:false) -> e6673:r2754:state->d2042:state; p1567:_ -> e6716:block { let my p1568:d2044:i = e6678:(e6677:(e6675:r2756:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e6674:r2755:chunk->d2043:chunk) e6676:1024); e6715:block { let my p1569:d2045:chunk_end = e6696:case e6689:(e6688:r2761:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6687:(e6686:(e6684:r2759:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e6683:(e6682:(e6680:r2758:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e6679:r2757:i->d2044:i) e6681:1024)) e6685:r2760:end->d2041:end)) { p1570:true -> e6694:(e6693:(e6691:r2763:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e6690:r2762:i->d2044:i) e6692:1024); p1571:false -> e6695:r2764:end->d2041:end }; e6714:(e6704:(e6702:(e6701:(e6699:(e6697:r2765:"std::data::range::range"->d511:"std.data.range.range" e6698:r2766:i->d2044:i) e6700:r2767:chunk_end->d2045:chunk_end).s284.fold=>d449:"std.data.fold.Fold.fold") e6703:r2768:state->d2042:state) e6713:(fn p1572:d2046:state -> e6712:(fn p1573:d2047:j -> e6711:(e6709:(e6707:(e6705:r2769:split_newline_bytes_step->d862:"std.text.str.split_newline_bytes_step" e6706:r2770:data->d2040:data) e6708:r2771:state->d2046:state) e6710:r2772:j->d2047:j)))) } } }))))
      my d862:"std.text.str.split_newline_bytes_step": std::text::bytes::bytes -> (int, std::data::list::list std::text::str::str, bool) -> int -> (int, std::data::list::list std::text::str::str, bool) = e6762:(fn p1574:d2048:data -> e6761:(fn p1575:d2049:state -> e6760:(fn p1576:d2050:i -> e6759:case e6722:r2773:state->d2049:state { p1580:(p1577:d2051:start, p1578:d2052:out, p1579:true) -> e6757:case e6727:(e6725:(e6723:r2774:"std::text::bytes::index_raw"->d656:"std.text.bytes.index_raw" e6724:r2775:data->d2048:data) e6726:r2776:i->d2050:i) { p1581:10 -> e6751:block { let my p1582:d2053:piece = e6738:(e6728:r2777:"std::text::bytes::to_utf8_lossy"->d666:"std.text.bytes.to_utf8_lossy" e6737:(e6731:(e6729:r2778:"std::text::bytes::index_range"->d657:"std.text.bytes.index_range" e6730:r2779:data->d2048:data) e6736:(e6734:(e6732:r2780:"std::data::range::range"->d511:"std.data.range.range" e6733:r2781:start->d2051:start) e6735:r2782:i->d2050:i))); e6750:(e6743:(e6742:(e6740:r2784:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e6739:r2783:i->d2050:i) e6741:1), e6748:(e6746:(e6744:r2785:"std::data::list::cons"->d491:"std.data.list.cons" e6745:r2786:piece->d2053:piece) e6747:r2787:out->d2052:out), e6749:true) }; p1583:13 -> e6755:(e6752:r2788:start->d2051:start, e6753:r2789:out->d2052:out, e6754:false); p1584:_ -> e6756:r2790:state->d2049:state }; p1585:_ -> e6758:r2791:state->d2049:state })))
      pub d863:"std.text.str.split_once": std::text::str::str -> std::text::str::str -> std::data::opt::opt (std::text::str::str, std::text::str::str) = e6806:(fn p1586:d2054:source -> e6805:(fn p1587:d2055:separator -> e6804:block { let my p1588:d2056:source_len = e6765:(e6763:r2792:"std::text::str::len"->d786:"std.text.str.len" e6764:r2793:source->d2054:source); e6803:block { let my p1589:d2057:separator_len = e6768:(e6766:r2794:"std::text::str::len"->d786:"std.text.str.len" e6767:r2795:separator->d2055:separator); e6802:case e6779:(e6777:(e6775:(e6773:(e6771:(e6769:r2796:find_at_len->d849:"std.text.str.find_at_len" e6770:r2797:source->d2054:source) e6772:r2798:source_len->d2056:source_len) e6774:r2799:separator->d2055:separator) e6776:r2800:separator_len->d2057:separator_len) e6778:0) { p1591:r2801:just->d504:"std.data.opt.opt.just"(p1590:d2058:i) -> e6800:(e6780:r2802:just->d504:"std.data.opt.opt.just" e6799:(e6787:(e6785:(e6783:(e6781:r2803:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e6782:r2804:source->d2054:source) e6784:0) e6786:r2805:i->d2058:i), e6798:(e6796:(e6790:(e6788:r2806:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e6789:r2807:source->d2054:source) e6795:(e6793:(e6791:r2808:"std::int::add"->d50:"std.int.add" e6792:r2809:i->d2058:i) e6794:r2810:separator_len->d2057:separator_len)) e6797:r2811:source_len->d2056:source_len))); p1592:r2812:nil->d503:"std.data.opt.opt.nil" -> e6801:r2813:nil->d503:"std.data.opt.opt.nil" } } }))
      my d864:"std.text.str.join_tail": std::data::list::list std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e6829:(fn p1593:d2059:parts -> e6828:(fn p1594:d2060:separator -> e6827:(fn p1595:d2061:out -> e6826:case e6809:(e6807:r2814:"std::data::list::uncons"->d492:"std.data.list.uncons" e6808:r2815:parts->d2059:parts) { p1596:r2816:nil->d503:"std.data.opt.opt.nil" -> e6810:r2817:out->d2061:out; p1600:r2818:just->d504:"std.data.opt.opt.just"(p1599:(p1597:d2062:part, p1598:d2063:rest)) -> e6825:(e6815:(e6813:(e6811:r2819:join_tail->d864:"std.text.str.join_tail" e6812:r2820:rest->d2063:rest) e6814:r2821:separator->d2060:separator) e6824:(e6822:(e6816:r2822:"std::text::str::concat"->d784:"std.text.str.concat" e6821:(e6819:(e6817:r2823:"std::text::str::concat"->d784:"std.text.str.concat" e6818:r2824:out->d2061:out) e6820:r2825:separator->d2060:separator)) e6823:r2826:part->d2062:part)) })))
      pub d865:"std.text.str.join": std::data::list::list std::text::str::str -> std::text::str::str -> std::text::str::str = e6843:(fn p1601:d2064:parts -> e6842:(fn p1602:d2065:separator -> e6841:case e6832:(e6830:r2827:"std::data::list::uncons"->d492:"std.data.list.uncons" e6831:r2828:parts->d2064:parts) { p1603:r2829:nil->d503:"std.data.opt.opt.nil" -> e6833:""; p1607:r2830:just->d504:"std.data.opt.opt.just"(p1606:(p1604:d2066:head, p1605:d2067:tail)) -> e6840:(e6838:(e6836:(e6834:r2831:join_tail->d864:"std.text.str.join_tail" e6835:r2832:tail->d2067:tail) e6837:r2833:separator->d2065:separator) e6839:r2834:head->d2066:head) }))
      my d866:"std.text.str.trim_start_index": std::text::str::str -> int -> int = e6876:(fn p1608:d2068:source -> e6875:(fn p1609:d2069:i -> e6874:case e6852:(e6851:r2839:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6850:(e6846:(e6844:r2835:"std::int::lt"->d46:"std.int.lt" e6845:r2836:i->d2069:i) e6849:(e6847:r2837:"std::text::str::len"->d786:"std.text.str.len" e6848:r2838:source->d2068:source))) { p1612:true -> e6872:case e6861:(e6860:r2844:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6859:(e6853:r2840:"std::text::char::is_whitespace"->d673:"std.text.char.is_whitespace" e6858:(e6856:(e6854:r2841:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e6855:r2842:source->d2068:source) e6857:r2843:i->d2069:i))) { p1610:true -> e6870:(e6864:(e6862:r2845:trim_start_index->d866:"std.text.str.trim_start_index" e6863:r2846:source->d2068:source) e6869:(e6867:(e6865:r2847:"std::int::add"->d50:"std.int.add" e6866:r2848:i->d2069:i) e6868:1)); p1611:false -> e6871:r2849:i->d2069:i }; p1613:false -> e6873:r2850:i->d2069:i }))
      my d867:"std.text.str.trim_end_index": std::text::str::str -> int -> int = e6909:(fn p1614:d2070:source -> e6908:(fn p1615:d2071:end -> e6907:case e6883:(e6882:r2853:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6881:(e6879:(e6877:r2851:"std::int::gt"->d48:"std.int.gt" e6878:r2852:end->d2071:end) e6880:0)) { p1619:true -> e6905:block { let my p1616:d2072:previous = e6888:(e6886:(e6884:r2854:"std::int::sub"->d51:"std.int.sub" e6885:r2855:end->d2071:end) e6887:1); e6904:case e6897:(e6896:r2860:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6895:(e6889:r2856:"std::text::char::is_whitespace"->d673:"std.text.char.is_whitespace" e6894:(e6892:(e6890:r2857:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e6891:r2858:source->d2070:source) e6893:r2859:previous->d2072:previous))) { p1617:true -> e6902:(e6900:(e6898:r2861:trim_end_index->d867:"std.text.str.trim_end_index" e6899:r2862:source->d2070:source) e6901:r2863:previous->d2072:previous); p1618:false -> e6903:r2864:end->d2071:end } }; p1620:false -> e6906:r2865:end->d2071:end }))
      pub d868:"std.text.str.trim_start": std::text::str::str -> std::text::str::str = e6923:(fn p1621:d2073:source -> e6922:(e6918:(e6912:(e6910:r2866:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e6911:r2867:source->d2073:source) e6917:(e6915:(e6913:r2868:trim_start_index->d866:"std.text.str.trim_start_index" e6914:r2869:source->d2073:source) e6916:0)) e6921:(e6919:r2870:"std::text::str::len"->d786:"std.text.str.len" e6920:r2871:source->d2073:source)))
      pub d869:"std.text.str.trim_end": std::text::str::str -> std::text::str::str = e6937:(fn p1622:d2074:source -> e6936:(e6928:(e6926:(e6924:r2872:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e6925:r2873:source->d2074:source) e6927:0) e6935:(e6931:(e6929:r2874:trim_end_index->d867:"std.text.str.trim_end_index" e6930:r2875:source->d2074:source) e6934:(e6932:r2876:"std::text::str::len"->d786:"std.text.str.len" e6933:r2877:source->d2074:source))))
      pub d870:"std.text.str.trim": std::text::str::str -> std::text::str::str = e6968:(fn p1623:d2075:source -> e6967:block { let my p1624:d2076:start = e6942:(e6940:(e6938:r2878:trim_start_index->d866:"std.text.str.trim_start_index" e6939:r2879:source->d2075:source) e6941:0); e6966:block { let my p1625:d2077:end = e6949:(e6945:(e6943:r2880:trim_end_index->d867:"std.text.str.trim_end_index" e6944:r2881:source->d2075:source) e6948:(e6946:r2882:"std::text::str::len"->d786:"std.text.str.len" e6947:r2883:source->d2075:source)); e6965:case e6956:(e6955:r2887:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6954:(e6952:(e6950:r2884:"std::int::le"->d47:"std.int.le" e6951:r2885:start->d2076:start) e6953:r2886:end->d2077:end)) { p1626:true -> e6963:(e6961:(e6959:(e6957:r2888:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e6958:r2889:source->d2075:source) e6960:r2890:start->d2076:start) e6962:r2891:end->d2077:end); p1627:false -> e6964:"" } } })
      pub d871:"std.text.str.repeat": std::text::str::str -> int -> std::text::str::str = e7009:(fn p1628:d2078:source -> e7008:(fn p1629:d2079:count -> e7007:block { let my p1630:d2080:loop = e6992:(fn p1631:d2081:i -> e6991:(fn p1632:d2082:out -> e6990:case e6975:(e6974:r2895:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6973:(e6971:(e6969:r2892:"std::int::lt"->d46:"std.int.lt" e6970:r2893:i->d2081:i) e6972:r2894:count->d2079:count)) { p1633:true -> e6988:(e6982:(e6976:r2896:loop->d2080:loop e6981:(e6979:(e6977:r2897:"std::int::add"->d50:"std.int.add" e6978:r2898:i->d2081:i) e6980:1)) e6987:(e6985:(e6983:r2899:"std::text::str::concat"->d784:"std.text.str.concat" e6984:r2900:out->d2082:out) e6986:r2901:source->d2078:source)); p1634:false -> e6989:r2902:out->d2082:out })); e7006:case e6999:(e6998:r2905:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6997:(e6995:(e6993:r2903:"std::int::le"->d47:"std.int.le" e6994:r2904:count->d2079:count) e6996:0)) { p1635:true -> e7000:""; p1636:false -> e7005:(e7003:(e7001:r2906:loop->d2080:loop e7002:0) e7004:"") } }))
      my d872:"std.text.str.digit_value": std::text::char::char -> std::data::opt::opt int = e7045:(fn p1637:d2083:item -> e7044:case e7012:(e7010:r2907:"std::text::char::to_string"->d672:"std.text.char.to_string" e7011:r2908:item->d2083:item) { p1638:"0" -> e7015:(e7013:r2909:just->d504:"std.data.opt.opt.just" e7014:0); p1639:"1" -> e7018:(e7016:r2910:just->d504:"std.data.opt.opt.just" e7017:1); p1640:"2" -> e7021:(e7019:r2911:just->d504:"std.data.opt.opt.just" e7020:2); p1641:"3" -> e7024:(e7022:r2912:just->d504:"std.data.opt.opt.just" e7023:3); p1642:"4" -> e7027:(e7025:r2913:just->d504:"std.data.opt.opt.just" e7026:4); p1643:"5" -> e7030:(e7028:r2914:just->d504:"std.data.opt.opt.just" e7029:5); p1644:"6" -> e7033:(e7031:r2915:just->d504:"std.data.opt.opt.just" e7032:6); p1645:"7" -> e7036:(e7034:r2916:just->d504:"std.data.opt.opt.just" e7035:7); p1646:"8" -> e7039:(e7037:r2917:just->d504:"std.data.opt.opt.just" e7038:8); p1647:"9" -> e7042:(e7040:r2918:just->d504:"std.data.opt.opt.just" e7041:9); p1648:_ -> e7043:r2919:nil->d503:"std.data.opt.opt.nil" })
      my d873:"std.text.str.parse_unsigned_int": std::text::str::str -> int -> int -> int -> std::data::opt::opt int = e7101:(fn p1649:d2084:source -> e7100:(fn p1650:d2085:start -> e7099:(fn p1651:d2086:i -> e7098:(fn p1652:d2087:acc -> e7097:case e7054:(e7053:r2924:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7052:(e7048:(e7046:r2920:"std::int::lt"->d46:"std.int.lt" e7047:r2921:i->d2086:i) e7051:(e7049:r2922:"std::text::str::len"->d786:"std.text.str.len" e7050:r2923:source->d2084:source))) { p1658:true -> e7084:case e7061:(e7055:r2925:digit_value->d872:"std.text.str.digit_value" e7060:(e7058:(e7056:r2926:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e7057:r2927:source->d2084:source) e7059:r2928:i->d2086:i)) { p1654:r2929:just->d504:"std.data.opt.opt.just"(p1653:d2088:digit) -> e7082:(e7072:(e7066:(e7064:(e7062:r2930:parse_unsigned_int->d873:"std.text.str.parse_unsigned_int" e7063:r2931:source->d2084:source) e7065:r2932:start->d2085:start) e7071:(e7069:(e7067:r2933:"std::int::add"->d50:"std.int.add" e7068:r2934:i->d2086:i) e7070:1)) e7081:(e7079:(e7073:r2935:"std::int::add"->d50:"std.int.add" e7078:(e7076:(e7074:r2936:"std::int::mul"->d52:"std.int.mul" e7075:r2937:acc->d2087:acc) e7077:10)) e7080:r2938:digit->d2088:digit)); p1655:r2939:nil->d503:"std.data.opt.opt.nil" -> e7083:r2940:nil->d503:"std.data.opt.opt.nil" }; p1659:false -> e7096:case e7091:(e7090:r2944:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7089:(e7087:(e7085:r2941:"std::int::eq"->d45:"std.int.eq" e7086:r2942:i->d2086:i) e7088:r2943:start->d2085:start)) { p1656:true -> e7092:r2945:nil->d503:"std.data.opt.opt.nil"; p1657:false -> e7095:(e7093:r2946:just->d504:"std.data.opt.opt.just" e7094:r2947:acc->d2087:acc) } }))))
      pub d874:"std.text.str.to_int": std::text::str::str -> std::data::opt::opt int = e7157:(fn p1660:d2089:source -> e7156:case e7110:(e7109:r2951:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7108:(e7106:(e7102:r2948:"std::int::eq"->d45:"std.int.eq" e7105:(e7103:r2949:"std::text::str::len"->d786:"std.text.str.len" e7104:r2950:source->d2089:source)) e7107:0)) { p1667:true -> e7111:r2952:nil->d503:"std.data.opt.opt.nil"; p1668:false -> e7155:case e7118:(e7112:r2953:"std::text::char::to_string"->d672:"std.text.char.to_string" e7117:(e7115:(e7113:r2954:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e7114:r2955:source->d2089:source) e7116:0)) { p1661:"-" -> e7136:case e7127:(e7125:(e7123:(e7121:(e7119:r2956:parse_unsigned_int->d873:"std.text.str.parse_unsigned_int" e7120:r2957:source->d2089:source) e7122:1) e7124:1) e7126:0) { p1663:r2958:just->d504:"std.data.opt.opt.just"(p1662:d2090:value) -> e7134:(e7128:r2959:just->d504:"std.data.opt.opt.just" e7133:(e7131:(e7129:r2960:"std::int::sub"->d51:"std.int.sub" e7130:0) e7132:r2961:value->d2090:value)); p1664:r2962:nil->d503:"std.data.opt.opt.nil" -> e7135:r2963:nil->d503:"std.data.opt.opt.nil" }; p1665:"+" -> e7145:(e7143:(e7141:(e7139:(e7137:r2964:parse_unsigned_int->d873:"std.text.str.parse_unsigned_int" e7138:r2965:source->d2089:source) e7140:1) e7142:1) e7144:0); p1666:_ -> e7154:(e7152:(e7150:(e7148:(e7146:r2966:parse_unsigned_int->d873:"std.text.str.parse_unsigned_int" e7147:r2967:source->d2089:source) e7149:0) e7151:0) e7153:0) } })
      pub d875:"std.text.str.replace_once": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e7209:(fn p1669:d2091:source -> e7208:(fn p1670:d2092:from -> e7207:(fn p1671:d2093:to -> e7206:case e7166:(e7165:r2971:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7164:(e7162:(e7158:r2968:"std::int::eq"->d45:"std.int.eq" e7161:(e7159:r2969:"std::text::str::len"->d786:"std.text.str.len" e7160:r2970:from->d2092:from)) e7163:0)) { p1675:true -> e7167:r2972:source->d2091:source; p1676:false -> e7205:case e7174:(e7172:(e7170:(e7168:r2973:find_at->d851:"std.text.str.find_at" e7169:r2974:source->d2091:source) e7171:r2975:from->d2092:from) e7173:0) { p1673:r2976:just->d504:"std.data.opt.opt.just"(p1672:d2094:i) -> e7203:(e7187:(e7175:r2977:"std::text::str::concat"->d784:"std.text.str.concat" e7186:(e7184:(e7176:r2978:"std::text::str::concat"->d784:"std.text.str.concat" e7183:(e7181:(e7179:(e7177:r2979:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e7178:r2980:source->d2091:source) e7180:0) e7182:r2981:i->d2094:i)) e7185:r2982:to->d2093:to)) e7202:(e7198:(e7190:(e7188:r2983:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e7189:r2984:source->d2091:source) e7197:(e7193:(e7191:r2985:"std::int::add"->d50:"std.int.add" e7192:r2986:i->d2094:i) e7196:(e7194:r2987:"std::text::str::len"->d786:"std.text.str.len" e7195:r2988:from->d2092:from))) e7201:(e7199:r2989:"std::text::str::len"->d786:"std.text.str.len" e7200:r2990:source->d2091:source))); p1674:r2991:nil->d503:"std.data.opt.opt.nil" -> e7204:r2992:source->d2091:source } })))
      pub d876:"std.text.str.replace": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e7219:(fn p1677:d2095:source -> e7218:(fn p1678:d2096:from -> e7217:(fn p1679:d2097:to -> e7216:(e7214:(e7212:(e7210:r2993:replace_all->d877:"std.text.str.replace_all" e7211:r2994:source->d2095:source) e7213:r2995:from->d2096:from) e7215:r2996:to->d2097:to))))
      pub d877:"std.text.str.replace_all": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e7289:(fn p1680:d2098:source -> e7288:(fn p1681:d2099:from -> e7287:(fn p1682:d2100:to -> e7286:case e7228:(e7227:r3000:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7226:(e7224:(e7220:r2997:"std::int::eq"->d45:"std.int.eq" e7223:(e7221:r2998:"std::text::str::len"->d786:"std.text.str.len" e7222:r2999:from->d2099:from)) e7225:0)) { p1690:true -> e7229:r3001:source->d2098:source; p1691:false -> e7285:block { let my p1683:d2101:loop = e7279:(fn p1684:d2102:start -> e7278:(fn p1685:d2103:out -> e7277:case e7236:(e7234:(e7232:(e7230:r3002:find_at->d851:"std.text.str.find_at" e7231:r3003:source->d2098:source) e7233:r3004:from->d2099:from) e7235:r3005:start->d2102:start) { p1687:r3006:just->d504:"std.data.opt.opt.just"(p1686:d2104:i) -> e7263:block { let my p1688:d2105:prefix = e7243:(e7241:(e7239:(e7237:r3007:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e7238:r3008:source->d2098:source) e7240:r3009:start->d2102:start) e7242:r3010:i->d2104:i); e7262:(e7252:(e7244:r3011:loop->d2101:loop e7251:(e7247:(e7245:r3012:"std::int::add"->d50:"std.int.add" e7246:r3013:i->d2104:i) e7250:(e7248:r3014:"std::text::str::len"->d786:"std.text.str.len" e7249:r3015:from->d2099:from))) e7261:(e7259:(e7253:r3016:"std::text::str::concat"->d784:"std.text.str.concat" e7258:(e7256:(e7254:r3017:"std::text::str::concat"->d784:"std.text.str.concat" e7255:r3018:out->d2103:out) e7257:r3019:prefix->d2105:prefix)) e7260:r3020:to->d2100:to)) }; p1689:r3021:nil->d503:"std.data.opt.opt.nil" -> e7276:(e7266:(e7264:r3022:"std::text::str::concat"->d784:"std.text.str.concat" e7265:r3023:out->d2103:out) e7275:(e7271:(e7269:(e7267:r3024:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e7268:r3025:source->d2098:source) e7270:r3026:start->d2102:start) e7274:(e7272:r3027:"std::text::str::len"->d786:"std.text.str.len" e7273:r3028:source->d2098:source))) })); e7284:(e7282:(e7280:r3029:loop->d2101:loop e7281:0) e7283:"") } })))
      my d878:"std.text.str.word_prefix_small_scan_limit": int = e7290:512
      pub d879:"std.text.str.word_prefix_at": std::text::str::str -> int -> std::text::str::str = e7384:(fn p1692:d2106:source -> e7383:(fn p1693:d2107:start -> e7382:block { let my p1694:d2108:source_len = e7293:(e7291:r3030:"std::text::str::len"->d786:"std.text.str.len" e7292:r3031:source->d2106:source); e7381:block { let my p1695:d2109:remaining = e7298:(e7297:(e7295:r3033:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e7294:r3032:source_len->d2108:source_len) e7296:r3034:start->d2107:start); e7380:case e7305:(e7304:r3038:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7303:(e7302:(e7300:r3036:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e7299:r3035:remaining->d2109:remaining) e7301:r3037:word_prefix_small_scan_limit->d878:"std.text.str.word_prefix_small_scan_limit")) { p1706:true -> e7351:block { let my p1696:d2110:loop = e7347:(fn p1697:d2111:i -> e7346:case e7312:(e7311:r3042:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7310:(e7309:(e7307:r3040:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e7306:r3039:i->d2111:i) e7308:r3041:source_len->d2108:source_len)) { p1701:true -> e7338:block { let my p1698:d2112:item = e7317:(e7315:(e7313:r3043:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e7314:r3044:source->d2106:source) e7316:r3045:i->d2111:i); e7337:case e7322:(e7321:r3048:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7320:(e7318:r3046:"std::text::char::is_word"->d675:"std.text.char.is_word" e7319:r3047:item->d2112:item)) { p1699:true -> e7329:(e7323:r3049:loop->d2110:loop e7328:(e7327:(e7325:r3051:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7324:r3050:i->d2111:i) e7326:1)); p1700:false -> e7336:(e7334:(e7332:(e7330:r3052:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e7331:r3053:source->d2106:source) e7333:r3054:start->d2107:start) e7335:r3055:i->d2111:i) } }; p1702:false -> e7345:(e7343:(e7341:(e7339:r3056:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e7340:r3057:source->d2106:source) e7342:r3058:start->d2107:start) e7344:r3059:i->d2111:i) }); e7350:(e7348:r3060:loop->d2110:loop e7349:r3061:start->d2107:start) }; p1707:false -> e7379:block { let my p1703:d2113:end = e7371:case e7358:(e7357:r3064:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7356:(e7355:(e7353:r3063:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e7352:r3062:start->d2107:start) e7354:0)) { p1704:true -> e7363:(e7361:(e7359:r3065:word_prefix_ascii_or_slow_end->d880:"std.text.str.word_prefix_ascii_or_slow_end" e7360:r3066:source->d2106:source) e7362:r3067:source_len->d2108:source_len); p1705:false -> e7370:(e7368:(e7366:(e7364:r3068:word_prefix_slow_end->d884:"std.text.str.word_prefix_slow_end" e7365:r3069:source->d2106:source) e7367:r3070:source_len->d2108:source_len) e7369:r3071:start->d2107:start) }; e7378:(e7376:(e7374:(e7372:r3072:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e7373:r3073:source->d2106:source) e7375:r3074:start->d2107:start) e7377:r3075:end->d2113:end) } } } }))
      my d880:"std.text.str.word_prefix_ascii_or_slow_end": std::text::str::str -> int -> int = e7437:(fn p1708:d2114:source -> e7436:(fn p1709:d2115:source_len -> e7435:block { let my p1710:d2116:data = e7387:(e7385:r3076:"std::text::str::to_bytes"->d794:"std.text.str.to_bytes" e7386:r3077:source->d2114:source); e7434:block { let my p1711:d2117:data_len = e7390:(e7388:r3078:"std::text::bytes::len"->d653:"std.text.bytes.len" e7389:r3079:data->d2116:data); e7433:block { let my p1712:d2118:chunk_count = e7399:(e7397:(e7391:r3080:"std::int::div"->d53:"std.int.div" e7396:(e7395:(e7393:r3082:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7392:r3081:data_len->d2117:data_len) e7394:1023)) e7398:1024); e7432:block { let my p1713:d2119:scan = e7421:(e7409:(e7405:(e7404:(e7403:(e7401:r3083:"#op:infix:..<"->d408:"std.core.ops.#op:infix:..<" e7400:0) e7402:r3084:chunk_count->d2118:chunk_count).s285.fold=>d449:"std.data.fold.Fold.fold") e7408:(e7406:0, e7407:0)) e7420:(fn p1714:d2120:state -> e7419:(fn p1715:d2121:chunk -> e7418:(e7416:(e7414:(e7412:(e7410:r3085:word_prefix_ascii_chunk->d881:"std.text.str.word_prefix_ascii_chunk" e7411:r3086:data->d2116:data) e7413:r3087:data_len->d2117:data_len) e7415:r3088:state->d2120:state) e7417:r3089:chunk->d2121:chunk)))); e7431:case e7422:r3090:scan->d2119:scan { p1718:(p1716:d2122:end, p1717:2) -> e7429:(e7427:(e7425:(e7423:r3091:word_prefix_slow_end->d884:"std.text.str.word_prefix_slow_end" e7424:r3092:source->d2114:source) e7426:r3093:source_len->d2115:source_len) e7428:r3094:end->d2122:end); p1721:(p1719:d2123:end, p1720:_) -> e7430:r3095:end->d2123:end } } } } }))
      my d881:"std.text.str.word_prefix_ascii_chunk": std::text::bytes::bytes -> int -> (int, int) -> int -> (int, int) = e7487:(fn p1722:d2124:data -> e7486:(fn p1723:d2125:data_len -> e7485:(fn p1724:d2126:state -> e7484:(fn p1725:d2127:chunk -> e7483:case e7438:r3096:state->d2126:state { p1728:(p1726:_, p1727:0) -> e7481:block { let my p1729:d2128:i = e7443:(e7442:(e7440:r3098:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e7439:r3097:chunk->d2127:chunk) e7441:1024); e7480:block { let my p1730:d2129:chunk_end = e7461:case e7454:(e7453:r3103:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7452:(e7451:(e7449:r3101:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e7448:(e7447:(e7445:r3100:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7444:r3099:i->d2128:i) e7446:1024)) e7450:r3102:data_len->d2125:data_len)) { p1731:true -> e7459:(e7458:(e7456:r3105:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7455:r3104:i->d2128:i) e7457:1024); p1732:false -> e7460:r3106:data_len->d2125:data_len }; e7479:(e7469:(e7467:(e7466:(e7464:(e7462:r3107:"std::data::range::range"->d511:"std.data.range.range" e7463:r3108:i->d2128:i) e7465:r3109:chunk_end->d2129:chunk_end).s286.fold=>d449:"std.data.fold.Fold.fold") e7468:r3110:state->d2126:state) e7478:(fn p1733:d2130:state -> e7477:(fn p1734:d2131:j -> e7476:(e7474:(e7472:(e7470:r3111:word_prefix_ascii_step->d882:"std.text.str.word_prefix_ascii_step" e7471:r3112:data->d2124:data) e7473:r3113:state->d2130:state) e7475:r3114:j->d2131:j)))) } }; p1735:_ -> e7482:r3115:state->d2126:state }))))
      my d882:"std.text.str.word_prefix_ascii_step": std::text::bytes::bytes -> (int, int) -> int -> (int, int) = e7526:(fn p1736:d2132:data -> e7525:(fn p1737:d2133:state -> e7524:(fn p1738:d2134:i -> e7523:case e7488:r3116:state->d2133:state { p1741:(p1739:d2135:end, p1740:0) -> e7521:block { let my p1742:d2136:byte = e7493:(e7491:(e7489:r3117:"std::text::bytes::index_raw"->d656:"std.text.bytes.index_raw" e7490:r3118:data->d2132:data) e7492:r3119:i->d2134:i); e7520:case e7498:(e7497:r3122:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7496:(e7494:r3120:ascii_word_byte->d883:"std.text.str.ascii_word_byte" e7495:r3121:byte->d2136:byte)) { p1745:true -> e7505:(e7503:(e7502:(e7500:r3124:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7499:r3123:i->d2134:i) e7501:1), e7504:0); p1746:false -> e7519:case e7512:(e7511:r3127:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7510:(e7509:(e7507:r3126:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e7506:r3125:byte->d2136:byte) e7508:128)) { p1743:true -> e7515:(e7513:r3128:i->d2134:i, e7514:1); p1744:false -> e7518:(e7516:r3129:i->d2134:i, e7517:2) } } }; p1747:_ -> e7522:r3130:state->d2133:state })))
      my d883:"std.text.str.ascii_word_byte": int -> bool = e7592:(fn p1748:d2137:byte -> e7591:(e7590:(e7572:r3145:"#op:infix:or"->d426:"std.core.ops.#op:infix:or" e7588:(fn p1759:() -> e7571:(e7570:(e7552:r3139:"#op:infix:or"->d426:"std.core.ops.#op:infix:or" e7568:(fn p1755:() -> e7551:(e7550:(e7532:r3133:"#op:infix:or"->d426:"std.core.ops.#op:infix:or" e7548:(fn p1751:() -> e7531:(e7530:(e7528:r3132:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e7527:r3131:byte->d2137:byte) e7529:95))) e7549:(fn p1752:() -> e7547:(e7546:(e7538:r3136:"#op:infix:and"->d425:"std.core.ops.#op:infix:and" e7544:(fn p1749:() -> e7537:(e7536:(e7534:r3134:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e7533:48) e7535:r3135:byte->d2137:byte))) e7545:(fn p1750:() -> e7543:(e7542:(e7540:r3138:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e7539:r3137:byte->d2137:byte) e7541:57))))))) e7569:(fn p1756:() -> e7567:(e7566:(e7558:r3142:"#op:infix:and"->d425:"std.core.ops.#op:infix:and" e7564:(fn p1753:() -> e7557:(e7556:(e7554:r3140:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e7553:65) e7555:r3141:byte->d2137:byte))) e7565:(fn p1754:() -> e7563:(e7562:(e7560:r3144:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e7559:r3143:byte->d2137:byte) e7561:90))))))) e7589:(fn p1760:() -> e7587:(e7586:(e7578:r3148:"#op:infix:and"->d425:"std.core.ops.#op:infix:and" e7584:(fn p1757:() -> e7577:(e7576:(e7574:r3146:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e7573:97) e7575:r3147:byte->d2137:byte))) e7585:(fn p1758:() -> e7583:(e7582:(e7580:r3150:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e7579:r3149:byte->d2137:byte) e7581:122))))))
      my d884:"std.text.str.word_prefix_slow_end": std::text::str::str -> int -> int -> int = e7639:(fn p1761:d2138:source -> e7638:(fn p1762:d2139:source_len -> e7637:(fn p1763:d2140:i -> e7636:block { let my p1764:d2141:count = e7597:(e7596:(e7594:r3152:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e7593:r3151:source_len->d2139:source_len) e7595:r3153:i->d2140:i); e7635:block { let my p1765:d2142:chunk_count = e7606:(e7604:(e7598:r3154:"std::int::div"->d53:"std.int.div" e7603:(e7602:(e7600:r3156:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7599:r3155:count->d2141:count) e7601:1023)) e7605:1024); e7634:block { let my p1766:d2143:scan = e7630:(e7616:(e7612:(e7611:(e7610:(e7608:r3157:"#op:infix:..<"->d408:"std.core.ops.#op:infix:..<" e7607:0) e7609:r3158:chunk_count->d2142:chunk_count).s287.fold=>d449:"std.data.fold.Fold.fold") e7615:(e7613:r3159:i->d2140:i, e7614:true)) e7629:(fn p1767:d2144:state -> e7628:(fn p1768:d2145:chunk -> e7627:(e7625:(e7623:(e7621:(e7619:(e7617:r3160:word_prefix_slow_chunk->d885:"std.text.str.word_prefix_slow_chunk" e7618:r3161:source->d2138:source) e7620:r3162:source_len->d2139:source_len) e7622:r3163:state->d2144:state) e7624:r3164:i->d2140:i) e7626:r3165:chunk->d2145:chunk)))); e7633:case e7631:r3166:scan->d2143:scan { p1771:(p1769:d2146:end, p1770:_) -> e7632:r3167:end->d2146:end } } } })))
      my d885:"std.text.str.word_prefix_slow_chunk": std::text::str::str -> int -> (int, bool) -> int -> int -> (int, bool) = e7694:(fn p1772:d2147:source -> e7693:(fn p1773:d2148:source_len -> e7692:(fn p1774:d2149:state -> e7691:(fn p1775:d2150:start -> e7690:(fn p1776:d2151:chunk -> e7689:case e7640:r3168:state->d2149:state { p1779:(p1777:_, p1778:true) -> e7687:block { let my p1780:d2152:i = e7649:(e7648:(e7642:r3170:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7641:r3169:start->d2150:start) e7647:(e7646:(e7644:r3172:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e7643:r3171:chunk->d2151:chunk) e7645:1024)); e7686:block { let my p1781:d2153:chunk_end = e7667:case e7660:(e7659:r3177:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7658:(e7657:(e7655:r3175:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e7654:(e7653:(e7651:r3174:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7650:r3173:i->d2152:i) e7652:1024)) e7656:r3176:source_len->d2148:source_len)) { p1782:true -> e7665:(e7664:(e7662:r3179:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7661:r3178:i->d2152:i) e7663:1024); p1783:false -> e7666:r3180:source_len->d2148:source_len }; e7685:(e7675:(e7673:(e7672:(e7670:(e7668:r3181:"std::data::range::range"->d511:"std.data.range.range" e7669:r3182:i->d2152:i) e7671:r3183:chunk_end->d2153:chunk_end).s288.fold=>d449:"std.data.fold.Fold.fold") e7674:r3184:state->d2149:state) e7684:(fn p1784:d2154:state -> e7683:(fn p1785:d2155:index -> e7682:(e7680:(e7678:(e7676:r3185:word_prefix_slow_step->d886:"std.text.str.word_prefix_slow_step" e7677:r3186:source->d2147:source) e7679:r3187:state->d2154:state) e7681:r3188:index->d2155:index)))) } }; p1786:_ -> e7688:r3189:state->d2149:state })))))
      my d886:"std.text.str.word_prefix_slow_step": std::text::str::str -> (int, bool) -> int -> (int, bool) = e7720:(fn p1787:d2156:source -> e7719:(fn p1788:d2157:state -> e7718:(fn p1789:d2158:i -> e7717:case e7695:r3190:state->d2157:state { p1792:(p1790:d2159:end, p1791:true) -> e7715:case e7704:(e7703:r3195:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7702:(e7696:r3191:"std::text::char::is_word"->d675:"std.text.char.is_word" e7701:(e7699:(e7697:r3192:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e7698:r3193:source->d2156:source) e7700:r3194:i->d2158:i))) { p1793:true -> e7711:(e7709:(e7708:(e7706:r3197:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7705:r3196:i->d2158:i) e7707:1), e7710:true); p1794:false -> e7714:(e7712:r3198:i->d2158:i, e7713:false) }; p1795:_ -> e7716:r3199:state->d2157:state })))
      my d887 mod {
        d888: std::text::str::str -> int -> std::text::char::char = e7727:(fn p1796:d2160:s -> e7726:(fn p1797:d2161:i -> e7725:(e7723:(e7721:r3200:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e7722:r3201:s->d2160:s) e7724:r3202:i->d2161:i)))
      }
      my d889 mod {
        d890: std::text::str::str -> std::data::range::range -> std::text::str::str = e7734:(fn p1798:d2162:s -> e7733:(fn p1799:d2163:r -> e7732:(e7730:(e7728:r3203:"std::text::str::index_range"->d790:"std.text.str.index_range" e7729:r3204:s->d2162:s) e7731:r3205:r->d2163:r)))
      }
      my d891 mod {
        d892: std::control::var::ref('a & 'b, std::text::str::str) -> std::data::range::range -> std::control::var::ref('b | 'a, 'c | std::text::str::str) = e7778:(fn p1800:d2164:r -> e7777:(fn p1801:d2165:i -> e7776:(e7735:r3206:ref->d235:"std.control.var.ref" e7775:{get: e7744:(fn p1802:() -> e7743:(e7741:(e7736:r3207:"std::text::str::index_range"->d790:"std.text.str.index_range" e7740:(e7738:(e7737:r3208:r->d2164:r.s289.get->d236) e7739:())) e7742:r3209:i->d2165:i)), update_effect: e7774:(fn p1803:() -> e7773:block { let my p1804:d2166:loop = e7766:(fn p1805:d2167:x -> e7765:catch e7745:r3210:x->d2167:x { std::control::var::ref_update::update p1806:d2168:old, p1807:d2169:k -> e7764:block { let my p1808:d2170:new_item = e7752:(e7746:r3211:"ref_update::update"->d234:"std.control.var.ref_update.update" e7751:(e7749:(e7747:r3212:"std::text::str::index_range"->d790:"std.text.str.index_range" e7748:r3213:old->d2168:old) e7750:r3214:i->d2165:i)); e7763:(e7753:r3215:loop->d2166:loop e7762:(e7754:r3216:k->d2169:k e7761:(e7759:(e7757:(e7755:r3217:"std::text::str::splice"->d792:"std.text.str.splice" e7756:r3218:old->d2168:old) e7758:r3219:i->d2165:i) e7760:r3220:new_item->d2170:new_item))) } }); e7772:(e7767:r3221:loop->d2166:loop e7771:(e7769:(e7768:r3222:r->d2164:r.s290.update_effect->d238) e7770:())) })})))
      }
      my d893 mod {
        d894: std::control::var::ref('a & 'b, std::text::str::str) -> int -> std::control::var::ref('b | 'a, 'c | std::text::char::char) = e7834:(fn p1809:d2171:r -> e7833:(fn p1810:d2172:i -> e7832:(e7779:r3223:ref->d235:"std.control.var.ref" e7831:{get: e7788:(fn p1811:() -> e7787:(e7785:(e7780:r3224:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e7784:(e7782:(e7781:r3225:r->d2171:r.s291.get->d236) e7783:())) e7786:r3226:i->d2172:i)), update_effect: e7830:(fn p1812:() -> e7829:block { let my p1813:d2173:loop = e7822:(fn p1814:d2174:x -> e7821:catch e7789:r3227:x->d2174:x { std::control::var::ref_update::update p1815:d2175:old, p1816:d2176:k -> e7820:block { let my p1817:d2177:new_item = e7796:(e7790:r3228:"ref_update::update"->d234:"std.control.var.ref_update.update" e7795:(e7793:(e7791:r3229:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e7792:r3230:old->d2175:old) e7794:r3231:i->d2172:i)); e7819:block { let my p1818:d2178:replacement = e7799:(e7797:r3232:"std::text::char::to_string"->d672:"std.text.char.to_string" e7798:r3233:new_item->d2177:new_item); e7818:(e7800:r3234:loop->d2173:loop e7817:(e7801:r3235:k->d2176:k e7816:(e7814:(e7804:(e7802:r3236:"std::text::str::splice"->d792:"std.text.str.splice" e7803:r3237:old->d2175:old) e7813:(e7807:(e7805:r3238:range->d511:"std.data.range.range" e7806:r3239:i->d2172:i) e7812:(e7811:(e7809:r3241:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7808:r3240:i->d2172:i) e7810:1))) e7815:r3242:replacement->d2178:replacement))) } } }); e7828:(e7823:r3243:loop->d2173:loop e7827:(e7825:(e7824:r3244:r->d2171:r.s292.update_effect->d238) e7826:())) })})))
      }
    }
    pub d116:"std.text.yumark" mod {
      pub d895:"std.text.yumark.yumark_algebra": {nil: () -> 'a, cons: 'a -> 'a -> 'a, text: std::text::str::str -> 'a, paragraph: 'a -> 'a, heading: std::text::str::str -> int -> 'a -> 'a, blank_line: std::text::str::str -> 'a, section_close: std::text::str::str -> 'a -> 'a, list_block: bool -> 'a -> 'a, list_item: std::text::str::str -> 'a -> 'a, list_item_body: 'a -> 'a, code_fence: std::text::str::str -> std::text::str::str -> 'a, quote_block: 'a -> 'a, emphasis: 'a -> 'a, strong: 'a -> 'a} -> std::text::yumark::yumark_algebra 'a = <missing>
      pub d924:"std.text.yumark.html_format": {marker: std::text::str::str} -> std::text::yumark::html_format = <missing>
      pub d927:"std.text.yumark.markdown_format": {marker: std::text::str::str} -> std::text::yumark::markdown_format = <missing>
      pub d930:"std.text.yumark.html_node": {tag: std::text::str::str, body: std::text::str::str} -> std::text::yumark::html_node = <missing>
      pub d935:"std.text.yumark.YumarkFormat" mod {
        d936:"std.text.yumark.YumarkFormat.yumark_algebra": 'a -> () -> std::text::yumark::yumark_algebra 'b where 'a: std::text::yumark::YumarkFormat(repr = 'b) = <missing>
      }
      pub d937:"std.text.yumark.nil": any -> std::text::yumark::yumark_algebra 'a -> 'a = e7840:(fn p1819:d2179:format -> e7839:(fn p1820:d2180:algebra -> e7838:(e7836:(e7835:r3245:algebra->d2180:algebra.s293.nil->d896) e7837:())))
      pub d938:"std.text.yumark.cons": ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7858:(fn p1821:d2181:head -> e7857:(fn p1822:d2182:tail -> e7856:(fn p1823:d2183:format -> e7855:(fn p1824:d2184:algebra -> e7854:(e7848:(e7842:(e7841:r3246:algebra->d2184:algebra.s294.cons->d898) e7847:(e7845:(e7843:r3247:head->d2181:head e7844:r3248:format->d2183:format) e7846:r3249:algebra->d2184:algebra)) e7853:(e7851:(e7849:r3250:tail->d2182:tail e7850:r3251:format->d2183:format) e7852:r3252:algebra->d2184:algebra))))))
      pub d939:"std.text.yumark.text": std::text::str::str -> any -> std::text::yumark::yumark_algebra 'a -> 'a = e7865:(fn p1825:d2185:value -> e7864:(fn p1826:d2186:format -> e7863:(fn p1827:d2187:algebra -> e7862:(e7860:(e7859:r3253:algebra->d2187:algebra.s295.text->d900) e7861:r3254:value->d2185:value))))
      pub d940:"std.text.yumark.paragraph": ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7876:(fn p1828:d2188:children -> e7875:(fn p1829:d2189:format -> e7874:(fn p1830:d2190:algebra -> e7873:(e7867:(e7866:r3255:algebra->d2190:algebra.s296.paragraph->d902) e7872:(e7870:(e7868:r3256:children->d2188:children e7869:r3257:format->d2189:format) e7871:r3258:algebra->d2190:algebra)))))
      pub d941:"std.text.yumark.heading": std::text::str::str -> int -> ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7893:(fn p1831:d2191:marker -> e7892:(fn p1832:d2192:level -> e7891:(fn p1833:d2193:children -> e7890:(fn p1834:d2194:format -> e7889:(fn p1835:d2195:algebra -> e7888:(e7882:(e7880:(e7878:(e7877:r3259:algebra->d2195:algebra.s297.heading->d904) e7879:r3260:marker->d2191:marker) e7881:r3261:level->d2192:level) e7887:(e7885:(e7883:r3262:children->d2193:children e7884:r3263:format->d2194:format) e7886:r3264:algebra->d2195:algebra)))))))
      pub d942:"std.text.yumark.blank_line": std::text::str::str -> any -> std::text::yumark::yumark_algebra 'a -> 'a = e7900:(fn p1836:d2196:marker -> e7899:(fn p1837:d2197:format -> e7898:(fn p1838:d2198:algebra -> e7897:(e7895:(e7894:r3265:algebra->d2198:algebra.s298.blank_line->d906) e7896:r3266:marker->d2196:marker))))
      pub d943:"std.text.yumark.section_close": std::text::str::str -> ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7914:(fn p1839:d2199:marker -> e7913:(fn p1840:d2200:children -> e7912:(fn p1841:d2201:format -> e7911:(fn p1842:d2202:algebra -> e7910:(e7904:(e7902:(e7901:r3267:algebra->d2202:algebra.s299.section_close->d908) e7903:r3268:marker->d2199:marker) e7909:(e7907:(e7905:r3269:children->d2200:children e7906:r3270:format->d2201:format) e7908:r3271:algebra->d2202:algebra))))))
      pub d944:"std.text.yumark.list_block": bool -> ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7928:(fn p1843:d2203:ordered -> e7927:(fn p1844:d2204:items -> e7926:(fn p1845:d2205:format -> e7925:(fn p1846:d2206:algebra -> e7924:(e7918:(e7916:(e7915:r3272:algebra->d2206:algebra.s300.list_block->d910) e7917:r3273:ordered->d2203:ordered) e7923:(e7921:(e7919:r3274:items->d2204:items e7920:r3275:format->d2205:format) e7922:r3276:algebra->d2206:algebra))))))
      pub d945:"std.text.yumark.list_item": std::text::str::str -> ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7942:(fn p1847:d2207:marker -> e7941:(fn p1848:d2208:children -> e7940:(fn p1849:d2209:format -> e7939:(fn p1850:d2210:algebra -> e7938:(e7932:(e7930:(e7929:r3277:algebra->d2210:algebra.s301.list_item->d912) e7931:r3278:marker->d2207:marker) e7937:(e7935:(e7933:r3279:children->d2208:children e7934:r3280:format->d2209:format) e7936:r3281:algebra->d2210:algebra))))))
      pub d946:"std.text.yumark.list_item_body": ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7953:(fn p1851:d2211:children -> e7952:(fn p1852:d2212:format -> e7951:(fn p1853:d2213:algebra -> e7950:(e7944:(e7943:r3282:algebra->d2213:algebra.s302.list_item_body->d914) e7949:(e7947:(e7945:r3283:children->d2211:children e7946:r3284:format->d2212:format) e7948:r3285:algebra->d2213:algebra)))))
      pub d947:"std.text.yumark.code_fence": std::text::str::str -> std::text::str::str -> any -> std::text::yumark::yumark_algebra 'a -> 'a = e7963:(fn p1854:d2214:info -> e7962:(fn p1855:d2215:body -> e7961:(fn p1856:d2216:format -> e7960:(fn p1857:d2217:algebra -> e7959:(e7957:(e7955:(e7954:r3286:algebra->d2217:algebra.s303.code_fence->d916) e7956:r3287:info->d2214:info) e7958:r3288:body->d2215:body)))))
      pub d948:"std.text.yumark.quote_block": ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7974:(fn p1858:d2218:children -> e7973:(fn p1859:d2219:format -> e7972:(fn p1860:d2220:algebra -> e7971:(e7965:(e7964:r3289:algebra->d2220:algebra.s304.quote_block->d918) e7970:(e7968:(e7966:r3290:children->d2218:children e7967:r3291:format->d2219:format) e7969:r3292:algebra->d2220:algebra)))))
      pub d949:"std.text.yumark.emphasis": ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7985:(fn p1861:d2221:children -> e7984:(fn p1862:d2222:format -> e7983:(fn p1863:d2223:algebra -> e7982:(e7976:(e7975:r3293:algebra->d2223:algebra.s305.emphasis->d920) e7981:(e7979:(e7977:r3294:children->d2221:children e7978:r3295:format->d2222:format) e7980:r3296:algebra->d2223:algebra)))))
      pub d950:"std.text.yumark.strong": ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7996:(fn p1864:d2224:children -> e7995:(fn p1865:d2225:format -> e7994:(fn p1866:d2226:algebra -> e7993:(e7987:(e7986:r3297:algebra->d2226:algebra.s306.strong->d922) e7992:(e7990:(e7988:r3298:children->d2224:children e7989:r3299:format->d2225:format) e7991:r3300:algebra->d2226:algebra)))))
      pub d951:"std.text.yumark.html_format_value": () -> std::text::yumark::html_format = e8001:(fn p1867:() -> e8000:(e7997:r3301:html_format->d924:"std.text.yumark.html_format" e7999:{marker: e7998:"html"}))
      pub d952:"std.text.yumark.markdown_format_value": () -> std::text::yumark::markdown_format = e8006:(fn p1868:() -> e8005:(e8002:r3302:markdown_format->d927:"std.text.yumark.markdown_format" e8004:{marker: e8003:"markdown"}))
      pub d953:"std.text.yumark.html_tag": std::text::yumark::html_node -> std::text::str::str = e8040:(fn p1869:d2227:node -> e8039:case e8014:(e8013:r3305:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e8012:(e8011:(e8009:r3304:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e8008:(e8007:r3303:node->d2227:node.s307.tag->d931)) e8010:"fragment")) { p1870:true -> e8016:(e8015:r3306:node->d2227:node.s308.body->d933); p1871:false -> e8038:(e8031:(e8029:(e8026:(e8017:r3307:cat4->d989:"std.text.yumark.cat4" e8025:(e8023:(e8020:(e8018:r3308:cat3->d988:"std.text.yumark.cat3" e8019:"<") e8022:(e8021:r3309:node->d2227:node.s309.tag->d931)) e8024:">")) e8028:(e8027:r3310:node->d2227:node.s310.body->d933)) e8030:"</") e8037:(e8035:(e8032:r3311:cat2->d987:"std.text.yumark.cat2" e8034:(e8033:r3312:node->d2227:node.s311.tag->d931)) e8036:">")) })
      pub d954:"std.text.yumark.html_algebra": () -> std::text::yumark::yumark_algebra std::text::yumark::html_node = e8058:(fn p1872:() -> e8057:(e8041:r3313:yumark_algebra->d895:"std.text.yumark.yumark_algebra" e8056:{nil: e8042:r3314:html_nil->d959:"std.text.yumark.html_nil", cons: e8043:r3315:html_cons->d960:"std.text.yumark.html_cons", text: e8044:r3316:html_text->d961:"std.text.yumark.html_text", paragraph: e8045:r3317:html_paragraph->d962:"std.text.yumark.html_paragraph", heading: e8046:r3318:html_heading->d963:"std.text.yumark.html_heading", blank_line: e8047:r3319:html_blank_line->d964:"std.text.yumark.html_blank_line", section_close: e8048:r3320:html_section_close->d965:"std.text.yumark.html_section_close", list_block: e8049:r3321:html_list_block->d966:"std.text.yumark.html_list_block", list_item: e8050:r3322:html_list_item->d967:"std.text.yumark.html_list_item", list_item_body: e8051:r3323:html_list_item_body->d968:"std.text.yumark.html_list_item_body", code_fence: e8052:r3324:html_code_fence->d969:"std.text.yumark.html_code_fence", quote_block: e8053:r3325:html_quote_block->d970:"std.text.yumark.html_quote_block", emphasis: e8054:r3326:html_emphasis->d971:"std.text.yumark.html_emphasis", strong: e8055:r3327:html_strong->d972:"std.text.yumark.html_strong"}))
      pub d955:"std.text.yumark.markdown_algebra": () -> std::text::yumark::yumark_algebra std::text::str::str = e8076:(fn p1873:() -> e8075:(e8059:r3328:yumark_algebra->d895:"std.text.yumark.yumark_algebra" e8074:{nil: e8060:r3329:markdown_nil->d973:"std.text.yumark.markdown_nil", cons: e8061:r3330:markdown_cons->d974:"std.text.yumark.markdown_cons", text: e8062:r3331:markdown_text->d975:"std.text.yumark.markdown_text", paragraph: e8063:r3332:markdown_paragraph->d976:"std.text.yumark.markdown_paragraph", heading: e8064:r3333:markdown_heading->d977:"std.text.yumark.markdown_heading", blank_line: e8065:r3334:markdown_blank_line->d978:"std.text.yumark.markdown_blank_line", section_close: e8066:r3335:markdown_section_close->d979:"std.text.yumark.markdown_section_close", list_block: e8067:r3336:markdown_list_block->d980:"std.text.yumark.markdown_list_block", list_item: e8068:r3337:markdown_list_item->d981:"std.text.yumark.markdown_list_item", list_item_body: e8069:r3338:markdown_list_item_body->d982:"std.text.yumark.markdown_list_item_body", code_fence: e8070:r3339:markdown_code_fence->d983:"std.text.yumark.markdown_code_fence", quote_block: e8071:r3340:markdown_quote_block->d984:"std.text.yumark.markdown_quote_block", emphasis: e8072:r3341:markdown_emphasis->d985:"std.text.yumark.markdown_emphasis", strong: e8073:r3342:markdown_strong->d986:"std.text.yumark.markdown_strong"}))
      pub d956:"std.text.yumark.run_yumark": 'a -> ('a -> ['b] std::text::yumark::yumark_algebra 'c -> ['d] 'e) -> ['d, 'b] 'e where 'a: std::text::yumark::YumarkFormat(repr = 'c) = e8086:(fn p1874:d2228:format -> e8085:(fn p1875:d2229:document -> e8084:(e8079:(e8077:r3343:document->d2229:document e8078:r3344:format->d2228:format) e8083:(e8081:(e8080:r3345:format->d2228:format.s312.yumark_algebra=>d936:"std.text.yumark.YumarkFormat.yumark_algebra") e8082:()))))
      pub d957:"std.text.yumark.render_html_doc": (std::text::yumark::html_format -> ['a] std::text::yumark::yumark_algebra std::text::yumark::html_node -> ['a] std::text::yumark::html_node) -> ['a] std::text::yumark::html_node = e8094:(fn p1876:d2230:document -> e8093:(e8091:(e8087:r3346:run_yumark->d956:"std.text.yumark.run_yumark" e8090:(e8088:r3347:html_format_value->d951:"std.text.yumark.html_format_value" e8089:())) e8092:r3348:document->d2230:document))
      pub d958:"std.text.yumark.render_markdown_doc": (std::text::yumark::markdown_format -> ['a] std::text::yumark::yumark_algebra std::text::str::str -> ['a] std::text::str::str) -> ['a] std::text::str::str = e8102:(fn p1877:d2231:document -> e8101:(e8099:(e8095:r3349:run_yumark->d956:"std.text.yumark.run_yumark" e8098:(e8096:r3350:markdown_format_value->d952:"std.text.yumark.markdown_format_value" e8097:())) e8100:r3351:document->d2231:document))
      my d959:"std.text.yumark.html_nil": () -> std::text::yumark::html_node = e8108:(fn p1878:() -> e8107:(e8103:r3352:html_node->d930:"std.text.yumark.html_node" e8106:{tag: e8104:"fragment", body: e8105:""}))
      my d960:"std.text.yumark.html_cons": std::text::yumark::html_node -> std::text::yumark::html_node -> std::text::yumark::html_node = e8123:(fn p1879:d2232:head -> e8122:(fn p1880:d2233:tail -> e8121:(e8109:r3353:html_node->d930:"std.text.yumark.html_node" e8120:{tag: e8110:"fragment", body: e8119:(e8115:(e8111:r3354:cat2->d987:"std.text.yumark.cat2" e8114:(e8112:r3355:html_tag->d953:"std.text.yumark.html_tag" e8113:r3356:head->d2232:head)) e8118:(e8116:r3357:html_tag->d953:"std.text.yumark.html_tag" e8117:r3358:tail->d2233:tail))})))
      my d961:"std.text.yumark.html_text": std::text::str::str -> std::text::yumark::html_node = e8129:(fn p1881:d2234:value -> e8128:(e8124:r3359:html_node->d930:"std.text.yumark.html_node" e8127:{tag: e8125:"span", body: e8126:r3360:value->d2234:value}))
      my d962:"std.text.yumark.html_paragraph": std::text::yumark::html_node -> std::text::yumark::html_node = e8137:(fn p1882:d2235:children -> e8136:(e8130:r3361:html_node->d930:"std.text.yumark.html_node" e8135:{tag: e8131:"p", body: e8134:(e8132:r3362:html_tag->d953:"std.text.yumark.html_tag" e8133:r3363:children->d2235:children)}))
      my d963:"std.text.yumark.html_heading": std::text::str::str -> int -> std::text::yumark::html_node -> std::text::yumark::html_node = e8153:(fn p1883:d2236:marker -> e8152:(fn p1884:d2237:level -> e8151:(fn p1885:d2238:children -> e8150:(e8138:r3364:html_node->d930:"std.text.yumark.html_node" e8149:{tag: e8145:(e8141:(e8139:r3365:cat2->d987:"std.text.yumark.cat2" e8140:"h") e8144:(e8142:r3366:"std::int::to_string"->d54:"std.int.to_string" e8143:r3367:level->d2237:level)), body: e8148:(e8146:r3368:html_tag->d953:"std.text.yumark.html_tag" e8147:r3369:children->d2238:children)}))))
      my d964:"std.text.yumark.html_blank_line": std::text::str::str -> std::text::yumark::html_node = e8159:(fn p1886:d2239:marker -> e8158:(e8154:r3370:html_node->d930:"std.text.yumark.html_node" e8157:{tag: e8155:"br", body: e8156:r3371:marker->d2239:marker}))
      my d965:"std.text.yumark.html_section_close": std::text::str::str -> std::text::yumark::html_node -> std::text::yumark::html_node = e8172:(fn p1887:d2240:marker -> e8171:(fn p1888:d2241:children -> e8170:(e8160:r3372:html_node->d930:"std.text.yumark.html_node" e8169:{tag: e8161:"section-close", body: e8168:(e8164:(e8162:r3373:cat2->d987:"std.text.yumark.cat2" e8163:r3374:marker->d2240:marker) e8167:(e8165:r3375:html_tag->d953:"std.text.yumark.html_tag" e8166:r3376:children->d2241:children))})))
      my d966:"std.text.yumark.html_list_block": bool -> std::text::yumark::html_node -> std::text::yumark::html_node = e8186:(fn p1889:d2242:ordered -> e8185:(fn p1890:d2243:items -> e8184:(e8173:r3377:html_node->d930:"std.text.yumark.html_node" e8183:{tag: e8179:case e8176:(e8175:r3379:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e8174:r3378:ordered->d2242:ordered) { p1891:true -> e8177:"ol"; p1892:false -> e8178:"ul" }, body: e8182:(e8180:r3380:html_tag->d953:"std.text.yumark.html_tag" e8181:r3381:items->d2243:items)})))
      my d967:"std.text.yumark.html_list_item": std::text::str::str -> std::text::yumark::html_node -> std::text::yumark::html_node = e8195:(fn p1893:d2244:marker -> e8194:(fn p1894:d2245:children -> e8193:(e8187:r3382:html_node->d930:"std.text.yumark.html_node" e8192:{tag: e8188:"li", body: e8191:(e8189:r3383:html_tag->d953:"std.text.yumark.html_tag" e8190:r3384:children->d2245:children)})))
      my d968:"std.text.yumark.html_list_item_body": std::text::yumark::html_node -> std::text::yumark::html_node = e8203:(fn p1895:d2246:children -> e8202:(e8196:r3385:html_node->d930:"std.text.yumark.html_node" e8201:{tag: e8197:"item-body", body: e8200:(e8198:r3386:html_tag->d953:"std.text.yumark.html_tag" e8199:r3387:children->d2246:children)}))
      my d969:"std.text.yumark.html_code_fence": std::text::str::str -> std::text::str::str -> std::text::yumark::html_node = e8230:(fn p1896:d2247:info -> e8229:(fn p1897:d2248:body -> e8228:block { let my p1898:d2249:info_node = e8208:(e8204:r3388:html_node->d930:"std.text.yumark.html_node" e8207:{tag: e8205:"code-info", body: e8206:r3389:info->d2247:info}); e8227:block { let my p1899:d2250:body_node = e8213:(e8209:r3390:html_node->d930:"std.text.yumark.html_node" e8212:{tag: e8210:"code", body: e8211:r3391:body->d2248:body}); e8226:(e8214:r3392:html_node->d930:"std.text.yumark.html_node" e8225:{tag: e8215:"pre", body: e8224:(e8220:(e8216:r3393:cat2->d987:"std.text.yumark.cat2" e8219:(e8217:r3394:html_tag->d953:"std.text.yumark.html_tag" e8218:r3395:info_node->d2249:info_node)) e8223:(e8221:r3396:html_tag->d953:"std.text.yumark.html_tag" e8222:r3397:body_node->d2250:body_node))}) } }))
      my d970:"std.text.yumark.html_quote_block": std::text::yumark::html_node -> std::text::yumark::html_node = e8238:(fn p1900:d2251:children -> e8237:(e8231:r3398:html_node->d930:"std.text.yumark.html_node" e8236:{tag: e8232:"blockquote", body: e8235:(e8233:r3399:html_tag->d953:"std.text.yumark.html_tag" e8234:r3400:children->d2251:children)}))
      my d971:"std.text.yumark.html_emphasis": std::text::yumark::html_node -> std::text::yumark::html_node = e8246:(fn p1901:d2252:children -> e8245:(e8239:r3401:html_node->d930:"std.text.yumark.html_node" e8244:{tag: e8240:"em", body: e8243:(e8241:r3402:html_tag->d953:"std.text.yumark.html_tag" e8242:r3403:children->d2252:children)}))
      my d972:"std.text.yumark.html_strong": std::text::yumark::html_node -> std::text::yumark::html_node = e8254:(fn p1902:d2253:children -> e8253:(e8247:r3404:html_node->d930:"std.text.yumark.html_node" e8252:{tag: e8248:"strong", body: e8251:(e8249:r3405:html_tag->d953:"std.text.yumark.html_tag" e8250:r3406:children->d2253:children)}))
      my d973:"std.text.yumark.markdown_nil": () -> std::text::str::str = e8256:(fn p1903:() -> e8255:"")
      my d974:"std.text.yumark.markdown_cons": std::text::str::str -> std::text::str::str -> std::text::str::str = e8263:(fn p1904:d2254:head -> e8262:(fn p1905:d2255:tail -> e8261:(e8259:(e8257:r3407:cat2->d987:"std.text.yumark.cat2" e8258:r3408:head->d2254:head) e8260:r3409:tail->d2255:tail)))
      my d975:"std.text.yumark.markdown_text": std::text::str::str -> std::text::str::str = e8265:(fn p1906:d2256:value -> e8264:r3410:value->d2256:value)
      my d976:"std.text.yumark.markdown_paragraph": std::text::str::str -> std::text::str::str = e8271:(fn p1907:d2257:children -> e8270:(e8268:(e8266:r3411:cat2->d987:"std.text.yumark.cat2" e8267:r3412:children->d2257:children) e8269:"\n\n"))
      my d977:"std.text.yumark.markdown_heading": std::text::str::str -> int -> std::text::str::str -> std::text::str::str = e8281:(fn p1908:d2258:marker -> e8280:(fn p1909:d2259:level -> e8279:(fn p1910:d2260:children -> e8278:(e8276:(e8274:(e8272:r3413:cat3->d988:"std.text.yumark.cat3" e8273:r3414:marker->d2258:marker) e8275:r3415:children->d2260:children) e8277:"\n\n"))))
      my d978:"std.text.yumark.markdown_blank_line": std::text::str::str -> std::text::str::str = e8283:(fn p1911:d2261:marker -> e8282:r3416:marker->d2261:marker)
      my d979:"std.text.yumark.markdown_section_close": std::text::str::str -> std::text::str::str -> std::text::str::str = e8292:(fn p1912:d2262:marker -> e8291:(fn p1913:d2263:children -> e8290:(e8288:(e8286:(e8284:r3417:cat3->d988:"std.text.yumark.cat3" e8285:r3418:marker->d2262:marker) e8287:r3419:children->d2263:children) e8289:"\n")))
      my d980:"std.text.yumark.markdown_list_block": bool -> std::text::str::str -> std::text::str::str = e8299:(fn p1914:d2264:ordered -> e8298:(fn p1915:d2265:items -> e8297:(e8295:(e8293:r3420:cat2->d987:"std.text.yumark.cat2" e8294:r3421:items->d2265:items) e8296:"\n")))
      my d981:"std.text.yumark.markdown_list_item": std::text::str::str -> std::text::str::str -> std::text::str::str = e8308:(fn p1916:d2266:marker -> e8307:(fn p1917:d2267:children -> e8306:(e8304:(e8302:(e8300:r3422:cat3->d988:"std.text.yumark.cat3" e8301:r3423:marker->d2266:marker) e8303:r3424:children->d2267:children) e8305:"\n")))
      my d982:"std.text.yumark.markdown_list_item_body": std::text::str::str -> std::text::str::str = e8310:(fn p1918:d2268:children -> e8309:r3425:children->d2268:children)
      my d983:"std.text.yumark.markdown_code_fence": std::text::str::str -> std::text::str::str -> std::text::str::str = e8325:(fn p1919:d2269:info -> e8324:(fn p1920:d2270:body -> e8323:(e8321:(e8311:r3426:cat2->d987:"std.text.yumark.cat2" e8320:(e8318:(e8316:(e8314:(e8312:r3427:cat4->d989:"std.text.yumark.cat4" e8313:"```") e8315:r3428:info->d2269:info) e8317:"\n") e8319:r3429:body->d2270:body)) e8322:"\n```\n\n")))
      my d984:"std.text.yumark.markdown_quote_block": std::text::str::str -> std::text::str::str = e8333:(fn p1921:d2271:children -> e8332:(e8330:(e8328:(e8326:r3430:cat3->d988:"std.text.yumark.cat3" e8327:"> ") e8329:r3431:children->d2271:children) e8331:"\n"))
      my d985:"std.text.yumark.markdown_emphasis": std::text::str::str -> std::text::str::str = e8341:(fn p1922:d2272:children -> e8340:(e8338:(e8336:(e8334:r3432:cat3->d988:"std.text.yumark.cat3" e8335:"*") e8337:r3433:children->d2272:children) e8339:"*"))
      my d986:"std.text.yumark.markdown_strong": std::text::str::str -> std::text::str::str = e8349:(fn p1923:d2273:children -> e8348:(e8346:(e8344:(e8342:r3434:cat3->d988:"std.text.yumark.cat3" e8343:"**") e8345:r3435:children->d2273:children) e8347:"**"))
      my d987:"std.text.yumark.cat2": std::text::str::str -> std::text::str::str -> std::text::str::str = e8356:(fn p1924:d2274:left -> e8355:(fn p1925:d2275:right -> e8354:(e8352:(e8350:r3436:"std::text::str::concat"->d784:"std.text.str.concat" e8351:r3437:left->d2274:left) e8353:r3438:right->d2275:right)))
      my d988:"std.text.yumark.cat3": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e8368:(fn p1926:d2276:a -> e8367:(fn p1927:d2277:b -> e8366:(fn p1928:d2278:c -> e8365:(e8363:(e8357:r3439:cat2->d987:"std.text.yumark.cat2" e8362:(e8360:(e8358:r3440:cat2->d987:"std.text.yumark.cat2" e8359:r3441:a->d2276:a) e8361:r3442:b->d2277:b)) e8364:r3443:c->d2278:c))))
      my d989:"std.text.yumark.cat4": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e8383:(fn p1929:d2279:a -> e8382:(fn p1930:d2280:b -> e8381:(fn p1931:d2281:c -> e8380:(fn p1932:d2282:d -> e8379:(e8377:(e8369:r3444:cat2->d987:"std.text.yumark.cat2" e8376:(e8374:(e8372:(e8370:r3445:cat3->d988:"std.text.yumark.cat3" e8371:r3446:a->d2279:a) e8373:r3447:b->d2280:b) e8375:r3448:c->d2281:c)) e8378:r3449:d->d2282:d)))))
      my d990 mod {
        d991: std::text::yumark::html_format -> () -> std::text::yumark::yumark_algebra std::text::yumark::html_node = e8388:(fn p1933:d2283:format -> e8387:(fn p1934:_ -> e8386:(e8384:r3450:html_algebra->d954:"std.text.yumark.html_algebra" e8385:())))
      }
      my d992 mod {
        d993: std::text::yumark::markdown_format -> () -> std::text::yumark::yumark_algebra std::text::str::str = e8393:(fn p1935:d2284:format -> e8392:(fn p1936:_ -> e8391:(e8389:r3451:markdown_algebra->d955:"std.text.yumark.markdown_algebra" e8390:())))
      }
    }
  }
  pub d8:"std.control" mod {
    pub d16:"std.control.flow" mod {
      pub d171:"std.control.flow.sub" mod {
        pub d173:"std.control.flow.sub.sub": 'a [std::control::flow::sub('b & 'a); 'c] -> ['c] 'a | 'b = e929:(fn p145:d1130:x -> e928:catch e925:r345:x->d1130:x { std::control::flow::sub::return p146:d1131:a, p147:_ -> e926:r346:a->d1131:a; p148:d1132:a -> e927:r347:a->d1132:a })
      }
      pub d174:"std.control.flow.label_sub" mod {
        pub d176:"std.control.flow.label_sub.label": {marker: ()} -> std::control::flow::label_sub::label = <missing>
        d179:"std.control.flow.label_sub.control_label": std::control::flow::label_sub::label = e933:(e930:r348:label->d176:"std.control.flow.label_sub.label" e932:{marker: e931:()})
        pub d180:"std.control.flow.label_sub.sub": 'a [std::control::flow::label_sub('b & 'a & 'c), std::control::flow::sub('c & 'a & 'b); 'd] -> ['d] 'a | 'b | 'c = e939:(fn p149:d1133:x -> e938:catch e934:r349:x->d1133:x { std::control::flow::label_sub::return p150:d1134:a, p151:_ -> e935:r350:a->d1134:a; std::control::flow::sub::return p152:d1135:a, p153:_ -> e936:r351:a->d1135:a; p154:d1136:a -> e937:r352:a->d1136:a })
      }
      pub d181:"std.control.flow.loop" mod {
        my d185:"std.control.flow.loop.last" mod {
          d187:"std.control.flow.loop.last.judge": any [std::control::flow::loop::last; 'a] -> ['a] bool = e944:(fn p155:d1137:x -> e943:catch e940:r353:x->d1137:x { std::control::flow::loop::last::break p156:_, p157:_ -> e941:true; p158:_ -> e942:false })
          d188:"std.control.flow.loop.last.sub": any [std::control::flow::loop::last; 'a] -> ['a] () = e949:(fn p159:d1138:x -> e948:catch e945:r354:x->d1138:x { std::control::flow::loop::last::break p160:_, p161:_ -> e946:(); p162:_ -> e947:() })
        }
        pub d189:"std.control.flow.loop.for_in": 'a -> ('b -> [std::control::flow::loop; 'c] any) -> ['c] () where 'a: std::data::fold::Fold(item = 'b) = e1022:(fn p179:d1143:xs -> e1021:(fn p180:d1144:f -> e1020:(e970:r359:"last::sub"->d188:"std.control.flow.loop.last.sub" e1019:(e974:(e972:(e971:r360:xs->d1143:xs.s36.fold=>d449:"std.data.fold.Fold.fold") e973:()) e1018:(fn p181:() -> e1017:(fn p182:d1145:x -> e1016:(e975:r361:"next::sub"->d997:"std.control.flow.loop.next.sub" e1015:block { e1011:block { let my p183:d1146:loop = e1009:(fn p184:d1147:b -> e1008:case e978:(e977:r363:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e976:r362:b->d1147:b) { p197:true -> e1006:block { e1004:(e979:r364:loop->d1146:loop e1003:(e980:r365:"redo::judge"->d1004:"std.control.flow.loop.redo.judge" e1002:catch e983:(e981:r366:f->d1144:f e982:r367:x->d1145:x) { std::control::flow::loop::last p185:_, p186:_ -> e986:(e984:r368:"last::break"->d186:"std.control.flow.loop.last.break" e985:()); std::control::flow::loop::next p187:_, p188:_ -> e989:(e987:r369:"next::break"->d995:"std.control.flow.loop.next.break" e988:()); std::control::flow::loop::redo p189:_, p190:_ -> e992:(e990:r370:"redo::break"->d1003:"std.control.flow.loop.redo.break" e991:()); std::control::flow::loop::last p191:_, p192:_ -> e995:(e993:r371:"last::break"->d186:"std.control.flow.loop.last.break" e994:()); std::control::flow::loop::next p193:_, p194:_ -> e998:(e996:r372:"next::break"->d995:"std.control.flow.loop.next.break" e997:()); std::control::flow::loop::redo p195:_, p196:_ -> e1001:(e999:r373:"redo::break"->d1003:"std.control.flow.loop.redo.break" e1000:()) })); e1005:() }; p198:false -> e1007:() }); e1010:() }; e1014:(e1012:r374:loop->d1146:loop e1013:true) })))))))
        my d994:"std.control.flow.loop.next" mod {
          d996:"std.control.flow.loop.next.judge": any [std::control::flow::loop::next; 'a] -> ['a] bool = e954:(fn p163:d1139:x -> e953:catch e950:r355:x->d1139:x { std::control::flow::loop::next::break p164:_, p165:_ -> e951:true; p166:_ -> e952:false })
          d997:"std.control.flow.loop.next.sub": any [std::control::flow::loop::next; 'a] -> ['a] () = e959:(fn p167:d1140:x -> e958:catch e955:r356:x->d1140:x { std::control::flow::loop::next::break p168:_, p169:_ -> e956:(); p170:_ -> e957:() })
        }
        my d1002:"std.control.flow.loop.redo" mod {
          d1004:"std.control.flow.loop.redo.judge": any [std::control::flow::loop::redo; 'a] -> ['a] bool = e964:(fn p171:d1141:x -> e963:catch e960:r357:x->d1141:x { std::control::flow::loop::redo::break p172:_, p173:_ -> e961:true; p174:_ -> e962:false })
          d1005:"std.control.flow.loop.redo.sub": any [std::control::flow::loop::redo; 'a] -> ['a] () = e969:(fn p175:d1142:x -> e968:catch e965:r358:x->d1142:x { std::control::flow::loop::redo::break p176:_, p177:_ -> e966:(); p178:_ -> e967:() })
        }
      }
      pub d190:"std.control.flow.LoopLabel" mod {
        pub d191:"std.control.flow.LoopLabel.last": 'a -> () -> never where 'a: std::control::flow::LoopLabel = <missing>
        pub d192:"std.control.flow.LoopLabel.next": 'a -> () -> never where 'a: std::control::flow::LoopLabel = <missing>
        pub d193:"std.control.flow.LoopLabel.redo": 'a -> () -> never where 'a: std::control::flow::LoopLabel = <missing>
      }
      pub d194:"std.control.flow.label_loop" mod {
        pub d198:"std.control.flow.label_loop.label": {last: () -> [std::control::flow::label_loop] never, next: () -> [std::control::flow::label_loop] never, redo: () -> [std::control::flow::label_loop] never} -> std::control::flow::label_loop::label = <missing>
        my d205:"std.control.flow.label_loop.last" mod {
          d207:"std.control.flow.label_loop.last.judge": any [std::control::flow::label_loop::last; 'a] -> ['a] bool = e1027:(fn p199:d1148:x -> e1026:catch e1023:r375:x->d1148:x { std::control::flow::label_loop::last::break p200:_, p201:_ -> e1024:true; p202:_ -> e1025:false })
          d208:"std.control.flow.label_loop.last.sub": any [std::control::flow::label_loop::last; 'a] -> ['a] () = e1032:(fn p203:d1149:x -> e1031:catch e1028:r376:x->d1149:x { std::control::flow::label_loop::last::break p204:_, p205:_ -> e1029:(); p206:_ -> e1030:() })
        }
        my d209:"std.control.flow.label_loop.control_label": std::control::flow::label_loop::label = e1058:(e1053:r381:"label_loop::label"->d198:"std.control.flow.label_loop.label" e1057:{last: e1054:r382:"label_loop::last"->d195:"std.control.flow.label_loop.last", next: e1055:r383:"label_loop::next"->d196:"std.control.flow.label_loop.next", redo: e1056:r384:"label_loop::redo"->d197:"std.control.flow.label_loop.redo"})
        pub d210:"std.control.flow.label_loop.for_in": 'a -> (std::control::flow::label_loop::label -> 'b -> [std::control::flow::label_loop, std::control::flow::loop; 'c] any) -> ['c] () where 'a: std::data::fold::Fold(item = 'b) = e1113:(fn p223:d1154:xs -> e1112:(fn p224:d1155:f -> e1111:(e1059:r385:"last::sub"->d208:"std.control.flow.label_loop.last.sub" e1110:(e1063:(e1061:(e1060:r386:xs->d1154:xs.s37.fold=>d449:"std.data.fold.Fold.fold") e1062:()) e1109:(fn p225:() -> e1108:(fn p226:d1156:x -> e1107:(e1064:r387:"next::sub"->d1009:"std.control.flow.label_loop.next.sub" e1106:block { e1102:block { let my p227:d1157:loop = e1100:(fn p228:d1158:b -> e1099:case e1067:(e1066:r389:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1065:r388:b->d1158:b) { p241:true -> e1097:block { e1095:(e1068:r390:loop->d1157:loop e1094:(e1069:r391:"redo::judge"->d1000:"std.control.flow.label_loop.redo.judge" e1093:catch e1074:(e1072:(e1070:r392:f->d1155:f e1071:r393:control_label->d209:"std.control.flow.label_loop.control_label") e1073:r394:x->d1156:x) { std::control::flow::label_loop::last p229:_, p230:_ -> e1077:(e1075:r395:"last::break"->d206:"std.control.flow.label_loop.last.break" e1076:()); std::control::flow::label_loop::next p231:_, p232:_ -> e1080:(e1078:r396:"next::break"->d1007:"std.control.flow.label_loop.next.break" e1079:()); std::control::flow::label_loop::redo p233:_, p234:_ -> e1083:(e1081:r397:"redo::break"->d999:"std.control.flow.label_loop.redo.break" e1082:()); std::control::flow::loop::last p235:_, p236:_ -> e1086:(e1084:r398:"last::break"->d206:"std.control.flow.label_loop.last.break" e1085:()); std::control::flow::loop::next p237:_, p238:_ -> e1089:(e1087:r399:"next::break"->d1007:"std.control.flow.label_loop.next.break" e1088:()); std::control::flow::loop::redo p239:_, p240:_ -> e1092:(e1090:r400:"redo::break"->d999:"std.control.flow.label_loop.redo.break" e1091:()) })); e1096:() }; p242:false -> e1098:() }); e1101:() }; e1105:(e1103:r401:loop->d1157:loop e1104:true) })))))))
        my d998:"std.control.flow.label_loop.redo" mod {
          d1000:"std.control.flow.label_loop.redo.judge": any [std::control::flow::label_loop::redo; 'a] -> ['a] bool = e1047:(fn p215:d1152:x -> e1046:catch e1043:r379:x->d1152:x { std::control::flow::label_loop::redo::break p216:_, p217:_ -> e1044:true; p218:_ -> e1045:false })
          d1001:"std.control.flow.label_loop.redo.sub": any [std::control::flow::label_loop::redo; 'a] -> ['a] () = e1052:(fn p219:d1153:x -> e1051:catch e1048:r380:x->d1153:x { std::control::flow::label_loop::redo::break p220:_, p221:_ -> e1049:(); p222:_ -> e1050:() })
        }
        my d1006:"std.control.flow.label_loop.next" mod {
          d1008:"std.control.flow.label_loop.next.judge": any [std::control::flow::label_loop::next; 'a] -> ['a] bool = e1037:(fn p207:d1150:x -> e1036:catch e1033:r377:x->d1150:x { std::control::flow::label_loop::next::break p208:_, p209:_ -> e1034:true; p210:_ -> e1035:false })
          d1009:"std.control.flow.label_loop.next.sub": any [std::control::flow::label_loop::next; 'a] -> ['a] () = e1042:(fn p211:d1151:x -> e1041:catch e1038:r378:x->d1151:x { std::control::flow::label_loop::next::break p212:_, p213:_ -> e1039:(); p214:_ -> e1040:() })
        }
      }
    }
    pub d17:"std.control.junction" mod {
      pub d211:"std.control.junction.junction" mod {
        pub d215:"std.control.junction.junction.any": 'a -> [std::control::junction::junction] 'b where 'a: std::data::fold::Fold(item = 'b) = e1135:(fn p243:d1159:xs -> e1134:(e1114:r402:"sub::sub"->d173:"std.control.flow.sub.sub" e1133:block { e1129:(e1118:(e1116:(e1115:r403:xs->d1159:xs.s38.fold=>d449:"std.data.fold.Fold.fold") e1117:()) e1128:(fn p244:() -> e1127:(fn p245:d1160:x -> e1126:case e1121:(e1119:r404:or->d212:"std.control.junction.junction.or" e1120:()) { p246:true -> e1124:(e1122:r405:"sub::return"->d172:"std.control.flow.sub.return" e1123:r406:x->d1160:x); p247:false -> e1125:() }))); e1132:(e1130:r407:ret->d214:"std.control.junction.junction.ret" e1131:false) }))
        pub d216:"std.control.junction.junction.all": 'a -> [std::control::junction::junction] 'b where 'a: std::data::fold::Fold(item = 'b) = e1157:(fn p248:d1161:xs -> e1156:(e1136:r408:"sub::sub"->d173:"std.control.flow.sub.sub" e1155:block { e1151:(e1140:(e1138:(e1137:r409:xs->d1161:xs.s39.fold=>d449:"std.data.fold.Fold.fold") e1139:()) e1150:(fn p249:() -> e1149:(fn p250:d1162:x -> e1148:case e1143:(e1141:r410:and->d213:"std.control.junction.junction.and" e1142:()) { p251:true -> e1146:(e1144:r411:"sub::return"->d172:"std.control.flow.sub.return" e1145:r412:x->d1162:x); p252:false -> e1147:() }))); e1154:(e1152:r413:ret->d214:"std.control.junction.junction.ret" e1153:true) }))
        pub d217:"std.control.junction.junction.junction": bool [std::control::junction::junction; 'a] -> ['a] bool = e1185:(fn p253:d1163:x -> e1184:catch e1158:r414:x->d1163:x { std::control::junction::junction::or p254:_, p255:d1164:k -> e1170:case e1163:(e1159:r415:junction->d217:"std.control.junction.junction.junction" e1162:(e1160:r416:k->d1164:k e1161:true)) { p256:true -> e1164:true; p257:_ -> e1169:(e1165:r417:junction->d217:"std.control.junction.junction.junction" e1168:(e1166:r418:k->d1164:k e1167:false)) }; std::control::junction::junction::and p258:_, p259:d1165:k -> e1182:case e1175:(e1171:r419:junction->d217:"std.control.junction.junction.junction" e1174:(e1172:r420:k->d1165:k e1173:true)) { p260:true -> e1180:(e1176:r421:junction->d217:"std.control.junction.junction.junction" e1179:(e1177:r422:k->d1165:k e1178:false)); p261:_ -> e1181:false }; std::control::junction::junction::ret p262:d1166:b, p263:_ -> e1183:r423:b->d1166:b })
      }
      pub d218:"std.control.junction.any": 'a -> [std::control::junction::junction] 'b where 'a: std::data::fold::Fold(item = 'b) = e1189:(fn p264:d1167:xs -> e1188:(e1186:r424:"junction::any"->d215:"std.control.junction.junction.any" e1187:r425:xs->d1167:xs))
      pub d219:"std.control.junction.all": 'a -> [std::control::junction::junction] 'b where 'a: std::data::fold::Fold(item = 'b) = e1193:(fn p265:d1168:xs -> e1192:(e1190:r426:"junction::all"->d216:"std.control.junction.junction.all" e1191:r427:xs->d1168:xs))
    }
    pub d18:"std.control.throw" mod {
      pub d231:"std.control.throw.Throw" mod {
        pub d232:"std.control.throw.Throw.throw": 'a -> ['b] never where 'a: std::control::throw::Throw(throws = 'b) = <missing>
      }
    }
    pub d19:"std.control.nondet" mod {
      pub d220:"std.control.nondet.nondet" mod {
        pub d223:"std.control.nondet.nondet.guard": bool -> [std::control::nondet::nondet] () = e1202:(fn p266:d1169:b -> e1201:case e1196:(e1195:r429:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1194:r428:b->d1169:b) { p267:true -> e1197:(); p268:false -> e1200:(e1198:r430:reject->d222:"std.control.nondet.nondet.reject" e1199:()) })
        pub d224:"std.control.nondet.nondet.each": 'a -> [std::control::nondet::nondet] 'b where 'a: std::data::fold::Fold(item = 'b) = e1226:(fn p269:d1170:xs -> e1225:(e1203:r431:"sub::sub"->d173:"std.control.flow.sub.sub" e1224:block { e1220:(e1207:(e1205:(e1204:r432:xs->d1170:xs.s40.fold=>d449:"std.data.fold.Fold.fold") e1206:()) e1219:(fn p270:() -> e1218:(fn p271:d1171:x -> e1217:case e1212:(e1211:r434:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1210:(e1208:r433:branch->d221:"std.control.nondet.nondet.branch" e1209:())) { p272:true -> e1215:(e1213:r435:"sub::return"->d172:"std.control.flow.sub.return" e1214:r436:x->d1171:x); p273:false -> e1216:() }))); e1223:(e1221:r437:reject->d222:"std.control.nondet.nondet.reject" e1222:()) }))
        pub d225:"std.control.nondet.nondet.#act-method:list:225": 'a [std::control::nondet::nondet; 'b] -> ['b] std::data::list::list 'a = e1246:(fn p274:d1172:x -> e1245:catch e1227:r438:x->d1172:x { std::control::nondet::nondet::branch p275:_, p276:d1173:k -> e1238:(e1233:(e1228:r439:"std::data::list::merge"->d478:"std.data.list.merge" e1232:(e1231:(e1229:r440:k->d1173:k e1230:true).s41.list->d225:"std.control.nondet.nondet.#act-method:list:225")) e1237:(e1236:(e1234:r441:k->d1173:k e1235:false).s42.list->d225:"std.control.nondet.nondet.#act-method:list:225")); std::control::nondet::nondet::reject p277:_, p278:_ -> e1241:(e1239:builtin_op::list_empty e1240:()); p279:d1174:v -> e1244:(e1243:builtin_op::list_singleton e1242:r442:v->d1174:v) })
        pub d226:"std.control.nondet.nondet.logic": any [std::control::nondet::nondet; 'a] -> ['a] std::data::list::list 'b = e1321:(fn p280:d1175:x -> e1320:block { e1308:block { let my p281:d1176:loop = e1306:(fn p282:d1177:x -> e1305:(fn p283:d1178:queue -> e1304:(fn p284:d1179:res -> e1303:catch e1247:r443:x->d1177:x { std::control::nondet::nondet::branch p285:_, p286:d1180:k -> e1262:(e1260:(e1252:(e1248:r444:loop->d1176:loop e1251:(e1249:r445:k->d1180:k e1250:true)) e1259:(e1255:(e1253:r446:"std::data::list::append"->d497:"std.data.list.append" e1254:r447:queue->d1178:queue) e1258:(e1257:builtin_op::list_singleton e1256:r448:k->d1180:k))) e1261:r449:res->d1179:res); std::control::nondet::nondet::reject p287:_, p288:_ -> e1276:case e1265:(e1263:r450:"std::data::list::uncons"->d492:"std.data.list.uncons" e1264:r451:queue->d1178:queue) { p289:r452:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil" -> e1266:r453:res->d1179:res; p293:r454:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just"(p292:(p290:d1181:k, p291:d1182:queue)) -> e1275:(e1273:(e1271:(e1267:r455:loop->d1176:loop e1270:(e1268:r456:k->d1181:k e1269:false)) e1272:r457:queue->d1182:queue) e1274:r458:res->d1179:res) }; p294:d1183:v -> e1302:case e1279:(e1277:r459:"std::data::list::uncons"->d492:"std.data.list.uncons" e1278:r460:queue->d1178:queue) { p295:r461:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil" -> e1286:(e1282:(e1280:r462:"std::data::list::append"->d497:"std.data.list.append" e1281:r463:res->d1179:res) e1285:(e1284:builtin_op::list_singleton e1283:r464:v->d1183:v)); p299:r465:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just"(p298:(p296:d1184:k, p297:d1185:queue)) -> e1301:(e1293:(e1291:(e1287:r466:loop->d1176:loop e1290:(e1288:r467:k->d1184:k e1289:false)) e1292:r468:queue->d1185:queue) e1300:(e1296:(e1294:r469:"std::data::list::append"->d497:"std.data.list.append" e1295:r470:res->d1179:res) e1299:(e1298:builtin_op::list_singleton e1297:r471:v->d1183:v))) } }))); e1307:() }; e1319:(e1315:(e1311:(e1309:r472:loop->d1176:loop e1310:r473:x->d1175:x) e1314:(e1312:builtin_op::list_empty e1313:())) e1318:(e1316:builtin_op::list_empty e1317:())) })
        pub d227:"std.control.nondet.nondet.once": 'a [std::control::nondet::nondet; 'b] -> ['b] std::data::opt::opt 'a = e1364:(fn p300:d1186:x -> e1363:block { e1355:block { let my p301:d1187:loop = e1353:(fn p302:d1188:x -> e1352:(fn p303:d1189:queue -> e1351:catch e1322:r474:x->d1188:x { std::control::nondet::nondet::branch p304:_, p305:d1190:k -> e1335:(e1327:(e1323:r475:loop->d1187:loop e1326:(e1324:r476:k->d1190:k e1325:true)) e1334:(e1330:(e1328:r477:"std::data::list::append"->d497:"std.data.list.append" e1329:r478:queue->d1189:queue) e1333:(e1332:builtin_op::list_singleton e1331:r479:k->d1190:k))); std::control::nondet::nondet::reject p306:_, p307:_ -> e1347:case e1338:(e1336:r480:"std::data::list::uncons"->d492:"std.data.list.uncons" e1337:r481:queue->d1189:queue) { p308:r482:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil" -> e1339:r483:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil"; p312:r484:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just"(p311:(p309:d1191:k, p310:d1192:queue)) -> e1346:(e1344:(e1340:r485:loop->d1187:loop e1343:(e1341:r486:k->d1191:k e1342:false)) e1345:r487:queue->d1192:queue) }; p313:d1193:v -> e1350:(e1348:r488:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just" e1349:r489:v->d1193:v) })); e1354:() }; e1362:(e1358:(e1356:r490:loop->d1187:loop e1357:r491:x->d1186:x) e1361:(e1359:builtin_op::list_empty e1360:())) })
        pub d228:"std.control.nondet.nondet.#act-method:logic:228": any [std::control::nondet::nondet; 'a] -> ['a] std::data::list::list 'b = e1368:(fn p314:d1194:x -> e1367:(e1365:r492:logic->d226:"std.control.nondet.nondet.logic" e1366:r493:x->d1194:x))
        pub d229:"std.control.nondet.nondet.#act-method:once:229": 'a [std::control::nondet::nondet; 'b] -> ['b] std::data::opt::opt 'a = e1372:(fn p315:d1195:x -> e1371:(e1369:r494:once->d227:"std.control.nondet.nondet.once" e1370:r495:x->d1195:x))
        pub d230:"std.control.nondet.nondet.#act-method:guard:230": 'a ['b] -> ('a ['b] -> ['c] bool) -> [std::control::nondet::nondet, 'b, 'c] 'a = e1381:(fn p316:d1196:x -> e1380:(fn p317:d1197:f -> e1379:block { e1377:(e1373:r496:guard->d223:"std.control.nondet.nondet.guard" e1376:(e1374:r497:f->d1197:f e1375:r498:x->d1196:x)); e1378:r499:x->d1196:x }))
      }
    }
    pub d20:"std.control.var" mod {
      pub d233:"std.control.var.ref_update" mod {
      }
      pub d235:"std.control.var.ref": {get: () -> ['a] 'b, update_effect: () -> [std::control::var::ref_update 'b; 'c] ()} -> std::control::var::ref('a | 'c, 'b) = <missing>
      pub d240:"std.control.var.ref" mod {
        pub d241:"std.control.var.ref.update": std::control::var::ref('a & 'b, 'c) -> ('c -> ['b] 'c) -> ['b, 'a] () = e1400:(fn p318:d1198:r -> e1399:(fn p319:d1199:f -> e1398:block { let my p320:d1200:loop = e1391:(fn p321:d1201:x -> e1390:catch e1382:r500:x->d1201:x { std::control::var::ref_update::update p322:d1202:v, p323:d1203:k -> e1389:(e1383:r501:loop->d1200:loop e1388:(e1384:r502:k->d1203:k e1387:(e1385:r503:f->d1199:f e1386:r504:v->d1202:v))) }); e1397:(e1392:r505:loop->d1200:loop e1396:(e1394:(e1393:r506:r->d1198:r.s43.update_effect->d238) e1395:())) }))
      }
      pub d242:"std.control.var.var" mod {
        my d245:"std.control.var.var.var_ref": () -> std::control::var::ref '[std::control::var::var 'a] 'a = e1416:(fn p324:() -> e1415:(e1401:r507:ref->d235:"std.control.var.ref" e1414:{get: e1405:(fn p325:() -> e1404:(e1402:r508:get->d243:"std.control.var.var.get" e1403:())), update_effect: e1413:(fn p326:() -> e1412:(e1406:r509:set->d244:"std.control.var.var.set" e1411:(e1407:r510:"ref_update::update"->d234:"std.control.var.ref_update.update" e1410:(e1408:r511:get->d243:"std.control.var.var.get" e1409:()))))}))
        my d246:"std.control.var.var.run": 'a -> 'b [std::control::var::var 'a; 'c] -> ['c] 'b = e1434:(fn p327:d1204:v -> e1433:(fn p328:d1205:x -> e1432:catch e1417:r512:x->d1205:x { std::control::var::var::get p329:_, p330:d1206:k -> e1424:(e1420:(e1418:r513:run->d246:"std.control.var.var.run" e1419:r514:v->d1204:v) e1423:(e1421:r515:k->d1206:k e1422:r516:v->d1204:v)); std::control::var::var::set p331:d1207:v, p332:d1208:k -> e1431:(e1427:(e1425:r517:run->d246:"std.control.var.var.run" e1426:r518:v->d1207:v) e1430:(e1428:r519:k->d1208:k e1429:())) }))
      }
    }
  }
  pub d9:"std.io" mod {
    pub d57:"std.io.console" mod {
      pub d537:"std.io.console.out" mod {
      }
      pub d539:"std.io.console.print": std::text::str::str -> [std::io::console::out] () = e3320:(fn p822:d1549:value -> e3319:(e3317:r1336:"out::write"->d538:"std.io.console.out.write" e3318:r1337:value->d1549:value))
      pub d540:"std.io.console.say": 'a -> [std::io::console::out] () where 'a: std::core::fmt::Display = e3329:(fn p823:d1550:value -> e3328:(e3321:r1338:"out::write"->d538:"std.io.console.out.write" e3327:(e3326:(e3324:r1340:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3323:(e3322:r1339:value->d1550:value.s126.show=>d319:"std.core.fmt.Display.show")) e3325:"\n")))
      pub d541:"std.io.console.println": std::text::str::str -> [std::io::console::out] () = e3337:(fn p824:d1551:value -> e3336:(e3330:r1341:"out::write"->d538:"std.io.console.out.write" e3335:(e3334:(e3332:r1343:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3331:r1342:value->d1551:value) e3333:"\n")))
      pub d542:"std.io.console.err" mod {
      }
      pub d544:"std.io.console.note": 'a -> [std::io::console::err] () where 'a: std::core::fmt::Display = e3346:(fn p825:d1552:value -> e3345:(e3338:r1344:"err::write"->d543:"std.io.console.err.write" e3344:(e3343:(e3341:r1346:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3340:(e3339:r1345:value->d1552:value.s127.show=>d319:"std.core.fmt.Display.show")) e3342:"\n")))
      pub d545:"std.io.console.eprint": std::text::str::str -> [std::io::console::err] () = e3350:(fn p826:d1553:value -> e3349:(e3347:r1347:"err::write"->d543:"std.io.console.err.write" e3348:r1348:value->d1553:value))
      pub d546:"std.io.console.eprintln": std::text::str::str -> [std::io::console::err] () = e3358:(fn p827:d1554:value -> e3357:(e3351:r1349:"err::write"->d543:"std.io.console.err.write" e3356:(e3355:(e3353:r1351:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3352:r1350:value->d1554:value) e3354:"\n")))
      pub d547:"std.io.console.dd": 'a -> [std::io::console::err] () where 'a: std::core::fmt::Debug = e3367:(fn p828:d1555:value -> e3366:(e3359:r1352:"err::write"->d543:"std.io.console.err.write" e3365:(e3364:(e3362:r1354:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3361:(e3360:r1353:value->d1555:value.s128.debug=>d323:"std.core.fmt.Debug.debug")) e3363:"\n")))
      pub d548:"std.io.console.warn" mod {
      }
      pub d550:"std.io.console.die" mod {
      }
    }
    pub d58:"std.io.file" mod {
      pub d552:"std.io.file.file_kind" mod {
        pub d553:"std.io.file.file_kind.missing": std::io::file::file_kind = <missing>
        pub d554:"std.io.file.file_kind.denied": std::io::file::file_kind = <missing>
        pub d555:"std.io.file.file_kind.file": std::io::file::file_kind = <missing>
        pub d556:"std.io.file.file_kind.dir": std::io::file::file_kind = <missing>
        pub d557:"std.io.file.file_kind.symlink": std::io::file::file_kind = <missing>
        pub d558:"std.io.file.file_kind.other": std::io::file::file_kind = <missing>
      }
      pub d559:"std.io.file.file_meta": {kind: std::io::file::file_kind, size: int, readonly: bool, modified: std::data::opt::opt std::time::instant} -> std::io::file::file_meta = <missing>
      pub d568:"std.io.file.file" mod {
      }
      pub d577:"std.io.file.io_err" mod {
        pub d578:"std.io.file.io_err.not_found": std::text::path::path -> std::io::file::io_err = <missing>
        pub d580:"std.io.file.io_err.denied": std::text::path::path -> std::io::file::io_err = <missing>
        pub d582:"std.io.file.io_err.invalid_path": std::text::path::path -> std::io::file::io_err = <missing>
        pub d584:"std.io.file.io_err.failed": std::text::path::path -> std::text::str::str -> std::io::file::io_err = <missing>
      }
      my d587:"std.io.file.unwrap_io": std::data::result::result 'a 'b -> ['c] 'a where 'b: std::control::throw::Throw(throws = 'c) = e3458:(fn p861:d1579:result -> e3457:case e3453:r1402:result->d1579:result { p863:r1403:"result::ok"->d529:"std.data.result.result.ok"(p862:d1580:value) -> e3454:r1404:value->d1580:value; p865:r1405:"result::err"->d530:"std.data.result.result.err"(p864:d1581:err) -> e3456:(e3455:r1406:err->d1581:err.s134.throw=>d232:"std.control.throw.Throw.throw") })
      pub d588:"std.io.file.meta": std::text::path::path -> [std::io::file::file] std::io::file::file_meta = e3462:(fn p866:d1582:path -> e3461:(e3459:r1407:"file::meta"->d571:"std.io.file.file.meta" e3460:r1408:path->d1582:path))
      pub d589:"std.io.file.exists": std::text::path::path -> [std::io::file::file] bool = e3471:(fn p867:d1583:path -> e3470:case e3466:(e3465:(e3463:r1409:meta->d588:"std.io.file.meta" e3464:r1410:path->d1583:path).s135.kind->d560) { p868:r1411:"file_kind::missing"->d553:"std.io.file.file_kind.missing" -> e3467:false; p869:r1412:"file_kind::denied"->d554:"std.io.file.file_kind.denied" -> e3468:false; p870:_ -> e3469:true })
      pub d590:"std.io.file.is_file": std::text::path::path -> [std::io::file::file] bool = e3479:(fn p871:d1584:path -> e3478:case e3475:(e3474:(e3472:r1413:meta->d588:"std.io.file.meta" e3473:r1414:path->d1584:path).s136.kind->d560) { p872:r1415:"file_kind::file"->d555:"std.io.file.file_kind.file" -> e3476:true; p873:_ -> e3477:false })
      pub d591:"std.io.file.is_dir": std::text::path::path -> [std::io::file::file] bool = e3487:(fn p874:d1585:path -> e3486:case e3483:(e3482:(e3480:r1416:meta->d588:"std.io.file.meta" e3481:r1417:path->d1585:path).s137.kind->d560) { p875:r1418:"file_kind::dir"->d556:"std.io.file.file_kind.dir" -> e3484:true; p876:_ -> e3485:false })
      pub d592:"std.io.file.read_at": std::text::path::path -> std::data::range::range -> [std::io::file::file, std::io::file::io_err] (std::text::str::str, std::data::range::range) = e3496:(fn p877:d1586:path -> e3495:(fn p878:d1587:r -> e3494:(e3488:r1419:unwrap_io->d587:"std.io.file.unwrap_io" e3493:(e3489:r1420:"file::read_at"->d575:"std.io.file.file.read_at" e3492:(e3490:r1421:path->d1586:path, e3491:r1422:r->d1587:r)))))
      pub d593:"std.io.file.write_at": std::text::path::path -> std::data::range::range -> std::text::str::str -> [std::io::file::file, std::io::file::io_err] () = e3507:(fn p879:d1588:path -> e3506:(fn p880:d1589:r -> e3505:(fn p881:d1590:text -> e3504:(e3497:r1423:unwrap_io->d587:"std.io.file.unwrap_io" e3503:(e3498:r1424:"file::write_at"->d576:"std.io.file.file.write_at" e3502:(e3499:r1425:path->d1588:path, e3500:r1426:r->d1589:r, e3501:r1427:text->d1590:text))))))
      pub d594:"std.io.file.read_text": std::text::path::path -> [std::io::file::file, std::io::file::io_err] std::text::str::str = e3513:(fn p882:d1591:path -> e3512:(e3508:r1428:unwrap_io->d587:"std.io.file.unwrap_io" e3511:(e3509:r1429:"file::load"->d569:"std.io.file.file.load" e3510:r1430:path->d1591:path)))
      pub d595:"std.io.file.write_text": std::text::path::path -> std::text::str::str -> [std::io::file::file, std::io::file::io_err] () = e3522:(fn p883:d1592:path -> e3521:(fn p884:d1593:text -> e3520:(e3514:r1431:unwrap_io->d587:"std.io.file.unwrap_io" e3519:(e3515:r1432:"file::store"->d570:"std.io.file.file.store" e3518:(e3516:r1433:path->d1592:path, e3517:r1434:text->d1593:text)))))
      pub d596:"std.io.file.text": std::text::path::path -> [std::io::file::file, std::io::file::io_err] std::control::var::ref '[std::io::file::file] std::text::str::str = e3546:(fn p885:d1594:path -> e3545:block { e3527:(e3523:r1435:unwrap_io->d587:"std.io.file.unwrap_io" e3526:(e3524:r1436:"file::ambient_touch"->d572:"std.io.file.file.ambient_touch" e3525:r1437:path->d1594:path)); e3544:(e3528:r1438:ref->d235:"std.control.var.ref" e3543:{get: e3532:(fn p886:() -> e3531:(e3529:r1439:"file::ambient_get"->d573:"std.io.file.file.ambient_get" e3530:r1440:path->d1594:path)), update_effect: e3542:(fn p887:() -> e3541:(e3533:r1441:"file::ambient_set"->d574:"std.io.file.file.ambient_set" e3540:(e3534:r1442:path->d1594:path, e3539:(e3535:r1443:"ref_update::update"->d234:"std.control.var.ref_update.update" e3538:(e3536:r1444:"file::ambient_get"->d573:"std.io.file.file.ambient_get" e3537:r1445:path->d1594:path)))))}) })
      pub d597:"std.io.file.text_with": std::text::path::path -> (std::text::str::str -> ['a] ('b, std::text::str::str)) -> [std::io::file::file, std::io::file::io_err, 'a] 'b = e3567:(fn p888:d1595:path -> e3566:(fn p889:d1596:f -> e3565:block { let my p890:d1597:initial = e3551:(e3547:r1446:unwrap_io->d587:"std.io.file.unwrap_io" e3550:(e3548:r1447:"file::load"->d569:"std.io.file.file.load" e3549:r1448:path->d1595:path)); e3564:block { let my p893:(p891:d1598:result, p892:d1599:final) = e3554:(e3552:r1449:f->d1596:f e3553:r1450:initial->d1597:initial); e3563:block { e3561:(e3555:r1451:unwrap_io->d587:"std.io.file.unwrap_io" e3560:(e3556:r1452:"file::store"->d570:"std.io.file.file.store" e3559:(e3557:r1453:path->d1595:path, e3558:r1454:final->d1599:final))); e3562:r1455:result->d1598:result } } }))
    }
    pub d59:"std.io.net" mod {
      pub d598:"std.io.net.request": {meta: std::io::net::request_meta, payload: std::text::bytes::bytes, slot: std::io::net::respond_slot} -> std::io::net::request = <missing>
      pub d605:"std.io.net.net_err" mod {
        pub d606:"std.io.net.net_err.unreachable": std::text::str::str -> std::io::net::net_err = <missing>
        pub d608:"std.io.net.net_err.refused": std::text::str::str -> std::io::net::net_err = <missing>
        pub d610:"std.io.net.net_err.already_bound": std::text::str::str -> std::io::net::net_err = <missing>
        pub d612:"std.io.net.net_err.closed": std::io::net::net_err = <missing>
        pub d614:"std.io.net.net_err.timeout": std::io::net::net_err = <missing>
        pub d616:"std.io.net.net_err.failed": std::text::str::str -> std::io::net::net_err = <missing>
      }
      pub d619:"std.io.net.net" mod {
      }
      pub d622:"std.io.net.server" mod {
      }
      my d625:"std.io.net.unwrap_net": std::data::result::result 'a 'b -> ['c] 'a where 'b: std::control::throw::Throw(throws = 'c) = e3655:(fn p930:d1620:result -> e3654:case e3650:r1507:result->d1620:result { p932:r1508:"result::ok"->d529:"std.data.result.result.ok"(p931:d1621:value) -> e3651:r1509:value->d1621:value; p934:r1510:"result::err"->d530:"std.data.result.result.err"(p933:d1622:err) -> e3653:(e3652:r1511:err->d1622:err.s142.throw=>d232:"std.control.throw.Throw.throw") })
      pub d626:"std.io.net.listen": int -> [std::io::net::net, std::io::net::net_err] std::io::net::listener = e3661:(fn p935:d1623:port -> e3660:(e3656:r1512:unwrap_net->d625:"std.io.net.unwrap_net" e3659:(e3657:r1513:"net::listen"->d620:"std.io.net.net.listen" e3658:r1514:port->d1623:port)))
      pub d627:"std.io.net.serve": int -> [std::io::net::net, std::io::net::net_err, std::io::net::server] std::io::net::request = e3669:(fn p936:d1624:port -> e3668:block { let my p937:d1625:listener = e3664:(e3662:r1515:listen->d626:"std.io.net.listen" e3663:r1516:port->d1624:port); e3667:(e3665:r1517:"server::accept"->d623:"std.io.net.server.accept" e3666:r1518:listener->d1625:listener) })
      pub d628:"std.io.net.listener" mod {
        pub d629:"std.io.net.listener.accept": std::io::net::listener -> () -> [std::io::net::server] std::io::net::request = e3674:(fn p938:d1626:l -> e3673:(fn p939:() -> e3672:(e3670:r1519:"server::accept"->d623:"std.io.net.server.accept" e3671:r1520:l->d1626:l)))
        pub d630:"std.io.net.listener.port": std::io::net::listener -> [std::io::net::net] int = e3678:(fn p940:d1627:l -> e3677:(e3675:r1521:"net::port"->d621:"std.io.net.net.port" e3676:r1522:l->d1627:l))
      }
      pub d631:"std.io.net.request" mod {
        pub d632:"std.io.net.request.respond": std::io::net::request -> std::text::bytes::bytes -> [std::io::net::net_err, std::io::net::server] () = e3688:(fn p941:d1628:req -> e3687:(fn p942:d1629:res -> e3686:(e3679:r1523:unwrap_net->d625:"std.io.net.unwrap_net" e3685:(e3680:r1524:"server::respond"->d624:"std.io.net.server.respond" e3684:(e3682:(e3681:r1525:req->d1628:req.s143.slot->d603), e3683:r1526:res->d1629:res)))))
      }
    }
  }
  pub d10:"std.time" mod {
    pub d117:"std.time.instant": {epoch_nanos: int} -> std::time::instant = <missing>
    pub d120:"std.time.duration": {nanos: int} -> std::time::duration = <missing>
    pub d123:"std.time.clock" mod {
    }
    pub d125:"std.time.instant_add": std::time::instant -> std::time::duration -> std::time::instant = e170:(fn p39:d1049:t -> e169:(fn p40:d1050:delta -> e168:(e159:r57:instant->d117:"std.time.instant" e167:{epoch_nanos: e166:(e163:(e160:r58:"std::int::add"->d50:"std.int.add" e162:(e161:r59:t->d1049:t.s2.epoch_nanos->d118)) e165:(e164:r60:delta->d1050:delta.s3.nanos->d121))})))
    pub d126:"std.time.instant_sub": std::time::instant -> std::time::duration -> std::time::instant = e182:(fn p41:d1051:t -> e181:(fn p42:d1052:delta -> e180:(e171:r61:instant->d117:"std.time.instant" e179:{epoch_nanos: e178:(e175:(e172:r62:"std::int::sub"->d51:"std.int.sub" e174:(e173:r63:t->d1051:t.s4.epoch_nanos->d118)) e177:(e176:r64:delta->d1052:delta.s5.nanos->d121))})))
    pub d127:"std.time.instant_since": std::time::instant -> std::time::instant -> std::time::duration = e194:(fn p43:d1053:later -> e193:(fn p44:d1054:earlier -> e192:(e183:r65:duration->d120:"std.time.duration" e191:{nanos: e190:(e187:(e184:r66:"std::int::sub"->d51:"std.int.sub" e186:(e185:r67:later->d1053:later.s6.epoch_nanos->d118)) e189:(e188:r68:earlier->d1054:earlier.s7.epoch_nanos->d118))})))
    pub d128:"std.time.duration_add": std::time::duration -> std::time::duration -> std::time::duration = e206:(fn p45:d1055:x -> e205:(fn p46:d1056:y -> e204:(e195:r69:duration->d120:"std.time.duration" e203:{nanos: e202:(e199:(e196:r70:"std::int::add"->d50:"std.int.add" e198:(e197:r71:x->d1055:x.s8.nanos->d121)) e201:(e200:r72:y->d1056:y.s9.nanos->d121))})))
    pub d129:"std.time.duration_sub": std::time::duration -> std::time::duration -> std::time::duration = e218:(fn p47:d1057:x -> e217:(fn p48:d1058:y -> e216:(e207:r73:duration->d120:"std.time.duration" e215:{nanos: e214:(e211:(e208:r74:"std::int::sub"->d51:"std.int.sub" e210:(e209:r75:x->d1057:x.s10.nanos->d121)) e213:(e212:r76:y->d1058:y.s11.nanos->d121))})))
    pub d130:"std.time.nanos": int -> std::time::duration = e223:(fn p49:d1059:count -> e222:(e219:r77:duration->d120:"std.time.duration" e221:{nanos: e220:r78:count->d1059:count}))
    pub d131:"std.time.micros": int -> std::time::duration = e231:(fn p50:d1060:count -> e230:(e224:r79:nanos->d130:"std.time.nanos" e229:(e227:(e225:r80:"std::int::mul"->d52:"std.int.mul" e226:r81:count->d1060:count) e228:1000)))
    pub d132:"std.time.millis": int -> std::time::duration = e239:(fn p51:d1061:count -> e238:(e232:r82:micros->d131:"std.time.micros" e237:(e235:(e233:r83:"std::int::mul"->d52:"std.int.mul" e234:r84:count->d1061:count) e236:1000)))
    pub d133:"std.time.secs": int -> std::time::duration = e247:(fn p52:d1062:count -> e246:(e240:r85:millis->d132:"std.time.millis" e245:(e243:(e241:r86:"std::int::mul"->d52:"std.int.mul" e242:r87:count->d1062:count) e244:1000)))
    pub d134:"std.time.mins": int -> std::time::duration = e255:(fn p53:d1063:count -> e254:(e248:r88:secs->d133:"std.time.secs" e253:(e251:(e249:r89:"std::int::mul"->d52:"std.int.mul" e250:r90:count->d1063:count) e252:60)))
    pub d135:"std.time.hours": int -> std::time::duration = e263:(fn p54:d1064:count -> e262:(e256:r91:mins->d134:"std.time.mins" e261:(e259:(e257:r92:"std::int::mul"->d52:"std.int.mul" e258:r93:count->d1064:count) e260:60)))
    pub d136:"std.time.days": int -> std::time::duration = e271:(fn p55:d1065:count -> e270:(e264:r94:hours->d135:"std.time.hours" e269:(e267:(e265:r95:"std::int::mul"->d52:"std.int.mul" e266:r96:count->d1065:count) e268:24)))
    my d137:"std.time.floor_div": int -> int -> int = e299:(fn p56:d1066:x -> e298:(fn p57:d1067:y -> e297:block { let my p58:d1068:q = e276:(e275:(e273:r98:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e272:r97:x->d1066:x) e274:r99:y->d1067:y); e296:block { let my p59:d1069:r = e281:(e280:(e278:r101:"#op:infix:mod"->d418:"std.core.ops.#op:infix:mod" e277:r100:x->d1066:x) e279:r102:y->d1067:y); e295:case e288:(e287:r105:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e286:(e285:(e283:r104:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e282:r103:r->d1069:r) e284:0)) { p60:true -> e293:(e292:(e290:r107:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e289:r106:q->d1068:q) e291:1); p61:false -> e294:r108:q->d1068:q } } }))
    my d138:"std.time.floor_mod": int -> int -> int = e314:(fn p62:d1070:x -> e313:(fn p63:d1071:y -> e312:(e311:(e301:r110:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e300:r109:x->d1070:x) e310:(e309:(e307:r114:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e306:(e304:(e302:r111:floor_div->d137:"std.time.floor_div" e303:r112:x->d1070:x) e305:r113:y->d1071:y)) e308:r115:y->d1071:y))))
    my d139:"std.time.civil_from_epoch_days": int -> (int, int, int) = e473:(fn p64:d1072:days_since_epoch -> e472:block { let my p65:d1073:z = e319:(e318:(e316:r117:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e315:r116:days_since_epoch->d1072:days_since_epoch) e317:719468); e471:block { let my p66:d1074:era = e324:(e322:(e320:r118:floor_div->d137:"std.time.floor_div" e321:r119:z->d1073:z) e323:146097); e470:block { let my p67:d1075:doe = e333:(e332:(e326:r121:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e325:r120:z->d1073:z) e331:(e330:(e328:r123:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e327:r122:era->d1074:era) e329:146097)); e469:block { let my p68:d1076:yoe = e362:(e361:(e359:r134:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e358:(e357:(e351:r131:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e350:(e349:(e343:r128:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e342:(e341:(e335:r125:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e334:r124:doe->d1075:doe) e340:(e339:(e337:r127:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e336:r126:doe->d1075:doe) e338:1460))) e348:(e347:(e345:r130:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e344:r129:doe->d1075:doe) e346:36524))) e356:(e355:(e353:r133:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e352:r132:doe->d1075:doe) e354:146096))) e360:365); e468:block { let my p69:d1077:year = e371:(e370:(e364:r136:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e363:r135:yoe->d1076:yoe) e369:(e368:(e366:r138:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e365:r137:era->d1074:era) e367:400)); e467:block { let my p70:d1078:doy = e396:(e395:(e373:r140:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e372:r139:doe->d1075:doe) e394:(e393:(e387:r146:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e386:(e385:(e379:r143:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e378:(e377:(e375:r141:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e374:365) e376:r142:yoe->d1076:yoe)) e384:(e383:(e381:r145:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e380:r144:yoe->d1076:yoe) e382:4))) e392:(e391:(e389:r148:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e388:r147:yoe->d1076:yoe) e390:100))); e466:block { let my p71:d1079:mp = e409:(e408:(e406:r152:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e405:(e404:(e402:r151:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e401:(e400:(e398:r149:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e397:5) e399:r150:doy->d1078:doy)) e403:2)) e407:153); e465:block { let my p72:d1080:day = e430:(e429:(e427:r159:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e426:(e425:(e411:r154:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e410:r153:doy->d1078:doy) e424:(e423:(e421:r158:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e420:(e419:(e417:r157:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e416:(e415:(e413:r155:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e412:153) e414:r156:mp->d1079:mp)) e418:2)) e422:5))) e428:1); e464:block { let my p73:d1081:month = e446:(e445:(e432:r161:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e431:r160:mp->d1079:mp) e444:case e439:(e438:r164:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e437:(e436:(e434:r163:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e433:r162:mp->d1079:mp) e435:10)) { p74:true -> e440:3; p75:false -> e443:(e441:r165:"#op:prefix:-"->d412:"std.core.ops.#op:prefix:-" e442:9) }); e463:(e460:case e453:(e452:r168:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e451:(e450:(e448:r167:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e447:r166:month->d1081:month) e449:2)) { p76:true -> e458:(e457:(e455:r170:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e454:r169:year->d1077:year) e456:1); p77:false -> e459:r171:year->d1077:year }, e461:r172:month->d1081:month, e462:r173:day->d1080:day) } } } } } } } } })
    my d140:"std.time.pad2": int -> std::text::str::str = e492:(fn p78:d1082:n -> e491:case e480:(e479:r176:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e478:(e477:(e475:r175:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e474:r174:n->d1082:n) e476:10)) { p79:true -> e487:(e486:(e482:r177:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e481:"0") e485:(e483:r178:"std::int::to_string"->d54:"std.int.to_string" e484:r179:n->d1082:n)); p80:false -> e490:(e488:r180:"std::int::to_string"->d54:"std.int.to_string" e489:r181:n->d1082:n) })
    my d141:"std.time.pad3": int -> std::text::str::str = e526:(fn p81:d1083:n -> e525:case e499:(e498:r184:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e497:(e496:(e494:r183:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e493:r182:n->d1083:n) e495:10)) { p84:true -> e506:(e505:(e501:r185:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e500:"00") e504:(e502:r186:"std::int::to_string"->d54:"std.int.to_string" e503:r187:n->d1083:n)); p85:false -> e524:case e513:(e512:r190:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e511:(e510:(e508:r189:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e507:r188:n->d1083:n) e509:100)) { p82:true -> e520:(e519:(e515:r191:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e514:"0") e518:(e516:r192:"std::int::to_string"->d54:"std.int.to_string" e517:r193:n->d1083:n)); p83:false -> e523:(e521:r194:"std::int::to_string"->d54:"std.int.to_string" e522:r195:n->d1083:n) } })
    my d142:"std.time.pad4": int -> std::text::str::str = e575:(fn p86:d1084:n -> e574:case e533:(e532:r198:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e531:(e530:(e528:r197:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e527:r196:n->d1084:n) e529:10)) { p91:true -> e540:(e539:(e535:r199:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e534:"000") e538:(e536:r200:"std::int::to_string"->d54:"std.int.to_string" e537:r201:n->d1084:n)); p92:false -> e573:case e547:(e546:r204:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e545:(e544:(e542:r203:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e541:r202:n->d1084:n) e543:100)) { p89:true -> e554:(e553:(e549:r205:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e548:"00") e552:(e550:r206:"std::int::to_string"->d54:"std.int.to_string" e551:r207:n->d1084:n)); p90:false -> e572:case e561:(e560:r210:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e559:(e558:(e556:r209:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e555:r208:n->d1084:n) e557:1000)) { p87:true -> e568:(e567:(e563:r211:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e562:"0") e566:(e564:r212:"std::int::to_string"->d54:"std.int.to_string" e565:r213:n->d1084:n)); p88:false -> e571:(e569:r214:"std::int::to_string"->d54:"std.int.to_string" e570:r215:n->d1084:n) } } })
    my d143:"std.time.pad9": int -> std::text::str::str = e607:(fn p93:d1085:n -> e606:(e605:(e597:r224:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e596:(e595:(e583:r219:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e582:(e576:r216:pad3->d141:"std.time.pad3" e581:(e580:(e578:r218:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e577:r217:n->d1085:n) e579:1000000))) e594:(e584:r220:pad3->d141:"std.time.pad3" e593:(e592:(e590:r223:"#op:infix:mod"->d418:"std.core.ops.#op:infix:mod" e589:(e588:(e586:r222:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e585:r221:n->d1085:n) e587:1000)) e591:1000)))) e604:(e598:r225:pad3->d141:"std.time.pad3" e603:(e602:(e600:r227:"#op:infix:mod"->d418:"std.core.ops.#op:infix:mod" e599:r226:n->d1085:n) e601:1000))))
    my d144:"std.time.trim_trailing_zeros": std::text::str::str -> std::text::str::str = e651:(fn p94:d1086:text -> e650:block { let my p95:d1087:len = e610:(e608:r228:"std::text::str::len"->d786:"std.text.str.len" e609:r229:text->d1086:text); e649:case e617:(e616:r232:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e615:(e614:(e612:r231:"#op:infix:<="->d422:"std.core.ops.#op:infix:<=" e611:r230:len->d1087:len) e613:0)) { p99:true -> e618:r233:text->d1086:text; p100:false -> e648:block { let my p96:d1088:end = e623:(e622:(e620:r235:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e619:r234:len->d1087:len) e621:1); e647:case e636:(e635:r241:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e634:(e633:(e631:r240:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e630:(e628:(e626:(e624:r236:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e625:r237:text->d1086:text) e627:r238:end->d1088:end) e629:r239:len->d1087:len)) e632:"0")) { p97:true -> e645:(e637:r242:trim_trailing_zeros->d144:"std.time.trim_trailing_zeros" e644:(e642:(e640:(e638:r243:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e639:r244:text->d1086:text) e641:0) e643:r245:end->d1088:end)); p98:false -> e646:r246:text->d1086:text } } } })
    my d145:"std.time.fraction_text": int -> std::text::str::str = e670:(fn p101:d1089:nanos_in_second -> e669:case e658:(e657:r249:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e656:(e655:(e653:r248:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e652:r247:nanos_in_second->d1089:nanos_in_second) e654:0)) { p102:true -> e659:""; p103:false -> e668:(e667:(e661:r250:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e660:".") e666:(e662:r251:trim_trailing_zeros->d144:"std.time.trim_trailing_zeros" e665:(e663:r252:pad9->d143:"std.time.pad9" e664:r253:nanos_in_second->d1089:nanos_in_second))) })
    my d146:"std.time.instant_rfc3339_utc": std::time::instant -> std::text::str::str = e790:(fn p104:d1090:x -> e789:block { let my p105:d1091:seconds = e676:(e674:(e671:r254:floor_div->d137:"std.time.floor_div" e673:(e672:r255:x->d1090:x.s12.epoch_nanos->d118)) e675:1000000000); e788:block { let my p106:d1092:nanos_in_second = e682:(e680:(e677:r256:floor_mod->d138:"std.time.floor_mod" e679:(e678:r257:x->d1090:x.s13.epoch_nanos->d118)) e681:1000000000); e787:block { let my p107:d1093:days = e687:(e685:(e683:r258:floor_div->d137:"std.time.floor_div" e684:r259:seconds->d1091:seconds) e686:86400); e786:block { let my p108:d1094:second_of_day = e692:(e690:(e688:r260:floor_mod->d138:"std.time.floor_mod" e689:r261:seconds->d1091:seconds) e691:86400); e785:block { let my p112:(p109:d1095:year, p110:d1096:month, p111:d1097:day) = e695:(e693:r262:civil_from_epoch_days->d139:"std.time.civil_from_epoch_days" e694:r263:days->d1093:days); e784:block { let my p113:d1098:hour = e700:(e699:(e697:r265:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e696:r264:second_of_day->d1094:second_of_day) e698:3600); e783:block { let my p114:d1099:minute = e709:(e708:(e706:r268:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e705:(e704:(e702:r267:"#op:infix:mod"->d418:"std.core.ops.#op:infix:mod" e701:r266:second_of_day->d1094:second_of_day) e703:3600)) e707:60); e782:block { let my p115:d1100:second = e714:(e713:(e711:r270:"#op:infix:mod"->d418:"std.core.ops.#op:infix:mod" e710:r269:second_of_day->d1094:second_of_day) e712:60); e781:block { let my p116:d1101:date = e737:(e736:(e732:r278:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e731:(e730:(e728:r277:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e727:(e726:(e722:r274:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e721:(e720:(e718:r273:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e717:(e715:r271:pad4->d142:"std.time.pad4" e716:r272:year->d1095:year)) e719:"-")) e725:(e723:r275:pad2->d140:"std.time.pad2" e724:r276:month->d1096:month))) e729:"-")) e735:(e733:r279:pad2->d140:"std.time.pad2" e734:r280:day->d1097:day)); e780:block { let my p117:d1102:clock = e760:(e759:(e755:r288:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e754:(e753:(e751:r287:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e750:(e749:(e745:r284:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e744:(e743:(e741:r283:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e740:(e738:r281:pad2->d140:"std.time.pad2" e739:r282:hour->d1098:hour)) e742:":")) e748:(e746:r285:pad2->d140:"std.time.pad2" e747:r286:minute->d1099:minute))) e752:":")) e758:(e756:r289:pad2->d140:"std.time.pad2" e757:r290:second->d1100:second)); e779:(e778:(e776:r298:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e775:(e774:(e770:r295:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e769:(e768:(e766:r293:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e765:(e764:(e762:r292:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e761:r291:date->d1101:date) e763:"T")) e767:r294:clock->d1102:clock)) e773:(e771:r296:fraction_text->d145:"std.time.fraction_text" e772:r297:nanos_in_second->d1092:nanos_in_second))) e777:"Z") } } } } } } } } } })
    my d147 mod {
      d148: std::time::instant -> std::time::instant -> bool = e799:(fn p118:d1103:x -> e798:(fn p119:d1104:y -> e797:(e794:(e791:r299:"std::int::eq"->d45:"std.int.eq" e793:(e792:r300:x->d1103:x.s14.epoch_nanos->d118)) e796:(e795:r301:y->d1104:y.s15.epoch_nanos->d118))))
    }
    my d149 mod {
      d150: std::time::instant -> std::time::instant -> bool = e808:(fn p120:d1105:x -> e807:(fn p121:d1106:y -> e806:(e803:(e800:r302:"std::int::lt"->d46:"std.int.lt" e802:(e801:r303:x->d1105:x.s16.epoch_nanos->d118)) e805:(e804:r304:y->d1106:y.s17.epoch_nanos->d118))))
      d151: std::time::instant -> std::time::instant -> bool = e817:(fn p122:d1107:x -> e816:(fn p123:d1108:y -> e815:(e812:(e809:r305:"std::int::le"->d47:"std.int.le" e811:(e810:r306:x->d1107:x.s18.epoch_nanos->d118)) e814:(e813:r307:y->d1108:y.s19.epoch_nanos->d118))))
      d152: std::time::instant -> std::time::instant -> bool = e826:(fn p124:d1109:x -> e825:(fn p125:d1110:y -> e824:(e821:(e818:r308:"std::int::gt"->d48:"std.int.gt" e820:(e819:r309:x->d1109:x.s20.epoch_nanos->d118)) e823:(e822:r310:y->d1110:y.s21.epoch_nanos->d118))))
      d153: std::time::instant -> std::time::instant -> bool = e835:(fn p126:d1111:x -> e834:(fn p127:d1112:y -> e833:(e830:(e827:r311:"std::int::ge"->d49:"std.int.ge" e829:(e828:r312:x->d1111:x.s22.epoch_nanos->d118)) e832:(e831:r313:y->d1112:y.s23.epoch_nanos->d118))))
    }
    my d154 mod {
      d155: std::time::duration -> std::time::duration -> bool = e844:(fn p128:d1113:x -> e843:(fn p129:d1114:y -> e842:(e839:(e836:r314:"std::int::eq"->d45:"std.int.eq" e838:(e837:r315:x->d1113:x.s24.nanos->d121)) e841:(e840:r316:y->d1114:y.s25.nanos->d121))))
    }
    my d156 mod {
      d157: std::time::duration -> std::time::duration -> bool = e853:(fn p130:d1115:x -> e852:(fn p131:d1116:y -> e851:(e848:(e845:r317:"std::int::lt"->d46:"std.int.lt" e847:(e846:r318:x->d1115:x.s26.nanos->d121)) e850:(e849:r319:y->d1116:y.s27.nanos->d121))))
      d158: std::time::duration -> std::time::duration -> bool = e862:(fn p132:d1117:x -> e861:(fn p133:d1118:y -> e860:(e857:(e854:r320:"std::int::le"->d47:"std.int.le" e856:(e855:r321:x->d1117:x.s28.nanos->d121)) e859:(e858:r322:y->d1118:y.s29.nanos->d121))))
      d159: std::time::duration -> std::time::duration -> bool = e871:(fn p134:d1119:x -> e870:(fn p135:d1120:y -> e869:(e866:(e863:r323:"std::int::gt"->d48:"std.int.gt" e865:(e864:r324:x->d1119:x.s30.nanos->d121)) e868:(e867:r325:y->d1120:y.s31.nanos->d121))))
      d160: std::time::duration -> std::time::duration -> bool = e880:(fn p136:d1121:x -> e879:(fn p137:d1122:y -> e878:(e875:(e872:r326:"std::int::ge"->d49:"std.int.ge" e874:(e873:r327:x->d1121:x.s32.nanos->d121)) e877:(e876:r328:y->d1122:y.s33.nanos->d121))))
    }
    my d161 mod {
      d162: std::time::instant -> std::text::str::str = e893:(fn p138:d1123:x -> e892:(e891:(e889:r332:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e888:(e887:(e882:r329:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e881:"instant { epoch_nanos: ") e886:(e883:r330:"std::int::to_string"->d54:"std.int.to_string" e885:(e884:r331:x->d1123:x.s34.epoch_nanos->d118)))) e890:" }"))
    }
    my d163 mod {
      d164: std::time::duration -> std::text::str::str = e906:(fn p139:d1124:x -> e905:(e904:(e902:r336:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e901:(e900:(e895:r333:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e894:"duration { nanos: ") e899:(e896:r334:"std::int::to_string"->d54:"std.int.to_string" e898:(e897:r335:x->d1124:x.s35.nanos->d121)))) e903:" }"))
    }
    my d165 mod {
      d166: std::time::instant -> std::text::str::str = e910:(fn p140:d1125:x -> e909:(e907:r337:instant_rfc3339_utc->d146:"std.time.instant_rfc3339_utc" e908:r338:x->d1125:x))
    }
    my d167 mod {
      d168: std::time::duration -> std::time::duration -> std::time::duration = e917:(fn p141:d1126:x -> e916:(fn p142:d1127:y -> e915:(e913:(e911:r339:duration_add->d128:"std.time.duration_add" e912:r340:x->d1126:x) e914:r341:y->d1127:y)))
    }
    my d169 mod {
      d170: std::time::duration -> std::time::duration -> std::time::duration = e924:(fn p143:d1128:x -> e923:(fn p144:d1129:y -> e922:(e920:(e918:r342:duration_sub->d129:"std.time.duration_sub" e919:r343:x->d1128:x) e921:r344:y->d1129:y)))
    }
  }
  pub d11:"std.testing" mod {
    pub d105:"std.testing.#op:prefix:assert": (() -> bool) -> [std::testing::assertion] () = e142:r50:"assertion::assert"->d108:"std.testing.assertion.assert"
    pub d106:"std.testing.#op:infix:assert_eq": (() -> 'a) -> (() -> 'a) -> [std::testing::assertion] () where 'a: std::core::cmp::Eq, 'a: std::core::fmt::Debug = e158:(fn p34:d1044:left -> e157:(fn p35:d1045:right -> e156:(e143:r51:"assertion::assert_eq"->d109:"std.testing.assertion.assert_eq" e155:(e144:r52:left->d1044:left, e145:r53:right->d1045:right, e151:(fn p36:d1046:expected -> e150:(fn p37:d1047:actual -> e149:(e147:(e146:r54:expected->d1046:expected.s0.eq=>d248:"std.core.cmp.Eq.eq") e148:r55:actual->d1047:actual))), e154:(fn p38:d1048:value -> e153:(e152:r56:value->d1048:value.s1.debug=>d323:"std.core.fmt.Debug.debug"))))))
    pub d107:"std.testing.assertion" mod {
    }
  }
  pub d12:"std.prelude" mod {
  }
  pub d108:"std.testing.assertion.assert": (() -> bool) -> [std::testing::assertion] () = <missing>
  pub d109:"std.testing.assertion.assert_eq": (() -> 'a, () -> 'a, 'a -> 'a -> bool, 'a -> std::text::str::str) -> [std::testing::assertion] () = <missing>
  pub d118: std::time::instant -> int = <missing>
  pub d119: std::control::var::ref 'a std::time::instant -> std::control::var::ref 'a int = <missing>
  pub d121: std::time::duration -> int = <missing>
  pub d122: std::control::var::ref 'a std::time::duration -> std::control::var::ref 'a int = <missing>
  pub d124:"std.time.clock.now": () -> [std::time::clock] std::time::instant = <missing>
  pub d172:"std.control.flow.sub.return": 'a -> [std::control::flow::sub 'a] never = <missing>
  pub d175:"std.control.flow.label_sub.return": 'a -> [std::control::flow::label_sub 'a] never = <missing>
  pub d177: std::control::flow::label_sub::label -> () = <missing>
  pub d178: std::control::var::ref 'a std::control::flow::label_sub::label -> std::control::var::ref 'a () = <missing>
  pub d182:"std.control.flow.loop.last": () -> [std::control::flow::loop] never = <missing>
  pub d183:"std.control.flow.loop.next": () -> [std::control::flow::loop] never = <missing>
  pub d184:"std.control.flow.loop.redo": () -> [std::control::flow::loop] never = <missing>
  d186:"std.control.flow.loop.last.break": () -> [std::control::flow::loop::last] never = <missing>
  pub d195:"std.control.flow.label_loop.last": () -> [std::control::flow::label_loop] never = <missing>
  pub d196:"std.control.flow.label_loop.next": () -> [std::control::flow::label_loop] never = <missing>
  pub d197:"std.control.flow.label_loop.redo": () -> [std::control::flow::label_loop] never = <missing>
  pub d199: std::control::flow::label_loop::label -> () -> [std::control::flow::label_loop] never = <missing>
  pub d200: std::control::var::ref 'a std::control::flow::label_loop::label -> std::control::var::ref('a, () ['[]] -> ['[std::control::flow::label_loop]] never) = <missing>
  pub d201: std::control::flow::label_loop::label -> () -> [std::control::flow::label_loop] never = <missing>
  pub d202: std::control::var::ref 'a std::control::flow::label_loop::label -> std::control::var::ref('a, () ['[]] -> ['[std::control::flow::label_loop]] never) = <missing>
  pub d203: std::control::flow::label_loop::label -> () -> [std::control::flow::label_loop] never = <missing>
  pub d204: std::control::var::ref 'a std::control::flow::label_loop::label -> std::control::var::ref('a, () ['[]] -> ['[std::control::flow::label_loop]] never) = <missing>
  d206:"std.control.flow.label_loop.last.break": () -> [std::control::flow::label_loop::last] never = <missing>
  my d212:"std.control.junction.junction.or": () -> [std::control::junction::junction] bool = <missing>
  my d213:"std.control.junction.junction.and": () -> [std::control::junction::junction] bool = <missing>
  my d214:"std.control.junction.junction.ret": bool -> [std::control::junction::junction] never = <missing>
  pub d221:"std.control.nondet.nondet.branch": () -> [std::control::nondet::nondet] bool = <missing>
  pub d222:"std.control.nondet.nondet.reject": () -> [std::control::nondet::nondet] never = <missing>
  pub d234:"std.control.var.ref_update.update": 'a -> [std::control::var::ref_update 'a] 'a = <missing>
  pub d236: std::control::var::ref 'a 'b -> () -> ['a] 'b = <missing>
  pub d237: std::control::var::ref('a, std::control::var::ref 'b 'c) -> std::control::var::ref('a, () ['[]] -> ['b] 'c) = <missing>
  pub d238: std::control::var::ref 'a 'b -> () -> [std::control::var::ref_update 'b, 'a#0[AllExcept(std::control::var::ref_update)]] () = <missing>
  pub d239: std::control::var::ref('a, std::control::var::ref 'b 'c) -> std::control::var::ref('a, () ['[]] -> ['[std::control::var::ref_update 'c, 'b] <: 'b & '[std::control::var::ref_update 'c; 'b]] ()) = <missing>
  pub d243:"std.control.var.var.get": () -> [std::control::var::var 'a] 'a = <missing>
  pub d244:"std.control.var.var.set": 'a -> [std::control::var::var 'a] () = <missing>
  my d285:"#cast": std::text::path::path -> std::text::bytes::bytes = e1593:(fn p389:d1253:p -> e1592:(e1590:r592:"std::text::path::to_bytes"->d778:"std.text.path.to_bytes" e1591:r593:p->d1253:p))
  my d286:"#cast": int -> std::num::frac::frac = e1599:(fn p390:d1254:x -> e1598:(e1596:(e1594:r594:"std::num::frac::new"->d641:"std.num.frac.new" e1595:r595:x->d1254:x) e1597:1))
  my d287:"#cast": int -> float = e1603:(fn p391:d1255:x -> e1602:(e1600:builtin_op::int_to_float e1601:r596:x->d1255:x))
  my d288:"#cast": std::num::frac::frac -> float = e1607:(fn p392:d1256:x -> e1606:(e1604:r597:"std::num::frac::to_float"->d651:"std.num.frac.to_float" e1605:r598:x->d1256:x))
  pub d302: std::core::fmt::format_spec -> std::core::fmt::format_kind = <missing>
  pub d303: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref 'a std::core::fmt::format_kind = <missing>
  pub d304: std::core::fmt::format_spec -> std::data::opt::opt std::core::fmt::format_align = <missing>
  pub d305: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref('a, std::data::opt::opt std::core::fmt::format_align) = <missing>
  pub d306: std::core::fmt::format_spec -> std::data::opt::opt std::core::fmt::format_sign = <missing>
  pub d307: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref('a, std::data::opt::opt std::core::fmt::format_sign) = <missing>
  pub d308: std::core::fmt::format_spec -> std::data::opt::opt std::text::str::str = <missing>
  pub d309: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref('a, std::data::opt::opt std::text::str::str) = <missing>
  pub d310: std::core::fmt::format_spec -> std::data::opt::opt int = <missing>
  pub d311: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref('a, std::data::opt::opt int) = <missing>
  pub d312: std::core::fmt::format_spec -> std::data::opt::opt int = <missing>
  pub d313: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref('a, std::data::opt::opt int) = <missing>
  pub d314: std::core::fmt::format_spec -> bool = <missing>
  pub d315: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref 'a bool = <missing>
  pub d316: std::core::fmt::format_spec -> bool = <missing>
  pub d317: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref 'a bool = <missing>
  pub d538:"std.io.console.out.write": std::text::str::str -> [std::io::console::out] () = <missing>
  pub d543:"std.io.console.err.write": std::text::str::str -> [std::io::console::err] () = <missing>
  pub d549:"std.io.console.warn.warn": std::text::str::str -> [std::io::console::warn] () = <missing>
  pub d551:"std.io.console.die.die": std::text::str::str -> [std::io::console::die] never = <missing>
  pub d560: std::io::file::file_meta -> std::io::file::file_kind = <missing>
  pub d561: std::control::var::ref 'a std::io::file::file_meta -> std::control::var::ref 'a std::io::file::file_kind = <missing>
  pub d562: std::io::file::file_meta -> int = <missing>
  pub d563: std::control::var::ref 'a std::io::file::file_meta -> std::control::var::ref 'a int = <missing>
  pub d564: std::io::file::file_meta -> bool = <missing>
  pub d565: std::control::var::ref 'a std::io::file::file_meta -> std::control::var::ref 'a bool = <missing>
  pub d566: std::io::file::file_meta -> std::data::opt::opt std::time::instant = <missing>
  pub d567: std::control::var::ref 'a std::io::file::file_meta -> std::control::var::ref('a, std::data::opt::opt std::time::instant) = <missing>
  pub d569:"std.io.file.file.load": std::text::path::path -> [std::io::file::file] std::data::result::result std::text::str::str std::io::file::io_err = <missing>
  pub d570:"std.io.file.file.store": (std::text::path::path, std::text::str::str) -> [std::io::file::file] std::data::result::result () std::io::file::io_err = <missing>
  pub d571:"std.io.file.file.meta": std::text::path::path -> [std::io::file::file] std::io::file::file_meta = <missing>
  pub d572:"std.io.file.file.ambient_touch": std::text::path::path -> [std::io::file::file] std::data::result::result () std::io::file::io_err = <missing>
  pub d573:"std.io.file.file.ambient_get": std::text::path::path -> [std::io::file::file] std::text::str::str = <missing>
  pub d574:"std.io.file.file.ambient_set": (std::text::path::path, std::text::str::str) -> [std::io::file::file] () = <missing>
  pub d575:"std.io.file.file.read_at": (std::text::path::path, std::data::range::range) -> [std::io::file::file] std::data::result::result (std::text::str::str, std::data::range::range) std::io::file::io_err = <missing>
  pub d576:"std.io.file.file.write_at": (std::text::path::path, std::data::range::range, std::text::str::str) -> [std::io::file::file] std::data::result::result () std::io::file::io_err = <missing>
  my d579: std::text::path::path -> [std::io::file::io_err] never = <missing>
  my d581: std::text::path::path -> [std::io::file::io_err] never = <missing>
  my d583: std::text::path::path -> [std::io::file::io_err] never = <missing>
  my d585: (std::text::path::path, std::text::str::str) -> [std::io::file::io_err] never = <missing>
  pub d586:"std.io.file.io_err.wrap": 'a [std::io::file::io_err; 'b] -> ['b] std::data::result::result('a, 'c | std::io::file::io_err) = e3452:(fn p849:d1572:action -> e3451:catch e3425:r1386:action->d1572:action { std::io::file::io_err::not_found p850:d1573:__error_payload_0_0, p851:_ -> e3430:(e3426:r1387:"std::data::result::result::err"->d530:"std.data.result.result.err" e3429:(e3427:r1388:not_found->d578:"std.io.file.io_err.not_found" e3428:r1389:__error_payload_0_0->d1573:__error_payload_0_0)); std::io::file::io_err::denied p852:d1574:__error_payload_1_0, p853:_ -> e3435:(e3431:r1390:"std::data::result::result::err"->d530:"std.data.result.result.err" e3434:(e3432:r1391:denied->d580:"std.io.file.io_err.denied" e3433:r1392:__error_payload_1_0->d1574:__error_payload_1_0)); std::io::file::io_err::invalid_path p854:d1575:__error_payload_2_0, p855:_ -> e3440:(e3436:r1393:"std::data::result::result::err"->d530:"std.data.result.result.err" e3439:(e3437:r1394:invalid_path->d582:"std.io.file.io_err.invalid_path" e3438:r1395:__error_payload_2_0->d1575:__error_payload_2_0)); std::io::file::io_err::failed p858:(p856:d1576:__error_payload_3_0, p857:d1577:__error_payload_3_1), p859:_ -> e3447:(e3441:r1396:"std::data::result::result::err"->d530:"std.data.result.result.err" e3446:(e3444:(e3442:r1397:failed->d584:"std.io.file.io_err.failed" e3443:r1398:__error_payload_3_0->d1576:__error_payload_3_0) e3445:r1399:__error_payload_3_1->d1577:__error_payload_3_1)); p860:d1578:value -> e3450:(e3448:r1400:"std::data::result::result::ok"->d529:"std.data.result.result.ok" e3449:r1401:value->d1578:value) })
  pub d599: std::io::net::request -> std::io::net::request_meta = <missing>
  pub d600: std::control::var::ref 'a std::io::net::request -> std::control::var::ref 'a std::io::net::request_meta = <missing>
  pub d601: std::io::net::request -> std::text::bytes::bytes = <missing>
  pub d602: std::control::var::ref 'a std::io::net::request -> std::control::var::ref 'a std::text::bytes::bytes = <missing>
  pub d603: std::io::net::request -> std::io::net::respond_slot = <missing>
  pub d604: std::control::var::ref 'a std::io::net::request -> std::control::var::ref 'a std::io::net::respond_slot = <missing>
  my d607: std::text::str::str -> [std::io::net::net_err] never = <missing>
  my d609: std::text::str::str -> [std::io::net::net_err] never = <missing>
  my d611: std::text::str::str -> [std::io::net::net_err] never = <missing>
  my d613: () -> [std::io::net::net_err] never = <missing>
  my d615: () -> [std::io::net::net_err] never = <missing>
  my d617: std::text::str::str -> [std::io::net::net_err] never = <missing>
  pub d618:"std.io.net.net_err.wrap": 'a [std::io::net::net_err; 'b] -> ['b] std::data::result::result('a, 'c | std::io::net::net_err) = e3649:(fn p916:d1614:action -> e3648:catch e3618:r1488:action->d1614:action { std::io::net::net_err::unreachable p917:d1615:__error_payload_0_0, p918:_ -> e3623:(e3619:r1489:"std::data::result::result::err"->d530:"std.data.result.result.err" e3622:(e3620:r1490:unreachable->d606:"std.io.net.net_err.unreachable" e3621:r1491:__error_payload_0_0->d1615:__error_payload_0_0)); std::io::net::net_err::refused p919:d1616:__error_payload_1_0, p920:_ -> e3628:(e3624:r1492:"std::data::result::result::err"->d530:"std.data.result.result.err" e3627:(e3625:r1493:refused->d608:"std.io.net.net_err.refused" e3626:r1494:__error_payload_1_0->d1616:__error_payload_1_0)); std::io::net::net_err::already_bound p921:d1617:__error_payload_2_0, p922:_ -> e3633:(e3629:r1495:"std::data::result::result::err"->d530:"std.data.result.result.err" e3632:(e3630:r1496:already_bound->d610:"std.io.net.net_err.already_bound" e3631:r1497:__error_payload_2_0->d1617:__error_payload_2_0)); std::io::net::net_err::closed p923:_, p924:_ -> e3636:(e3634:r1498:"std::data::result::result::err"->d530:"std.data.result.result.err" e3635:r1499:closed->d612:"std.io.net.net_err.closed"); std::io::net::net_err::timeout p925:_, p926:_ -> e3639:(e3637:r1500:"std::data::result::result::err"->d530:"std.data.result.result.err" e3638:r1501:timeout->d614:"std.io.net.net_err.timeout"); std::io::net::net_err::failed p927:d1618:__error_payload_5_0, p928:_ -> e3644:(e3640:r1502:"std::data::result::result::err"->d530:"std.data.result.result.err" e3643:(e3641:r1503:failed->d616:"std.io.net.net_err.failed" e3642:r1504:__error_payload_5_0->d1618:__error_payload_5_0)); p929:d1619:value -> e3647:(e3645:r1505:"std::data::result::result::ok"->d529:"std.data.result.result.ok" e3646:r1506:value->d1619:value) })
  pub d620:"std.io.net.net.listen": int -> [std::io::net::net] std::data::result::result std::io::net::listener std::io::net::net_err = <missing>
  pub d621:"std.io.net.net.port": std::io::net::listener -> [std::io::net::net] int = <missing>
  pub d623:"std.io.net.server.accept": std::io::net::listener -> [std::io::net::server] std::io::net::request = <missing>
  pub d624:"std.io.net.server.respond": (std::io::net::respond_slot, std::text::bytes::bytes) -> [std::io::net::server] std::data::result::result () std::io::net::net_err = <missing>
  pub d634: std::num::frac::frac -> int = <missing>
  pub d635: std::control::var::ref 'a std::num::frac::frac -> std::control::var::ref 'a int = <missing>
  pub d636: std::num::frac::frac -> int = <missing>
  pub d637: std::control::var::ref 'a std::num::frac::frac -> std::control::var::ref 'a int = <missing>
  pub d682: std::text::config::section -> std::text::str::str = <missing>
  pub d683: std::control::var::ref 'a std::text::config::section -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d684: std::text::config::section -> std::data::list::list (std::text::str::str, std::text::str::str) = <missing>
  pub d685: std::control::var::ref 'a std::text::config::section -> std::control::var::ref('a, std::data::list::list (std::text::str::str, std::text::str::str)) = <missing>
  pub d687: std::text::config::config -> std::data::list::list std::text::config::section = <missing>
  pub d688: std::control::var::ref 'a std::text::config::config -> std::control::var::ref('a, std::data::list::list std::text::config::section) = <missing>
  pub d709:"std.text.parse.parse.item": () -> [std::text::parse::parse 'a 'b 'c 'd] 'a = <missing>
  pub d710:"std.text.parse.parse.fail": 'a -> [std::text::parse::parse 'b 'a 'c 'd] never = <missing>
  pub d711:"std.text.parse.parse.eof": () -> [std::text::parse::parse 'a 'b 'c 'd] bool = <missing>
  pub d712:"std.text.parse.parse.pos": () -> [std::text::parse::parse 'a 'b 'c 'd] 'c = <missing>
  pub d713:"std.text.parse.parse.cut": () -> [std::text::parse::parse 'a 'b 'c 'd] () = <missing>
  pub d714:"std.text.parse.parse.snapshot": () -> [std::text::parse::parse 'a 'b 'c 'd] 'd = <missing>
  pub d715:"std.text.parse.parse.restore": 'a -> [std::text::parse::parse 'b 'c 'd 'a] () = <missing>
  pub d716:"std.text.parse.parse.advance": int -> [std::text::parse::parse 'a 'b 'c 'd] () = <missing>
  pub d723: std::text::parse::str_error -> int = <missing>
  pub d724: std::control::var::ref 'a std::text::parse::str_error -> std::control::var::ref 'a int = <missing>
  pub d725: std::text::parse::str_error -> int = <missing>
  pub d726: std::control::var::ref 'a std::text::parse::str_error -> std::control::var::ref 'a int = <missing>
  pub d727: std::text::parse::str_error -> std::data::opt::opt std::text::char::char = <missing>
  pub d728: std::control::var::ref 'a std::text::parse::str_error -> std::control::var::ref('a, std::data::opt::opt std::text::char::char) = <missing>
  pub d729: std::text::parse::str_error -> std::data::list::list std::text::str::str = <missing>
  pub d730: std::control::var::ref 'a std::text::parse::str_error -> std::control::var::ref('a, std::data::list::list std::text::str::str) = <missing>
  pub d731: std::text::parse::str_error -> std::data::list::list std::text::str::str = <missing>
  pub d732: std::control::var::ref 'a std::text::parse::str_error -> std::control::var::ref('a, std::data::list::list std::text::str::str) = <missing>
  pub d740: std::text::parse::prefix_result 'a -> 'a = <missing>
  pub d741: std::control::var::ref('a, std::text::parse::prefix_result 'b) -> std::control::var::ref 'a 'b = <missing>
  pub d742: std::text::parse::prefix_result 'a -> std::text::str::str = <missing>
  pub d743: std::control::var::ref('a, std::text::parse::prefix_result 'b) -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d745: std::text::parse::match_result 'a -> 'a = <missing>
  pub d746: std::control::var::ref('a, std::text::parse::match_result 'b) -> std::control::var::ref 'a 'b = <missing>
  pub d747: std::text::parse::match_result 'a -> int = <missing>
  pub d748: std::control::var::ref('a, std::text::parse::match_result 'b) -> std::control::var::ref 'a int = <missing>
  pub d749: std::text::parse::match_result 'a -> int = <missing>
  pub d750: std::control::var::ref('a, std::text::parse::match_result 'b) -> std::control::var::ref 'a int = <missing>
  pub d751: std::text::parse::match_result 'a -> std::text::str::str = <missing>
  pub d752: std::control::var::ref('a, std::text::parse::match_result 'b) -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d796: std::text::str::lines -> std::text::str::str = <missing>
  pub d797: std::control::var::ref 'a std::text::str::lines -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d800: std::text::str::ref_lines 'a -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d801: std::control::var::ref('a, std::text::str::ref_lines 'b) -> std::control::var::ref('a, std::control::var::ref 'b std::text::str::str) = <missing>
  pub d896: std::text::yumark::yumark_algebra 'a -> () -> 'a = <missing>
  pub d897: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, () ['[]] -> ['[]] 'b) = <missing>
  pub d898: std::text::yumark::yumark_algebra 'a -> 'a -> 'a -> 'a = <missing>
  pub d899: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b ['[]] -> ['[]] 'b) = <missing>
  pub d900: std::text::yumark::yumark_algebra 'a -> std::text::str::str -> 'a = <missing>
  pub d901: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, std::text::str::str ['[]] -> ['[]] 'b) = <missing>
  pub d902: std::text::yumark::yumark_algebra 'a -> 'a -> 'a = <missing>
  pub d903: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  pub d904: std::text::yumark::yumark_algebra 'a -> std::text::str::str -> int -> 'a -> 'a = <missing>
  pub d905: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, std::text::str::str ['[]] -> ['[]] int ['[]] -> ['[]] 'b ['[]] -> ['[]] 'b) = <missing>
  pub d906: std::text::yumark::yumark_algebra 'a -> std::text::str::str -> 'a = <missing>
  pub d907: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, std::text::str::str ['[]] -> ['[]] 'b) = <missing>
  pub d908: std::text::yumark::yumark_algebra 'a -> std::text::str::str -> 'a -> 'a = <missing>
  pub d909: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, std::text::str::str ['[]] -> ['[]] 'b ['[]] -> ['[]] 'b) = <missing>
  pub d910: std::text::yumark::yumark_algebra 'a -> bool -> 'a -> 'a = <missing>
  pub d911: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, bool ['[]] -> ['[]] 'b ['[]] -> ['[]] 'b) = <missing>
  pub d912: std::text::yumark::yumark_algebra 'a -> std::text::str::str -> 'a -> 'a = <missing>
  pub d913: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, std::text::str::str ['[]] -> ['[]] 'b ['[]] -> ['[]] 'b) = <missing>
  pub d914: std::text::yumark::yumark_algebra 'a -> 'a -> 'a = <missing>
  pub d915: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  pub d916: std::text::yumark::yumark_algebra 'a -> std::text::str::str -> std::text::str::str -> 'a = <missing>
  pub d917: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, std::text::str::str ['[]] -> ['[]] std::text::str::str ['[]] -> ['[]] 'b) = <missing>
  pub d918: std::text::yumark::yumark_algebra 'a -> 'a -> 'a = <missing>
  pub d919: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  pub d920: std::text::yumark::yumark_algebra 'a -> 'a -> 'a = <missing>
  pub d921: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  pub d922: std::text::yumark::yumark_algebra 'a -> 'a -> 'a = <missing>
  pub d923: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  pub d925: std::text::yumark::html_format -> std::text::str::str = <missing>
  pub d926: std::control::var::ref 'a std::text::yumark::html_format -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d928: std::text::yumark::markdown_format -> std::text::str::str = <missing>
  pub d929: std::control::var::ref 'a std::text::yumark::markdown_format -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d931: std::text::yumark::html_node -> std::text::str::str = <missing>
  pub d932: std::control::var::ref 'a std::text::yumark::html_node -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d933: std::text::yumark::html_node -> std::text::str::str = <missing>
  pub d934: std::control::var::ref 'a std::text::yumark::html_node -> std::control::var::ref 'a std::text::str::str = <missing>
  d995:"std.control.flow.loop.next.break": () -> [std::control::flow::loop::next] never = <missing>
  d999:"std.control.flow.label_loop.redo.break": () -> [std::control::flow::label_loop::redo] never = <missing>
  d1003:"std.control.flow.loop.redo.break": () -> [std::control::flow::loop::redo] never = <missing>
  d1007:"std.control.flow.label_loop.next.break": () -> [std::control::flow::label_loop::next] never = <missing>
  d1010:x arg
  d1011:f arg
  d1012:g arg
  d1013:x arg
  d1014:x arg
  d1015:y arg
  d1016:x arg
  d1017:y arg
  d1018:x arg
  d1019:y arg
  d1020:x arg
  d1021:y arg
  d1022:x arg
  d1023:x arg
  d1024:x arg
  d1025:y arg
  d1026:x arg
  d1027:y arg
  d1028:x arg
  d1029:y arg
  d1030:x arg
  d1031:y arg
  d1032:x arg
  d1033:y arg
  d1034:x arg
  d1035:y arg
  d1036:x arg
  d1037:y arg
  d1038:x arg
  d1039:y arg
  d1040:x arg
  d1041:y arg
  d1042:xs arg
  d1043:ys arg
  d1044:left arg
  d1045:right arg
  d1046:expected arg
  d1047:actual arg
  d1048:value arg
  d1049:t arg
  d1050:delta arg
  d1051:t arg
  d1052:delta arg
  d1053:later arg
  d1054:earlier arg
  d1055:x arg
  d1056:y arg
  d1057:x arg
  d1058:y arg
  d1059:count arg
  d1060:count arg
  d1061:count arg
  d1062:count arg
  d1063:count arg
  d1064:count arg
  d1065:count arg
  d1066:x arg
  d1067:y arg
  my d1068:q: 'a = e276:(e275:(e273:r98:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e272:r97:x->d1066:x) e274:r99:y->d1067:y)
  my d1069:r: 'a = e281:(e280:(e278:r101:"#op:infix:mod"->d418:"std.core.ops.#op:infix:mod" e277:r100:x->d1066:x) e279:r102:y->d1067:y)
  d1070:x arg
  d1071:y arg
  d1072:days_since_epoch arg
  my d1073:z: 'a = e319:(e318:(e316:r117:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e315:r116:days_since_epoch->d1072:days_since_epoch) e317:719468)
  my d1074:era: 'a = e324:(e322:(e320:r118:floor_div->d137:"std.time.floor_div" e321:r119:z->d1073:z) e323:146097)
  my d1075:doe: 'a = e333:(e332:(e326:r121:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e325:r120:z->d1073:z) e331:(e330:(e328:r123:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e327:r122:era->d1074:era) e329:146097))
  my d1076:yoe: 'a = e362:(e361:(e359:r134:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e358:(e357:(e351:r131:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e350:(e349:(e343:r128:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e342:(e341:(e335:r125:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e334:r124:doe->d1075:doe) e340:(e339:(e337:r127:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e336:r126:doe->d1075:doe) e338:1460))) e348:(e347:(e345:r130:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e344:r129:doe->d1075:doe) e346:36524))) e356:(e355:(e353:r133:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e352:r132:doe->d1075:doe) e354:146096))) e360:365)
  my d1077:year: 'a = e371:(e370:(e364:r136:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e363:r135:yoe->d1076:yoe) e369:(e368:(e366:r138:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e365:r137:era->d1074:era) e367:400))
  my d1078:doy: 'a = e396:(e395:(e373:r140:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e372:r139:doe->d1075:doe) e394:(e393:(e387:r146:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e386:(e385:(e379:r143:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e378:(e377:(e375:r141:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e374:365) e376:r142:yoe->d1076:yoe)) e384:(e383:(e381:r145:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e380:r144:yoe->d1076:yoe) e382:4))) e392:(e391:(e389:r148:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e388:r147:yoe->d1076:yoe) e390:100)))
  my d1079:mp: 'a = e409:(e408:(e406:r152:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e405:(e404:(e402:r151:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e401:(e400:(e398:r149:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e397:5) e399:r150:doy->d1078:doy)) e403:2)) e407:153)
  my d1080:day: 'a = e430:(e429:(e427:r159:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e426:(e425:(e411:r154:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e410:r153:doy->d1078:doy) e424:(e423:(e421:r158:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e420:(e419:(e417:r157:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e416:(e415:(e413:r155:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e412:153) e414:r156:mp->d1079:mp)) e418:2)) e422:5))) e428:1)
  my d1081:month: 'a = e446:(e445:(e432:r161:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e431:r160:mp->d1079:mp) e444:case e439:(e438:r164:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e437:(e436:(e434:r163:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e433:r162:mp->d1079:mp) e435:10)) { p74:true -> e440:3; p75:false -> e443:(e441:r165:"#op:prefix:-"->d412:"std.core.ops.#op:prefix:-" e442:9) })
  d1082:n arg
  d1083:n arg
  d1084:n arg
  d1085:n arg
  d1086:text arg
  my d1087:len: 'a = e610:(e608:r228:"std::text::str::len"->d786:"std.text.str.len" e609:r229:text->d1086:text)
  my d1088:end: 'a = e623:(e622:(e620:r235:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e619:r234:len->d1087:len) e621:1)
  d1089:nanos_in_second arg
  d1090:x arg
  my d1091:seconds: 'a = e676:(e674:(e671:r254:floor_div->d137:"std.time.floor_div" e673:(e672:r255:x->d1090:x.s12.epoch_nanos->d118)) e675:1000000000)
  my d1092:nanos_in_second: 'a = e682:(e680:(e677:r256:floor_mod->d138:"std.time.floor_mod" e679:(e678:r257:x->d1090:x.s13.epoch_nanos->d118)) e681:1000000000)
  my d1093:days: 'a = e687:(e685:(e683:r258:floor_div->d137:"std.time.floor_div" e684:r259:seconds->d1091:seconds) e686:86400)
  my d1094:second_of_day: 'a = e692:(e690:(e688:r260:floor_mod->d138:"std.time.floor_mod" e689:r261:seconds->d1091:seconds) e691:86400)
  d1095:year arg
  d1096:month arg
  d1097:day arg
  my d1098:hour: 'a = e700:(e699:(e697:r265:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e696:r264:second_of_day->d1094:second_of_day) e698:3600)
  my d1099:minute: 'a = e709:(e708:(e706:r268:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e705:(e704:(e702:r267:"#op:infix:mod"->d418:"std.core.ops.#op:infix:mod" e701:r266:second_of_day->d1094:second_of_day) e703:3600)) e707:60)
  my d1100:second: 'a = e714:(e713:(e711:r270:"#op:infix:mod"->d418:"std.core.ops.#op:infix:mod" e710:r269:second_of_day->d1094:second_of_day) e712:60)
  my d1101:date: 'a = e737:(e736:(e732:r278:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e731:(e730:(e728:r277:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e727:(e726:(e722:r274:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e721:(e720:(e718:r273:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e717:(e715:r271:pad4->d142:"std.time.pad4" e716:r272:year->d1095:year)) e719:"-")) e725:(e723:r275:pad2->d140:"std.time.pad2" e724:r276:month->d1096:month))) e729:"-")) e735:(e733:r279:pad2->d140:"std.time.pad2" e734:r280:day->d1097:day))
  my d1102:clock: 'a = e760:(e759:(e755:r288:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e754:(e753:(e751:r287:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e750:(e749:(e745:r284:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e744:(e743:(e741:r283:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e740:(e738:r281:pad2->d140:"std.time.pad2" e739:r282:hour->d1098:hour)) e742:":")) e748:(e746:r285:pad2->d140:"std.time.pad2" e747:r286:minute->d1099:minute))) e752:":")) e758:(e756:r289:pad2->d140:"std.time.pad2" e757:r290:second->d1100:second))
  d1103:x arg
  d1104:y arg
  d1105:x arg
  d1106:y arg
  d1107:x arg
  d1108:y arg
  d1109:x arg
  d1110:y arg
  d1111:x arg
  d1112:y arg
  d1113:x arg
  d1114:y arg
  d1115:x arg
  d1116:y arg
  d1117:x arg
  d1118:y arg
  d1119:x arg
  d1120:y arg
  d1121:x arg
  d1122:y arg
  d1123:x arg
  d1124:x arg
  d1125:x arg
  d1126:x arg
  d1127:y arg
  d1128:x arg
  d1129:y arg
  d1130:x arg
  d1131:a arg
  d1132:a arg
  d1133:x arg
  d1134:a arg
  d1135:a arg
  d1136:a arg
  d1137:x arg
  d1138:x arg
  d1139:x arg
  d1140:x arg
  d1141:x arg
  d1142:x arg
  d1143:xs arg
  d1144:f arg
  d1145:x arg
  my d1146:loop: any -> ['a] () = e1009:(fn p184:d1147:b -> e1008:case e978:(e977:r363:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e976:r362:b->d1147:b) { p197:true -> e1006:block { e1004:(e979:r364:loop->d1146:loop e1003:(e980:r365:"redo::judge"->d1004:"std.control.flow.loop.redo.judge" e1002:catch e983:(e981:r366:f->d1144:f e982:r367:x->d1145:x) { std::control::flow::loop::last p185:_, p186:_ -> e986:(e984:r368:"last::break"->d186:"std.control.flow.loop.last.break" e985:()); std::control::flow::loop::next p187:_, p188:_ -> e989:(e987:r369:"next::break"->d995:"std.control.flow.loop.next.break" e988:()); std::control::flow::loop::redo p189:_, p190:_ -> e992:(e990:r370:"redo::break"->d1003:"std.control.flow.loop.redo.break" e991:()); std::control::flow::loop::last p191:_, p192:_ -> e995:(e993:r371:"last::break"->d186:"std.control.flow.loop.last.break" e994:()); std::control::flow::loop::next p193:_, p194:_ -> e998:(e996:r372:"next::break"->d995:"std.control.flow.loop.next.break" e997:()); std::control::flow::loop::redo p195:_, p196:_ -> e1001:(e999:r373:"redo::break"->d1003:"std.control.flow.loop.redo.break" e1000:()) })); e1005:() }; p198:false -> e1007:() })
  d1147:b arg
  d1148:x arg
  d1149:x arg
  d1150:x arg
  d1151:x arg
  d1152:x arg
  d1153:x arg
  d1154:xs arg
  d1155:f arg
  d1156:x arg
  my d1157:loop: any -> ['a] () = e1100:(fn p228:d1158:b -> e1099:case e1067:(e1066:r389:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1065:r388:b->d1158:b) { p241:true -> e1097:block { e1095:(e1068:r390:loop->d1157:loop e1094:(e1069:r391:"redo::judge"->d1000:"std.control.flow.label_loop.redo.judge" e1093:catch e1074:(e1072:(e1070:r392:f->d1155:f e1071:r393:control_label->d209:"std.control.flow.label_loop.control_label") e1073:r394:x->d1156:x) { std::control::flow::label_loop::last p229:_, p230:_ -> e1077:(e1075:r395:"last::break"->d206:"std.control.flow.label_loop.last.break" e1076:()); std::control::flow::label_loop::next p231:_, p232:_ -> e1080:(e1078:r396:"next::break"->d1007:"std.control.flow.label_loop.next.break" e1079:()); std::control::flow::label_loop::redo p233:_, p234:_ -> e1083:(e1081:r397:"redo::break"->d999:"std.control.flow.label_loop.redo.break" e1082:()); std::control::flow::loop::last p235:_, p236:_ -> e1086:(e1084:r398:"last::break"->d206:"std.control.flow.label_loop.last.break" e1085:()); std::control::flow::loop::next p237:_, p238:_ -> e1089:(e1087:r399:"next::break"->d1007:"std.control.flow.label_loop.next.break" e1088:()); std::control::flow::loop::redo p239:_, p240:_ -> e1092:(e1090:r400:"redo::break"->d999:"std.control.flow.label_loop.redo.break" e1091:()) })); e1096:() }; p242:false -> e1098:() })
  d1158:b arg
  d1159:xs arg
  d1160:x arg
  d1161:xs arg
  d1162:x arg
  d1163:x arg
  d1164:k arg
  d1165:k arg
  d1166:b arg
  d1167:xs arg
  d1168:xs arg
  d1169:b arg
  d1170:xs arg
  d1171:x arg
  d1172:x arg
  d1173:k arg
  d1174:v arg
  d1175:x arg
  my d1176:loop: any [std::control::nondet::nondet; 'a] -> any -> 'b -> ['a] 'b = e1306:(fn p282:d1177:x -> e1305:(fn p283:d1178:queue -> e1304:(fn p284:d1179:res -> e1303:catch e1247:r443:x->d1177:x { std::control::nondet::nondet::branch p285:_, p286:d1180:k -> e1262:(e1260:(e1252:(e1248:r444:loop->d1176:loop e1251:(e1249:r445:k->d1180:k e1250:true)) e1259:(e1255:(e1253:r446:"std::data::list::append"->d497:"std.data.list.append" e1254:r447:queue->d1178:queue) e1258:(e1257:builtin_op::list_singleton e1256:r448:k->d1180:k))) e1261:r449:res->d1179:res); std::control::nondet::nondet::reject p287:_, p288:_ -> e1276:case e1265:(e1263:r450:"std::data::list::uncons"->d492:"std.data.list.uncons" e1264:r451:queue->d1178:queue) { p289:r452:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil" -> e1266:r453:res->d1179:res; p293:r454:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just"(p292:(p290:d1181:k, p291:d1182:queue)) -> e1275:(e1273:(e1271:(e1267:r455:loop->d1176:loop e1270:(e1268:r456:k->d1181:k e1269:false)) e1272:r457:queue->d1182:queue) e1274:r458:res->d1179:res) }; p294:d1183:v -> e1302:case e1279:(e1277:r459:"std::data::list::uncons"->d492:"std.data.list.uncons" e1278:r460:queue->d1178:queue) { p295:r461:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil" -> e1286:(e1282:(e1280:r462:"std::data::list::append"->d497:"std.data.list.append" e1281:r463:res->d1179:res) e1285:(e1284:builtin_op::list_singleton e1283:r464:v->d1183:v)); p299:r465:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just"(p298:(p296:d1184:k, p297:d1185:queue)) -> e1301:(e1293:(e1291:(e1287:r466:loop->d1176:loop e1290:(e1288:r467:k->d1184:k e1289:false)) e1292:r468:queue->d1185:queue) e1300:(e1296:(e1294:r469:"std::data::list::append"->d497:"std.data.list.append" e1295:r470:res->d1179:res) e1299:(e1298:builtin_op::list_singleton e1297:r471:v->d1183:v))) } })))
  d1177:x arg
  d1178:queue arg
  d1179:res arg
  d1180:k arg
  d1181:k arg
  d1182:queue arg
  d1183:v arg
  d1184:k arg
  d1185:queue arg
  d1186:x arg
  my d1187:loop: any [std::control::nondet::nondet; 'a] -> any -> ['a] never = e1353:(fn p302:d1188:x -> e1352:(fn p303:d1189:queue -> e1351:catch e1322:r474:x->d1188:x { std::control::nondet::nondet::branch p304:_, p305:d1190:k -> e1335:(e1327:(e1323:r475:loop->d1187:loop e1326:(e1324:r476:k->d1190:k e1325:true)) e1334:(e1330:(e1328:r477:"std::data::list::append"->d497:"std.data.list.append" e1329:r478:queue->d1189:queue) e1333:(e1332:builtin_op::list_singleton e1331:r479:k->d1190:k))); std::control::nondet::nondet::reject p306:_, p307:_ -> e1347:case e1338:(e1336:r480:"std::data::list::uncons"->d492:"std.data.list.uncons" e1337:r481:queue->d1189:queue) { p308:r482:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil" -> e1339:r483:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil"; p312:r484:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just"(p311:(p309:d1191:k, p310:d1192:queue)) -> e1346:(e1344:(e1340:r485:loop->d1187:loop e1343:(e1341:r486:k->d1191:k e1342:false)) e1345:r487:queue->d1192:queue) }; p313:d1193:v -> e1350:(e1348:r488:"std::data::opt::opt::just"->d504:"std.data.opt.opt.just" e1349:r489:v->d1193:v) }))
  d1188:x arg
  d1189:queue arg
  d1190:k arg
  d1191:k arg
  d1192:queue arg
  d1193:v arg
  d1194:x arg
  d1195:x arg
  d1196:x arg
  d1197:f arg
  d1198:r arg
  d1199:f arg
  my d1200:loop: 'a [[['b & 'c] & 'd] & [std::control::var::ref_update('e | 'f | 'g | 'h | 'i <: 'e & 'f & 'g & 'i & 'h); [[['j & 'k] & 'l] & 'm] & 'n]] -> ['p#0[AllExcept([std::control::var::ref_update 'e])], 'k, 'j, 'n, 'o, 'm, 'l] 'a = e1391:(fn p321:d1201:x -> e1390:catch e1382:r500:x->d1201:x { std::control::var::ref_update::update p322:d1202:v, p323:d1203:k -> e1389:(e1383:r501:loop->d1200:loop e1388:(e1384:r502:k->d1203:k e1387:(e1385:r503:f->d1199:f e1386:r504:v->d1202:v))) })
  d1201:x arg
  d1202:v arg
  d1203:k arg
  d1204:v arg
  d1205:x arg
  d1206:k arg
  d1207:v arg
  d1208:k arg
  d1209:x arg
  d1210:y arg
  d1211:x arg
  d1212:y arg
  d1213:x arg
  d1214:y arg
  d1215:x arg
  d1216:y arg
  d1217:x arg
  d1218:y arg
  d1219:x arg
  d1220:y arg
  d1221:x arg
  d1222:y arg
  d1223:x arg
  d1224:y arg
  d1225:x arg
  d1226:y arg
  d1227:x arg
  d1228:y arg
  d1229:x arg
  d1230:y arg
  d1231:x arg
  d1232:y arg
  d1233:x arg
  d1234:y arg
  d1235:x arg
  d1236:y arg
  d1237:x arg
  d1238:y arg
  d1239:x arg
  d1240:y arg
  d1241:x arg
  d1242:y arg
  d1243:x arg
  d1244:y arg
  d1245:xs arg
  d1246:ys arg
  d1247:x arg
  d1248:y arg
  d1249:xl arg
  d1250:xr arg
  d1251:yl arg
  d1252:yr arg
  d1253:p arg
  d1254:x arg
  d1255:x arg
  d1256:x arg
  d1257:a arg
  d1258:a arg
  d1259:a arg
  d1260:text arg
  d1261:count arg
  d1262:spec arg
  d1263:fill arg
  d1264:spec arg
  d1265:body arg
  d1266:limit arg
  d1267:body arg
  d1268:spec arg
  d1269:head arg
  d1270:body arg
  d1271:spec arg
  d1272:head arg
  d1273:body arg
  my d1274:clipped: 'a = e1742:(e1740:(e1738:r657:format_body->d327:"std.core.fmt.format_body" e1739:r658:spec->d1271:spec) e1741:r659:body->d1273:body)
  my d1275:body_prefix: 'a = e1749:(e1747:(e1745:(e1743:r660:format_sign_prefix->d329:"std.core.fmt.format_sign_prefix" e1744:r661:spec->d1271:spec) e1746:r662:head->d1272:head) e1748:r663:clipped->d1274:clipped)
  d1276:width arg
  my d1277:clipped: 'a = e1761:(e1759:(e1757:r668:format_body->d327:"std.core.fmt.format_body" e1758:r669:spec->d1271:spec) e1760:r670:body->d1273:body)
  my d1278:body_prefix: 'a = e1768:(e1766:(e1764:(e1762:r671:format_sign_prefix->d329:"std.core.fmt.format_sign_prefix" e1763:r672:spec->d1271:spec) e1765:r673:head->d1272:head) e1767:r674:clipped->d1277:clipped)
  my d1279:text: 'a = e1773:(e1772:(e1770:r676:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1769:r675:body_prefix->d1278:body_prefix) e1771:r677:clipped->d1277:clipped)
  my d1280:missing: 'a = e1779:(e1778:(e1775:r679:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e1774:r678:width->d1276:width) e1777:(e1776:r680:text->d1279:text.s56.len->d838:"std.text.str.str.len"))
  my d1281:fill: 'a = e1790:(e1788:r685:format_fill->d326:"std.core.fmt.format_fill" e1789:r686:spec->d1271:spec)
  my d1282:left: 'a = e1806:(e1805:(e1803:r698:"#op:infix:div"->d417:"std.core.ops.#op:infix:div" e1802:r697:missing->d1280:missing) e1804:2)
  my d1283:right: 'a = e1811:(e1810:(e1808:r700:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e1807:r699:missing->d1280:missing) e1809:r701:left->d1282:left)
  my d1284:padding: 'a = e1839:(e1837:(e1835:r713:repeat->d325:"std.core.fmt.repeat" e1836:r714:fill->d1281:fill) e1838:r715:missing->d1280:missing)
  my d1285:padded_prefix: 'a = e1844:(e1843:(e1841:r717:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e1840:r716:body_prefix->d1278:body_prefix) e1842:r718:padding->d1284:padding)
  d1286:spec arg
  d1287:value arg
  d1288:spec arg
  d1289:value arg
  d1290:spec arg
  d1291:value arg
  my d1292:head: 'a | std::text::str::str = e1899:case e1896:(e1895:r734:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1894:(e1893:r733:spec->d1290:spec.s61.alternate->d314)) { p459:true -> e1897:"0x"; p460:false -> e1898:"" }
  d1293:spec arg
  d1294:value arg
  my d1295:head: 'a | std::text::str::str = e1917:case e1914:(e1913:r740:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e1912:(e1911:r739:spec->d1293:spec.s63.alternate->d314)) { p464:true -> e1915:"0X"; p465:false -> e1916:"" }
  d1296:x arg
  d1297:x arg
  d1298:x arg
  d1299:x arg
  d1300:x arg
  d1301:x arg
  d1302:x arg
  d1303:x arg
  d1304:x arg
  d1305:x arg
  d1306:x arg
  d1307:xs arg
  d1308:item arg
  d1309:left arg
  d1310:right arg
  my d1311:left_text: 'a | 'b | 'c = e1973:(e1971:r766:show_list_items->d357:"std.core.fmt.show_list_items" e1972:r767:left->d1309:left)
  my d1312:right_text: 'a | 'b | 'c = e1976:(e1974:r768:show_list_items->d357:"std.core.fmt.show_list_items" e1975:r769:right->d1310:right)
  d1313:xs arg
  d1314:value arg
  d1315:inner arg
  d1316:value arg
  d1317:inner arg
  d1318:inner arg
  d1319:value arg
  d1320:a arg
  d1321:b arg
  d1322:value arg
  d1323:a arg
  d1324:b arg
  d1325:c arg
  d1326:value arg
  d1327:a arg
  d1328:b arg
  d1329:c arg
  d1330:d arg
  d1331:value arg
  d1332:a arg
  d1333:b arg
  d1334:c arg
  d1335:d arg
  d1336:e arg
  d1337:x arg
  d1338:x arg
  d1339:x arg
  d1340:xs arg
  d1341:item arg
  d1342:left arg
  d1343:right arg
  my d1344:left_text: 'a | 'b | 'c = e2201:(e2199:r849:debug_list_items->d378:"std.core.fmt.debug_list_items" e2200:r850:left->d1342:left)
  my d1345:right_text: 'a | 'b | 'c = e2204:(e2202:r851:debug_list_items->d378:"std.core.fmt.debug_list_items" e2203:r852:right->d1343:right)
  d1346:xs arg
  d1347:value arg
  d1348:inner arg
  d1349:value arg
  d1350:inner arg
  d1351:inner arg
  d1352:value arg
  d1353:a arg
  d1354:b arg
  d1355:value arg
  d1356:a arg
  d1357:b arg
  d1358:c arg
  d1359:value arg
  d1360:a arg
  d1361:b arg
  d1362:c arg
  d1363:d arg
  d1364:value arg
  d1365:a arg
  d1366:b arg
  d1367:c arg
  d1368:d arg
  d1369:e arg
  d1370:e arg
  d1371:x arg
  d1372:x arg
  d1373:y arg
  d1374:x arg
  d1375:y arg
  d1376:x arg
  d1377:y arg
  d1378:x arg
  d1379:y arg
  d1380:x arg
  d1381:y arg
  d1382:x arg
  d1383:y arg
  d1384:x arg
  d1385:y arg
  d1386:x arg
  d1387:y arg
  d1388:x arg
  d1389:y arg
  d1390:x arg
  d1391:y arg
  d1392:a arg
  d1393:b arg
  d1394:a arg
  d1395:b arg
  d1396:label arg
  d1397:label arg
  d1398:label arg
  d1399:s arg
  d1400:xs arg
  d1401:s arg
  d1402:xs arg
  d1403:b arg
  d1404:x arg
  d1405:container arg
  d1406:f arg
  my d1407:nil: never = e2590:r990:"std::data::opt::opt::nil"->d503:"std.data.opt.opt.nil"
  d1408:x arg
  d1409:container arg
  d1410:target arg
  my d1411:found: 'a = e2622:(e2615:(e2614:r1000:container->d1409:container.s121.find=>d450:"std.data.fold.Fold.find") e2621:(fn p619:d1412:x -> e2620:(e2619:(e2617:r1002:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e2616:r1001:x->d1412:x) e2618:r1003:target->d1410:target)))
  d1412:x arg
  d1413:container arg
  d1414:xs arg
  d1415:ys arg
  d1416:xs arg
  d1417:f arg
  d1418:xs arg
  d1419:pred arg
  d1420:xs arg
  d1421:r arg
  d1422:ys arg
  d1423:xs arg
  d1424:separator arg
  d1425:xs arg
  d1426:xs arg
  d1427:xs arg
  d1428:xs arg
  d1429:xs arg
  d1430:"&xs" arg
  d1431:x arg
  d1432:xs arg
  d1433:i arg
  d1434:xs arg
  d1435:r arg
  d1436:r arg
  d1437:i arg
  my d1438:loop: 'a [std::control::var::ref_update 'b; 'c] -> [std::control::var::ref_update 'd, 'c] 'a = e2758:(fn p651:d1439:x -> e2757:catch e2729:r1048:x->d1439:x { std::control::var::ref_update::update p652:d1440:old, p653:d1441:k -> e2756:block { let my p654:d1442:new_item = e2736:(e2730:r1049:"ref_update::update"->d234:"std.control.var.ref_update.update" e2735:(e2733:(e2731:r1050:"std::data::list::index_raw"->d480:"std.data.list.index_raw" e2732:r1051:old->d1440:old) e2734:r1052:i->d1437:i)); e2755:(e2737:r1053:loop->d1438:loop e2754:(e2738:r1054:k->d1441:k e2753:(e2749:(e2743:(e2741:(e2739:r1055:"std::data::list::splice_raw"->d484:"std.data.list.splice_raw" e2740:r1056:old->d1440:old) e2742:r1057:i->d1437:i) e2748:(e2747:(e2745:r1059:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e2744:r1058:i->d1437:i) e2746:1)) e2752:(e2751:builtin_op::list_singleton e2750:r1060:new_item->d1442:new_item)))) } })
  d1439:x arg
  d1440:old arg
  d1441:k arg
  my d1442:new_item: 'a = e2736:(e2730:r1049:"ref_update::update"->d234:"std.control.var.ref_update.update" e2735:(e2733:(e2731:r1050:"std::data::list::index_raw"->d480:"std.data.list.index_raw" e2732:r1051:old->d1440:old) e2734:r1052:i->d1437:i))
  d1443:xs arg
  d1444:z arg
  d1445:f arg
  d1446:x arg
  d1447:left arg
  d1448:right arg
  d1449:xs arg
  d1450:z arg
  d1451:f arg
  d1452:x arg
  d1453:xs arg
  d1454:x arg
  d1455:xs arg
  d1456:xs arg
  my d1457:n: 'a = e2842:(e2840:r1091:"std::data::list::len"->d479:"std.data.list.len" e2841:r1092:xs->d1456:xs)
  d1458:xs arg
  d1459:z arg
  d1460:f arg
  d1461:xs arg
  d1462:x arg
  d1463:left arg
  d1464:right arg
  d1465:xs arg
  d1466:f arg
  d1467:x arg
  d1468:left arg
  d1469:right arg
  d1470:xs arg
  d1471:pred arg
  d1472:x arg
  d1473:left arg
  d1474:right arg
  d1475:xs arg
  d1476:ys arg
  d1477:xs arg
  d1478:head arg
  d1479:xs arg
  d1480:head arg
  d1481:tail arg
  d1482:xs arg
  d1483:x arg
  d1484:y arg
  d1485:y arg
  d1486:l arg
  d1487:r arg
  d1488:ll arg
  d1489:lr arg
  d1490:rl arg
  d1491:rr arg
  d1492:xs arg
  d1493:x arg
  d1494:xs arg
  d1495:l arg
  d1496:r arg
  d1497:start arg
  d1498:end arg
  d1499:start arg
  d1500:end arg
  d1501:start arg
  d1502:end arg
  d1503:start arg
  d1504:end arg
  d1505:start arg
  d1506:start arg
  d1507:end arg
  d1508:end arg
  d1509:r arg
  d1510:start arg
  d1511:r arg
  d1512:end arg
  d1513:b arg
  d1514:x arg
  d1515:x arg
  d1516:b arg
  d1517:x arg
  d1518:x arg
  d1519:f arg
  d1520:i arg
  d1521:end arg
  d1522:acc arg
  d1523:f arg
  d1524:i arg
  d1525:acc arg
  d1526:r arg
  d1527:z arg
  d1528:f arg
  d1529:start arg
  d1530:start arg
  d1531:end arg
  d1532:r arg
  d1533:f arg
  d1534:r arg
  d1535:f arg
  d1536:r arg
  d1537:fallback arg
  d1538:r arg
  d1539:f arg
  d1540:value arg
  d1541:err arg
  d1542:r arg
  d1543:f arg
  d1544:value arg
  d1545:err arg
  d1546:r arg
  d1547:fallback arg
  d1548:value arg
  d1549:value arg
  d1550:value arg
  d1551:value arg
  d1552:value arg
  d1553:value arg
  d1554:value arg
  d1555:value arg
  my d1556 mod {
    d1557:"io_err::throw#error": std::io::file::io_err -> [std::io::file::io_err] never = e3384:(fn p829:d1558:error -> e3383:case e3368:r1355:error->d1558:error { p831:r1356:not_found->d578:"std.io.file.io_err.not_found"(p830:d1559:__error_payload_0_0) -> e3371:(e3369:r1357:"std::io::file::io_err::not_found"->d579 e3370:r1358:__error_payload_0_0->d1559:__error_payload_0_0); p833:r1359:denied->d580:"std.io.file.io_err.denied"(p832:d1560:__error_payload_1_0) -> e3374:(e3372:r1360:"std::io::file::io_err::denied"->d581 e3373:r1361:__error_payload_1_0->d1560:__error_payload_1_0); p835:r1362:invalid_path->d582:"std.io.file.io_err.invalid_path"(p834:d1561:__error_payload_2_0) -> e3377:(e3375:r1363:"std::io::file::io_err::invalid_path"->d583 e3376:r1364:__error_payload_2_0->d1561:__error_payload_2_0); p838:r1365:failed->d584:"std.io.file.io_err.failed"(p836:d1562:__error_payload_3_0, p837:d1563:__error_payload_3_1) -> e3382:(e3378:r1366:"std::io::file::io_err::failed"->d585 e3381:(e3379:r1367:__error_payload_3_0->d1562:__error_payload_3_0, e3380:r1368:__error_payload_3_1->d1563:__error_payload_3_1)) })
  }
  d1558:error arg
  d1559:__error_payload_0_0 arg
  d1560:__error_payload_1_0 arg
  d1561:__error_payload_2_0 arg
  d1562:__error_payload_3_0 arg
  d1563:__error_payload_3_1 arg
  my d1564 mod {
    d1565:"io_err::show#error": std::io::file::io_err -> std::text::str::str = e3424:(fn p839:d1566:__error_value -> e3423:case e3385:r1369:__error_value->d1566:__error_value { p841:r1370:not_found->d578:"std.io.file.io_err.not_found"(p840:d1567:__error_payload_0_0) -> e3391:(e3390:(e3387:r1371:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3386:"not_found: ") e3389:(e3388:r1372:__error_payload_0_0->d1567:__error_payload_0_0.s129.show=>d319:"std.core.fmt.Display.show")); p843:r1373:denied->d580:"std.io.file.io_err.denied"(p842:d1568:__error_payload_1_0) -> e3397:(e3396:(e3393:r1374:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3392:"denied: ") e3395:(e3394:r1375:__error_payload_1_0->d1568:__error_payload_1_0.s130.show=>d319:"std.core.fmt.Display.show")); p845:r1376:invalid_path->d582:"std.io.file.io_err.invalid_path"(p844:d1569:__error_payload_2_0) -> e3403:(e3402:(e3399:r1377:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3398:"invalid_path: ") e3401:(e3400:r1378:__error_payload_2_0->d1569:__error_payload_2_0.s131.show=>d319:"std.core.fmt.Display.show")); p848:r1379:failed->d584:"std.io.file.io_err.failed"(p846:d1570:__error_payload_3_0, p847:d1571:__error_payload_3_1) -> e3422:(e3421:(e3419:r1385:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3418:(e3417:(e3414:r1383:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3413:(e3412:(e3410:r1382:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3409:(e3408:(e3405:r1380:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3404:"failed(") e3407:(e3406:r1381:__error_payload_3_0->d1570:__error_payload_3_0.s132.show=>d319:"std.core.fmt.Display.show"))) e3411:", ")) e3416:(e3415:r1384:__error_payload_3_1->d1571:__error_payload_3_1.s133.show=>d319:"std.core.fmt.Display.show"))) e3420:")") })
  }
  d1566:__error_value arg
  d1567:__error_payload_0_0 arg
  d1568:__error_payload_1_0 arg
  d1569:__error_payload_2_0 arg
  d1570:__error_payload_3_0 arg
  d1571:__error_payload_3_1 arg
  d1572:action arg
  d1573:__error_payload_0_0 arg
  d1574:__error_payload_1_0 arg
  d1575:__error_payload_2_0 arg
  d1576:__error_payload_3_0 arg
  d1577:__error_payload_3_1 arg
  d1578:value arg
  d1579:result arg
  d1580:value arg
  d1581:err arg
  d1582:path arg
  d1583:path arg
  d1584:path arg
  d1585:path arg
  d1586:path arg
  d1587:r arg
  d1588:path arg
  d1589:r arg
  d1590:text arg
  d1591:path arg
  d1592:path arg
  d1593:text arg
  d1594:path arg
  d1595:path arg
  d1596:f arg
  my d1597:initial: 'a = e3551:(e3547:r1446:unwrap_io->d587:"std.io.file.unwrap_io" e3550:(e3548:r1447:"file::load"->d569:"std.io.file.file.load" e3549:r1448:path->d1595:path))
  d1598:result arg
  d1599:final arg
  my d1600 mod {
    d1601:"net_err::throw#error": std::io::net::net_err -> [std::io::net::net_err] never = e3588:(fn p894:d1602:error -> e3587:case e3568:r1456:error->d1602:error { p896:r1457:unreachable->d606:"std.io.net.net_err.unreachable"(p895:d1603:__error_payload_0_0) -> e3571:(e3569:r1458:"std::io::net::net_err::unreachable"->d607 e3570:r1459:__error_payload_0_0->d1603:__error_payload_0_0); p898:r1460:refused->d608:"std.io.net.net_err.refused"(p897:d1604:__error_payload_1_0) -> e3574:(e3572:r1461:"std::io::net::net_err::refused"->d609 e3573:r1462:__error_payload_1_0->d1604:__error_payload_1_0); p900:r1463:already_bound->d610:"std.io.net.net_err.already_bound"(p899:d1605:__error_payload_2_0) -> e3577:(e3575:r1464:"std::io::net::net_err::already_bound"->d611 e3576:r1465:__error_payload_2_0->d1605:__error_payload_2_0); p901:r1466:closed->d612:"std.io.net.net_err.closed" -> e3580:(e3578:r1467:"std::io::net::net_err::closed"->d613 e3579:()); p902:r1468:timeout->d614:"std.io.net.net_err.timeout" -> e3583:(e3581:r1469:"std::io::net::net_err::timeout"->d615 e3582:()); p904:r1470:failed->d616:"std.io.net.net_err.failed"(p903:d1606:__error_payload_5_0) -> e3586:(e3584:r1471:"std::io::net::net_err::failed"->d617 e3585:r1472:__error_payload_5_0->d1606:__error_payload_5_0) })
  }
  d1602:error arg
  d1603:__error_payload_0_0 arg
  d1604:__error_payload_1_0 arg
  d1605:__error_payload_2_0 arg
  d1606:__error_payload_5_0 arg
  my d1607 mod {
    d1608:"net_err::show#error": std::io::net::net_err -> std::text::str::str = e3617:(fn p905:d1609:__error_value -> e3616:case e3589:r1473:__error_value->d1609:__error_value { p907:r1474:unreachable->d606:"std.io.net.net_err.unreachable"(p906:d1610:__error_payload_0_0) -> e3595:(e3594:(e3591:r1475:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3590:"unreachable: ") e3593:(e3592:r1476:__error_payload_0_0->d1610:__error_payload_0_0.s138.show=>d319:"std.core.fmt.Display.show")); p909:r1477:refused->d608:"std.io.net.net_err.refused"(p908:d1611:__error_payload_1_0) -> e3601:(e3600:(e3597:r1478:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3596:"refused: ") e3599:(e3598:r1479:__error_payload_1_0->d1611:__error_payload_1_0.s139.show=>d319:"std.core.fmt.Display.show")); p911:r1480:already_bound->d610:"std.io.net.net_err.already_bound"(p910:d1612:__error_payload_2_0) -> e3607:(e3606:(e3603:r1481:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3602:"already_bound: ") e3605:(e3604:r1482:__error_payload_2_0->d1612:__error_payload_2_0.s140.show=>d319:"std.core.fmt.Display.show")); p912:r1483:closed->d612:"std.io.net.net_err.closed" -> e3608:"closed"; p913:r1484:timeout->d614:"std.io.net.net_err.timeout" -> e3609:"timeout"; p915:r1485:failed->d616:"std.io.net.net_err.failed"(p914:d1613:__error_payload_5_0) -> e3615:(e3614:(e3611:r1486:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e3610:"failed: ") e3613:(e3612:r1487:__error_payload_5_0->d1613:__error_payload_5_0.s141.show=>d319:"std.core.fmt.Display.show")) })
  }
  d1609:__error_value arg
  d1610:__error_payload_0_0 arg
  d1611:__error_payload_1_0 arg
  d1612:__error_payload_2_0 arg
  d1613:__error_payload_5_0 arg
  d1614:action arg
  d1615:__error_payload_0_0 arg
  d1616:__error_payload_1_0 arg
  d1617:__error_payload_2_0 arg
  d1618:__error_payload_5_0 arg
  d1619:value arg
  d1620:result arg
  d1621:value arg
  d1622:err arg
  d1623:port arg
  d1624:port arg
  my d1625:listener: 'a = e3664:(e3662:r1515:listen->d626:"std.io.net.listen" e3663:r1516:port->d1624:port)
  d1626:l arg
  d1627:l arg
  d1628:req arg
  d1629:res arg
  d1630:x arg
  d1631:a arg
  d1632:b arg
  d1633:a arg
  d1634:b arg
  d1635:n arg
  d1636:d arg
  my d1637:divisor: 'a = e3739:(e3737:(e3735:r1547:gcd->d640:"std.num.frac.gcd" e3736:r1548:n->d1635:n) e3738:r1549:d->d1636:d)
  my d1638:normalized_num: 'a = e3744:(e3742:(e3740:r1550:"std::int::div"->d53:"std.int.div" e3741:r1551:n->d1635:n) e3743:r1552:divisor->d1637:divisor)
  my d1639:normalized_den: 'a = e3749:(e3747:(e3745:r1553:"std::int::div"->d53:"std.int.div" e3746:r1554:d->d1636:d) e3748:r1555:divisor->d1637:divisor)
  d1640:x arg
  d1641:y arg
  d1642:x arg
  d1643:y arg
  d1644:x arg
  d1645:y arg
  d1646:x arg
  d1647:y arg
  d1648:x arg
  d1649:y arg
  d1650:x arg
  d1651:y arg
  d1652:x arg
  d1653:y arg
  d1654:x arg
  d1655:y arg
  d1656:x arg
  d1657:y arg
  d1658:x arg
  d1659:x arg
  d1660:b arg
  d1661:b arg
  d1662:b arg
  d1663:other arg
  d1664:b arg
  d1665:b arg
  d1666:b arg
  d1667:b arg
  d1668:text arg
  d1669:b arg
  d1670:i arg
  d1671:b arg
  d1672:r arg
  d1673:c arg
  d1674:c arg
  d1675:c arg
  d1676:c arg
  d1677:c arg
  d1678:section_name arg
  d1679:key arg
  d1680:c arg
  d1681:name arg
  d1682:c arg
  d1683:sections arg
  d1684:name arg
  d1685:head arg
  d1686:tail arg
  d1687:head arg
  d1688:tail arg
  d1689:c arg
  d1690:name arg
  d1691:sections arg
  d1692:section_name arg
  d1693:entry arg
  d1694:head arg
  d1695:tail arg
  d1696:head arg
  d1697:tail arg
  d1698:c arg
  d1699:section_name arg
  d1700:entry arg
  d1701:clean arg
  d1702:pair arg
  d1703:key arg
  d1704:value arg
  d1705:state arg
  d1706:line arg
  d1707:cfg arg
  d1708:current_section arg
  my d1709:clean = e4255:(e4254:r1744:line->d1706:line.s191.trim->d826:"std.text.str.str.trim")
  d1710:name arg
  d1711:pair arg
  d1712:source arg
  d1713:cfg arg
  d1714:entries arg
  d1715:key arg
  d1716:candidate arg
  d1717:value arg
  d1718:rest arg
  d1719:rest arg
  d1720:entries arg
  d1721:key arg
  d1722:sections arg
  d1723:section_name arg
  d1724:key arg
  d1725:head arg
  d1726:rest arg
  d1727:rest arg
  d1728:c arg
  d1729:section_name arg
  d1730:key arg
  d1731:path arg
  d1732:e arg
  d1733:f arg
  d1734:u arg
  d1735:l arg
  d1736:c arg
  d1737:label arg
  d1738:l arg
  d1739:c arg
  d1740:e arg
  d1741:label arg
  d1742:input arg
  d1743:count arg
  d1744:line arg
  d1745:column arg
  my d1746:data: 'a = e4515:(e4513:r1857:"std::text::str::to_bytes"->d794:"std.text.str.to_bytes" e4514:r1858:input->d1742:input)
  d1747:data arg
  d1748:count arg
  d1749:i arg
  d1750:line arg
  d1751:column arg
  my d1752:chunk_end: 'a | 'b | 'c | int = e4578:case e4571:(e4570:r1882:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4569:(e4568:(e4566:r1880:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e4565:(e4564:(e4562:r1879:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4561:r1878:i->d1749:i) e4563:1024)) e4567:r1881:count->d1748:count)) { p1126:true -> e4576:(e4575:(e4573:r1884:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4572:r1883:i->d1749:i) e4574:1024); p1127:false -> e4577:r1885:count->d1748:count }
  d1753:line arg
  d1754:column arg
  d1755:data arg
  d1756:count arg
  d1757:i arg
  d1758:line arg
  d1759:column arg
  d1760:input arg
  d1761:count arg
  d1762:i arg
  d1763:line arg
  d1764:column arg
  my d1765:chunk_end: 'a | 'b | 'c | int = e4696:case e4689:(e4688:r1932:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4687:(e4686:(e4684:r1930:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e4683:(e4682:(e4680:r1929:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4679:r1928:i->d1762:i) e4681:1024)) e4685:r1931:count->d1761:count)) { p1150:true -> e4694:(e4693:(e4691:r1934:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e4690:r1933:i->d1762:i) e4692:1024); p1151:false -> e4695:r1935:count->d1761:count }
  d1766:line arg
  d1767:column arg
  d1768:input arg
  d1769:count arg
  d1770:i arg
  d1771:line arg
  d1772:column arg
  my d1773:item: 'a = e4741:(e4739:(e4737:r1954:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e4738:r1955:input->d1768:input) e4740:r1956:i->d1770:i)
  d1774:input arg
  d1775:line arg
  d1776:column arg
  d1777:parser arg
  d1778:k arg
  d1779:k arg
  my d1780:item: 'a = e4820:(e4818:(e4816:r1984:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e4817:r1985:input->d1774:input) e4819:0)
  my d1781:rest: 'a = e4827:(e4823:(e4821:r1986:"std::text::str::index_range"->d790:"std.text.str.index_range" e4822:r1987:input->d1774:input) e4826:(e4824:r1988:"std::data::range::from_excluded"->d516:"std.data.range.from_excluded" e4825:0))
  d1782:e arg
  d1783:k arg
  d1784:k arg
  d1785:k arg
  d1786:k arg
  d1787:input arg
  d1788:line arg
  d1789:column arg
  d1790:k arg
  d1791:count arg
  d1792:k arg
  my d1793:input_len = e4932:(e4931:r2037:input->d1774:input.s223.len->d838:"std.text.str.str.len")
  my d1794:end: 'a | 'b | 'c | int = e4942:case e4939:(e4938:r2041:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e4937:(e4936:(e4934:r2039:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e4933:r2038:count->d1791:count) e4935:r2040:input_len->d1793:input_len)) { p1206:true -> e4940:r2042:count->d1791:count; p1207:false -> e4941:r2043:input_len->d1793:input_len }
  my d1795:rest: 'a = e4949:(e4947:(e4945:(e4943:r2044:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e4944:r2045:input->d1774:input) e4946:r2046:end->d1794:end) e4948:r2047:input_len->d1793:input_len)
  d1796:line arg
  d1797:column arg
  d1798:v arg
  d1799:input arg
  d1800:line arg
  d1801:column arg
  d1802:parser arg
  d1803:k arg
  d1804:k arg
  my d1805:item: 'a = e5009:(e5007:(e5005:r2069:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e5006:r2070:input->d1799:input) e5008:0)
  my d1806:rest: 'a = e5016:(e5012:(e5010:r2071:"std::text::str::index_range"->d790:"std.text.str.index_range" e5011:r2072:input->d1799:input) e5015:(e5013:r2073:"std::data::range::from_excluded"->d516:"std.data.range.from_excluded" e5014:0))
  d1807:e arg
  d1808:k arg
  d1809:k arg
  d1810:k arg
  d1811:k arg
  d1812:input arg
  d1813:line arg
  d1814:column arg
  d1815:k arg
  d1816:count arg
  d1817:k arg
  my d1818:input_len = e5121:(e5120:r2122:input->d1799:input.s227.len->d838:"std.text.str.str.len")
  my d1819:end: 'a | 'b | 'c | int = e5131:case e5128:(e5127:r2126:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e5126:(e5125:(e5123:r2124:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e5122:r2123:count->d1816:count) e5124:r2125:input_len->d1818:input_len)) { p1248:true -> e5129:r2127:count->d1816:count; p1249:false -> e5130:r2128:input_len->d1818:input_len }
  my d1820:rest: 'a = e5138:(e5136:(e5134:(e5132:r2129:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5133:r2130:input->d1799:input) e5135:r2131:end->d1819:end) e5137:r2132:input_len->d1818:input_len)
  d1821:line arg
  d1822:column arg
  d1823:v arg
  d1824:source arg
  d1825:parser arg
  d1826:source arg
  d1827:start arg
  d1828:parser arg
  my d1829:rest: 'a = e5203:(e5200:(e5198:(e5196:r2154:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5197:r2155:source->d1826:source) e5199:r2156:start->d1827:start) e5202:(e5201:r2157:source->d1826:source.s229.len->d838:"std.text.str.str.len"))
  d1830:found arg
  my d1831:consumed: 'a = e5226:(e5225:(e5221:r2165:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e5220:(e5219:r2164:rest->d1829:rest.s230.len->d838:"std.text.str.str.len")) e5224:(e5223:(e5222:r2166:found->d1830:found.s231.rest->d742).s232.len->d838:"std.text.str.str.len"))
  d1832:source arg
  d1833:parser arg
  d1834:source arg
  d1835:parser arg
  d1836:replacement arg
  d1837:found arg
  d1838:source arg
  d1839:parser arg
  d1840:replacement arg
  my d1841:loop: int -> std::text::str::str -> std::text::str::str = e5382:(fn p1282:d1842:start -> e5381:(fn p1283:d1843:out -> e5380:case e5343:(e5341:(e5339:(e5337:r2215:find_from->d761:"std.text.parse.find_from" e5338:r2216:source->d1838:source) e5340:r2217:start->d1842:start) e5342:r2218:parser->d1839:parser) { p1285:r2219:just->d504:"std.data.opt.opt.just"(p1284:d1844:found) -> e5367:(e5347:(e5344:r2220:loop->d1841:loop e5346:(e5345:r2221:found->d1844:found.s238.end->d749)) e5366:(e5361:(e5348:r2222:"std::text::str::concat"->d784:"std.text.str.concat" e5360:(e5351:(e5349:r2223:"std::text::str::concat"->d784:"std.text.str.concat" e5350:r2224:out->d1843:out) e5359:(e5356:(e5354:(e5352:r2225:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5353:r2226:source->d1838:source) e5355:r2227:start->d1842:start) e5358:(e5357:r2228:found->d1844:found.s239.start->d747)))) e5365:(e5362:r2229:replacement->d1840:replacement e5364:(e5363:r2230:found->d1844:found.s240.value->d745)))); p1286:r2231:nil->d503:"std.data.opt.opt.nil" -> e5379:(e5370:(e5368:r2232:"std::text::str::concat"->d784:"std.text.str.concat" e5369:r2233:out->d1843:out) e5378:(e5375:(e5373:(e5371:r2234:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5372:r2235:source->d1838:source) e5374:r2236:start->d1842:start) e5377:(e5376:r2237:source->d1838:source.s241.len->d838:"std.text.str.str.len"))) }))
  d1842:start arg
  d1843:out arg
  d1844:found arg
  d1845:source arg
  d1846:parser arg
  d1847:replacement arg
  d1848:found arg
  d1849:source arg
  d1850:parser arg
  d1851:replacement arg
  my d1852:loop: int -> std::text::str::str -> std::text::str::str = e5470:(fn p1297:d1853:start -> e5469:(fn p1298:d1854:out -> e5468:case e5434:(e5432:(e5430:(e5428:r2255:find_from->d761:"std.text.parse.find_from" e5429:r2256:source->d1849:source) e5431:r2257:start->d1853:start) e5433:r2258:parser->d1850:parser) { p1300:r2259:just->d504:"std.data.opt.opt.just"(p1299:d1855:found) -> e5455:(e5438:(e5435:r2260:loop->d1852:loop e5437:(e5436:r2261:found->d1855:found.s245.end->d749)) e5454:(e5452:(e5439:r2262:"std::text::str::concat"->d784:"std.text.str.concat" e5451:(e5442:(e5440:r2263:"std::text::str::concat"->d784:"std.text.str.concat" e5441:r2264:out->d1854:out) e5450:(e5447:(e5445:(e5443:r2265:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5444:r2266:source->d1849:source) e5446:r2267:start->d1853:start) e5449:(e5448:r2268:found->d1855:found.s246.start->d747)))) e5453:r2269:replacement->d1851:replacement)); p1301:r2270:nil->d503:"std.data.opt.opt.nil" -> e5467:(e5458:(e5456:r2271:"std::text::str::concat"->d784:"std.text.str.concat" e5457:r2272:out->d1854:out) e5466:(e5463:(e5461:(e5459:r2273:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e5460:r2274:source->d1849:source) e5462:r2275:start->d1853:start) e5465:(e5464:r2276:source->d1849:source.s247.len->d838:"std.text.str.str.len"))) }))
  d1853:start arg
  d1854:out arg
  d1855:found arg
  d1856:parser arg
  d1857:replacement arg
  d1858:source arg
  d1859:p arg
  d1860:q arg
  my d1861:snap: 'a = e5492:(e5490:r2282:"parse::snapshot"->d714:"std.text.parse.parse.snapshot" e5491:())
  d1862:k arg
  d1863:e arg
  d1864:e1 arg
  d1865:e2 arg
  d1866:p arg
  my d1867:pos: 'a = e5528:(e5526:r2294:"parse::pos"->d712:"std.text.parse.parse.pos" e5527:())
  my d1868:item: 'a = e5543:(e5541:r2301:"parse::item"->d709:"std.text.parse.parse.item" e5542:())
  d1869:expected arg
  d1870:input arg
  d1871:input arg
  d1872:p arg
  d1873:p arg
  d1874:p arg
  d1875:p arg
  d1876:label_text arg
  d1877:e arg
  d1878:input arg
  my d1879:found: 'a = e5704:(e5702:(e5700:r2352:"std::text::str::word_prefix_at"->d879:"std.text.str.word_prefix_at" e5701:r2353:input->d1878:input) e5703:0)
  d1880:p arg
  d1881:b arg
  d1882:p arg
  d1883:ls arg
  d1884:i arg
  my d1885:line_range: 'a = e5768:(e5766:(e5760:r2371:"std::text::str::line_range"->d788:"std.text.str.line_range" e5765:(e5763:(e5762:(e5761:r2372:ls->d1883:ls.s257.source->d800).s258.get->d236) e5764:())) e5767:r2373:i->d1884:i)
  my d1886:loop: 'a [std::control::var::ref_update 'b; 'c] -> [std::control::var::ref_update 'd, 'c] 'a = e5807:(fn p1372:d1887:x -> e5806:catch e5780:r2377:x->d1887:x { std::control::var::ref_update::update p1373:d1888:old, p1374:d1889:k -> e5805:block { let my p1375:d1890:line_range = e5785:(e5783:(e5781:r2378:"std::text::str::line_range"->d788:"std.text.str.line_range" e5782:r2379:old->d1888:old) e5784:r2380:i->d1884:i); e5804:block { let my p1376:d1891:new_item = e5792:(e5786:r2381:"ref_update::update"->d234:"std.control.var.ref_update.update" e5791:(e5789:(e5787:r2382:"std::text::str::index_range"->d790:"std.text.str.index_range" e5788:r2383:old->d1888:old) e5790:r2384:line_range->d1890:line_range)); e5803:(e5793:r2385:loop->d1886:loop e5802:(e5794:r2386:k->d1889:k e5801:(e5799:(e5797:(e5795:r2387:"std::text::str::splice"->d792:"std.text.str.splice" e5796:r2388:old->d1888:old) e5798:r2389:line_range->d1890:line_range) e5800:r2390:new_item->d1891:new_item))) } } })
  d1887:x arg
  d1888:old arg
  d1889:k arg
  my d1890:line_range: 'a = e5785:(e5783:(e5781:r2378:"std::text::str::line_range"->d788:"std.text.str.line_range" e5782:r2379:old->d1888:old) e5784:r2380:i->d1884:i)
  my d1891:new_item: 'a = e5792:(e5786:r2381:"ref_update::update"->d234:"std.control.var.ref_update.update" e5791:(e5789:(e5787:r2382:"std::text::str::index_range"->d790:"std.text.str.index_range" e5788:r2383:old->d1888:old) e5790:r2384:line_range->d1890:line_range))
  d1892:source arg
  d1893:source arg
  d1894:ls arg
  d1895:i arg
  my d1896:line_range: 'a = e5836:(e5834:(e5831:r2397:"std::text::str::line_range"->d788:"std.text.str.line_range" e5833:(e5832:r2398:ls->d1894:ls.s263.source->d796)) e5835:r2399:i->d1895:i)
  d1897:ls arg
  d1898:i arg
  my d1899:line_range: 'a = e5855:(e5853:(e5847:r2404:"std::text::str::line_range"->d788:"std.text.str.line_range" e5852:(e5850:(e5849:(e5848:r2405:ls->d1897:ls.s265.source->d800).s266.get->d236) e5851:())) e5854:r2406:i->d1898:i)
  my d1900:loop: 'a [std::control::var::ref_update 'b; 'c] -> [std::control::var::ref_update 'd, 'c] 'a = e5894:(fn p1388:d1901:x -> e5893:catch e5867:r2410:x->d1901:x { std::control::var::ref_update::update p1389:d1902:old, p1390:d1903:k -> e5892:block { let my p1391:d1904:line_range = e5872:(e5870:(e5868:r2411:"std::text::str::line_range"->d788:"std.text.str.line_range" e5869:r2412:old->d1902:old) e5871:r2413:i->d1898:i); e5891:block { let my p1392:d1905:new_item = e5879:(e5873:r2414:"ref_update::update"->d234:"std.control.var.ref_update.update" e5878:(e5876:(e5874:r2415:"std::text::str::index_range"->d790:"std.text.str.index_range" e5875:r2416:old->d1902:old) e5877:r2417:line_range->d1904:line_range)); e5890:(e5880:r2418:loop->d1900:loop e5889:(e5881:r2419:k->d1903:k e5888:(e5886:(e5884:(e5882:r2420:"std::text::str::splice"->d792:"std.text.str.splice" e5883:r2421:old->d1902:old) e5885:r2422:line_range->d1904:line_range) e5887:r2423:new_item->d1905:new_item))) } } })
  d1901:x arg
  d1902:old arg
  d1903:k arg
  my d1904:line_range: 'a = e5872:(e5870:(e5868:r2411:"std::text::str::line_range"->d788:"std.text.str.line_range" e5869:r2412:old->d1902:old) e5871:r2413:i->d1898:i)
  my d1905:new_item: 'a = e5879:(e5873:r2414:"ref_update::update"->d234:"std.control.var.ref_update.update" e5878:(e5876:(e5874:r2415:"std::text::str::index_range"->d790:"std.text.str.index_range" e5875:r2416:old->d1902:old) e5877:r2417:line_range->d1904:line_range))
  d1906:ls arg
  d1907:i arg
  d1908:end arg
  d1909:acc arg
  d1910:f arg
  d1911:ls arg
  d1912:i arg
  d1913:end arg
  d1914:acc arg
  d1915:f arg
  d1916:ls arg
  d1917:z arg
  d1918:f arg
  d1919:ls arg
  d1920:z arg
  d1921:f arg
  d1922:s arg
  d1923:r arg
  d1924:insert arg
  d1925:s arg
  d1926:needle arg
  d1927:s arg
  d1928:needle arg
  d1929:s arg
  d1930:prefix arg
  d1931:s arg
  d1932:suffix arg
  d1933:s arg
  d1934:separator arg
  d1935:s arg
  d1936:separator arg
  d1937:s arg
  d1938:from arg
  d1939:to arg
  d1940:s arg
  d1941:from arg
  d1942:to arg
  d1943:s arg
  d1944:s arg
  d1945:s arg
  d1946:"&r" arg
  d1947:pattern arg
  d1948:replacement arg
  d1949:s arg
  d1950:"&r" arg
  d1951:pattern arg
  d1952:replacement arg
  d1953:s arg
  d1954:"&r" arg
  d1955:pattern arg
  d1956:replacement arg
  d1957:s arg
  d1958:"&r" arg
  d1959:range arg
  d1960:replacement arg
  d1961:s arg
  d1962:"&r" arg
  d1963:s arg
  d1964:"&r" arg
  d1965:s arg
  d1966:"&r" arg
  d1967:s arg
  d1968:s arg
  d1969:count arg
  d1970:s arg
  d1971:s arg
  d1972:s arg
  d1973:s arg
  d1974:"&s" arg
  d1975:s arg
  d1976:s arg
  d1977:s arg
  d1978:s arg
  d1979:s arg
  d1980:source arg
  d1981:source_len arg
  d1982:needle arg
  d1983:needle_len arg
  d1984:start arg
  my d1985:end: 'a = e6236:(e6234:(e6232:r2557:"std::int::add"->d50:"std.int.add" e6233:r2558:start->d1984:start) e6235:r2559:needle_len->d1983:needle_len)
  d1986:source arg
  d1987:needle arg
  d1988:start arg
  d1989:source arg
  d1990:source_len arg
  d1991:needle arg
  d1992:needle_len arg
  d1993:start arg
  d1994:source arg
  d1995:source_len arg
  d1996:needle arg
  d1997:needle_len arg
  d1998:limit arg
  d1999:i arg
  d2000:source arg
  d2001:needle arg
  d2002:start arg
  d2003:source arg
  d2004:needle arg
  d2005:i arg
  d2006:source arg
  d2007:needle arg
  d2008:source arg
  d2009:prefix arg
  d2010:source arg
  d2011:suffix arg
  my d2012:source_len: 'a = e6428:(e6426:r2643:"std::text::str::len"->d786:"std.text.str.len" e6427:r2644:source->d2010:source)
  my d2013:suffix_len: 'a = e6431:(e6429:r2645:"std::text::str::len"->d786:"std.text.str.len" e6430:r2646:suffix->d2011:suffix)
  d2014:source arg
  d2015:separator arg
  my d2016:source_len: 'a = e6459:(e6457:r2657:"std::text::str::len"->d786:"std.text.str.len" e6458:r2658:source->d2014:source)
  my d2017:separator_len: 'a = e6462:(e6460:r2659:"std::text::str::len"->d786:"std.text.str.len" e6461:r2660:separator->d2015:separator)
  d2018:parts arg
  d2019:source arg
  d2020:source_len arg
  d2021:separator arg
  d2022:separator_len arg
  d2023:source arg
  d2024:source_len arg
  d2025:separator arg
  d2026:separator_len arg
  d2027:start arg
  d2028:out arg
  d2029:i arg
  my d2030:piece: 'a = e6562:(e6560:(e6558:(e6556:r2704:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e6557:r2705:source->d2023:source) e6559:r2706:start->d2027:start) e6561:r2707:i->d2029:i)
  d2031:source arg
  my d2032:data: 'a = e6607:(e6605:r2727:"std::text::str::to_bytes"->d794:"std.text.str.to_bytes" e6606:r2728:source->d2031:source)
  my d2033:end: 'a = e6610:(e6608:r2729:"std::text::bytes::len"->d653:"std.text.bytes.len" e6609:r2730:data->d2032:data)
  my d2034:chunk_count: 'a = e6619:(e6617:(e6611:r2731:"std::int::div"->d53:"std.int.div" e6616:(e6615:(e6613:r2733:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e6612:r2732:end->d2033:end) e6614:1023)) e6618:1024)
  my d2035:scan: 'a = e6644:(e6632:(e6625:(e6624:(e6623:(e6621:r2734:"#op:infix:..<"->d408:"std.core.ops.#op:infix:..<" e6620:0) e6622:r2735:chunk_count->d2034:chunk_count).s283.fold=>d449:"std.data.fold.Fold.fold") e6631:(e6626:0, e6629:(e6627:builtin_op::list_empty e6628:()), e6630:true)) e6643:(fn p1552:d2036:state -> e6642:(fn p1553:d2037:chunk -> e6641:(e6639:(e6637:(e6635:(e6633:r2736:split_newline_bytes_chunk->d861:"std.text.str.split_newline_bytes_chunk" e6634:r2737:data->d2032:data) e6636:r2738:end->d2033:end) e6638:r2739:state->d2036:state) e6640:r2740:chunk->d2037:chunk))))
  d2036:state arg
  d2037:chunk arg
  d2038:start arg
  d2039:out arg
  d2040:data arg
  d2041:end arg
  d2042:state arg
  d2043:chunk arg
  my d2044:i: 'a = e6678:(e6677:(e6675:r2756:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e6674:r2755:chunk->d2043:chunk) e6676:1024)
  my d2045:chunk_end: 'a | 'b | 'c | int = e6696:case e6689:(e6688:r2761:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6687:(e6686:(e6684:r2759:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e6683:(e6682:(e6680:r2758:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e6679:r2757:i->d2044:i) e6681:1024)) e6685:r2760:end->d2041:end)) { p1570:true -> e6694:(e6693:(e6691:r2763:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e6690:r2762:i->d2044:i) e6692:1024); p1571:false -> e6695:r2764:end->d2041:end }
  d2046:state arg
  d2047:j arg
  d2048:data arg
  d2049:state arg
  d2050:i arg
  d2051:start arg
  d2052:out arg
  my d2053:piece: 'a = e6738:(e6728:r2777:"std::text::bytes::to_utf8_lossy"->d666:"std.text.bytes.to_utf8_lossy" e6737:(e6731:(e6729:r2778:"std::text::bytes::index_range"->d657:"std.text.bytes.index_range" e6730:r2779:data->d2048:data) e6736:(e6734:(e6732:r2780:"std::data::range::range"->d511:"std.data.range.range" e6733:r2781:start->d2051:start) e6735:r2782:i->d2050:i)))
  d2054:source arg
  d2055:separator arg
  my d2056:source_len: 'a = e6765:(e6763:r2792:"std::text::str::len"->d786:"std.text.str.len" e6764:r2793:source->d2054:source)
  my d2057:separator_len: 'a = e6768:(e6766:r2794:"std::text::str::len"->d786:"std.text.str.len" e6767:r2795:separator->d2055:separator)
  d2058:i arg
  d2059:parts arg
  d2060:separator arg
  d2061:out arg
  d2062:part arg
  d2063:rest arg
  d2064:parts arg
  d2065:separator arg
  d2066:head arg
  d2067:tail arg
  d2068:source arg
  d2069:i arg
  d2070:source arg
  d2071:end arg
  my d2072:previous: 'a = e6888:(e6886:(e6884:r2854:"std::int::sub"->d51:"std.int.sub" e6885:r2855:end->d2071:end) e6887:1)
  d2073:source arg
  d2074:source arg
  d2075:source arg
  my d2076:start: 'a = e6942:(e6940:(e6938:r2878:trim_start_index->d866:"std.text.str.trim_start_index" e6939:r2879:source->d2075:source) e6941:0)
  my d2077:end: 'a = e6949:(e6945:(e6943:r2880:trim_end_index->d867:"std.text.str.trim_end_index" e6944:r2881:source->d2075:source) e6948:(e6946:r2882:"std::text::str::len"->d786:"std.text.str.len" e6947:r2883:source->d2075:source))
  d2078:source arg
  d2079:count arg
  my d2080:loop: int -> std::text::str::str -> std::text::str::str = e6992:(fn p1631:d2081:i -> e6991:(fn p1632:d2082:out -> e6990:case e6975:(e6974:r2895:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e6973:(e6971:(e6969:r2892:"std::int::lt"->d46:"std.int.lt" e6970:r2893:i->d2081:i) e6972:r2894:count->d2079:count)) { p1633:true -> e6988:(e6982:(e6976:r2896:loop->d2080:loop e6981:(e6979:(e6977:r2897:"std::int::add"->d50:"std.int.add" e6978:r2898:i->d2081:i) e6980:1)) e6987:(e6985:(e6983:r2899:"std::text::str::concat"->d784:"std.text.str.concat" e6984:r2900:out->d2082:out) e6986:r2901:source->d2078:source)); p1634:false -> e6989:r2902:out->d2082:out }))
  d2081:i arg
  d2082:out arg
  d2083:item arg
  d2084:source arg
  d2085:start arg
  d2086:i arg
  d2087:acc arg
  d2088:digit arg
  d2089:source arg
  d2090:value arg
  d2091:source arg
  d2092:from arg
  d2093:to arg
  d2094:i arg
  d2095:source arg
  d2096:from arg
  d2097:to arg
  d2098:source arg
  d2099:from arg
  d2100:to arg
  my d2101:loop: int -> std::text::str::str -> std::text::str::str = e7279:(fn p1684:d2102:start -> e7278:(fn p1685:d2103:out -> e7277:case e7236:(e7234:(e7232:(e7230:r3002:find_at->d851:"std.text.str.find_at" e7231:r3003:source->d2098:source) e7233:r3004:from->d2099:from) e7235:r3005:start->d2102:start) { p1687:r3006:just->d504:"std.data.opt.opt.just"(p1686:d2104:i) -> e7263:block { let my p1688:d2105:prefix = e7243:(e7241:(e7239:(e7237:r3007:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e7238:r3008:source->d2098:source) e7240:r3009:start->d2102:start) e7242:r3010:i->d2104:i); e7262:(e7252:(e7244:r3011:loop->d2101:loop e7251:(e7247:(e7245:r3012:"std::int::add"->d50:"std.int.add" e7246:r3013:i->d2104:i) e7250:(e7248:r3014:"std::text::str::len"->d786:"std.text.str.len" e7249:r3015:from->d2099:from))) e7261:(e7259:(e7253:r3016:"std::text::str::concat"->d784:"std.text.str.concat" e7258:(e7256:(e7254:r3017:"std::text::str::concat"->d784:"std.text.str.concat" e7255:r3018:out->d2103:out) e7257:r3019:prefix->d2105:prefix)) e7260:r3020:to->d2100:to)) }; p1689:r3021:nil->d503:"std.data.opt.opt.nil" -> e7276:(e7266:(e7264:r3022:"std::text::str::concat"->d784:"std.text.str.concat" e7265:r3023:out->d2103:out) e7275:(e7271:(e7269:(e7267:r3024:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e7268:r3025:source->d2098:source) e7270:r3026:start->d2102:start) e7274:(e7272:r3027:"std::text::str::len"->d786:"std.text.str.len" e7273:r3028:source->d2098:source))) }))
  d2102:start arg
  d2103:out arg
  d2104:i arg
  my d2105:prefix: 'a = e7243:(e7241:(e7239:(e7237:r3007:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e7238:r3008:source->d2098:source) e7240:r3009:start->d2102:start) e7242:r3010:i->d2104:i)
  d2106:source arg
  d2107:start arg
  my d2108:source_len: 'a = e7293:(e7291:r3030:"std::text::str::len"->d786:"std.text.str.len" e7292:r3031:source->d2106:source)
  my d2109:remaining: 'a = e7298:(e7297:(e7295:r3033:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e7294:r3032:source_len->d2108:source_len) e7296:r3034:start->d2107:start)
  my d2110:loop: int -> std::text::str::str = e7347:(fn p1697:d2111:i -> e7346:case e7312:(e7311:r3042:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7310:(e7309:(e7307:r3040:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e7306:r3039:i->d2111:i) e7308:r3041:source_len->d2108:source_len)) { p1701:true -> e7338:block { let my p1698:d2112:item = e7317:(e7315:(e7313:r3043:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e7314:r3044:source->d2106:source) e7316:r3045:i->d2111:i); e7337:case e7322:(e7321:r3048:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7320:(e7318:r3046:"std::text::char::is_word"->d675:"std.text.char.is_word" e7319:r3047:item->d2112:item)) { p1699:true -> e7329:(e7323:r3049:loop->d2110:loop e7328:(e7327:(e7325:r3051:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7324:r3050:i->d2111:i) e7326:1)); p1700:false -> e7336:(e7334:(e7332:(e7330:r3052:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e7331:r3053:source->d2106:source) e7333:r3054:start->d2107:start) e7335:r3055:i->d2111:i) } }; p1702:false -> e7345:(e7343:(e7341:(e7339:r3056:"std::text::str::index_range_raw"->d791:"std.text.str.index_range_raw" e7340:r3057:source->d2106:source) e7342:r3058:start->d2107:start) e7344:r3059:i->d2111:i) })
  d2111:i arg
  my d2112:item: 'a = e7317:(e7315:(e7313:r3043:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e7314:r3044:source->d2106:source) e7316:r3045:i->d2111:i)
  my d2113:end: 'a = e7371:case e7358:(e7357:r3064:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7356:(e7355:(e7353:r3063:"#op:infix:=="->d419:"std.core.ops.#op:infix:==" e7352:r3062:start->d2107:start) e7354:0)) { p1704:true -> e7363:(e7361:(e7359:r3065:word_prefix_ascii_or_slow_end->d880:"std.text.str.word_prefix_ascii_or_slow_end" e7360:r3066:source->d2106:source) e7362:r3067:source_len->d2108:source_len); p1705:false -> e7370:(e7368:(e7366:(e7364:r3068:word_prefix_slow_end->d884:"std.text.str.word_prefix_slow_end" e7365:r3069:source->d2106:source) e7367:r3070:source_len->d2108:source_len) e7369:r3071:start->d2107:start) }
  d2114:source arg
  d2115:source_len arg
  my d2116:data: 'a = e7387:(e7385:r3076:"std::text::str::to_bytes"->d794:"std.text.str.to_bytes" e7386:r3077:source->d2114:source)
  my d2117:data_len: 'a = e7390:(e7388:r3078:"std::text::bytes::len"->d653:"std.text.bytes.len" e7389:r3079:data->d2116:data)
  my d2118:chunk_count: 'a = e7399:(e7397:(e7391:r3080:"std::int::div"->d53:"std.int.div" e7396:(e7395:(e7393:r3082:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7392:r3081:data_len->d2117:data_len) e7394:1023)) e7398:1024)
  my d2119:scan: 'a = e7421:(e7409:(e7405:(e7404:(e7403:(e7401:r3083:"#op:infix:..<"->d408:"std.core.ops.#op:infix:..<" e7400:0) e7402:r3084:chunk_count->d2118:chunk_count).s285.fold=>d449:"std.data.fold.Fold.fold") e7408:(e7406:0, e7407:0)) e7420:(fn p1714:d2120:state -> e7419:(fn p1715:d2121:chunk -> e7418:(e7416:(e7414:(e7412:(e7410:r3085:word_prefix_ascii_chunk->d881:"std.text.str.word_prefix_ascii_chunk" e7411:r3086:data->d2116:data) e7413:r3087:data_len->d2117:data_len) e7415:r3088:state->d2120:state) e7417:r3089:chunk->d2121:chunk))))
  d2120:state arg
  d2121:chunk arg
  d2122:end arg
  d2123:end arg
  d2124:data arg
  d2125:data_len arg
  d2126:state arg
  d2127:chunk arg
  my d2128:i: 'a = e7443:(e7442:(e7440:r3098:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e7439:r3097:chunk->d2127:chunk) e7441:1024)
  my d2129:chunk_end: 'a | 'b | 'c | int = e7461:case e7454:(e7453:r3103:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7452:(e7451:(e7449:r3101:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e7448:(e7447:(e7445:r3100:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7444:r3099:i->d2128:i) e7446:1024)) e7450:r3102:data_len->d2125:data_len)) { p1731:true -> e7459:(e7458:(e7456:r3105:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7455:r3104:i->d2128:i) e7457:1024); p1732:false -> e7460:r3106:data_len->d2125:data_len }
  d2130:state arg
  d2131:j arg
  d2132:data arg
  d2133:state arg
  d2134:i arg
  d2135:end arg
  my d2136:byte: 'a = e7493:(e7491:(e7489:r3117:"std::text::bytes::index_raw"->d656:"std.text.bytes.index_raw" e7490:r3118:data->d2132:data) e7492:r3119:i->d2134:i)
  d2137:byte arg
  d2138:source arg
  d2139:source_len arg
  d2140:i arg
  my d2141:count: 'a = e7597:(e7596:(e7594:r3152:"#op:infix:-"->d414:"std.core.ops.#op:infix:-" e7593:r3151:source_len->d2139:source_len) e7595:r3153:i->d2140:i)
  my d2142:chunk_count: 'a = e7606:(e7604:(e7598:r3154:"std::int::div"->d53:"std.int.div" e7603:(e7602:(e7600:r3156:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7599:r3155:count->d2141:count) e7601:1023)) e7605:1024)
  my d2143:scan: 'a = e7630:(e7616:(e7612:(e7611:(e7610:(e7608:r3157:"#op:infix:..<"->d408:"std.core.ops.#op:infix:..<" e7607:0) e7609:r3158:chunk_count->d2142:chunk_count).s287.fold=>d449:"std.data.fold.Fold.fold") e7615:(e7613:r3159:i->d2140:i, e7614:true)) e7629:(fn p1767:d2144:state -> e7628:(fn p1768:d2145:chunk -> e7627:(e7625:(e7623:(e7621:(e7619:(e7617:r3160:word_prefix_slow_chunk->d885:"std.text.str.word_prefix_slow_chunk" e7618:r3161:source->d2138:source) e7620:r3162:source_len->d2139:source_len) e7622:r3163:state->d2144:state) e7624:r3164:i->d2140:i) e7626:r3165:chunk->d2145:chunk))))
  d2144:state arg
  d2145:chunk arg
  d2146:end arg
  d2147:source arg
  d2148:source_len arg
  d2149:state arg
  d2150:start arg
  d2151:chunk arg
  my d2152:i: 'a = e7649:(e7648:(e7642:r3170:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7641:r3169:start->d2150:start) e7647:(e7646:(e7644:r3172:"#op:infix:*"->d415:"std.core.ops.#op:infix:*" e7643:r3171:chunk->d2151:chunk) e7645:1024))
  my d2153:chunk_end: 'a | 'b | 'c | int = e7667:case e7660:(e7659:r3177:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e7658:(e7657:(e7655:r3175:"#op:infix:<"->d421:"std.core.ops.#op:infix:<" e7654:(e7653:(e7651:r3174:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7650:r3173:i->d2152:i) e7652:1024)) e7656:r3176:source_len->d2148:source_len)) { p1782:true -> e7665:(e7664:(e7662:r3179:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7661:r3178:i->d2152:i) e7663:1024); p1783:false -> e7666:r3180:source_len->d2148:source_len }
  d2154:state arg
  d2155:index arg
  d2156:source arg
  d2157:state arg
  d2158:i arg
  d2159:end arg
  d2160:s arg
  d2161:i arg
  d2162:s arg
  d2163:r arg
  d2164:r arg
  d2165:i arg
  my d2166:loop: 'a [std::control::var::ref_update 'b; 'c] -> [std::control::var::ref_update 'd, 'c] 'a = e7766:(fn p1805:d2167:x -> e7765:catch e7745:r3210:x->d2167:x { std::control::var::ref_update::update p1806:d2168:old, p1807:d2169:k -> e7764:block { let my p1808:d2170:new_item = e7752:(e7746:r3211:"ref_update::update"->d234:"std.control.var.ref_update.update" e7751:(e7749:(e7747:r3212:"std::text::str::index_range"->d790:"std.text.str.index_range" e7748:r3213:old->d2168:old) e7750:r3214:i->d2165:i)); e7763:(e7753:r3215:loop->d2166:loop e7762:(e7754:r3216:k->d2169:k e7761:(e7759:(e7757:(e7755:r3217:"std::text::str::splice"->d792:"std.text.str.splice" e7756:r3218:old->d2168:old) e7758:r3219:i->d2165:i) e7760:r3220:new_item->d2170:new_item))) } })
  d2167:x arg
  d2168:old arg
  d2169:k arg
  my d2170:new_item: 'a = e7752:(e7746:r3211:"ref_update::update"->d234:"std.control.var.ref_update.update" e7751:(e7749:(e7747:r3212:"std::text::str::index_range"->d790:"std.text.str.index_range" e7748:r3213:old->d2168:old) e7750:r3214:i->d2165:i))
  d2171:r arg
  d2172:i arg
  my d2173:loop: 'a [std::control::var::ref_update 'b; 'c] -> [std::control::var::ref_update 'd, 'c] 'a = e7822:(fn p1814:d2174:x -> e7821:catch e7789:r3227:x->d2174:x { std::control::var::ref_update::update p1815:d2175:old, p1816:d2176:k -> e7820:block { let my p1817:d2177:new_item = e7796:(e7790:r3228:"ref_update::update"->d234:"std.control.var.ref_update.update" e7795:(e7793:(e7791:r3229:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e7792:r3230:old->d2175:old) e7794:r3231:i->d2172:i)); e7819:block { let my p1818:d2178:replacement = e7799:(e7797:r3232:"std::text::char::to_string"->d672:"std.text.char.to_string" e7798:r3233:new_item->d2177:new_item); e7818:(e7800:r3234:loop->d2173:loop e7817:(e7801:r3235:k->d2176:k e7816:(e7814:(e7804:(e7802:r3236:"std::text::str::splice"->d792:"std.text.str.splice" e7803:r3237:old->d2175:old) e7813:(e7807:(e7805:r3238:range->d511:"std.data.range.range" e7806:r3239:i->d2172:i) e7812:(e7811:(e7809:r3241:"#op:infix:+"->d413:"std.core.ops.#op:infix:+" e7808:r3240:i->d2172:i) e7810:1))) e7815:r3242:replacement->d2178:replacement))) } } })
  d2174:x arg
  d2175:old arg
  d2176:k arg
  my d2177:new_item: 'a = e7796:(e7790:r3228:"ref_update::update"->d234:"std.control.var.ref_update.update" e7795:(e7793:(e7791:r3229:"std::text::str::index_raw"->d789:"std.text.str.index_raw" e7792:r3230:old->d2175:old) e7794:r3231:i->d2172:i))
  my d2178:replacement: 'a = e7799:(e7797:r3232:"std::text::char::to_string"->d672:"std.text.char.to_string" e7798:r3233:new_item->d2177:new_item)
  d2179:format arg
  d2180:algebra arg
  d2181:head arg
  d2182:tail arg
  d2183:format arg
  d2184:algebra arg
  d2185:value arg
  d2186:format arg
  d2187:algebra arg
  d2188:children arg
  d2189:format arg
  d2190:algebra arg
  d2191:marker arg
  d2192:level arg
  d2193:children arg
  d2194:format arg
  d2195:algebra arg
  d2196:marker arg
  d2197:format arg
  d2198:algebra arg
  d2199:marker arg
  d2200:children arg
  d2201:format arg
  d2202:algebra arg
  d2203:ordered arg
  d2204:items arg
  d2205:format arg
  d2206:algebra arg
  d2207:marker arg
  d2208:children arg
  d2209:format arg
  d2210:algebra arg
  d2211:children arg
  d2212:format arg
  d2213:algebra arg
  d2214:info arg
  d2215:body arg
  d2216:format arg
  d2217:algebra arg
  d2218:children arg
  d2219:format arg
  d2220:algebra arg
  d2221:children arg
  d2222:format arg
  d2223:algebra arg
  d2224:children arg
  d2225:format arg
  d2226:algebra arg
  d2227:node arg
  d2228:format arg
  d2229:document arg
  d2230:document arg
  d2231:document arg
  d2232:head arg
  d2233:tail arg
  d2234:value arg
  d2235:children arg
  d2236:marker arg
  d2237:level arg
  d2238:children arg
  d2239:marker arg
  d2240:marker arg
  d2241:children arg
  d2242:ordered arg
  d2243:items arg
  d2244:marker arg
  d2245:children arg
  d2246:children arg
  d2247:info arg
  d2248:body arg
  my d2249:info_node: 'a = e8208:(e8204:r3388:html_node->d930:"std.text.yumark.html_node" e8207:{tag: e8205:"code-info", body: e8206:r3389:info->d2247:info})
  my d2250:body_node: 'a = e8213:(e8209:r3390:html_node->d930:"std.text.yumark.html_node" e8212:{tag: e8210:"code", body: e8211:r3391:body->d2248:body})
  d2251:children arg
  d2252:children arg
  d2253:children arg
  d2254:head arg
  d2255:tail arg
  d2256:value arg
  d2257:children arg
  d2258:marker arg
  d2259:level arg
  d2260:children arg
  d2261:marker arg
  d2262:marker arg
  d2263:children arg
  d2264:ordered arg
  d2265:items arg
  d2266:marker arg
  d2267:children arg
  d2268:children arg
  d2269:info arg
  d2270:body arg
  d2271:children arg
  d2272:children arg
  d2273:children arg
  d2274:left arg
  d2275:right arg
  d2276:a arg
  d2277:b arg
  d2278:c arg
  d2279:a arg
  d2280:b arg
  d2281:c arg
  d2282:d arg
  d2283:format arg
  d2284:format arg
  d2286: user_id -> int = <missing>
  d2287: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d2288:"#cast": user_id -> int = e8396:(fn p1937:d2290:x -> e8395:(e8394:r3452:x->d2290:x.s313.raw->d2286))
  d2290:x arg
  d2291:flag arg
}
```

### run

Command: `./target/release/yulang --std-root lib run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/cast-branch-if-run.yu`

開始: 2026-11-08T11:54:16.487234+00:00、所要 0.121 秒、exit 0。

```text
run roots [(1, 2)]
```

## control-standard

```yulang
pub lazy infix(and) 2.0.0 2.0.1 = \a -> \b ->
    if a():
        b()
    else:
        false
act ping:
    our get: () -> bool
our no_else_true = if true: 42
our no_else_false = if false: 42
our where_guard = case 1:
    value where false -> 9
    value -> value
our if_guard = case 1:
    value if false -> 9
    value -> value
our short = catch (false and ping::get()):
    ping::get(), k -> true
    value -> value
our force = catch (true and ping::get()):
    ping::get(), k -> true
    value -> value
(no_else_true,no_else_false,where_guard,if_guard,short,force)
```

### check

Command: `./target/release/yulang --std-root lib check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/control-standard.yu`

開始: 2026-11-08T11:47:27.349066+00:00、所要 142.511 秒、exit -9。

```text
```

### run

Command: `./target/release/yulang --std-root lib run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/control-standard.yu`

開始: 2026-11-08T11:49:49.860192+00:00、所要 0.245 秒、exit 0。

```text
run roots [((), (), 1, 1, false, true)]
```

### check

Command: `./target/release/yulang --std-root lib check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/control-standard.yu`

開始: 2026-11-08T11:58:53.334876+00:00、所要 149.007 秒、exit 0。

```text
```

## f1-direct

```yulang
act ping:
    our get: () -> int
our id(x) = x
our direct() = id(ping::get())
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-direct.yu`

開始: 2026-11-08T11:32:54.779075+00:00、所要 0.013 秒、exit 0。

```text
roots d0:ping d2:id d3:direct
d0:ping mod {
}
d2:id: 'a -> 'a = e1:(fn p0:d4:x -> e0:r0:x->d4:x)
d3:direct: () -> [ping] int = e7:(fn p1:() -> e6:(e2:r1:id->d2:id e5:(e3:r2:"ping::get"->d1:"ping.get" e4:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-direct.yu`

開始: 2026-11-08T11:32:54.792149+00:00、所要 0.015 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-direct.yu`

開始: 2026-11-08T11:32:54.807264+00:00、所要 0.015 秒、exit 0。

```text
run roots []
```

## f1-pipe

```yulang
act ping:
    our get: () -> int
our id(x) = x
our piped() = ping::get() | id
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-pipe.yu`

開始: 2026-11-08T11:32:54.821902+00:00、所要 0.011 秒、exit 0。

```text
roots d0:ping d2:id d3:piped
d0:ping mod {
}
d2:id: 'a -> 'a = e1:(fn p0:d4:x -> e0:r0:x->d4:x)
d3:piped: () -> [ping] int = e7:(fn p1:() -> e6:(e5:r2:id->d2:id e4:(e2:r1:"ping::get"->d1:"ping.get" e3:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-pipe.yu`

開始: 2026-11-08T11:32:54.833410+00:00、所要 0.036 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-pipe.yu`

開始: 2026-11-08T11:32:54.869096+00:00、所要 0.014 秒、exit 0。

```text
run roots []
```

## f1-higher

```yulang
act ping:
    our get: () -> int
our id(x) = x
our apply(f: [ping] int -> [ping] int) = f(ping::get())
our higher() = apply id
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher.yu`

開始: 2026-11-08T11:32:54.883371+00:00、所要 0.027 秒、exit 0。

```text
roots d0:ping d2:id d3:apply d4:higher
d0:ping mod {
}
d2:id: 'a -> 'a = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:apply: (int -> [ping] int) -> int = e7:(fn p1:d6:f -> e6:(e2:r1:f->d6:f e5:(e3:r2:"ping::get"->d1:"ping.get" e4:())))
d4:higher: () -> int = e11:(fn p2:() -> e10:(e8:r3:apply->d3:apply e9:r4:id->d2:id))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:f arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher.yu`

開始: 2026-11-08T11:32:54.909972+00:00、所要 0.022 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-higher.yu`

開始: 2026-11-08T11:32:54.931682+00:00、所要 0.062 秒、exit 0。

```text
run roots []
```

## f1-ascribe

```yulang
act ping:
    our get: () -> int
our id(x) = x
our lifted = id as ([ping] int -> [ping] int)
our used() = lifted(ping::get())
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-ascribe.yu`

開始: 2026-11-08T11:32:54.993965+00:00、所要 0.022 秒、exit 0。

```text
roots d0:ping d2:id d3:lifted d4:used
d0:ping mod {
}
d2:id: 'a -> 'a = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:lifted: int -> int = e2:r1:id->d2:id
d4:used: () -> [ping] int = e8:(fn p1:() -> e7:(e3:r2:lifted->d3:lifted e6:(e4:r3:"ping::get"->d1:"ping.get" e5:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-ascribe.yu`

開始: 2026-11-08T11:32:55.015800+00:00、所要 0.018 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-ascribe.yu`

開始: 2026-11-08T11:32:55.033509+00:00、所要 0.028 秒、exit 0。

```text
run roots []
```

## f1-direct-run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(plain(ping::get()))
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-direct-run.yu`

開始: 2026-11-08T11:32:55.061844+00:00、所要 0.03 秒、exit 0。

```text
roots d0:ping d2:plain d3:handle
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d4:x -> e0:r0:x->d4:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d5:action -> e7:catch e2:r1:action->d5:action { ping::get p2:_, p3:d6:k -> e5:(e3:r2:k->d6:k e4:7); p4:d7:v -> e6:r3:v->d7:v })
root exprs e15:(e9:r4:handle->d3:handle e14:(e10:r5:plain->d2:plain e13:(e11:r6:"ping::get"->d1:"ping.get" e12:())))
runtime roots e15:(e9:r4:handle->d3:handle e14:(e10:r5:plain->d2:plain e13:(e11:r6:"ping::get"->d1:"ping.get" e12:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:x arg
  d5:action arg
  d6:k arg
  d7:v arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-direct-run.yu`

開始: 2026-11-08T11:32:55.092172+00:00、所要 0.027 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/f1-direct-run.yu`

開始: 2026-11-08T11:32:55.119028+00:00、所要 0.011 秒、exit 0。

```text
run roots [7]
```

## handler-multishot

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> (k 3, k 7)
    v -> v
handle(ping::get())
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/handler-multishot.yu`

開始: 2026-11-08T11:32:55.425958+00:00、所要 0.037 秒、exit 0。

```text
roots d0:ping d2:handle
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int | (int, int) = e10:(fn p0:d3:action -> e9:catch e0:r0:action->d3:action { ping::get p1:_, p2:d4:k -> e7:(e3:(e1:r1:k->d4:k e2:3), e6:(e4:r2:k->d4:k e5:7)); p3:d5:v -> e8:r3:v->d5:v })
root exprs e15:(e11:r4:handle->d2:handle e14:(e12:r5:"ping::get"->d1:"ping.get" e13:()))
runtime roots e15:(e11:r4:handle->d2:handle e14:(e12:r5:"ping::get"->d1:"ping.get" e13:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:action arg
  d4:k arg
  d5:v arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/handler-multishot.yu`

開始: 2026-11-08T11:32:55.462747+00:00、所要 0.027 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/handler-multishot.yu`

開始: 2026-11-08T11:32:55.490112+00:00、所要 0.03 秒、exit 1。

```text
conflicting type candidates: (int, int) vs int
```

## handler-shallow-run

```yulang
act ping:
    our get: () -> int
our twice() =
    my first = ping::get()
    ping::get()
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(twice())
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/handler-shallow-run.yu`

開始: 2026-11-08T11:32:55.520548+00:00、所要 0.042 秒、exit 0。

```text
roots d0:ping d2:twice d3:handle
d0:ping mod {
}
d2:twice: () -> [ping] int = e7:(fn p0:() -> e6:block { let my p1:d4:first = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()); e5:(e3:r1:"ping::get"->d1:"ping.get" e4:()) })
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e14:(fn p2:d5:action -> e13:catch e8:r2:action->d5:action { ping::get p3:_, p4:d6:k -> e11:(e9:r3:k->d6:k e10:7); p5:d7:v -> e12:r4:v->d7:v })
root exprs e19:(e15:r5:handle->d3:handle e18:(e16:r6:twice->d2:twice e17:()))
runtime roots e19:(e15:r5:handle->d3:handle e18:(e16:r6:twice->d2:twice e17:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  my d4:first: 'a | int = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:())
  d5:action arg
  d6:k arg
  d7:v arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/handler-shallow-run.yu`

開始: 2026-11-08T11:32:55.562514+00:00、所要 0.028 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/handler-shallow-run.yu`

開始: 2026-11-08T11:32:55.590388+00:00、所要 0.018 秒、exit 1。

```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
    --> line 5, column 5
    5 |     ping::get()
      |     ^^^^^^^^^
  hint: handle this computation with a matching effect handler before running it
  note: application occurs here
    --> line 5, column 5
    5 |     ping::get()
      |     ^^^^^^^^^^^
```

## handler-rehandle-run

```yulang
act ping:
    our get: () -> int
our twice() =
    my first = ping::get()
    ping::get()
our handle(action: [ping] int) = catch action:
    ping::get(), k -> handle(k 7)
    v -> v
handle(twice())
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/handler-rehandle-run.yu`

開始: 2026-11-08T11:32:55.607985+00:00、所要 0.074 秒、exit 0。

```text
roots d0:ping d2:twice d3:handle
d0:ping mod {
}
d2:twice: () -> [ping] int = e7:(fn p0:() -> e6:block { let my p1:d4:first = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()); e5:(e3:r1:"ping::get"->d1:"ping.get" e4:()) })
d3:handle: int [ping; 'a] -> ['a] int = e16:(fn p2:d5:action -> e15:catch e8:r2:action->d5:action { ping::get p3:_, p4:d6:k -> e13:(e9:r3:handle->d3:handle e12:(e10:r4:k->d6:k e11:7)); p5:d7:v -> e14:r5:v->d7:v })
root exprs e21:(e17:r6:handle->d3:handle e20:(e18:r7:twice->d2:twice e19:()))
runtime roots e21:(e17:r6:handle->d3:handle e20:(e18:r7:twice->d2:twice e19:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  my d4:first: 'a | int = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:())
  d5:action arg
  d6:k arg
  d7:v arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/handler-rehandle-run.yu`

開始: 2026-11-08T11:32:55.681801+00:00、所要 0.02 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/handler-rehandle-run.yu`

開始: 2026-11-08T11:32:55.702075+00:00、所要 0.024 秒、exit 0。

```text
run roots [7]
```

## record-default

```yulang
our f {a = 1, b = a} = (a, b)
f {}
f {a: 7}
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default.yu`

開始: 2026-11-08T11:32:55.725933+00:00、所要 0.025 秒、exit 0。

```text
roots d0:f
d0:f: {a?: 'a & 'b, b?: 'b} -> ('a | int, 'b | 'a | int) = e5:(fn p2:{a: p0:d1:a = e0:1, b: p1:d2:b = e1:r0:a->d1:a} -> e4:(e2:r1:a->d1:a, e3:r2:b->d2:b))
root exprs e8:(e6:r3:f->d0:f e7:{}) e12:(e9:r4:f->d0:f e11:{a: e10:7})
runtime roots e8:(e6:r3:f->d0:f e7:{}) e12:(e9:r4:f->d0:f e11:{a: e10:7})
detached {
  d1:a arg
  d2:b arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default.yu`

開始: 2026-11-08T11:32:55.750868+00:00、所要 0.008 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-default.yu`

開始: 2026-11-08T11:32:55.758699+00:00、所要 0.02 秒、exit 0。

```text
run roots [(1, 1), (7, 7)]
```

## record-spread

```yulang
our keep {width, ..input} = input
keep {width: 3, height: 4}
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-spread.yu`

開始: 2026-11-08T11:32:55.778816+00:00、所要 0.013 秒、exit 0。

```text
roots d0:keep
d0:keep: ('a & {width: 'b}) -> 'a | {width: 'b, ..never} = e1:(fn p2:{width: p0:d1:width, ..d2:input} -> e0:r0:input->d2:input)
root exprs e6:(e2:r1:keep->d0:keep e5:{width: e3:3, height: e4:4})
runtime roots e6:(e2:r1:keep->d0:keep e5:{width: e3:3, height: e4:4})
detached {
  d1:width arg
  d2:input arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-spread.yu`

開始: 2026-11-08T11:32:55.792033+00:00、所要 0.006 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/record-spread.yu`

開始: 2026-11-08T11:32:55.797654+00:00、所要 0.004 秒、exit 0。

```text
run roots [{width: 3, height: 4}]
```

## application-forms

```yulang
our f(x)(y) = (x, y)
f 1 2
f(1, 2)
our unit(x) = x
unit()
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/application-forms.yu`

開始: 2026-11-08T11:32:55.801767+00:00、所要 0.008 秒、exit 0。

```text
roots d0:f d1:unit
d0:f: 'a -> 'b -> ('a, 'b) = e4:(fn p0:d2:x -> e3:(fn p1:d3:y -> e2:(e0:r0:x->d2:x, e1:r1:y->d3:y)))
d1:unit: 'a -> 'a = e16:(fn p2:d6:x -> e15:r4:x->d6:x)
root exprs e9:(e7:(e5:r2:f->d0:f e6:1) e8:2) e14:(e12:(e10:r3:f->d0:f e11:1) e13:2) e19:(e17:r5:unit->d1:unit e18:())
runtime roots e9:(e7:(e5:r2:f->d0:f e6:1) e8:2) e14:(e12:(e10:r3:f->d0:f e11:1) e13:2) e19:(e17:r5:unit->d1:unit e18:())
detached {
  d2:x arg
  d3:y arg
  d6:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/application-forms.yu`

開始: 2026-11-08T11:32:55.809707+00:00、所要 0.006 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/application-forms.yu`

開始: 2026-11-08T11:32:55.815944+00:00、所要 0.004 秒、exit 0。

```text
run roots [(1, 2), (1, 2), ()]
```

## application-spaces

```yulang
our f(x) = (\y -> (x, y))
our g(x) = x
f g (7)
f g(7)
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/application-spaces.yu`

開始: 2026-11-08T11:32:55.820232+00:00、所要 0.015 秒、exit 0。

```text
roots d0:f d1:g
d0:f: 'a -> 'b -> ('a, 'b) = e4:(fn p0:d2:x -> e3:(fn p1:d3:y -> e2:(e0:r0:x->d2:x, e1:r1:y->d3:y)))
d1:g: 'a -> 'a = e6:(fn p2:d4:x -> e5:r2:x->d4:x)
root exprs e11:(e9:(e7:r3:f->d0:f e8:r4:g->d1:g) e10:7) e16:(e12:r5:f->d0:f e15:(e13:r6:g->d1:g e14:7))
runtime roots e11:(e9:(e7:r3:f->d0:f e8:r4:g->d1:g) e10:7) e16:(e12:r5:f->d0:f e15:(e13:r6:g->d1:g e14:7))
detached {
  d2:x arg
  d3:y arg
  d4:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/application-spaces.yu`

開始: 2026-11-08T11:32:55.835548+00:00、所要 0.035 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/application-spaces.yu`

開始: 2026-11-08T11:32:55.870259+00:00、所要 0.012 秒、exit 0。

```text
run roots [(<closure>, 7), <closure>]
```

## copy-private

```yulang
act original:
    our tick: () -> int
    my helper = 10
    our number = helper
act local = original
local::number
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/copy-private.yu`

開始: 2026-11-08T11:32:55.882688+00:00、所要 0.012 秒、exit 0。

```text
roots d0:original d4:local
d0:original mod {
  my d2:"original.helper": int = e0:10
  d3:"original.number": int = e1:r0:helper->d2:"original.helper"
}
d4:local mod {
  d6:"local.number": never = <missing>
}
root exprs e2:r1:"local::number"->d6:"local.number"
runtime roots e2:r1:"local::number"->d6:"local.number"
detached {
  d1:"original.tick": () -> [original] int = <missing>
  d5:"local.tick": () -> [local] int = <missing>
}
error: unresolved value name: helper
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/copy-private.yu`

開始: 2026-11-08T11:32:55.895233+00:00、所要 0.017 秒、exit 1。

```text
diagnostics:
  error [yulang.unresolved-value]: local.number: unresolved value name: helper
    hint: define `helper` before this use, or import the module that provides it
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/copy-private.yu`

開始: 2026-11-08T11:32:55.912811+00:00、所要 0.01 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: helper
  hint: run `yulang check` to see source ranges before running
```

## copy-family

```yulang
act original:
    our tick: () -> int
act local = original
our result() = local::tick()
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/copy-family.yu`

開始: 2026-11-08T11:32:55.922492+00:00、所要 0.017 秒、exit 0。

```text
roots d0:original d2:result d3:local
d0:original mod {
}
d2:result: () -> [local] int = e3:(fn p0:() -> e2:(e0:r0:"local::tick"->d4:"local.tick" e1:()))
d3:local mod {
}
detached {
  d1:"original.tick": () -> [original] int = <missing>
  d4:"local.tick": () -> [local] int = <missing>
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/copy-family.yu`

開始: 2026-11-08T11:32:55.939183+00:00、所要 0.027 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/copy-family.yu`

開始: 2026-11-08T11:32:55.965907+00:00、所要 0.012 秒、exit 0。

```text
run roots []
```

## value-restriction

```yulang
our id = \x -> x
our computed = (\f -> f)(\x -> x)
(id 1, id "a")
(computed 1, computed "a")
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/value-restriction.yu`

開始: 2026-11-08T11:32:55.977665+00:00、所要 0.015 秒、exit 0。

```text
roots d0:id d1:computed
d0:id: 'a -> 'a = e1:(fn p0:d2:x -> e0:r0:x->d2:x)
d1:computed: 'a -> 'a = e6:(e3:(fn p1:d3:f -> e2:r1:f->d3:f) e5:(fn p2:d4:x -> e4:r2:x->d4:x))
root exprs e13:(e9:(e7:r3:id->d0:id e8:1), e12:(e10:r4:id->d0:id e11:"a")) e20:(e16:(e14:r5:computed->d1:computed e15:1), e19:(e17:r6:computed->d1:computed e18:"a"))
runtime roots d1:computed e13:(e9:(e7:r3:id->d0:id e8:1), e12:(e10:r4:id->d0:id e11:"a")) e20:(e16:(e14:r5:computed->d1:computed e15:1), e19:(e17:r6:computed->d1:computed e18:"a"))
detached {
  d2:x arg
  d3:f arg
  d4:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/value-restriction.yu`

開始: 2026-11-08T11:32:55.993136+00:00、所要 0.014 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/value-restriction.yu`

開始: 2026-11-08T11:32:56.007300+00:00、所要 0.012 秒、exit 0。

```text
run roots [(1, "a"), (1, "a")]
```

## computed-cycle

```yulang
our make(x) = x
our a = make b
our b = make a
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/computed-cycle.yu`

開始: 2026-11-08T11:32:56.019179+00:00、所要 0.077 秒、exit 0。

```text
roots d0:make d1:a d2:b
d0:make: 'a -> 'a = e1:(fn p0:d3:x -> e0:r0:x->d3:x)
d1:a: never = e4:(e2:r1:make->d0:make e3:r2:b->d2:b)
d2:b: never = e7:(e5:r3:make->d0:make e6:r4:a->d1:a)
runtime roots d1:a d2:b
detached {
  d3:x arg
}
error: computed value fetch in recursive component: component d1,d2, edge d2 -> d1
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/computed-cycle.yu`

開始: 2026-11-08T11:32:56.095872+00:00、所要 0.073 秒、exit 1。

```text
diagnostics:
  error [yulang.analysis]: b: computed value fetch in recursive component: component d1,d2, edge d2 -> d1
    --> line 3, column 5
    3 | our b = make a
      |     ^
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/computed-cycle.yu`

開始: 2026-11-08T11:32:56.168598+00:00、所要 0.034 秒、exit 1。

```text
compile error [yulang.lowering]: source has lowering errors
  detail: computed value fetch in recursive component: component d1,d2, edge d2 -> d1
  hint: run `yulang check` to see source ranges before running
```

## row-notation

```yulang
act ping:
    our get: () -> int
our f(x: [ping; 'e] 'a) = x
```

### dump

Command: `./target/release/yulang --std-root lib --no-prelude dump --poly /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/row-notation.yu`

開始: 2026-11-08T11:32:56.203139+00:00、所要 0.017 秒、exit 0。

```text
roots d0:ping d2:f
d0:ping mod {
}
d2:f: 'a [ping; 'b] -> ['b] 'a = e1:(fn p0:d3:x -> e0:r0:x->d3:x)
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:x arg
}
```

### check

Command: `./target/release/yulang --std-root lib --no-prelude check /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/row-notation.yu`

開始: 2026-11-08T11:32:56.220098+00:00、所要 0.012 秒、exit 0。

```text
```

### run

Command: `./target/release/yulang --std-root lib --no-prelude run --print-roots /workspace/scratch/1d0b4aaa3394/yulang-audit-cycle1/notes/audit/examples/row-notation.yu`

開始: 2026-11-08T11:32:56.232307+00:00、所要 0.029 秒、exit 0。

```text
run roots []
```

## F1 constraint unit tests

`cargo test -p infer pure_function_argument_effect_passes --lib`、exit 0、86秒（初回debug test build込み）。以下はログ末尾。全ログはローカル `/tmp/yulang-audit-f1-unit.log` に残す。

```text
    Finished `test` profile [unoptimized + debuginfo] target(s) in 1m 26s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 3 tests
test constraints::tests::case_02::pure_function_argument_effect_passes_to_return_effect ... ok
test constraints::tests::case_02::pure_function_argument_effect_passes_outside_return_stack_marker ... ok
test constraints::tests::case_02::pure_function_argument_effect_passes_through_with_right_side_weights ... ok

test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 1390 filtered out; finished in 0.00s

```

## 標準prelude付き初回dump

`./target/release/yulang --std-root lib dump --poly ../yulang-audit-cycle1/notes/audit/examples/f1-direct.yu`、exit 0、179秒。出力全文は406469 bytesで、`logs/f1-direct-standard-dump.txt`に保存。最初はhome cacheがread-onlyだったためwarningがある。その後は公式環境変数YULANG_CACHE_DIRをworkspaceへ設定。
