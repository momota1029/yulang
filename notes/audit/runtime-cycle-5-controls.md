# Cycle 5 continuation-result runtime controls

旧Y2 d4c8bc8fc、自己完結 no-prelude、各10秒上限。ソース・コマンド・出力はそのまま。

## 1. pure-add / ['--no-prelude', 'check', '/tmp/audit5/pure-add.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
add 100 7
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/pure-add.yu
```
UTC: 2026-11-08T15:00:24.874427+00:00; elapsed: 0.005624s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 2. pure-add / ['dump', '--mono', '/tmp/audit5/pure-add.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
add 100 7
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/pure-add.yu
```
UTC: 2026-11-08T15:00:24.880103+00:00; elapsed: 0.006226s; exit: 0

stdout:
```text
mono roots [((m0 100) 7)]
m0 = d0 : int -> int -> int
  \d3 -> \d4 -> ((<prim int_add> d3) d4)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 3. pure-add / ['run', '--print-roots', '/tmp/audit5/pure-add.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
add 100 7
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/pure-add.yu
```
UTC: 2026-11-08T15:00:24.886385+00:00; elapsed: 0.009159s; exit: 0

stdout:
```text
run roots [107]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)
```

## 4. pure-add / ['--interpreter', '--print-roots', '/tmp/audit5/pure-add.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
add 100 7
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/pure-add.yu
```
UTC: 2026-11-08T15:00:24.895655+00:00; elapsed: 0.009220s; exit: 0

stdout:
```text
run roots [107]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 5. resume-only / ['--no-prelude', 'check', '/tmp/audit5/resume-only.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/resume-only.yu
```
UTC: 2026-11-08T15:00:24.905051+00:00; elapsed: 0.012146s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 6. resume-only / ['dump', '--mono', '/tmp/audit5/resume-only.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/resume-only.yu
```
UTC: 2026-11-08T15:00:24.917294+00:00; elapsed: 0.018083s; exit: 0

stdout:
```text
mono roots [(m0 (<effect-op ping::get> ()))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> (d7 7), d8 -> d8
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 7. resume-only / ['run', '--print-roots', '/tmp/audit5/resume-only.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/resume-only.yu
```
UTC: 2026-11-08T15:00:24.935477+00:00; elapsed: 0.013994s; exit: 0

stdout:
```text
run roots [7]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)
```

## 8. resume-only / ['--interpreter', '--print-roots', '/tmp/audit5/resume-only.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/resume-only.yu
```
UTC: 2026-11-08T15:00:24.949598+00:00; elapsed: 0.011090s; exit: 0

stdout:
```text
run roots [7]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 9. resume-add / ['--no-prelude', 'check', '/tmp/audit5/resume-add.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 (k 7)
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/resume-add.yu
```
UTC: 2026-11-08T15:00:24.960859+00:00; elapsed: 0.013864s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 10. resume-add / ['dump', '--mono', '/tmp/audit5/resume-add.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 (k 7)
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/resume-add.yu
```
UTC: 2026-11-08T15:00:24.974812+00:00; elapsed: 0.011792s; exit: 0

stdout:
```text
mono roots [(m0 (<effect-op ping::get> ()))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> ((m1 100) (d7 7)), d8 -> d8
m1 = d0 : int -> int -> int
  \d4 -> \d5 -> ((<prim int_add> d4) d5)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 11. resume-add / ['run', '--print-roots', '/tmp/audit5/resume-add.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 (k 7)
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/resume-add.yu
```
UTC: 2026-11-08T15:00:24.986753+00:00; elapsed: 0.014061s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)
runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: non-int primitive argument
  hint: try the interpreter oracle or reduce this source to a smaller report
```

## 12. resume-add / ['--interpreter', '--print-roots', '/tmp/audit5/resume-add.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 (k 7)
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/resume-add.yu
```
UTC: 2026-11-08T15:00:25.000948+00:00; elapsed: 0.011762s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
runtime error [yulang.runtime-type]: expected int, got <thunk>
  hint: check the value passed to this operation
```

## 13. resume-lambda / ['--no-prelude', 'check', '/tmp/audit5/resume-lambda.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> (\r -> add 100 r)(k 7)
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/resume-lambda.yu
```
UTC: 2026-11-08T15:00:25.012872+00:00; elapsed: 0.017496s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 14. resume-lambda / ['dump', '--mono', '/tmp/audit5/resume-lambda.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> (\r -> add 100 r)(k 7)
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/resume-lambda.yu
```
UTC: 2026-11-08T15:00:25.030476+00:00; elapsed: 0.016155s; exit: 0

stdout:
```text
mono roots [(m0 (<effect-op ping::get> ()))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> (\d8 -> ((m1 100) d8) (d7 7)), d9 -> d9
m1 = d0 : int -> int -> int
  \d4 -> \d5 -> ((<prim int_add> d4) d5)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 15. resume-lambda / ['run', '--print-roots', '/tmp/audit5/resume-lambda.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> (\r -> add 100 r)(k 7)
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/resume-lambda.yu
```
UTC: 2026-11-08T15:00:25.046727+00:00; elapsed: 0.018977s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)
runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: non-int primitive argument
  hint: try the interpreter oracle or reduce this source to a smaller report
```

## 16. resume-lambda / ['--interpreter', '--print-roots', '/tmp/audit5/resume-lambda.yu']

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> (\r -> add 100 r)(k 7)
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/resume-lambda.yu
```
UTC: 2026-11-08T15:00:25.065799+00:00; elapsed: 0.016585s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
runtime error [yulang.runtime-type]: expected int, got <thunk>
  hint: check the value passed to this operation
```
