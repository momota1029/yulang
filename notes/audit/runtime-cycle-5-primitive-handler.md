# Cycle 5 raw runtime: primitive-handler

旧Y2 d4c8bc8fc。各10秒上限。ソース・コマンド・出力はそのまま。解釈はcycle-5.md。

## 1. 42-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/42-direct.yu
```
UTC: 2026-11-08T14:59:39.875163+00:00; elapsed: 0.013059s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 2. 42-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/42-direct.yu
```
UTC: 2026-11-08T14:59:39.888411+00:00; elapsed: 0.013934s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> ((m2 100) (d7 7)), d8 -> d8
m1 = d4 : int -> int
  \d9 -> 42
m2 = d0 : int -> int -> int
  <prim int_add>
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 3. 42-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/42-direct.yu
```
UTC: 2026-11-08T14:59:39.903307+00:00; elapsed: 0.015955s; exit: 1

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

## 4. 42-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/42-direct.yu
```
UTC: 2026-11-08T14:59:39.919521+00:00; elapsed: 0.021519s; exit: 1

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

## 5. 42-higher

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/42-higher.yu
```
UTC: 2026-11-08T14:59:39.941315+00:00; elapsed: 0.010218s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 6. 42-higher

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/42-higher.yu
```
UTC: 2026-11-08T14:59:39.951770+00:00; elapsed: 0.013619s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> ((m3 100) (d7 7)), d8 -> d8
m1 = d5 : (thunk[[ping], int] -> int) -> int
  \d10 -> (d10 (<effect-op ping::get> ()))
m2 = d4 : thunk[[ping], int] -> int
  \d9 -> 42
m3 = d0 : int -> int -> int
  <prim int_add>
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 7. 42-higher

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/42-higher.yu
```
UTC: 2026-11-08T14:59:39.965681+00:00; elapsed: 0.012577s; exit: 0

stdout:
```text
run roots [42]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)
```

## 8. 42-higher

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/42-higher.yu
```
UTC: 2026-11-08T14:59:39.978508+00:00; elapsed: 0.011799s; exit: 0

stdout:
```text
run roots [42]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 9. 42-eta

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/42-eta.yu
```
UTC: 2026-11-08T14:59:39.990571+00:00; elapsed: 0.011450s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 10. 42-eta

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/42-eta.yu
```
UTC: 2026-11-08T14:59:40.002255+00:00; elapsed: 0.013386s; exit: 0

stdout:
```text
mono roots [(m0 (m1 \d12 -> make-thunk[int ! [ping] => thunk[[ping], int]]((m2 force-thunk[thunk[[ping], int] => int ! [ping]](d12)))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> ((m3 100) (d7 7)), d8 -> d8
m1 = d5 : (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]
  \d10 -> (d10 (<effect-op ping::get> ()))
m2 = d4 : int -> int
  \d9 -> 42
m3 = d0 : int -> int -> int
  <prim int_add>
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 11. 42-eta

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/42-eta.yu
```
UTC: 2026-11-08T14:59:40.016072+00:00; elapsed: 0.014568s; exit: 1

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

## 12. 42-eta

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/42-eta.yu
```
UTC: 2026-11-08T14:59:40.030929+00:00; elapsed: 0.013109s; exit: 1

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

## 13. x-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/x-direct.yu
```
UTC: 2026-11-08T14:59:40.044558+00:00; elapsed: 0.012557s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 14. x-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/x-direct.yu
```
UTC: 2026-11-08T14:59:40.057874+00:00; elapsed: 0.015073s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> ((m2 100) (d7 7)), d8 -> d8
m1 = d4 : int -> int
  \d9 -> d9
m2 = d0 : int -> int -> int
  <prim int_add>
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 15. x-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/x-direct.yu
```
UTC: 2026-11-08T14:59:40.073693+00:00; elapsed: 0.012877s; exit: 1

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

## 16. x-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/x-direct.yu
```
UTC: 2026-11-08T14:59:40.087040+00:00; elapsed: 0.011250s; exit: 1

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

## 17. x-higher

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/x-higher.yu
```
UTC: 2026-11-08T14:59:40.098649+00:00; elapsed: 0.010843s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 18. x-higher

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/x-higher.yu
```
UTC: 2026-11-08T14:59:40.109903+00:00; elapsed: 0.011722s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> ((m3 100) (d7 7)), d8 -> d8
m1 = d5 : (thunk[[ping], int] -> int) -> int
  \d10 -> (d10 (<effect-op ping::get> ()))
m2 = d4 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d9 -> d9)
m3 = d0 : int -> int -> int
  <prim int_add>
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 19. x-higher

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/x-higher.yu
```
UTC: 2026-11-08T14:59:40.122029+00:00; elapsed: 0.018387s; exit: 1

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

## 20. x-higher

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/x-higher.yu
```
UTC: 2026-11-08T14:59:40.140873+00:00; elapsed: 0.013829s; exit: 1

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

## 21. x-eta

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/x-eta.yu
```
UTC: 2026-11-08T14:59:40.155364+00:00; elapsed: 0.013127s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 22. x-eta

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/x-eta.yu
```
UTC: 2026-11-08T14:59:40.169290+00:00; elapsed: 0.014257s; exit: 0

stdout:
```text
mono roots [(m0 (m1 \d12 -> make-thunk[int ! [ping] => thunk[[ping], int]]((m2 force-thunk[thunk[[ping], int] => int ! [ping]](d12)))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> ((m3 100) (d7 7)), d8 -> d8
m1 = d5 : (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]
  \d10 -> (d10 (<effect-op ping::get> ()))
m2 = d4 : int -> int
  \d9 -> d9
m3 = d0 : int -> int -> int
  <prim int_add>
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 23. x-eta

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/x-eta.yu
```
UTC: 2026-11-08T14:59:40.183958+00:00; elapsed: 0.013247s; exit: 1

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

## 24. x-eta

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/x-eta.yu
```
UTC: 2026-11-08T14:59:40.197731+00:00; elapsed: 0.012207s; exit: 1

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

## 25. xplusx-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/xplusx-direct.yu
```
UTC: 2026-11-08T14:59:40.210366+00:00; elapsed: 0.013253s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 26. xplusx-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/xplusx-direct.yu
```
UTC: 2026-11-08T14:59:40.224018+00:00; elapsed: 0.013273s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> ((m2 100) (d7 7)), d8 -> d8
m1 = d4 : int -> int
  \d9 -> ((m2 d9) d9)
m2 = d0 : int -> int -> int
  <prim int_add>
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 27. xplusx-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/xplusx-direct.yu
```
UTC: 2026-11-08T14:59:40.237814+00:00; elapsed: 0.016824s; exit: 1

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

## 28. xplusx-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/xplusx-direct.yu
```
UTC: 2026-11-08T14:59:40.255149+00:00; elapsed: 0.015081s; exit: 1

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

## 29. xplusx-higher

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/xplusx-higher.yu
```
UTC: 2026-11-08T14:59:40.270757+00:00; elapsed: 0.013058s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 30. xplusx-higher

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/xplusx-higher.yu
```
UTC: 2026-11-08T14:59:40.284352+00:00; elapsed: 0.016316s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
conflicting type candidates: [ping] vs []
```

## 31. xplusx-higher

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/xplusx-higher.yu
```
UTC: 2026-11-08T14:59:40.301200+00:00; elapsed: 0.022073s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
conflicting type candidates: [ping] vs []
```

## 32. xplusx-higher

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/xplusx-higher.yu
```
UTC: 2026-11-08T14:59:40.323894+00:00; elapsed: 0.012584s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
conflicting type candidates: [ping] vs []
```

## 33. xplusx-eta

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/xplusx-eta.yu
```
UTC: 2026-11-08T14:59:40.337453+00:00; elapsed: 0.013550s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 34. xplusx-eta

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/xplusx-eta.yu
```
UTC: 2026-11-08T14:59:40.351566+00:00; elapsed: 0.014827s; exit: 0

stdout:
```text
mono roots [(m0 (m1 \d12 -> make-thunk[int ! [ping] => thunk[[ping], int]]((m2 force-thunk[thunk[[ping], int] => int ! [ping]](d12)))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> ((m3 100) (d7 7)), d8 -> d8
m1 = d5 : (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]
  \d10 -> (d10 (<effect-op ping::get> ()))
m2 = d4 : int -> int
  \d9 -> ((m3 d9) d9)
m3 = d0 : int -> int -> int
  <prim int_add>
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 35. xplusx-eta

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/xplusx-eta.yu
```
UTC: 2026-11-08T14:59:40.366977+00:00; elapsed: 0.015193s; exit: 1

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

## 36. xplusx-eta

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> 100 + k 7
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/xplusx-eta.yu
```
UTC: 2026-11-08T14:59:40.382742+00:00; elapsed: 0.016010s; exit: 1

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
