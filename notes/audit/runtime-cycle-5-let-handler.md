# Cycle 5 raw runtime: let-handler

旧Y2 d4c8bc8fc。各10秒上限。ソース・コマンド・出力はそのまま。解釈はcycle-5.md。

## 1. 42-direct

```yulang
our infix (+) 5.0.0 5.0.1 = builtin_op::int_add
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/42-direct.yu
```
UTC: 2026-11-08T14:59:56.021769+00:00; elapsed: 0.012770s; exit: 0

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/42-direct.yu
```
UTC: 2026-11-08T14:59:56.034785+00:00; elapsed: 0.012675s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> { my d8 = (d7 7); ((m2 100) d8) }, d9 -> d9
m1 = d4 : int -> int
  \d10 -> 42
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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/42-direct.yu
```
UTC: 2026-11-08T14:59:56.047674+00:00; elapsed: 0.012798s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/42-direct.yu
```
UTC: 2026-11-08T14:59:56.060717+00:00; elapsed: 0.012885s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/42-higher.yu
```
UTC: 2026-11-08T14:59:56.074180+00:00; elapsed: 0.011222s; exit: 0

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/42-higher.yu
```
UTC: 2026-11-08T14:59:56.085644+00:00; elapsed: 0.011492s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> { my d8 = (d7 7); ((m3 100) d8) }, d9 -> d9
m1 = d5 : (thunk[[ping], int] -> int) -> int
  \d11 -> (d11 (<effect-op ping::get> ()))
m2 = d4 : thunk[[ping], int] -> int
  \d10 -> 42
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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/42-higher.yu
```
UTC: 2026-11-08T14:59:56.097579+00:00; elapsed: 0.012668s; exit: 0

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/42-higher.yu
```
UTC: 2026-11-08T14:59:56.110460+00:00; elapsed: 0.011824s; exit: 0

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/42-eta.yu
```
UTC: 2026-11-08T14:59:56.122549+00:00; elapsed: 0.012239s; exit: 0

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/42-eta.yu
```
UTC: 2026-11-08T14:59:56.135011+00:00; elapsed: 0.012781s; exit: 0

stdout:
```text
mono roots [(m0 (m1 \d13 -> make-thunk[int ! [ping] => thunk[[ping], int]]((m2 force-thunk[thunk[[ping], int] => int ! [ping]](d13)))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> { my d8 = (d7 7); ((m3 100) d8) }, d9 -> d9
m1 = d5 : (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]
  \d11 -> (d11 (<effect-op ping::get> ()))
m2 = d4 : int -> int
  \d10 -> 42
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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/42-eta.yu
```
UTC: 2026-11-08T14:59:56.148334+00:00; elapsed: 0.013349s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/42-eta.yu
```
UTC: 2026-11-08T14:59:56.161946+00:00; elapsed: 0.013210s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/x-direct.yu
```
UTC: 2026-11-08T14:59:56.175454+00:00; elapsed: 0.013544s; exit: 0

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/x-direct.yu
```
UTC: 2026-11-08T14:59:56.189269+00:00; elapsed: 0.012465s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> { my d8 = (d7 7); ((m2 100) d8) }, d9 -> d9
m1 = d4 : int -> int
  \d10 -> d10
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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/x-direct.yu
```
UTC: 2026-11-08T14:59:56.202034+00:00; elapsed: 0.013995s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/x-direct.yu
```
UTC: 2026-11-08T14:59:56.216349+00:00; elapsed: 0.011893s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/x-higher.yu
```
UTC: 2026-11-08T14:59:56.228701+00:00; elapsed: 0.010549s; exit: 0

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/x-higher.yu
```
UTC: 2026-11-08T14:59:56.239556+00:00; elapsed: 0.012405s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> { my d8 = (d7 7); ((m3 100) d8) }, d9 -> d9
m1 = d5 : (thunk[[ping], int] -> int) -> int
  \d11 -> (d11 (<effect-op ping::get> ()))
m2 = d4 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d10 -> d10)
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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/x-higher.yu
```
UTC: 2026-11-08T14:59:56.252276+00:00; elapsed: 0.012221s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/x-higher.yu
```
UTC: 2026-11-08T14:59:56.264862+00:00; elapsed: 0.013783s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/x-eta.yu
```
UTC: 2026-11-08T14:59:56.279012+00:00; elapsed: 0.012620s; exit: 0

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/x-eta.yu
```
UTC: 2026-11-08T14:59:56.291983+00:00; elapsed: 0.016568s; exit: 0

stdout:
```text
mono roots [(m0 (m1 \d13 -> make-thunk[int ! [ping] => thunk[[ping], int]]((m2 force-thunk[thunk[[ping], int] => int ! [ping]](d13)))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> { my d8 = (d7 7); ((m3 100) d8) }, d9 -> d9
m1 = d5 : (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]
  \d11 -> (d11 (<effect-op ping::get> ()))
m2 = d4 : int -> int
  \d10 -> d10
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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/x-eta.yu
```
UTC: 2026-11-08T14:59:56.308960+00:00; elapsed: 0.014022s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/x-eta.yu
```
UTC: 2026-11-08T14:59:56.323372+00:00; elapsed: 0.014098s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/xplusx-direct.yu
```
UTC: 2026-11-08T14:59:56.337937+00:00; elapsed: 0.012516s; exit: 0

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/xplusx-direct.yu
```
UTC: 2026-11-08T14:59:56.351229+00:00; elapsed: 0.013852s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> { my d8 = (d7 7); ((m2 100) d8) }, d9 -> d9
m1 = d4 : int -> int
  \d10 -> ((m2 d10) d10)
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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/xplusx-direct.yu
```
UTC: 2026-11-08T14:59:56.365792+00:00; elapsed: 0.014535s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/xplusx-direct.yu
```
UTC: 2026-11-08T14:59:56.381006+00:00; elapsed: 0.014481s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/xplusx-higher.yu
```
UTC: 2026-11-08T14:59:56.396161+00:00; elapsed: 0.012052s; exit: 0

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/xplusx-higher.yu
```
UTC: 2026-11-08T14:59:56.408851+00:00; elapsed: 0.011562s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/xplusx-higher.yu
```
UTC: 2026-11-08T14:59:56.421102+00:00; elapsed: 0.022749s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/xplusx-higher.yu
```
UTC: 2026-11-08T14:59:56.444349+00:00; elapsed: 0.012394s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/xplusx-eta.yu
```
UTC: 2026-11-08T14:59:56.457241+00:00; elapsed: 0.012974s; exit: 0

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/xplusx-eta.yu
```
UTC: 2026-11-08T14:59:56.470998+00:00; elapsed: 0.016298s; exit: 0

stdout:
```text
mono roots [(m0 (m1 \d13 -> make-thunk[int ! [ping] => thunk[[ping], int]]((m2 force-thunk[thunk[[ping], int] => int ! [ping]](d13)))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> { my d8 = (d7 7); ((m3 100) d8) }, d9 -> d9
m1 = d5 : (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]
  \d11 -> (d11 (<effect-op ping::get> ()))
m2 = d4 : int -> int
  \d10 -> ((m3 d10) d10)
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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/xplusx-eta.yu
```
UTC: 2026-11-08T14:59:56.487855+00:00; elapsed: 0.015588s; exit: 1

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
    ping::get(), k ->
        my r: int = k 7
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/xplusx-eta.yu
```
UTC: 2026-11-08T14:59:56.504014+00:00; elapsed: 0.015110s; exit: 1

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
