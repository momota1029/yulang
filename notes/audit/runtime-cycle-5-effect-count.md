# Cycle 5 raw runtime: effect-count

旧Y2 d4c8bc8fc。各10秒上限。ソース・コマンド・出力はそのまま。解釈はcycle-5.md。

## 1. 42-direct

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/42-direct.yu
```
UTC: 2026-11-08T15:01:59.305550+00:00; elapsed: 0.029684s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 2. 42-direct

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/42-direct.yu
```
UTC: 2026-11-08T15:01:59.335481+00:00; elapsed: 0.027126s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())))))]
m0 = d3 : thunk[[ping], int] -> int
  \d8 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d8)): ping::get _, d9 -> { my d10 = (m0 make-thunk[int ! [] => thunk[[ping], int]]((d9 7))); ((m2 100) d10) }, d11 -> d11
m1 = d4 : int -> int
  \d12 -> 42
m2 = d0 : int -> int -> int
  \d6 -> \d7 -> ((<prim int_add> d6) d7)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 3. 42-direct

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/42-direct.yu
```
UTC: 2026-11-08T15:01:59.362899+00:00; elapsed: 0.028965s; exit: 0

stdout:
```text
run roots [142]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)
```

## 4. 42-direct

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/42-direct.yu
```
UTC: 2026-11-08T15:01:59.392207+00:00; elapsed: 0.029177s; exit: 0

stdout:
```text
run roots [142]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 5. 42-higher

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/42-higher.yu
```
UTC: 2026-11-08T15:01:59.421709+00:00; elapsed: 0.026791s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 6. 42-higher

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/42-higher.yu
```
UTC: 2026-11-08T15:01:59.448778+00:00; elapsed: 0.038184s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d3 : thunk[[ping], int] -> int
  \d8 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d8)): ping::get _, d9 -> { my d10 = (m0 make-thunk[int ! [] => thunk[[ping], int]]((d9 7))); ((m3 100) d10) }, d11 -> d11
m1 = d5 : (thunk[[ping], int] -> int) -> int
  \d13 -> (d13 (<effect-op ping::get> ()))
m2 = d4 : thunk[[ping], int] -> int
  \d12 -> 42
m3 = d0 : int -> int -> int
  \d6 -> \d7 -> ((<prim int_add> d6) d7)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 7. 42-higher

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/42-higher.yu
```
UTC: 2026-11-08T15:01:59.487495+00:00; elapsed: 0.038854s; exit: 0

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
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/42-higher.yu
```
UTC: 2026-11-08T15:01:59.526896+00:00; elapsed: 0.033009s; exit: 0

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
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/42-eta.yu
```
UTC: 2026-11-08T15:01:59.560247+00:00; elapsed: 0.044281s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 10. 42-eta

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/42-eta.yu
```
UTC: 2026-11-08T15:01:59.604910+00:00; elapsed: 0.041374s; exit: 0

stdout:
```text
mono roots [(m0 (m1 \d15 -> make-thunk[int ! [ping] => thunk[[ping], int]]((m2 force-thunk[thunk[[ping], int] => int ! [ping]](d15)))))]
m0 = d3 : thunk[[ping], int] -> int
  \d8 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d8)): ping::get _, d9 -> { my d10 = (m0 make-thunk[int ! [] => thunk[[ping], int]]((d9 7))); ((m3 100) d10) }, d11 -> d11
m1 = d5 : (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]
  \d13 -> (d13 (<effect-op ping::get> ()))
m2 = d4 : int -> int
  \d12 -> 42
m3 = d0 : int -> int -> int
  \d6 -> \d7 -> ((<prim int_add> d6) d7)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 11. 42-eta

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/42-eta.yu
```
UTC: 2026-11-08T15:01:59.646750+00:00; elapsed: 0.034848s; exit: 0

stdout:
```text
run roots [142]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)
```

## 12. 42-eta

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = 42
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/42-eta.yu
```
UTC: 2026-11-08T15:01:59.682704+00:00; elapsed: 0.036610s; exit: 0

stdout:
```text
run roots [142]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 13. x-direct

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/x-direct.yu
```
UTC: 2026-11-08T15:01:59.720455+00:00; elapsed: 0.041631s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 14. x-direct

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/x-direct.yu
```
UTC: 2026-11-08T15:01:59.762463+00:00; elapsed: 0.034290s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())))))]
m0 = d3 : thunk[[ping], int] -> int
  \d8 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d8)): ping::get _, d9 -> { my d10 = (m0 make-thunk[int ! [] => thunk[[ping], int]]((d9 7))); ((m2 100) d10) }, d11 -> d11
m1 = d4 : int -> int
  \d12 -> d12
m2 = d0 : int -> int -> int
  \d6 -> \d7 -> ((<prim int_add> d6) d7)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 15. x-direct

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/x-direct.yu
```
UTC: 2026-11-08T15:01:59.797132+00:00; elapsed: 0.046840s; exit: 0

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

## 16. x-direct

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/x-direct.yu
```
UTC: 2026-11-08T15:01:59.844632+00:00; elapsed: 0.037741s; exit: 0

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

## 17. x-higher

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/x-higher.yu
```
UTC: 2026-11-08T15:01:59.882923+00:00; elapsed: 0.034429s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 18. x-higher

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/x-higher.yu
```
UTC: 2026-11-08T15:01:59.917851+00:00; elapsed: 0.031216s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d3 : thunk[[ping], int] -> int
  \d8 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d8)): ping::get _, d9 -> { my d10 = (m0 make-thunk[int ! [] => thunk[[ping], int]]((d9 7))); ((m3 100) d10) }, d11 -> d11
m1 = d5 : (thunk[[ping], int] -> int) -> int
  \d13 -> (d13 (<effect-op ping::get> ()))
m2 = d4 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d12 -> d12)
m3 = d0 : int -> int -> int
  \d6 -> \d7 -> ((<prim int_add> d6) d7)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 19. x-higher

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/x-higher.yu
```
UTC: 2026-11-08T15:01:59.949534+00:00; elapsed: 0.030968s; exit: 0

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

## 20. x-higher

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/x-higher.yu
```
UTC: 2026-11-08T15:01:59.981266+00:00; elapsed: 0.031107s; exit: 0

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

## 21. x-eta

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/x-eta.yu
```
UTC: 2026-11-08T15:02:00.012922+00:00; elapsed: 0.027952s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 22. x-eta

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/x-eta.yu
```
UTC: 2026-11-08T15:02:00.041286+00:00; elapsed: 0.029796s; exit: 0

stdout:
```text
mono roots [(m0 (m1 \d15 -> make-thunk[int ! [ping] => thunk[[ping], int]]((m2 force-thunk[thunk[[ping], int] => int ! [ping]](d15)))))]
m0 = d3 : thunk[[ping], int] -> int
  \d8 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d8)): ping::get _, d9 -> { my d10 = (m0 make-thunk[int ! [] => thunk[[ping], int]]((d9 7))); ((m3 100) d10) }, d11 -> d11
m1 = d5 : (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]
  \d13 -> (d13 (<effect-op ping::get> ()))
m2 = d4 : int -> int
  \d12 -> d12
m3 = d0 : int -> int -> int
  \d6 -> \d7 -> ((<prim int_add> d6) d7)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 23. x-eta

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/x-eta.yu
```
UTC: 2026-11-08T15:02:00.072302+00:00; elapsed: 0.038623s; exit: 0

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

## 24. x-eta

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/x-eta.yu
```
UTC: 2026-11-08T15:02:00.113173+00:00; elapsed: 0.033983s; exit: 0

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

## 25. xplusx-direct

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/xplusx-direct.yu
```
UTC: 2026-11-08T15:02:00.149347+00:00; elapsed: 0.054817s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 26. xplusx-direct

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/xplusx-direct.yu
```
UTC: 2026-11-08T15:02:00.205161+00:00; elapsed: 0.036038s; exit: 0

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())))))]
m0 = d3 : thunk[[ping], int] -> int
  \d8 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d8)): ping::get _, d9 -> { my d10 = (m0 make-thunk[int ! [] => thunk[[ping], int]]((d9 7))); ((m2 100) d10) }, d11 -> d11
m1 = d4 : int -> int
  \d12 -> ((m2 d12) d12)
m2 = d0 : int -> int -> int
  \d6 -> \d7 -> ((<prim int_add> d6) d7)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 27. xplusx-direct

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/xplusx-direct.yu
```
UTC: 2026-11-08T15:02:00.241721+00:00; elapsed: 0.035242s; exit: 0

stdout:
```text
run roots [114]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)
```

## 28. xplusx-direct

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(actual(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/xplusx-direct.yu
```
UTC: 2026-11-08T15:02:00.277779+00:00; elapsed: 0.036724s; exit: 0

stdout:
```text
run roots [114]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 29. xplusx-higher

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/xplusx-higher.yu
```
UTC: 2026-11-08T15:02:00.315353+00:00; elapsed: 0.029053s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 30. xplusx-higher

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/xplusx-higher.yu
```
UTC: 2026-11-08T15:02:00.345149+00:00; elapsed: 0.030986s; exit: 1

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
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/xplusx-higher.yu
```
UTC: 2026-11-08T15:02:00.376855+00:00; elapsed: 0.070198s; exit: 1

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
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher actual)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/xplusx-higher.yu
```
UTC: 2026-11-08T15:02:00.447898+00:00; elapsed: 0.051075s; exit: 1

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
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/xplusx-eta.yu
```
UTC: 2026-11-08T15:02:00.499651+00:00; elapsed: 0.036330s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 34. xplusx-eta

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/xplusx-eta.yu
```
UTC: 2026-11-08T15:02:00.536825+00:00; elapsed: 0.028947s; exit: 0

stdout:
```text
mono roots [(m0 (m1 \d15 -> make-thunk[int ! [ping] => thunk[[ping], int]]((m2 force-thunk[thunk[[ping], int] => int ! [ping]](d15)))))]
m0 = d3 : thunk[[ping], int] -> int
  \d8 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d8)): ping::get _, d9 -> { my d10 = (m0 make-thunk[int ! [] => thunk[[ping], int]]((d9 7))); ((m3 100) d10) }, d11 -> d11
m1 = d5 : (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]
  \d13 -> (d13 (<effect-op ping::get> ()))
m2 = d4 : int -> int
  \d12 -> ((m3 d12) d12)
m3 = d0 : int -> int -> int
  \d6 -> \d7 -> ((<prim int_add> d6) d7)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 35. xplusx-eta

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/xplusx-eta.yu
```
UTC: 2026-11-08T15:02:00.566447+00:00; elapsed: 0.027485s; exit: 0

stdout:
```text
run roots [114]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)
```

## 36. xplusx-eta

```yulang
our infix (+) 5.0.0 5.0.1 = \x -> \y -> builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k ->
        my r: int = handle(k 7)
        100 + r
    value -> value
our actual(x:int):int = x + x
our higher f=f(ping::get())
handle(higher(\x -> actual x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/xplusx-eta.yu
```
UTC: 2026-11-08T15:02:00.594531+00:00; elapsed: 0.026018s; exit: 0

stdout:
```text
run roots [114]
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```
