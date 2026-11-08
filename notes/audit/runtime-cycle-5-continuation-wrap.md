# Cycle 5 raw runtime: continuation-wrap

旧Y2 d4c8bc8fc。各10秒上限。ソース・コマンド・出力はそのまま。解釈はcycle-5.md。

## 1. wrapped

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 (handle(k 7))
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/wrapped.yu
```
UTC: 2026-11-08T15:01:38.481234+00:00; elapsed: 0.040653s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 2. wrapped

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 (handle(k 7))
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/wrapped.yu
```
UTC: 2026-11-08T15:01:38.522036+00:00; elapsed: 0.040622s; exit: 0

stdout:
```text
mono roots [(m0 (<effect-op ping::get> ()))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> ((m1 100) (m0 make-thunk[int ! [] => thunk[[ping], int]]((d7 7)))), d8 -> d8
m1 = d0 : int -> int -> int
  \d4 -> \d5 -> ((<prim int_add> d4) d5)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 3. wrapped

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 (handle(k 7))
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/wrapped.yu
```
UTC: 2026-11-08T15:01:38.562758+00:00; elapsed: 0.045471s; exit: 0

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

## 4. wrapped

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 (handle(k 7))
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/wrapped.yu
```
UTC: 2026-11-08T15:01:38.608386+00:00; elapsed: 0.043030s; exit: 0

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

## 5. wrapped-only

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> handle(k 7)
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/wrapped-only.yu
```
UTC: 2026-11-08T15:01:38.651634+00:00; elapsed: 0.020011s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 6. wrapped-only

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> handle(k 7)
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/wrapped-only.yu
```
UTC: 2026-11-08T15:01:38.671730+00:00; elapsed: 0.020471s; exit: 0

stdout:
```text
mono roots [(m0 (<effect-op ping::get> ()))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> (m0 make-thunk[int ! [] => thunk[[ping], int]]((d7 7))), d8 -> d8
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 7. wrapped-only

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> handle(k 7)
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/wrapped-only.yu
```
UTC: 2026-11-08T15:01:38.692294+00:00; elapsed: 0.017493s; exit: 0

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

## 8. wrapped-only

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> handle(k 7)
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/wrapped-only.yu
```
UTC: 2026-11-08T15:01:38.709997+00:00; elapsed: 0.014101s; exit: 0

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

## 9. literal

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 7
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/literal.yu
```
UTC: 2026-11-08T15:01:38.724267+00:00; elapsed: 0.008212s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 10. literal

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 7
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/literal.yu
```
UTC: 2026-11-08T15:01:38.732552+00:00; elapsed: 0.008796s; exit: 0

stdout:
```text
mono roots [(m0 (<effect-op ping::get> ()))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> ((m1 100) 7), d8 -> d8
m1 = d0 : int -> int -> int
  \d4 -> \d5 -> ((<prim int_add> d4) d5)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 11. literal

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 7
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/literal.yu
```
UTC: 2026-11-08T15:01:38.741494+00:00; elapsed: 0.008966s; exit: 0

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

## 12. literal

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 7
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/literal.yu
```
UTC: 2026-11-08T15:01:38.750537+00:00; elapsed: 0.008439s; exit: 0

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

## 13. nested

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 ((\x -> x)(k 7))
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit5/nested.yu
```
UTC: 2026-11-08T15:01:38.759123+00:00; elapsed: 0.017497s; exit: 0

stdout:
```text
```

stderr:
```text
```

## 14. nested

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 ((\x -> x)(k 7))
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit5/nested.yu
```
UTC: 2026-11-08T15:01:38.776708+00:00; elapsed: 0.019267s; exit: 0

stdout:
```text
mono roots [(m0 (<effect-op ping::get> ()))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> ((m1 100) (\d8 -> d8 (d7 7))), d9 -> d9
m1 = d0 : int -> int -> int
  \d4 -> \d5 -> ((<prim int_add> d4) d5)
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
```

## 15. nested

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 ((\x -> x)(k 7))
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit5/nested.yu
```
UTC: 2026-11-08T15:01:38.796063+00:00; elapsed: 0.020964s; exit: 1

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

## 16. nested

```yulang
our add(x:int)(y:int):int = builtin_op::int_add x y
act ping:
    our get: () -> int
our handle(action:[ping] int) = catch action:
    ping::get(), k -> add 100 ((\x -> x)(k 7))
    value -> value
handle(ping::get())
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit5/nested.yu
```
UTC: 2026-11-08T15:01:38.817121+00:00; elapsed: 0.015804s; exit: 1

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
