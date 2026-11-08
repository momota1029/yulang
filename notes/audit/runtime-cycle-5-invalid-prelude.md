# Cycle 5 raw runtime: invalid-prelude

旧Y2 d4c8bc8fc。各10秒上限。ソース・コマンド・出力はそのまま。解釈はcycle-5.md。

## 1. 42-direct

```yulang
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
UTC: 2026-11-08T14:57:52.228793+00:00; elapsed: 0.012556s; exit: 1

stdout:
```text
diagnostics:
  error [yulang.unresolved-value]: handle: unresolved value name: #op:infix:+
    --> line 4, column 27
    4 |     ping::get(), k -> 100 + k 7
      |                           ^
    hint: define `#op:infix:+` before this use, or import the module that provides it
```

stderr:
```text
```

## 2. 42-direct

```yulang
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
UTC: 2026-11-08T14:57:52.241726+00:00; elapsed: 0.007277s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 3. 42-direct

```yulang
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
UTC: 2026-11-08T14:57:52.249450+00:00; elapsed: 0.008559s; exit: 1

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
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 4. 42-direct

```yulang
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
UTC: 2026-11-08T14:57:52.258419+00:00; elapsed: 0.007308s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 5. 42-higher

```yulang
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
UTC: 2026-11-08T14:57:52.265979+00:00; elapsed: 0.005410s; exit: 1

stdout:
```text
diagnostics:
  error [yulang.unresolved-value]: handle: unresolved value name: #op:infix:+
    --> line 4, column 27
    4 |     ping::get(), k -> 100 + k 7
      |                           ^
    hint: define `#op:infix:+` before this use, or import the module that provides it
```

stderr:
```text
```

## 6. 42-higher

```yulang
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
UTC: 2026-11-08T14:57:52.271696+00:00; elapsed: 0.005841s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 7. 42-higher

```yulang
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
UTC: 2026-11-08T14:57:52.277934+00:00; elapsed: 0.007366s; exit: 1

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
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 8. 42-higher

```yulang
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
UTC: 2026-11-08T14:57:52.285646+00:00; elapsed: 0.006787s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 9. 42-eta

```yulang
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
UTC: 2026-11-08T14:57:52.292973+00:00; elapsed: 0.005582s; exit: 1

stdout:
```text
diagnostics:
  error [yulang.unresolved-value]: handle: unresolved value name: #op:infix:+
    --> line 4, column 27
    4 |     ping::get(), k -> 100 + k 7
      |                           ^
    hint: define `#op:infix:+` before this use, or import the module that provides it
```

stderr:
```text
```

## 10. 42-eta

```yulang
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
UTC: 2026-11-08T14:57:52.298830+00:00; elapsed: 0.005445s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 11. 42-eta

```yulang
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
UTC: 2026-11-08T14:57:52.304675+00:00; elapsed: 0.009035s; exit: 1

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
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 12. 42-eta

```yulang
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
UTC: 2026-11-08T14:57:52.314318+00:00; elapsed: 0.007172s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 13. x-direct

```yulang
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
UTC: 2026-11-08T14:57:52.321893+00:00; elapsed: 0.005002s; exit: 1

stdout:
```text
diagnostics:
  error [yulang.unresolved-value]: handle: unresolved value name: #op:infix:+
    --> line 4, column 27
    4 |     ping::get(), k -> 100 + k 7
      |                           ^
    hint: define `#op:infix:+` before this use, or import the module that provides it
```

stderr:
```text
```

## 14. x-direct

```yulang
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
UTC: 2026-11-08T14:57:52.327215+00:00; elapsed: 0.005727s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 15. x-direct

```yulang
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
UTC: 2026-11-08T14:57:52.333496+00:00; elapsed: 0.009396s; exit: 1

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
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 16. x-direct

```yulang
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
UTC: 2026-11-08T14:57:52.343506+00:00; elapsed: 0.007727s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 17. x-higher

```yulang
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
UTC: 2026-11-08T14:57:52.351905+00:00; elapsed: 0.006228s; exit: 1

stdout:
```text
diagnostics:
  error [yulang.unresolved-value]: handle: unresolved value name: #op:infix:+
    --> line 4, column 27
    4 |     ping::get(), k -> 100 + k 7
      |                           ^
    hint: define `#op:infix:+` before this use, or import the module that provides it
```

stderr:
```text
```

## 18. x-higher

```yulang
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
UTC: 2026-11-08T14:57:52.358534+00:00; elapsed: 0.006761s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 19. x-higher

```yulang
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
UTC: 2026-11-08T14:57:52.365955+00:00; elapsed: 0.007438s; exit: 1

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
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 20. x-higher

```yulang
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
UTC: 2026-11-08T14:57:52.373765+00:00; elapsed: 0.005512s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 21. x-eta

```yulang
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
UTC: 2026-11-08T14:57:52.379868+00:00; elapsed: 0.007350s; exit: 1

stdout:
```text
diagnostics:
  error [yulang.unresolved-value]: handle: unresolved value name: #op:infix:+
    --> line 4, column 27
    4 |     ping::get(), k -> 100 + k 7
      |                           ^
    hint: define `#op:infix:+` before this use, or import the module that provides it
```

stderr:
```text
```

## 22. x-eta

```yulang
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
UTC: 2026-11-08T14:57:52.387648+00:00; elapsed: 0.006198s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 23. x-eta

```yulang
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
UTC: 2026-11-08T14:57:52.394389+00:00; elapsed: 0.010932s; exit: 1

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
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 24. x-eta

```yulang
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
UTC: 2026-11-08T14:57:52.405931+00:00; elapsed: 0.006686s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 25. xplusx-direct

```yulang
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
UTC: 2026-11-08T14:57:52.413269+00:00; elapsed: 0.006230s; exit: 1

stdout:
```text
diagnostics:
  error [yulang.unresolved-value]: handle: unresolved value name: #op:infix:+
    --> line 4, column 27
    4 |     ping::get(), k -> 100 + k 7
      |                           ^
    hint: define `#op:infix:+` before this use, or import the module that provides it
  error [yulang.unresolved-value]: actual: unresolved value name: #op:infix:+
    --> line 6, column 27
    6 | our actual(x:int):int = x + x
      |                           ^
    hint: define `#op:infix:+` before this use, or import the module that provides it
```

stderr:
```text
```

## 26. xplusx-direct

```yulang
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
UTC: 2026-11-08T14:57:52.419983+00:00; elapsed: 0.007943s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 27. xplusx-direct

```yulang
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
UTC: 2026-11-08T14:57:52.428376+00:00; elapsed: 0.007219s; exit: 1

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
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 28. xplusx-direct

```yulang
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
UTC: 2026-11-08T14:57:52.436179+00:00; elapsed: 0.005956s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 29. xplusx-higher

```yulang
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
UTC: 2026-11-08T14:57:52.442663+00:00; elapsed: 0.004609s; exit: 1

stdout:
```text
diagnostics:
  error [yulang.unresolved-value]: handle: unresolved value name: #op:infix:+
    --> line 4, column 27
    4 |     ping::get(), k -> 100 + k 7
      |                           ^
    hint: define `#op:infix:+` before this use, or import the module that provides it
  error [yulang.unresolved-value]: actual: unresolved value name: #op:infix:+
    --> line 6, column 27
    6 | our actual(x:int):int = x + x
      |                           ^
    hint: define `#op:infix:+` before this use, or import the module that provides it
```

stderr:
```text
```

## 30. xplusx-higher

```yulang
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
UTC: 2026-11-08T14:57:52.448213+00:00; elapsed: 0.005534s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 31. xplusx-higher

```yulang
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
UTC: 2026-11-08T14:57:52.454217+00:00; elapsed: 0.007924s; exit: 1

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
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 32. xplusx-higher

```yulang
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
UTC: 2026-11-08T14:57:52.462845+00:00; elapsed: 0.006296s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 33. xplusx-eta

```yulang
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
UTC: 2026-11-08T14:57:52.469884+00:00; elapsed: 0.005236s; exit: 1

stdout:
```text
diagnostics:
  error [yulang.unresolved-value]: handle: unresolved value name: #op:infix:+
    --> line 4, column 27
    4 |     ping::get(), k -> 100 + k 7
      |                           ^
    hint: define `#op:infix:+` before this use, or import the module that provides it
  error [yulang.unresolved-value]: actual: unresolved value name: #op:infix:+
    --> line 6, column 27
    6 | our actual(x:int):int = x + x
      |                           ^
    hint: define `#op:infix:+` before this use, or import the module that provides it
```

stderr:
```text
```

## 34. xplusx-eta

```yulang
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
UTC: 2026-11-08T14:57:52.475737+00:00; elapsed: 0.005485s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 35. xplusx-eta

```yulang
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
UTC: 2026-11-08T14:57:52.482071+00:00; elapsed: 0.008969s; exit: 1

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
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```

## 36. xplusx-eta

```yulang
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
UTC: 2026-11-08T14:57:52.491696+00:00; elapsed: 0.007413s; exit: 1

stdout:
```text
```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: #op:infix:+
  detail: unresolved value name: #op:infix:+
  hint: run `yulang check` to see source ranges before running
```
