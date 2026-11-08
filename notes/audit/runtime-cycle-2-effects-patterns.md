# Cycle 2 runtime raw log: X22–X25

基点 Y2 `d4c8bc8fc`。各出力はそのまま。dump の exit 0 は診断なしを意味しない。

## 1. x22-optional-missing / check

```yulang
our read_port(config: {port?: int}): int = case config:
    {port: p} -> p
    _ -> 80
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x22-optional-missing.yu
```

UTC start: 2026-11-08T12:32:59.995319+00:00; elapsed: 0.009 s; exit: 1

```text
diagnostics:
  error [yulang.unsupported-type-syntax]: read_port: unsupported type annotation syntax: record type annotation
    --> line 1, column 23
    1 | our read_port(config: {port?: int}): int = case config:
      |                       ^^^^^^^^^^^^
    hint: use a supported type annotation form and keep effect rows in effect position
```

## 2. x22-optional-missing / dump

```yulang
our read_port(config: {port?: int}): int = case config:
    {port: p} -> p
    _ -> 80
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x22-optional-missing.yu
```

UTC start: 2026-11-08T12:33:00.004973+00:00; elapsed: 0.004 s; exit: 0

```text
roots d0:read_port
d0:read_port: never = <missing>
root exprs e2:(e0:r0:read_port->d0:read_port e1:{})
runtime roots e2:(e0:r0:read_port->d0:read_port e1:{})
error: unsupported type annotation syntax: record type annotation
```

## 3. x22-optional-missing / run

```yulang
our read_port(config: {port?: int}): int = case config:
    {port: p} -> p
    _ -> 80
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x22-optional-missing.yu
```

UTC start: 2026-11-08T12:33:00.009253+00:00; elapsed: 0.004 s; exit: 1

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unsupported type annotation syntax: record type annotation
  hint: run `yulang check` to see source ranges before running
```

## 4. x22-optional-present / check

```yulang
our read_port(config: {port?: int}): int = case config:
    {port: p} -> p
    _ -> 80
read_port {port: 443}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x22-optional-present.yu
```

UTC start: 2026-11-08T12:33:00.013842+00:00; elapsed: 0.003 s; exit: 1

```text
diagnostics:
  error [yulang.unsupported-type-syntax]: read_port: unsupported type annotation syntax: record type annotation
    --> line 1, column 23
    1 | our read_port(config: {port?: int}): int = case config:
      |                       ^^^^^^^^^^^^
    hint: use a supported type annotation form and keep effect rows in effect position
```

## 5. x22-optional-present / dump

```yulang
our read_port(config: {port?: int}): int = case config:
    {port: p} -> p
    _ -> 80
read_port {port: 443}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x22-optional-present.yu
```

UTC start: 2026-11-08T12:33:00.016684+00:00; elapsed: 0.006 s; exit: 0

```text
roots d0:read_port
d0:read_port: never = <missing>
root exprs e3:(e0:r0:read_port->d0:read_port e2:{port: e1:443})
runtime roots e3:(e0:r0:read_port->d0:read_port e2:{port: e1:443})
error: unsupported type annotation syntax: record type annotation
```

## 6. x22-optional-present / run

```yulang
our read_port(config: {port?: int}): int = case config:
    {port: p} -> p
    _ -> 80
read_port {port: 443}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x22-optional-present.yu
```

UTC start: 2026-11-08T12:33:00.022910+00:00; elapsed: 0.003 s; exit: 1

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unsupported type annotation syntax: record type annotation
  hint: run `yulang check` to see source ranges before running
```

## 7. x22-inferred-missing / check

```yulang
our read_port(config) = case config:
    {port: p} -> p
    _ -> 80
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x22-inferred-missing.yu
```

UTC start: 2026-11-08T12:33:00.026556+00:00; elapsed: 0.006 s; exit: 0

```text
```

## 8. x22-inferred-missing / dump

```yulang
our read_port(config) = case config:
    {port: p} -> p
    _ -> 80
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x22-inferred-missing.yu
```

UTC start: 2026-11-08T12:33:00.032256+00:00; elapsed: 0.005 s; exit: 0

```text
roots d0:read_port
d0:read_port: {port: 'a} -> 'a | int = e4:(fn p0:d1:config -> e3:case e0:r0:config->d1:config { p2:{port: p1:d2:p} -> e1:r1:p->d2:p; p3:_ -> e2:80 })
root exprs e7:(e5:r2:read_port->d0:read_port e6:{})
runtime roots e7:(e5:r2:read_port->d0:read_port e6:{})
detached {
  d1:config arg
  d2:p arg
}
```

## 9. x22-inferred-missing / run

```yulang
our read_port(config) = case config:
    {port: p} -> p
    _ -> 80
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x22-inferred-missing.yu
```

UTC start: 2026-11-08T12:33:00.037874+00:00; elapsed: 0.005 s; exit: 1

```text
compile error [yulang.unsatisfied-subtype]: record is missing field `port`
  detail: unsatisfied subtype constraint: {} <: {port: 'open0}
  hint: add `port` to this record or use a value that provides it; actual record has no fields
```

## 10. x22-default-present / check

```yulang
our read_port {port = 80} = port
read_port {port: 443}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x22-default-present.yu
```

UTC start: 2026-11-08T12:33:00.043219+00:00; elapsed: 0.004 s; exit: 0

```text
```

## 11. x22-default-present / dump

```yulang
our read_port {port = 80} = port
read_port {port: 443}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x22-default-present.yu
```

UTC start: 2026-11-08T12:33:00.047033+00:00; elapsed: 0.004 s; exit: 0

```text
roots d0:read_port
d0:read_port: {port?: 'a} -> 'a | int = e2:(fn p1:{port: p0:d1:port = e0:80} -> e1:r0:port->d1:port)
root exprs e6:(e3:r1:read_port->d0:read_port e5:{port: e4:443})
runtime roots e6:(e3:r1:read_port->d0:read_port e5:{port: e4:443})
detached {
  d1:port arg
}
```

## 12. x22-default-present / run

```yulang
our read_port {port = 80} = port
read_port {port: 443}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x22-default-present.yu
```

UTC start: 2026-11-08T12:33:00.051091+00:00; elapsed: 0.004 s; exit: 0

```text
run roots [443]
```

## 13. x22-default-missing / check

```yulang
our read_port {port = 80} = port
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x22-default-missing.yu
```

UTC start: 2026-11-08T12:33:00.055486+00:00; elapsed: 0.004 s; exit: 0

```text
```

## 14. x22-default-missing / dump

```yulang
our read_port {port = 80} = port
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x22-default-missing.yu
```

UTC start: 2026-11-08T12:33:00.059399+00:00; elapsed: 0.004 s; exit: 0

```text
roots d0:read_port
d0:read_port: {port?: 'a} -> 'a | int = e2:(fn p1:{port: p0:d1:port = e0:80} -> e1:r0:port->d1:port)
root exprs e5:(e3:r1:read_port->d0:read_port e4:{})
runtime roots e5:(e3:r1:read_port->d0:read_port e4:{})
detached {
  d1:port arg
}
```

## 15. x22-default-missing / run

```yulang
our read_port {port = 80} = port
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x22-default-missing.yu
```

UTC start: 2026-11-08T12:33:00.063440+00:00; elapsed: 0.003 s; exit: 0

```text
run roots [80]
```

## 16. x23-unreachable-body / check

```yulang
act ping:
    our get: () -> int
our f x = case x:
    _ -> 1
    _ -> ping::get()
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x23-unreachable-body.yu
```

UTC start: 2026-11-08T12:33:00.066952+00:00; elapsed: 0.005 s; exit: 0

```text
```

## 17. x23-unreachable-body / dump

```yulang
act ping:
    our get: () -> int
our f x = case x:
    _ -> 1
    _ -> ping::get()
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x23-unreachable-body.yu
```

UTC start: 2026-11-08T12:33:00.072106+00:00; elapsed: 0.005 s; exit: 0

```text
roots d0:ping d2:f
d0:ping mod {
}
d2:f: any -> [ping] int = e6:(fn p0:d3:x -> e5:case e0:r0:x->d3:x { p1:_ -> e1:1; p2:_ -> e4:(e2:r1:"ping::get"->d1:"ping.get" e3:()) })
root exprs e9:(e7:r2:f->d2:f e8:0)
runtime roots e9:(e7:r2:f->d2:f e8:0)
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:x arg
}
```

## 18. x23-unreachable-body / run

```yulang
act ping:
    our get: () -> int
our f x = case x:
    _ -> 1
    _ -> ping::get()
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x23-unreachable-body.yu
```

UTC start: 2026-11-08T12:33:00.077141+00:00; elapsed: 0.003 s; exit: 0

```text
run roots [1]
```

## 19. x23-unreachable-pure-annotation / check

```yulang
act ping:
    our get: () -> int
our f(x: int): int = case x:
    _ -> 1
    _ -> ping::get()
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x23-unreachable-pure-annotation.yu
```

UTC start: 2026-11-08T12:33:00.080643+00:00; elapsed: 0.005 s; exit: 0

```text
```

## 20. x23-unreachable-pure-annotation / dump

```yulang
act ping:
    our get: () -> int
our f(x: int): int = case x:
    _ -> 1
    _ -> ping::get()
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x23-unreachable-pure-annotation.yu
```

UTC start: 2026-11-08T12:33:00.085916+00:00; elapsed: 0.006 s; exit: 0

```text
roots d0:ping d2:f
d0:ping mod {
}
d2:f: int -> [ping] int = e6:(fn p0:d3:x -> e5:case e0:r0:x->d3:x { p1:_ -> e1:1; p2:_ -> e4:(e2:r1:"ping::get"->d1:"ping.get" e3:()) })
root exprs e9:(e7:r2:f->d2:f e8:0)
runtime roots e9:(e7:r2:f->d2:f e8:0)
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:x arg
}
```

## 21. x23-unreachable-pure-annotation / run

```yulang
act ping:
    our get: () -> int
our f(x: int): int = case x:
    _ -> 1
    _ -> ping::get()
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x23-unreachable-pure-annotation.yu
```

UTC start: 2026-11-08T12:33:00.092048+00:00; elapsed: 0.003 s; exit: 0

```text
run roots [1]
```

## 22. x23-unreachable-guard / check

```yulang
act ping:
    our test: () -> bool
our f x = case x:
    _ -> 1
    _ if ping::test() -> 2
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x23-unreachable-guard.yu
```

UTC start: 2026-11-08T12:33:00.095681+00:00; elapsed: 0.003 s; exit: 1

```text
diagnostics:
  error [yulang.unresolved-value]: f: unresolved value name: std::control::junction::junction::junction
    --> line 3, column 5
    3 | our f x = case x:
      |     ^
    hint: define `std::control::junction::junction::junction` before this use, or import the module that provides it
```

## 23. x23-unreachable-guard / dump

```yulang
act ping:
    our test: () -> bool
our f x = case x:
    _ -> 1
    _ if ping::test() -> 2
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x23-unreachable-guard.yu
```

UTC start: 2026-11-08T12:33:00.099227+00:00; elapsed: 0.003 s; exit: 0

```text
roots d0:ping d2:f
d0:ping mod {
}
d2:f: never = <missing>
root exprs e7:(e5:r2:f->d2:f e6:0)
runtime roots e7:(e5:r2:f->d2:f e6:0)
detached {
  d1:"ping.test": () -> [ping] bool = <missing>
  d3:x arg
}
error: unresolved value name: std::control::junction::junction::junction
```

## 24. x23-unreachable-guard / run

```yulang
act ping:
    our test: () -> bool
our f x = case x:
    _ -> 1
    _ if ping::test() -> 2
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x23-unreachable-guard.yu
```

UTC start: 2026-11-08T12:33:00.102861+00:00; elapsed: 0.004 s; exit: 1

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: std::control::junction::junction::junction
  hint: run `yulang check` to see source ranges before running
```

## 25. x24-pipe-catch / check

```yulang
act ping:
    our get: () -> int
ping::get() | catch:
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x24-pipe-catch.yu
```

UTC start: 2026-11-08T12:33:00.107173+00:00; elapsed: 0.003 s; exit: 1

```text
diagnostics:
  error [yulang.missing-catch-scrutinee]: catch expression is missing the computation to handle
    --> line 3, column 15
    3 | ping::get() | catch:
      |               ^^^^^
    hint: write `catch <expr>:` before the handler arms
```

## 26. x24-pipe-catch / dump

```yulang
act ping:
    our get: () -> int
ping::get() | catch:
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x24-pipe-catch.yu
```

UTC start: 2026-11-08T12:33:00.110270+00:00; elapsed: 0.003 s; exit: 0

```text
roots d0:ping
d0:ping mod {
}
detached {
  d1:"ping.get": () -> [ping] int = <missing>
}
error: catch expression is missing the computation to handle
```

## 27. x24-pipe-catch / run

```yulang
act ping:
    our get: () -> int
ping::get() | catch:
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x24-pipe-catch.yu
```

UTC start: 2026-11-08T12:33:00.113488+00:00; elapsed: 0.003 s; exit: 1

```text
compile error [yulang.lowering]: source has lowering errors
  detail: catch expression is missing the computation to handle
  hint: run `yulang check` to see source ranges before running
```

## 28. x24-direct-catch / check

```yulang
act ping:
    our get: () -> int
catch ping::get():
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x24-direct-catch.yu
```

UTC start: 2026-11-08T12:33:00.117322+00:00; elapsed: 0.004 s; exit: 0

```text
```

## 29. x24-direct-catch / dump

```yulang
act ping:
    our get: () -> int
catch ping::get():
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x24-direct-catch.yu
```

UTC start: 2026-11-08T12:33:00.121163+00:00; elapsed: 0.004 s; exit: 0

```text
roots d0:ping
d0:ping mod {
}
root exprs e7:catch e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()) { ping::get p0:_, p1:d3:k -> e5:(e3:r1:k->d3:k e4:7); p2:d4:value -> e6:r2:value->d4:value }
runtime roots e7:catch e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()) { ping::get p0:_, p1:d3:k -> e5:(e3:r1:k->d3:k e4:7); p2:d4:value -> e6:r2:value->d4:value }
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:k arg
  d4:value arg
}
```

## 30. x24-direct-catch / run

```yulang
act ping:
    our get: () -> int
catch ping::get():
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x24-direct-catch.yu
```

UTC start: 2026-11-08T12:33:00.125331+00:00; elapsed: 0.003 s; exit: 0

```text
run roots [7]
```

## 31. x24-catch-function / check

```yulang
act ping:
    our get: () -> int
our h = catch:
    ping::get(), k -> k 7
    value -> value
ping::get() | h
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x24-catch-function.yu
```

UTC start: 2026-11-08T12:33:00.128545+00:00; elapsed: 0.002 s; exit: 1

```text
diagnostics:
  error [yulang.missing-catch-scrutinee]: h: catch expression is missing the computation to handle
    --> line 3, column 9
    3 | our h = catch:
      |         ^^^^^
    hint: write `catch <expr>:` before the handler arms
```

## 32. x24-catch-function / dump

```yulang
act ping:
    our get: () -> int
our h = catch:
    ping::get(), k -> k 7
    value -> value
ping::get() | h
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x24-catch-function.yu
```

UTC start: 2026-11-08T12:33:00.131359+00:00; elapsed: 0.003 s; exit: 0

```text
roots d0:ping d2:h
d0:ping mod {
}
d2:h: never = <missing>
root exprs e4:(e3:r1:h->d2:h e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()))
runtime roots e4:(e3:r1:h->d2:h e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
}
error: catch expression is missing the computation to handle
```

## 33. x24-catch-function / run

```yulang
act ping:
    our get: () -> int
our h = catch:
    ping::get(), k -> k 7
    value -> value
ping::get() | h
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x24-catch-function.yu
```

UTC start: 2026-11-08T12:33:00.134551+00:00; elapsed: 0.003 s; exit: 1

```text
compile error [yulang.lowering]: source has lowering errors
  detail: catch expression is missing the computation to handle
  hint: run `yulang check` to see source ranges before running
```

## 34. x25-f1-direct-run / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(plain(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-f1-direct-run.yu
```

UTC start: 2026-11-08T12:33:00.138274+00:00; elapsed: 0.009 s; exit: 0

```text
```

## 35. x25-f1-direct-run / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(plain(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-f1-direct-run.yu
```

UTC start: 2026-11-08T12:33:00.147332+00:00; elapsed: 0.008 s; exit: 0

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

## 36. x25-f1-direct-run / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(plain(ping::get()))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-f1-direct-run.yu
```

UTC start: 2026-11-08T12:33:00.156186+00:00; elapsed: 0.004 s; exit: 0

```text
run roots [7]
```

## 37. x25-f1-pipe-run / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(ping::get() | plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-f1-pipe-run.yu
```

UTC start: 2026-11-08T12:33:00.160258+00:00; elapsed: 0.009 s; exit: 0

```text
```

## 38. x25-f1-pipe-run / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(ping::get() | plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-f1-pipe-run.yu
```

UTC start: 2026-11-08T12:33:00.169632+00:00; elapsed: 0.012 s; exit: 0

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

## 39. x25-f1-pipe-run / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(ping::get() | plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-f1-pipe-run.yu
```

UTC start: 2026-11-08T12:33:00.182166+00:00; elapsed: 0.004 s; exit: 0

```text
run roots [7]
```

## 40. x25-f1-higher-run / check

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

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-f1-higher-run.yu
```

UTC start: 2026-11-08T12:33:00.186389+00:00; elapsed: 0.01 s; exit: 0

```text
```

## 41. x25-f1-higher-run / dump

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

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-f1-higher-run.yu
```

UTC start: 2026-11-08T12:33:00.196693+00:00; elapsed: 0.009 s; exit: 0

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

## 42. x25-f1-higher-run / run

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

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-f1-higher-run.yu
```

UTC start: 2026-11-08T12:33:00.206460+00:00; elapsed: 0.011 s; exit: 1

```text
conflicting type candidates: [ping] vs []
```

## 43. x25-f1-higher-inferred-run / check

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

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-f1-higher-inferred-run.yu
```

UTC start: 2026-11-08T12:33:00.217907+00:00; elapsed: 0.008 s; exit: 0

```text
```

## 44. x25-f1-higher-inferred-run / dump

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

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-f1-higher-inferred-run.yu
```

UTC start: 2026-11-08T12:33:00.226763+00:00; elapsed: 0.01 s; exit: 0

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

## 45. x25-f1-higher-inferred-run / run

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

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-f1-higher-inferred-run.yu
```

UTC start: 2026-11-08T12:33:00.237733+00:00; elapsed: 0.004 s; exit: 0

```text
run roots [7]
```

## 46. x25-explicit-eta / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-explicit-eta.yu
```

UTC start: 2026-11-08T12:34:00.502269+00:00; elapsed: 0.011 s; exit: 0

```text
```

## 47. x25-explicit-eta / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-explicit-eta.yu
```

UTC start: 2026-11-08T12:34:00.513804+00:00; elapsed: 0.009 s; exit: 0

```text
roots d0:ping d2:plain d3:handle d4:higher
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d6:action -> e7:catch e2:r1:action->d6:action { ping::get p2:_, p3:d7:k -> e5:(e3:r2:k->d7:k e4:7); p4:d8:value -> e6:r3:value->d8:value })
d4:higher: (int -> [ping] int) -> int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e22:(e15:r6:handle->d3:handle e21:(e16:r7:higher->d4:higher e20:(fn p6:d11:x -> e19:(e17:r8:plain->d2:plain e18:r9:x->d11:x))))
runtime roots e22:(e15:r6:handle->d3:handle e21:(e16:r7:higher->d4:higher e20:(fn p6:d11:x -> e19:(e17:r8:plain->d2:plain e18:r9:x->d11:x))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:action arg
  d7:k arg
  d8:value arg
  d9:f arg
  d11:x arg
}
```

## 48. x25-explicit-eta / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-explicit-eta.yu
```

UTC start: 2026-11-08T12:34:00.523251+00:00; elapsed: 0.01 s; exit: 1

```text
conflicting type candidates: [ping] vs []
```

## 49. x25-explicit-direct / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-explicit-direct.yu
```

UTC start: 2026-11-08T12:34:00.533043+00:00; elapsed: 0.012 s; exit: 0

```text
```

## 50. x25-explicit-direct / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-explicit-direct.yu
```

UTC start: 2026-11-08T12:34:00.545170+00:00; elapsed: 0.01 s; exit: 0

```text
roots d0:ping d2:plain d3:handle d4:higher
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d6:action -> e7:catch e2:r1:action->d6:action { ping::get p2:_, p3:d7:k -> e5:(e3:r2:k->d7:k e4:7); p4:d8:value -> e6:r3:value->d8:value })
d4:higher: (int -> [ping] int) -> int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e19:(e15:r6:handle->d3:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d2:plain))
runtime roots e19:(e15:r6:handle->d3:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d2:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:action arg
  d7:k arg
  d8:value arg
  d9:f arg
}
```

## 51. x25-explicit-direct / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-explicit-direct.yu
```

UTC start: 2026-11-08T12:34:00.555809+00:00; elapsed: 0.01 s; exit: 1

```text
conflicting type candidates: [ping] vs []
```

## 52. x25-argonly-eta / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-argonly-eta.yu
```

UTC start: 2026-11-08T12:34:00.565675+00:00; elapsed: 0.01 s; exit: 0

```text
```

## 53. x25-argonly-eta / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-argonly-eta.yu
```

UTC start: 2026-11-08T12:34:00.575938+00:00; elapsed: 0.009 s; exit: 0

```text
roots d0:ping d2:plain d3:handle d4:higher
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d6:action -> e7:catch e2:r1:action->d6:action { ping::get p2:_, p3:d7:k -> e5:(e3:r2:k->d7:k e4:7); p4:d8:value -> e6:r3:value->d8:value })
d4:higher: (int [ping] -> ['a] int) -> ['a] int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e22:(e15:r6:handle->d3:handle e21:(e16:r7:higher->d4:higher e20:(fn p6:d11:x -> e19:(e17:r8:plain->d2:plain e18:r9:x->d11:x))))
runtime roots e22:(e15:r6:handle->d3:handle e21:(e16:r7:higher->d4:higher e20:(fn p6:d11:x -> e19:(e17:r8:plain->d2:plain e18:r9:x->d11:x))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:action arg
  d7:k arg
  d8:value arg
  d9:f arg
  d11:x arg
}
```

## 54. x25-argonly-eta / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-argonly-eta.yu
```

UTC start: 2026-11-08T12:34:00.585154+00:00; elapsed: 0.005 s; exit: 0

```text
run roots [7]
```

## 55. x25-argonly-direct / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-argonly-direct.yu
```

UTC start: 2026-11-08T12:34:00.589974+00:00; elapsed: 0.011 s; exit: 0

```text
```

## 56. x25-argonly-direct / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-argonly-direct.yu
```

UTC start: 2026-11-08T12:34:00.601278+00:00; elapsed: 0.01 s; exit: 0

```text
roots d0:ping d2:plain d3:handle d4:higher
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d6:action -> e7:catch e2:r1:action->d6:action { ping::get p2:_, p3:d7:k -> e5:(e3:r2:k->d7:k e4:7); p4:d8:value -> e6:r3:value->d8:value })
d4:higher: (int [ping] -> ['a] int) -> ['a] int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e19:(e15:r6:handle->d3:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d2:plain))
runtime roots e19:(e15:r6:handle->d3:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d2:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:action arg
  d7:k arg
  d8:value arg
  d9:f arg
}
```

## 57. x25-argonly-direct / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-argonly-direct.yu
```

UTC start: 2026-11-08T12:34:00.612055+00:00; elapsed: 0.006 s; exit: 0

```text
run roots [7]
```

## 58. x25-resultonly-eta / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-resultonly-eta.yu
```

UTC start: 2026-11-08T12:34:00.617963+00:00; elapsed: 0.01 s; exit: 0

```text
```

## 59. x25-resultonly-eta / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-resultonly-eta.yu
```

UTC start: 2026-11-08T12:34:00.628502+00:00; elapsed: 0.011 s; exit: 0

```text
roots d0:ping d2:plain d3:handle d4:higher
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d6:action -> e7:catch e2:r1:action->d6:action { ping::get p2:_, p3:d7:k -> e5:(e3:r2:k->d7:k e4:7); p4:d8:value -> e6:r3:value->d8:value })
d4:higher: (int -> [ping] int) -> int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e22:(e15:r6:handle->d3:handle e21:(e16:r7:higher->d4:higher e20:(fn p6:d11:x -> e19:(e17:r8:plain->d2:plain e18:r9:x->d11:x))))
runtime roots e22:(e15:r6:handle->d3:handle e21:(e16:r7:higher->d4:higher e20:(fn p6:d11:x -> e19:(e17:r8:plain->d2:plain e18:r9:x->d11:x))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:action arg
  d7:k arg
  d8:value arg
  d9:f arg
  d11:x arg
}
```

## 60. x25-resultonly-eta / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-resultonly-eta.yu
```

UTC start: 2026-11-08T12:34:00.640260+00:00; elapsed: 0.015 s; exit: 1

```text
conflicting type candidates: [ping] vs []
```

## 61. x25-resultonly-direct / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-resultonly-direct.yu
```

UTC start: 2026-11-08T12:34:00.655376+00:00; elapsed: 0.009 s; exit: 0

```text
```

## 62. x25-resultonly-direct / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-resultonly-direct.yu
```

UTC start: 2026-11-08T12:34:00.664428+00:00; elapsed: 0.009 s; exit: 0

```text
roots d0:ping d2:plain d3:handle d4:higher
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d6:action -> e7:catch e2:r1:action->d6:action { ping::get p2:_, p3:d7:k -> e5:(e3:r2:k->d7:k e4:7); p4:d8:value -> e6:r3:value->d8:value })
d4:higher: (int -> [ping] int) -> int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e19:(e15:r6:handle->d3:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d2:plain))
runtime roots e19:(e15:r6:handle->d3:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d2:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:action arg
  d7:k arg
  d8:value arg
  d9:f arg
}
```

## 63. x25-resultonly-direct / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-resultonly-direct.yu
```

UTC start: 2026-11-08T12:34:00.673810+00:00; elapsed: 0.013 s; exit: 1

```text
conflicting type candidates: [ping] vs []
```

## 64. x25-wildarg-eta / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-wildarg-eta.yu
```

UTC start: 2026-11-08T12:34:00.687371+00:00; elapsed: 0.01 s; exit: 0

```text
```

## 65. x25-wildarg-eta / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-wildarg-eta.yu
```

UTC start: 2026-11-08T12:34:00.698243+00:00; elapsed: 0.013 s; exit: 0

```text
roots d0:ping d2:plain d3:handle d4:higher
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d6:action -> e7:catch e2:r1:action->d6:action { ping::get p2:_, p3:d7:k -> e5:(e3:r2:k->d7:k e4:7); p4:d8:value -> e6:r3:value->d8:value })
d4:higher: (int [ping] -> ['a & [ping; 'b]] int) -> ['b#0[ping], 'a] int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e22:(e15:r6:handle->d3:handle e21:(e16:r7:higher->d4:higher e20:(fn p6:d11:x -> e19:(e17:r8:plain->d2:plain e18:r9:x->d11:x))))
runtime roots e22:(e15:r6:handle->d3:handle e21:(e16:r7:higher->d4:higher e20:(fn p6:d11:x -> e19:(e17:r8:plain->d2:plain e18:r9:x->d11:x))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:action arg
  d7:k arg
  d8:value arg
  d9:f arg
  d11:x arg
}
```

## 66. x25-wildarg-eta / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-wildarg-eta.yu
```

UTC start: 2026-11-08T12:34:00.711802+00:00; elapsed: 0.004 s; exit: 0

```text
run roots [7]
```

## 67. x25-wildarg-direct / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-wildarg-direct.yu
```

UTC start: 2026-11-08T12:34:00.716094+00:00; elapsed: 0.008 s; exit: 0

```text
```

## 68. x25-wildarg-direct / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-wildarg-direct.yu
```

UTC start: 2026-11-08T12:34:00.724744+00:00; elapsed: 0.014 s; exit: 0

```text
roots d0:ping d2:plain d3:handle d4:higher
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d6:action -> e7:catch e2:r1:action->d6:action { ping::get p2:_, p3:d7:k -> e5:(e3:r2:k->d7:k e4:7); p4:d8:value -> e6:r3:value->d8:value })
d4:higher: (int [ping] -> ['a & [ping; 'b]] int) -> ['b#0[ping], 'a] int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e19:(e15:r6:handle->d3:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d2:plain))
runtime roots e19:(e15:r6:handle->d3:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d2:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:action arg
  d7:k arg
  d8:value arg
  d9:f arg
}
```

## 69. x25-wildarg-direct / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-wildarg-direct.yu
```

UTC start: 2026-11-08T12:34:00.739084+00:00; elapsed: 0.004 s; exit: 1

```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
    --> line 7, column 42
    7 | our higher(f: [_] int -> [ping] int) = f(ping::get())
      |                                          ^^^^^^^^^
  hint: handle this computation with a matching effect handler before running it
  note: application occurs here
    --> line 7, column 42
    7 | our higher(f: [_] int -> [ping] int) = f(ping::get())
      |                                          ^^^^^^^^^^^
```

## 70. x25-wildresult-eta / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [_] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-wildresult-eta.yu
```

UTC start: 2026-11-08T12:34:00.743922+00:00; elapsed: 0.012 s; exit: 0

```text
```

## 71. x25-wildresult-eta / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [_] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-wildresult-eta.yu
```

UTC start: 2026-11-08T12:34:00.756299+00:00; elapsed: 0.012 s; exit: 0

```text
roots d0:ping d2:plain d3:handle d4:higher
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d6:action -> e7:catch e2:r1:action->d6:action { ping::get p2:_, p3:d7:k -> e5:(e3:r2:k->d7:k e4:7); p4:d8:value -> e6:r3:value->d8:value })
d4:higher: (int [ping] -> ['a] int) -> ['a] int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e22:(e15:r6:handle->d3:handle e21:(e16:r7:higher->d4:higher e20:(fn p6:d11:x -> e19:(e17:r8:plain->d2:plain e18:r9:x->d11:x))))
runtime roots e22:(e15:r6:handle->d3:handle e21:(e16:r7:higher->d4:higher e20:(fn p6:d11:x -> e19:(e17:r8:plain->d2:plain e18:r9:x->d11:x))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:action arg
  d7:k arg
  d8:value arg
  d9:f arg
  d11:x arg
}
```

## 72. x25-wildresult-eta / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [_] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-wildresult-eta.yu
```

UTC start: 2026-11-08T12:34:00.769145+00:00; elapsed: 0.005 s; exit: 0

```text
run roots [7]
```

## 73. x25-wildresult-direct / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [_] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-wildresult-direct.yu
```

UTC start: 2026-11-08T12:34:00.774152+00:00; elapsed: 0.009 s; exit: 0

```text
```

## 74. x25-wildresult-direct / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [_] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-wildresult-direct.yu
```

UTC start: 2026-11-08T12:34:00.783509+00:00; elapsed: 0.01 s; exit: 0

```text
roots d0:ping d2:plain d3:handle d4:higher
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d6:action -> e7:catch e2:r1:action->d6:action { ping::get p2:_, p3:d7:k -> e5:(e3:r2:k->d7:k e4:7); p4:d8:value -> e6:r3:value->d8:value })
d4:higher: (int [ping] -> ['a] int) -> ['a] int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e19:(e15:r6:handle->d3:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d2:plain))
runtime roots e19:(e15:r6:handle->d3:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d2:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:action arg
  d7:k arg
  d8:value arg
  d9:f arg
}
```

## 75. x25-wildresult-direct / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [_] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-wildresult-direct.yu
```

UTC start: 2026-11-08T12:34:00.794370+00:00; elapsed: 0.005 s; exit: 0

```text
run roots [7]
```

## 76. x25-effectfree-eta / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-effectfree-eta.yu
```

UTC start: 2026-11-08T12:34:00.799397+00:00; elapsed: 0.009 s; exit: 0

```text
```

## 77. x25-effectfree-eta / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-effectfree-eta.yu
```

UTC start: 2026-11-08T12:34:00.809293+00:00; elapsed: 0.009 s; exit: 0

```text
roots d0:ping d2:plain d3:handle d4:higher
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d6:action -> e7:catch e2:r1:action->d6:action { ping::get p2:_, p3:d7:k -> e5:(e3:r2:k->d7:k e4:7); p4:d8:value -> e6:r3:value->d8:value })
d4:higher: (int [ping] -> ['a] int) -> ['a] int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e22:(e15:r6:handle->d3:handle e21:(e16:r7:higher->d4:higher e20:(fn p6:d11:x -> e19:(e17:r8:plain->d2:plain e18:r9:x->d11:x))))
runtime roots e22:(e15:r6:handle->d3:handle e21:(e16:r7:higher->d4:higher e20:(fn p6:d11:x -> e19:(e17:r8:plain->d2:plain e18:r9:x->d11:x))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:action arg
  d7:k arg
  d8:value arg
  d9:f arg
  d11:x arg
}
```

## 78. x25-effectfree-eta / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-effectfree-eta.yu
```

UTC start: 2026-11-08T12:34:00.818503+00:00; elapsed: 0.004 s; exit: 0

```text
run roots [7]
```

## 79. x25-effectfree-direct / check

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x25-effectfree-direct.yu
```

UTC start: 2026-11-08T12:34:00.823371+00:00; elapsed: 0.008 s; exit: 0

```text
```

## 80. x25-effectfree-direct / dump

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x25-effectfree-direct.yu
```

UTC start: 2026-11-08T12:34:00.831302+00:00; elapsed: 0.009 s; exit: 0

```text
roots d0:ping d2:plain d3:handle d4:higher
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:handle: int ['a & [ping; 'a]] -> ['a] int = e8:(fn p1:d6:action -> e7:catch e2:r1:action->d6:action { ping::get p2:_, p3:d7:k -> e5:(e3:r2:k->d7:k e4:7); p4:d8:value -> e6:r3:value->d8:value })
d4:higher: (int [ping] -> ['a] int) -> ['a] int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e19:(e15:r6:handle->d3:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d2:plain))
runtime roots e19:(e15:r6:handle->d3:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d2:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:action arg
  d7:k arg
  d8:value arg
  d9:f arg
}
```

## 81. x25-effectfree-direct / run

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x25-effectfree-direct.yu
```

UTC start: 2026-11-08T12:34:00.840712+00:00; elapsed: 0.004 s; exit: 0

```text
run roots [7]
```

## 82. x22-inferred-present / check

```yulang
our read_port config = case config:
    {port: p} -> p
    _ -> 80
read_port {port: 443}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x22-inferred-present.yu
```

UTC start: 2026-11-08T12:34:00.845112+00:00; elapsed: 0.005 s; exit: 0

```text
```

## 83. x22-inferred-present / dump

```yulang
our read_port config = case config:
    {port: p} -> p
    _ -> 80
read_port {port: 443}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x22-inferred-present.yu
```

UTC start: 2026-11-08T12:34:00.851268+00:00; elapsed: 0.005 s; exit: 0

```text
roots d0:read_port
d0:read_port: {port: 'a} -> 'a | int = e4:(fn p0:d1:config -> e3:case e0:r0:config->d1:config { p2:{port: p1:d2:p} -> e1:r1:p->d2:p; p3:_ -> e2:80 })
root exprs e8:(e5:r2:read_port->d0:read_port e7:{port: e6:443})
runtime roots e8:(e5:r2:read_port->d0:read_port e7:{port: e6:443})
detached {
  d1:config arg
  d2:p arg
}
```

## 84. x22-inferred-present / run

```yulang
our read_port config = case config:
    {port: p} -> p
    _ -> 80
read_port {port: 443}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x22-inferred-present.yu
```

UTC start: 2026-11-08T12:34:00.856527+00:00; elapsed: 0.003 s; exit: 0

```text
run roots [443]
```

## 85. x22-default-shared-input / check

```yulang
our fallback {port = 80} = port
our read_port config = case config:
    {port: p} -> p
    _ -> fallback config
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x22-default-shared-input.yu
```

UTC start: 2026-11-08T12:34:00.860025+00:00; elapsed: 0.005 s; exit: 0

```text
```

## 86. x22-default-shared-input / dump

```yulang
our fallback {port = 80} = port
our read_port config = case config:
    {port: p} -> p
    _ -> fallback config
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x22-default-shared-input.yu
```

UTC start: 2026-11-08T12:34:00.866050+00:00; elapsed: 0.006 s; exit: 0

```text
roots d0:fallback d1:read_port
d0:fallback: {port?: 'a} -> 'a | int = e2:(fn p1:{port: p0:d2:port = e0:80} -> e1:r0:port->d2:port)
d1:read_port: {port: 'a} -> 'a | int = e9:(fn p2:d3:config -> e8:case e3:r1:config->d3:config { p4:{port: p3:d4:p} -> e4:r2:p->d4:p; p5:_ -> e7:(e5:r3:fallback->d0:fallback e6:r4:config->d3:config) })
root exprs e12:(e10:r5:read_port->d1:read_port e11:{})
runtime roots e12:(e10:r5:read_port->d1:read_port e11:{})
detached {
  d2:port arg
  d3:config arg
  d4:p arg
}
```

## 87. x22-default-shared-input / run

```yulang
our fallback {port = 80} = port
our read_port config = case config:
    {port: p} -> p
    _ -> fallback config
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x22-default-shared-input.yu
```

UTC start: 2026-11-08T12:34:00.872517+00:00; elapsed: 0.007 s; exit: 1

```text
compile error [yulang.unsatisfied-subtype]: record is missing field `port`
  detail: unsatisfied subtype constraint: {} <: {port: 'open0}
  hint: add `port` to this record or use a value that provides it; actual record has no fields
```

## 88. x25-explicit-direct / run --interpreter

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit2-case/x25-explicit-direct.yu
```

UTC start: 2026-11-08T12:34:12.798545+00:00; elapsed: 0.004 s; exit: 1

```text
conflicting type candidates: [ping] vs []
```

## 89. x25-explicit-direct / run --evidence-vm

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --evidence-vm --print-roots /tmp/audit2-case/x25-explicit-direct.yu
```

UTC start: 2026-11-08T12:34:12.803131+00:00; elapsed: 0.011 s; exit: 1

```text
conflicting type candidates: [ping] vs []
```

## 90. x25-argonly-direct / run --interpreter

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit2-case/x25-argonly-direct.yu
```

UTC start: 2026-11-08T12:34:12.814488+00:00; elapsed: 0.003 s; exit: 0

```text
run roots [7]
```

## 91. x25-argonly-direct / run --evidence-vm

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --evidence-vm --print-roots /tmp/audit2-case/x25-argonly-direct.yu
```

UTC start: 2026-11-08T12:34:12.817428+00:00; elapsed: 0.003 s; exit: 0

```text
run roots [7]
```

## 92. x25-wildarg-direct / run --interpreter

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit2-case/x25-wildarg-direct.yu
```

UTC start: 2026-11-08T12:34:12.820440+00:00; elapsed: 0.002 s; exit: 1

```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
  hint: handle this computation with a matching effect handler before running it
```

## 93. x25-wildarg-direct / run --evidence-vm

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --evidence-vm --print-roots /tmp/audit2-case/x25-wildarg-direct.yu
```

UTC start: 2026-11-08T12:34:12.823070+00:00; elapsed: 0.003 s; exit: 1

```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
    --> line 7, column 42
    7 | our higher(f: [_] int -> [ping] int) = f(ping::get())
      |                                          ^^^^^^^^^
  hint: handle this computation with a matching effect handler before running it
  note: application occurs here
    --> line 7, column 42
    7 | our higher(f: [_] int -> [ping] int) = f(ping::get())
      |                                          ^^^^^^^^^^^
```

## 94. x25-wildarg-eta / run --interpreter

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit2-case/x25-wildarg-eta.yu
```

UTC start: 2026-11-08T12:34:12.826353+00:00; elapsed: 0.002 s; exit: 0

```text
run roots [7]
```

## 95. x25-wildarg-eta / run --evidence-vm

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --evidence-vm --print-roots /tmp/audit2-case/x25-wildarg-eta.yu
```

UTC start: 2026-11-08T12:34:12.829030+00:00; elapsed: 0.003 s; exit: 0

```text
run roots [7]
```

## 96. x22-inferred-missing / run --interpreter

```yulang
our read_port(config) = case config:
    {port: p} -> p
    _ -> 80
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit2-case/x22-inferred-missing.yu
```

UTC start: 2026-11-08T12:34:12.832318+00:00; elapsed: 0.002 s; exit: 1

```text
compile error [yulang.unsatisfied-subtype]: record is missing field `port`
  detail: unsatisfied subtype constraint: {} <: {port: 'open0}
  hint: add `port` to this record or use a value that provides it; actual record has no fields
```

## 97. x22-inferred-missing / run --evidence-vm

```yulang
our read_port(config) = case config:
    {port: p} -> p
    _ -> 80
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --evidence-vm --print-roots /tmp/audit2-case/x22-inferred-missing.yu
```

UTC start: 2026-11-08T12:34:12.834279+00:00; elapsed: 0.005 s; exit: 1

```text
compile error [yulang.unsatisfied-subtype]: record is missing field `port`
  detail: unsatisfied subtype constraint: {} <: {port: 'open0}
  hint: add `port` to this record or use a value that provides it; actual record has no fields
```

## 98. x23-pure-filter / check

```yulang
act ping:
    our get: () -> int
our f(x: int): [] int = case x:
    _ -> 1
    _ -> ping::get()
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x23-pure-filter.yu
```

UTC start: 2026-11-08T12:34:40.283819+00:00; elapsed: 0.006 s; exit: 1

```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: ping is not allowed by []
```

## 99. x23-pure-filter / dump

```yulang
act ping:
    our get: () -> int
our f(x: int): [] int = case x:
    _ -> 1
    _ -> ping::get()
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x23-pure-filter.yu
```

UTC start: 2026-11-08T12:34:40.290182+00:00; elapsed: 0.007 s; exit: 0

```text
roots d0:ping d2:f
d0:ping mod {
}
d2:f: int -> [ping] int = e6:(fn p0:d3:x -> e5:case e0:r0:x->d3:x { p1:_ -> e1:1; p2:_ -> e4:(e2:r1:"ping::get"->d1:"ping.get" e3:()) })
root exprs e9:(e7:r2:f->d2:f e8:0)
runtime roots e9:(e7:r2:f->d2:f e8:0)
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:x arg
}
error: effect filter mismatch: ping is not allowed by []
```

## 100. x23-pure-filter / run

```yulang
act ping:
    our get: () -> int
our f(x: int): [] int = case x:
    _ -> 1
    _ -> ping::get()
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x23-pure-filter.yu
```

UTC start: 2026-11-08T12:34:40.297102+00:00; elapsed: 0.006 s; exit: 1

```text
compile error [yulang.lowering]: source has lowering errors
  detail: effect filter mismatch: ping is not allowed by []
  hint: run `yulang check` to see source ranges before running
```

## 101. x23-handled-unreachable / check

```yulang
act ping:
    our get: () -> int
our f x = case x:
    _ -> 1
    _ -> ping::get()
catch f 0:
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x23-handled-unreachable.yu
```

UTC start: 2026-11-08T12:34:40.304011+00:00; elapsed: 0.005 s; exit: 0

```text
```

## 102. x23-handled-unreachable / dump

```yulang
act ping:
    our get: () -> int
our f x = case x:
    _ -> 1
    _ -> ping::get()
catch f 0:
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x23-handled-unreachable.yu
```

UTC start: 2026-11-08T12:34:40.309315+00:00; elapsed: 0.005 s; exit: 0

```text
roots d0:ping d2:f
d0:ping mod {
}
d2:f: any -> [ping] int = e6:(fn p0:d3:x -> e5:case e0:r0:x->d3:x { p1:_ -> e1:1; p2:_ -> e4:(e2:r1:"ping::get"->d1:"ping.get" e3:()) })
root exprs e14:catch e9:(e7:r2:f->d2:f e8:0) { ping::get p3:_, p4:d5:k -> e12:(e10:r3:k->d5:k e11:7); p5:d6:value -> e13:r4:value->d6:value }
runtime roots e14:catch e9:(e7:r2:f->d2:f e8:0) { ping::get p3:_, p4:d5:k -> e12:(e10:r3:k->d5:k e11:7); p5:d6:value -> e13:r4:value->d6:value }
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:x arg
  d5:k arg
  d6:value arg
}
```

## 103. x23-handled-unreachable / run

```yulang
act ping:
    our get: () -> int
our f x = case x:
    _ -> 1
    _ -> ping::get()
catch f 0:
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x23-handled-unreachable.yu
```

UTC start: 2026-11-08T12:34:40.314897+00:00; elapsed: 0.003 s; exit: 0

```text
run roots [1]
```

## 104. x24-pipe-explicit-function / check

```yulang
act ping:
    our get: () -> int
our h(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
ping::get() | h
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x24-pipe-explicit-function.yu
```

UTC start: 2026-11-08T12:34:40.318307+00:00; elapsed: 0.006 s; exit: 0

```text
```

## 105. x24-pipe-explicit-function / dump

```yulang
act ping:
    our get: () -> int
our h(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
ping::get() | h
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x24-pipe-explicit-function.yu
```

UTC start: 2026-11-08T12:34:40.324332+00:00; elapsed: 0.006 s; exit: 0

```text
roots d0:ping d2:h
d0:ping mod {
}
d2:h: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d3:action -> e5:catch e0:r0:action->d3:action { ping::get p1:_, p2:d4:k -> e3:(e1:r1:k->d4:k e2:7); p3:d5:value -> e4:r2:value->d5:value })
root exprs e11:(e10:r4:h->d2:h e9:(e7:r3:"ping::get"->d1:"ping.get" e8:()))
runtime roots e11:(e10:r4:h->d2:h e9:(e7:r3:"ping::get"->d1:"ping.get" e8:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:action arg
  d4:k arg
  d5:value arg
}
```

## 106. x24-pipe-explicit-function / run

```yulang
act ping:
    our get: () -> int
our h(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
ping::get() | h
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x24-pipe-explicit-function.yu
```

UTC start: 2026-11-08T12:34:40.330757+00:00; elapsed: 0.003 s; exit: 0

```text
run roots [7]
```

## 107. x24-pipe-lambda / check

```yulang
act ping:
    our get: () -> int
ping::get() | (\action -> catch action:
    ping::get(), k -> k 7
    value -> value)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x24-pipe-lambda.yu
```

UTC start: 2026-11-08T12:34:40.334180+00:00; elapsed: 0.005 s; exit: 1

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 19
    5 |     value -> value)
      |                   ^
  error [yulang.syntax]: syntax error: unexpected end of input
    --> line 5, column 20
    5 |     value -> value)
      |                    ^
```

## 108. x24-pipe-lambda / dump

```yulang
act ping:
    our get: () -> int
ping::get() | (\action -> catch action:
    ping::get(), k -> k 7
    value -> value)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x24-pipe-lambda.yu
```

UTC start: 2026-11-08T12:34:40.339126+00:00; elapsed: 0.005 s; exit: 0

```text
roots d0:ping
d0:ping mod {
}
root exprs e10:(e9:(fn p0:d3:action -> e8:catch e3:r1:action->d3:action { ping::get p1:_, p2:d4:k -> e6:(e4:r2:k->d4:k e5:7); p3:d5:value -> e7:r3:value->d5:value }) e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()))
runtime roots e10:(e9:(fn p0:d3:action -> e8:catch e3:r1:action->d3:action { ping::get p1:_, p2:d4:k -> e6:(e4:r2:k->d4:k e5:7); p3:d5:value -> e7:r3:value->d5:value }) e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:action arg
  d4:k arg
  d5:value arg
}
```

## 109. x24-pipe-lambda / run

```yulang
act ping:
    our get: () -> int
ping::get() | (\action -> catch action:
    ping::get(), k -> k 7
    value -> value)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x24-pipe-lambda.yu
```

UTC start: 2026-11-08T12:34:40.344174+00:00; elapsed: 0.002 s; exit: 1

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 19
    5 |     value -> value)
      |                   ^
  error [yulang.syntax]: syntax error: unexpected end of input
    --> line 5, column 20
    5 |     value -> value)
      |                    ^
```

## 110. x24-pipe-annotated-lambda / check

```yulang
act ping:
    our get: () -> int
ping::get() | (\(action: [ping] int) -> catch action:
    ping::get(), k -> k 7
    value -> value)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/x24-pipe-annotated-lambda.yu
```

UTC start: 2026-11-08T12:34:40.346906+00:00; elapsed: 0.006 s; exit: 1

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 19
    5 |     value -> value)
      |                   ^
  error [yulang.syntax]: syntax error: unexpected end of input
    --> line 5, column 20
    5 |     value -> value)
      |                    ^
```

## 111. x24-pipe-annotated-lambda / dump

```yulang
act ping:
    our get: () -> int
ping::get() | (\(action: [ping] int) -> catch action:
    ping::get(), k -> k 7
    value -> value)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/x24-pipe-annotated-lambda.yu
```

UTC start: 2026-11-08T12:34:40.353712+00:00; elapsed: 0.007 s; exit: 0

```text
roots d0:ping
d0:ping mod {
}
root exprs e10:(e9:(fn p0:d3:action -> e8:catch e3:r1:action->d3:action { ping::get p1:_, p2:d4:k -> e6:(e4:r2:k->d4:k e5:7); p3:d5:value -> e7:r3:value->d5:value }) e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()))
runtime roots e10:(e9:(fn p0:d3:action -> e8:catch e3:r1:action->d3:action { ping::get p1:_, p2:d4:k -> e6:(e4:r2:k->d4:k e5:7); p3:d5:value -> e7:r3:value->d5:value }) e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:action arg
  d4:k arg
  d5:value arg
}
```

## 112. x24-pipe-annotated-lambda / run

```yulang
act ping:
    our get: () -> int
ping::get() | (\(action: [ping] int) -> catch action:
    ping::get(), k -> k 7
    value -> value)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/x24-pipe-annotated-lambda.yu
```

UTC start: 2026-11-08T12:34:40.360767+00:00; elapsed: 0.002 s; exit: 1

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 19
    5 |     value -> value)
      |                   ^
  error [yulang.syntax]: syntax error: unexpected end of input
    --> line 5, column 20
    5 |     value -> value)
      |                    ^
```

## 113. x23-unreachable-guard-standard / check

```yulang
act ping:
    our test: () -> bool
our f x = case x:
    _ -> 1
    _ if ping::test() -> 2
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib check /tmp/audit2-case/x23-unreachable-guard.yu
```

UTC start: 2026-11-08T12:33:29.296549+00:00; elapsed: 140.776 s; exit: 0

```text
```

## 114. x23-unreachable-guard-standard / dump

```yulang
act ping:
    our test: () -> bool
our f x = case x:
    _ -> 1
    _ if ping::test() -> 2
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib dump --poly /tmp/audit2-case/x23-unreachable-guard.yu
```

UTC start: 2026-11-08T12:35:50.073060+00:00; elapsed: 148.84 s; exit: 0

```text
roots d0:std d2285:ping d2287:f
d0:std mod {
}
d2285:ping mod {
}
d2287:f: any -> [ping] int = e8403:(fn p1937:d2288:x -> e8402:case e8394:r3452:x->d2288:x { p1938:_ -> e8395:1; p1939:_ if e8400:(e8399:r3454:"std::control::junction::junction::junction"->d217:"std.control.junction.junction.junction" e8398:(e8396:r3453:"ping::test"->d2286:"ping.test" e8397:())) -> e8401:2 })
root exprs e8406:(e8404:r3455:f->d2287:f e8405:0)
runtime roots d179:"std.control.flow.label_sub.control_label" d209:"std.control.flow.label_loop.control_label" e8406:(e8404:r3455:f->d2287:f e8405:0)
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
  d2286:"ping.test": () -> [ping] bool = <missing>
  d2288:x arg
}
```

## 115. x23-unreachable-guard-standard / run

```yulang
act ping:
    our test: () -> bool
our f x = case x:
    _ -> 1
    _ if ping::test() -> 2
f 0
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit2-case/x23-unreachable-guard.yu
```

UTC start: 2026-11-08T12:38:18.915234+00:00; elapsed: 0.114 s; exit: 0

```text
run roots [1]
```

## 116. x24-pipe-catch-standard / check

```yulang
act ping:
    our get: () -> int
ping::get() | catch:
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib check /tmp/audit2-case/x24-pipe-catch.yu
```

UTC start: 2026-11-08T12:38:19.031596+00:00; elapsed: 158.346 s; exit: 1

```text
diagnostics:
  error [yulang.missing-catch-scrutinee]: catch expression is missing the computation to handle
    --> line 3, column 15
    3 | ping::get() | catch:
      |               ^^^^^
    hint: write `catch <expr>:` before the handler arms
```

## 117. x24-pipe-catch-standard / dump

```yulang
act ping:
    our get: () -> int
ping::get() | catch:
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib dump --poly /tmp/audit2-case/x24-pipe-catch.yu
```

UTC start: 2026-11-08T12:40:57.379310+00:00; elapsed: 166.248 s; exit: 0

```text
roots d0:std d1:ping
d0:std mod {
  pub d3:"std.core" mod {
    pub d23:"std.core.cmp" mod {
      pub d249:"std.core.cmp.Eq" mod {
        pub d250:"std.core.cmp.Eq.eq": 'a -> 'a -> bool where 'a: std::core::cmp::Eq = <missing>
      }
      pub d251:"std.core.cmp.Ord" mod {
        pub d252:"std.core.cmp.Ord.lt": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = <missing>
        pub d253:"std.core.cmp.Ord.le": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = <missing>
        pub d254:"std.core.cmp.Ord.gt": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = <missing>
        pub d255:"std.core.cmp.Ord.ge": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = <missing>
      }
      my d256 mod {
        d257: int -> int -> bool = e1444:(fn p333:d1212:x -> e1443:(fn p334:d1213:y -> e1442:(e1440:(e1438:r521:"std::int::eq"->d47:"std.int.eq" e1439:r522:x->d1212:x) e1441:r523:y->d1213:y)))
      }
      my d258 mod {
        d259: int -> int -> bool = e1451:(fn p335:d1214:x -> e1450:(fn p336:d1215:y -> e1449:(e1447:(e1445:r524:"std::int::lt"->d48:"std.int.lt" e1446:r525:x->d1214:x) e1448:r526:y->d1215:y)))
        d260: int -> int -> bool = e1458:(fn p337:d1216:x -> e1457:(fn p338:d1217:y -> e1456:(e1454:(e1452:r527:"std::int::le"->d49:"std.int.le" e1453:r528:x->d1216:x) e1455:r529:y->d1217:y)))
        d261: int -> int -> bool = e1465:(fn p339:d1218:x -> e1464:(fn p340:d1219:y -> e1463:(e1461:(e1459:r530:"std::int::gt"->d50:"std.int.gt" e1460:r531:x->d1218:x) e1462:r532:y->d1219:y)))
        d262: int -> int -> bool = e1472:(fn p341:d1220:x -> e1471:(fn p342:d1221:y -> e1470:(e1468:(e1466:r533:"std::int::ge"->d51:"std.int.ge" e1467:r534:x->d1220:x) e1469:r535:y->d1221:y)))
      }
      my d263 mod {
        d264: float -> float -> bool = e1479:(fn p343:d1222:x -> e1478:(fn p344:d1223:y -> e1477:(e1475:(e1473:r536:"std::float::eq"->d36:"std.float.eq" e1474:r537:x->d1222:x) e1476:r538:y->d1223:y)))
      }
      my d265 mod {
        d266: float -> float -> bool = e1486:(fn p345:d1224:x -> e1485:(fn p346:d1225:y -> e1484:(e1482:(e1480:r539:"std::float::lt"->d37:"std.float.lt" e1481:r540:x->d1224:x) e1483:r541:y->d1225:y)))
        d267: float -> float -> bool = e1493:(fn p347:d1226:x -> e1492:(fn p348:d1227:y -> e1491:(e1489:(e1487:r542:"std::float::le"->d38:"std.float.le" e1488:r543:x->d1226:x) e1490:r544:y->d1227:y)))
        d268: float -> float -> bool = e1500:(fn p349:d1228:x -> e1499:(fn p350:d1229:y -> e1498:(e1496:(e1494:r545:"std::float::gt"->d39:"std.float.gt" e1495:r546:x->d1228:x) e1497:r547:y->d1229:y)))
        d269: float -> float -> bool = e1507:(fn p351:d1230:x -> e1506:(fn p352:d1231:y -> e1505:(e1503:(e1501:r548:"std::float::ge"->d40:"std.float.ge" e1502:r549:x->d1230:x) e1504:r550:y->d1231:y)))
      }
      my d270 mod {
        d271: std::num::frac::frac -> std::num::frac::frac -> bool = e1514:(fn p353:d1232:x -> e1513:(fn p354:d1233:y -> e1512:(e1510:(e1508:r551:"std::num::frac::eq"->d648:"std.num.frac.eq" e1509:r552:x->d1232:x) e1511:r553:y->d1233:y)))
      }
      my d272 mod {
        d273: std::num::frac::frac -> std::num::frac::frac -> bool = e1521:(fn p355:d1234:x -> e1520:(fn p356:d1235:y -> e1519:(e1517:(e1515:r554:"std::num::frac::lt"->d649:"std.num.frac.lt" e1516:r555:x->d1234:x) e1518:r556:y->d1235:y)))
        d274: std::num::frac::frac -> std::num::frac::frac -> bool = e1528:(fn p357:d1236:x -> e1527:(fn p358:d1237:y -> e1526:(e1524:(e1522:r557:"std::num::frac::le"->d650:"std.num.frac.le" e1523:r558:x->d1236:x) e1525:r559:y->d1237:y)))
        d275: std::num::frac::frac -> std::num::frac::frac -> bool = e1535:(fn p359:d1238:x -> e1534:(fn p360:d1239:y -> e1533:(e1531:(e1529:r560:"std::num::frac::gt"->d651:"std.num.frac.gt" e1530:r561:x->d1238:x) e1532:r562:y->d1239:y)))
        d276: std::num::frac::frac -> std::num::frac::frac -> bool = e1542:(fn p361:d1240:x -> e1541:(fn p362:d1241:y -> e1540:(e1538:(e1536:r563:"std::num::frac::ge"->d652:"std.num.frac.ge" e1537:r564:x->d1240:x) e1539:r565:y->d1241:y)))
      }
      my d277 mod {
        d278: bool -> bool -> bool = e1549:(fn p363:d1242:x -> e1548:(fn p364:d1243:y -> e1547:(e1545:(e1543:r566:"std::bool::eq"->d15:"std.bool.eq" e1544:r567:x->d1242:x) e1546:r568:y->d1243:y)))
      }
      my d279 mod {
        d280: std::text::str::str -> std::text::str::str -> bool = e1556:(fn p365:d1244:x -> e1555:(fn p366:d1245:y -> e1554:(e1552:(e1550:r569:"std::text::str::eq"->d787:"std.text.str.eq" e1551:r570:x->d1244:x) e1553:r571:y->d1245:y)))
      }
      my d281 mod {
        d282: std::text::char::char -> std::text::char::char -> bool = e1563:(fn p367:d1246:x -> e1562:(fn p368:d1247:y -> e1561:(e1559:(e1557:r572:"std::text::char::eq"->d673:"std.text.char.eq" e1558:r573:x->d1246:x) e1560:r574:y->d1247:y)))
      }
      my d283 mod {
        d284: std::data::list::list int -> std::data::list::list int -> bool = e1592:(fn p369:d1248:xs -> e1591:(fn p370:d1249:ys -> e1590:case e1570:(e1566:(e1564:r575:"std::data::list::view_raw"->d479:"std.data.list.view_raw" e1565:r576:xs->d1248:xs), e1569:(e1567:r577:"std::data::list::view_raw"->d479:"std.data.list.view_raw" e1568:r578:ys->d1249:ys)) { p373:(p371:r579:"std::data::list::list_view::empty"->d458:"std.data.list.list_view.empty", p372:r580:"std::data::list::list_view::empty"->d458:"std.data.list.list_view.empty") -> e1571:true; p378:(p375:r581:"std::data::list::list_view::leaf"->d459:"std.data.list.list_view.leaf"(p374:d1250:x), p377:r582:"std::data::list::list_view::leaf"->d459:"std.data.list.list_view.leaf"(p376:d1251:y)) -> e1576:(e1574:(e1572:r583:"std::int::eq"->d47:"std.int.eq" e1573:r584:x->d1250:x) e1575:r585:y->d1251:y); p385:(p381:r586:"std::data::list::list_view::node"->d460:"std.data.list.list_view.node"(p379:d1252:xl, p380:d1253:xr), p384:r587:"std::data::list::list_view::node"->d460:"std.data.list.list_view.node"(p382:d1254:yl, p383:d1255:yr)) -> e1588:case e1582:(e1581:r590:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1580:(e1578:(e1577:r588:xl->d1252:xl.s44.eq=>d250:"std.core.cmp.Eq.eq") e1579:r589:yl->d1254:yl)) { p386:true -> e1586:(e1584:(e1583:r591:xr->d1253:xr.s45.eq=>d250:"std.core.cmp.Eq.eq") e1585:r592:yr->d1255:yr); p387:false -> e1587:false }; p388:_ -> e1589:false }))
      }
    }
    pub d24:"std.core.convert" mod {
      pub d285:"std.core.convert.Cast" mod {
        pub d286:"std.core.convert.Cast.cast": 'a -> 'b where 'a: std::core::convert::Cast(to = 'b) = <missing>
      }
    }
    pub d25:"std.core.fmt" mod {
      pub d291:"std.core.fmt.format_kind" mod {
        pub d292:"std.core.fmt.format_kind.display": std::core::fmt::format_kind = <missing>
        pub d293:"std.core.fmt.format_kind.debug": std::core::fmt::format_kind = <missing>
        pub d294:"std.core.fmt.format_kind.lower_hex": std::core::fmt::format_kind = <missing>
        pub d295:"std.core.fmt.format_kind.upper_hex": std::core::fmt::format_kind = <missing>
      }
      pub d296:"std.core.fmt.format_align" mod {
        pub d297:"std.core.fmt.format_align.left": std::core::fmt::format_align = <missing>
        pub d298:"std.core.fmt.format_align.right": std::core::fmt::format_align = <missing>
        pub d299:"std.core.fmt.format_align.center": std::core::fmt::format_align = <missing>
      }
      pub d300:"std.core.fmt.format_sign" mod {
        pub d301:"std.core.fmt.format_sign.plus": std::core::fmt::format_sign = <missing>
        pub d302:"std.core.fmt.format_sign.minus": std::core::fmt::format_sign = <missing>
      }
      pub d303:"std.core.fmt.format_spec": {kind: std::core::fmt::format_kind, align: std::data::opt::opt std::core::fmt::format_align, sign: std::data::opt::opt std::core::fmt::format_sign, fill: std::data::opt::opt std::text::str::str, width: std::data::opt::opt int, precision: std::data::opt::opt int, alternate: bool, zero_pad: bool} -> std::core::fmt::format_spec = <missing>
      pub d320:"std.core.fmt.Display" mod {
        pub d321:"std.core.fmt.Display.show": 'a -> std::text::str::str where 'a: std::core::fmt::Display = <missing>
        pub d322:"std.core.fmt.Display.say": 'a -> [std::io::console::out] () where 'a: std::core::fmt::Display = e1619:(fn p393:d1260:a -> e1618:(e1611:r600:"std::io::out::write"->d540:"std.io.console.out.write" e1617:(e1616:(e1614:r602:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1613:(e1612:r601:a->d1260:a.s46.show=>d321:"std.core.fmt.Display.show")) e1615:"\n")))
        pub d323:"std.core.fmt.Display.note": 'a -> [std::io::console::err] () where 'a: std::core::fmt::Display = e1628:(fn p394:d1261:a -> e1627:(e1620:r603:"std::io::err::write"->d545:"std.io.console.err.write" e1626:(e1625:(e1623:r605:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1622:(e1621:r604:a->d1261:a.s47.show=>d321:"std.core.fmt.Display.show")) e1624:"\n")))
      }
      pub d324:"std.core.fmt.Debug" mod {
        pub d325:"std.core.fmt.Debug.debug": 'a -> std::text::str::str where 'a: std::core::fmt::Debug = <missing>
        pub d326:"std.core.fmt.Debug.dd": 'a -> [std::io::console::err] () where 'a: std::core::fmt::Debug = e1637:(fn p395:d1262:a -> e1636:(e1629:r606:"std::io::err::write"->d545:"std.io.console.err.write" e1635:(e1634:(e1632:r608:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1631:(e1630:r607:a->d1262:a.s48.debug=>d325:"std.core.fmt.Debug.debug")) e1633:"\n")))
      }
      my d327:"std.core.fmt.repeat": std::text::str::str -> int -> std::text::str::str = e1661:(fn p396:d1263:text -> e1660:(fn p397:d1264:count -> e1659:case e1644:(e1643:r611:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1642:(e1641:(e1639:r610:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e1638:r609:count->d1264:count) e1640:0)) { p398:true -> e1645:""; p399:false -> e1658:(e1657:(e1647:r613:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1646:r612:text->d1263:text) e1656:(e1650:(e1648:r614:repeat->d327:"std.core.fmt.repeat" e1649:r615:text->d1263:text) e1655:(e1654:(e1652:r617:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e1651:r616:count->d1264:count) e1653:1))) }))
      my d328:"std.core.fmt.format_fill": std::core::fmt::format_spec -> std::text::str::str = e1673:(fn p400:d1265:spec -> e1672:case e1663:(e1662:r618:spec->d1265:spec.s49.fill->d310) { p402:r619:"opt::just"->d506:"std.data.opt.opt.just"(p401:d1266:fill) -> e1664:r620:fill->d1266:fill; p403:r621:"opt::nil"->d505:"std.data.opt.opt.nil" -> e1671:case e1668:(e1667:r623:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1666:(e1665:r622:spec->d1265:spec.s50.zero_pad->d318)) { p404:true -> e1669:"0"; p405:false -> e1670:" " } })
      my d329:"std.core.fmt.format_body": std::core::fmt::format_spec -> std::text::str::str -> std::text::str::str = e1696:(fn p406:d1267:spec -> e1695:(fn p407:d1268:body -> e1694:case e1675:(e1674:r624:spec->d1267:spec.s51.precision->d314) { p409:r625:"opt::just"->d506:"std.data.opt.opt.just"(p408:d1269:limit) -> e1692:case e1683:(e1682:r629:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1681:(e1680:(e1678:r627:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e1677:(e1676:r626:body->d1268:body.s52.len->d840:"std.text.str.str.len")) e1679:r628:limit->d1269:limit)) { p410:true -> e1684:r630:body->d1268:body; p411:false -> e1691:(e1689:(e1687:(e1685:r631:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e1686:r632:body->d1268:body) e1688:0) e1690:r633:limit->d1269:limit) }; p412:r634:"opt::nil"->d505:"std.data.opt.opt.nil" -> e1693:r635:body->d1268:body }))
      my d330:"std.core.fmt.starts_with_minus": std::text::str::str -> bool = e1718:(fn p413:d1270:body -> e1717:case e1704:(e1703:r638:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1702:(e1701:(e1699:r637:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e1698:(e1697:r636:body->d1270:body.s53.len->d840:"std.text.str.str.len")) e1700:0)) { p414:true -> e1705:false; p415:false -> e1716:(e1715:(e1713:r641:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e1712:(e1710:(e1708:(e1706:r639:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e1707:r640:body->d1270:body) e1709:0) e1711:1)) e1714:"-") })
      my d331:"std.core.fmt.format_sign_prefix": std::core::fmt::format_spec -> std::text::str::str -> std::text::str::str -> std::text::str::str = e1738:(fn p416:d1271:spec -> e1737:(fn p417:d1272:head -> e1736:(fn p418:d1273:body -> e1735:case e1720:(e1719:r642:spec->d1271:spec.s54.sign->d308) { p420:r643:"opt::just"->d506:"std.data.opt.opt.just"(p419:r644:"format_sign::plus"->d301:"std.core.fmt.format_sign.plus") -> e1732:case e1725:(e1724:r647:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1723:(e1721:r645:starts_with_minus->d330:"std.core.fmt.starts_with_minus" e1722:r646:body->d1273:body)) { p421:true -> e1726:r648:head->d1272:head; p422:false -> e1731:(e1730:(e1728:r649:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1727:"+") e1729:r650:head->d1272:head) }; p424:r651:"opt::just"->d506:"std.data.opt.opt.just"(p423:r652:"format_sign::minus"->d302:"std.core.fmt.format_sign.minus") -> e1733:r653:head->d1272:head; p425:r654:"opt::nil"->d505:"std.data.opt.opt.nil" -> e1734:r655:head->d1272:head })))
      my d332:"std.core.fmt.format_with_padding": std::core::fmt::format_spec -> std::text::str::str -> std::text::str::str -> std::text::str::str = e1875:(fn p426:d1274:spec -> e1874:(fn p427:d1275:head -> e1873:(fn p428:d1276:body -> e1872:case e1740:(e1739:r656:spec->d1274:spec.s55.width->d312) { p429:r657:"opt::nil"->d505:"std.data.opt.opt.nil" -> e1759:block { let my p430:d1277:clipped = e1745:(e1743:(e1741:r658:format_body->d329:"std.core.fmt.format_body" e1742:r659:spec->d1274:spec) e1744:r660:body->d1276:body); e1758:block { let my p431:d1278:body_prefix = e1752:(e1750:(e1748:(e1746:r661:format_sign_prefix->d331:"std.core.fmt.format_sign_prefix" e1747:r662:spec->d1274:spec) e1749:r663:head->d1275:head) e1751:r664:clipped->d1277:clipped); e1757:(e1756:(e1754:r666:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1753:r665:body_prefix->d1278:body_prefix) e1755:r667:clipped->d1277:clipped) } }; p433:r668:"opt::just"->d506:"std.data.opt.opt.just"(p432:d1279:width) -> e1871:block { let my p434:d1280:clipped = e1764:(e1762:(e1760:r669:format_body->d329:"std.core.fmt.format_body" e1761:r670:spec->d1274:spec) e1763:r671:body->d1276:body); e1870:block { let my p435:d1281:body_prefix = e1771:(e1769:(e1767:(e1765:r672:format_sign_prefix->d331:"std.core.fmt.format_sign_prefix" e1766:r673:spec->d1274:spec) e1768:r674:head->d1275:head) e1770:r675:clipped->d1280:clipped); e1869:block { let my p436:d1282:text = e1776:(e1775:(e1773:r677:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1772:r676:body_prefix->d1281:body_prefix) e1774:r678:clipped->d1280:clipped); e1868:block { let my p437:d1283:missing = e1782:(e1781:(e1778:r680:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e1777:r679:width->d1279:width) e1780:(e1779:r681:text->d1282:text.s56.len->d840:"std.text.str.str.len")); e1867:case e1789:(e1788:r684:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1787:(e1786:(e1784:r683:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e1783:r682:missing->d1283:missing) e1785:0)) { p450:true -> e1790:r685:text->d1282:text; p451:false -> e1866:block { let my p438:d1284:fill = e1793:(e1791:r686:format_fill->d328:"std.core.fmt.format_fill" e1792:r687:spec->d1274:spec); e1865:case e1795:(e1794:r688:spec->d1274:spec.s57.align->d306) { p440:r689:"opt::just"->d506:"std.data.opt.opt.just"(p439:r690:"format_align::left"->d297:"std.core.fmt.format_align.left") -> e1804:(e1803:(e1797:r692:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1796:r691:text->d1282:text) e1802:(e1800:(e1798:r693:repeat->d327:"std.core.fmt.repeat" e1799:r694:fill->d1284:fill) e1801:r695:missing->d1283:missing)); p442:r696:"opt::just"->d506:"std.data.opt.opt.just"(p441:r697:"format_align::center"->d299:"std.core.fmt.format_align.center") -> e1833:block { let my p443:d1285:left = e1809:(e1808:(e1806:r699:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e1805:r698:missing->d1283:missing) e1807:2); e1832:block { let my p444:d1286:right = e1814:(e1813:(e1811:r701:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e1810:r700:missing->d1283:missing) e1812:r702:left->d1285:left); e1831:(e1830:(e1824:r708:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1823:(e1822:(e1820:r706:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1819:(e1817:(e1815:r703:repeat->d327:"std.core.fmt.repeat" e1816:r704:fill->d1284:fill) e1818:r705:left->d1285:left)) e1821:r707:text->d1282:text)) e1829:(e1827:(e1825:r709:repeat->d327:"std.core.fmt.repeat" e1826:r710:fill->d1284:fill) e1828:r711:right->d1286:right)) } }; p445:_ -> e1864:case e1837:(e1836:r713:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1835:(e1834:r712:spec->d1274:spec.s58.zero_pad->d318)) { p448:true -> e1854:block { let my p446:d1287:padding = e1842:(e1840:(e1838:r714:repeat->d327:"std.core.fmt.repeat" e1839:r715:fill->d1284:fill) e1841:r716:missing->d1283:missing); e1853:block { let my p447:d1288:padded_prefix = e1847:(e1846:(e1844:r718:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1843:r717:body_prefix->d1281:body_prefix) e1845:r719:padding->d1287:padding); e1852:(e1851:(e1849:r721:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1848:r720:padded_prefix->d1288:padded_prefix) e1850:r722:clipped->d1280:clipped) } }; p449:false -> e1863:(e1862:(e1860:r726:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1859:(e1857:(e1855:r723:repeat->d327:"std.core.fmt.repeat" e1856:r724:fill->d1284:fill) e1858:r725:missing->d1283:missing)) e1861:r727:text->d1282:text) } } } } } } } } })))
      pub d333:"std.core.fmt.format_display": std::core::fmt::format_spec -> 'a -> std::text::str::str where 'a: std::core::fmt::Display = e1885:(fn p452:d1289:spec -> e1884:(fn p453:d1290:value -> e1883:(e1880:(e1878:(e1876:r728:format_with_padding->d332:"std.core.fmt.format_with_padding" e1877:r729:spec->d1289:spec) e1879:"") e1882:(e1881:r730:value->d1290:value.s59.show=>d321:"std.core.fmt.Display.show"))))
      pub d334:"std.core.fmt.format_debug": std::core::fmt::format_spec -> 'a -> std::text::str::str where 'a: std::core::fmt::Debug = e1895:(fn p454:d1291:spec -> e1894:(fn p455:d1292:value -> e1893:(e1890:(e1888:(e1886:r731:format_with_padding->d332:"std.core.fmt.format_with_padding" e1887:r732:spec->d1291:spec) e1889:"") e1892:(e1891:r733:value->d1292:value.s60.debug=>d325:"std.core.fmt.Debug.debug"))))
      pub d335:"std.core.fmt.format_lower_hex": std::core::fmt::format_spec -> 'a -> std::text::str::str where 'a: std::num::LowerHex = e1913:(fn p456:d1293:spec -> e1912:(fn p457:d1294:value -> e1911:block { let my p458:d1295:head = e1902:case e1899:(e1898:r735:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1897:(e1896:r734:spec->d1293:spec.s61.alternate->d316)) { p459:true -> e1900:"0x"; p460:false -> e1901:"" }; e1910:(e1907:(e1905:(e1903:r736:format_with_padding->d332:"std.core.fmt.format_with_padding" e1904:r737:spec->d1293:spec) e1906:r738:head->d1295:head) e1909:(e1908:r739:value->d1294:value.s62.lower_hex=>d72:"std.num.LowerHex.lower_hex")) }))
      pub d336:"std.core.fmt.format_upper_hex": std::core::fmt::format_spec -> 'a -> std::text::str::str where 'a: std::num::UpperHex = e1931:(fn p461:d1296:spec -> e1930:(fn p462:d1297:value -> e1929:block { let my p463:d1298:head = e1920:case e1917:(e1916:r741:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1915:(e1914:r740:spec->d1296:spec.s63.alternate->d316)) { p464:true -> e1918:"0X"; p465:false -> e1919:"" }; e1928:(e1925:(e1923:(e1921:r742:format_with_padding->d332:"std.core.fmt.format_with_padding" e1922:r743:spec->d1296:spec) e1924:r744:head->d1298:head) e1927:(e1926:r745:value->d1297:value.s64.upper_hex=>d74:"std.num.UpperHex.upper_hex")) }))
      my d337 mod {
        d338: int -> std::text::str::str = e1935:(fn p466:d1299:x -> e1934:(e1932:r746:"std::int::to_string"->d56:"std.int.to_string" e1933:r747:x->d1299:x))
      }
      my d339 mod {
        d340: int -> std::text::str::str = e1938:(fn p467:d1300:x -> e1937:(e1936:r748:x->d1300:x.s65.show=>d321:"std.core.fmt.Display.show"))
      }
      my d341 mod {
        d342: float -> std::text::str::str = e1942:(fn p468:d1301:x -> e1941:(e1939:r749:"std::float::to_string"->d45:"std.float.to_string" e1940:r750:x->d1301:x))
      }
      my d343 mod {
        d344: float -> std::text::str::str = e1945:(fn p469:d1302:x -> e1944:(e1943:r751:x->d1302:x.s66.show=>d321:"std.core.fmt.Display.show"))
      }
      my d345 mod {
        d346: std::num::frac::frac -> std::text::str::str = e1949:(fn p470:d1303:x -> e1948:(e1946:r752:"std::num::frac::to_string"->d654:"std.num.frac.to_string" e1947:r753:x->d1303:x))
      }
      my d347 mod {
        d348: std::num::frac::frac -> std::text::str::str = e1952:(fn p471:d1304:x -> e1951:(e1950:r754:x->d1304:x.s67.show=>d321:"std.core.fmt.Display.show"))
      }
      my d349 mod {
        d350: bool -> std::text::str::str = e1956:(fn p472:d1305:x -> e1955:(e1953:r755:"std::bool::to_string"->d17:"std.bool.to_string" e1954:r756:x->d1305:x))
      }
      my d351 mod {
        d352: bool -> std::text::str::str = e1959:(fn p473:d1306:x -> e1958:(e1957:r757:x->d1306:x.s68.show=>d321:"std.core.fmt.Display.show"))
      }
      my d353 mod {
        d354: std::text::str::str -> std::text::str::str = e1961:(fn p474:d1307:x -> e1960:r758:x->d1307:x)
      }
      my d355 mod {
        d356: std::text::char::char -> std::text::str::str = e1965:(fn p475:d1308:x -> e1964:(e1962:r759:"std::text::char::to_string"->d674:"std.text.char.to_string" e1963:r760:x->d1308:x))
      }
      my d357 mod {
        d358: () -> std::text::str::str = e1967:(fn p476:d1309:x -> e1966:"()")
      }
      my d359:"std.core.fmt.show_list_items": std::data::list::list 'a -> std::text::str::str where 'a: std::core::fmt::Display = e1992:(fn p477:d1310:xs -> e1991:case e1970:(e1968:r761:"std::data::list::view_raw"->d479:"std.data.list.view_raw" e1969:r762:xs->d1310:xs) { p478:r763:"std::data::list::list_view::empty"->d458:"std.data.list.list_view.empty" -> e1971:""; p480:r764:"std::data::list::list_view::leaf"->d459:"std.data.list.list_view.leaf"(p479:d1311:item) -> e1973:(e1972:r765:item->d1311:item.s69.show=>d321:"std.core.fmt.Display.show"); p483:r766:"std::data::list::list_view::node"->d460:"std.data.list.list_view.node"(p481:d1312:left, p482:d1313:right) -> e1990:block { let my p484:d1314:left_text = e1976:(e1974:r767:show_list_items->d359:"std.core.fmt.show_list_items" e1975:r768:left->d1312:left); e1989:block { let my p485:d1315:right_text = e1979:(e1977:r769:show_list_items->d359:"std.core.fmt.show_list_items" e1978:r770:right->d1313:right); e1988:(e1987:(e1985:r773:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1984:(e1983:(e1981:r772:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1980:r771:left_text->d1314:left_text) e1982:", ")) e1986:r774:right_text->d1315:right_text) } } })
      my d360 mod {
        d361: std::data::list::list 'a -> std::text::str::str where 'a: std::core::fmt::Display = e2004:(fn p486:d1316:xs -> e2003:(e2002:(e2000:r778:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1999:(e1998:(e1994:r775:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1993:"[") e1997:(e1995:r776:show_list_items->d359:"std.core.fmt.show_list_items" e1996:r777:xs->d1316:xs))) e2001:"]"))
      }
      my d362 mod {
        d363: std::data::opt::opt 'a -> std::text::str::str where 'a: std::core::fmt::Display = e2014:(fn p487:d1317:value -> e2013:case e2005:r779:value->d1317:value { p488:r780:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil" -> e2006:"nil"; p490:r781:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just"(p489:d1318:inner) -> e2012:(e2011:(e2008:r782:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2007:"just ") e2010:(e2009:r783:inner->d1318:inner.s70.show=>d321:"std.core.fmt.Display.show")) })
      }
      my d364 mod {
        d365: std::data::result::result 'a 'b -> std::text::str::str where 'a: std::core::fmt::Display, 'b: std::core::fmt::Display = e2029:(fn p491:d1319:value -> e2028:case e2015:r784:value->d1319:value { p493:r785:"std::data::result::result::ok"->d531:"std.data.result.result.ok"(p492:d1320:inner) -> e2021:(e2020:(e2017:r786:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2016:"ok ") e2019:(e2018:r787:inner->d1320:inner.s71.show=>d321:"std.core.fmt.Display.show")); p495:r788:"std::data::result::result::err"->d532:"std.data.result.result.err"(p494:d1321:inner) -> e2027:(e2026:(e2023:r789:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2022:"err ") e2025:(e2024:r790:inner->d1321:inner.s72.show=>d321:"std.core.fmt.Display.show")) })
      }
      my d366 mod {
        d367: ('a, 'b) -> std::text::str::str where 'a: std::core::fmt::Display, 'b: std::core::fmt::Display = e2051:(fn p496:d1322:value -> e2050:case e2030:r791:value->d1322:value { p499:(p497:d1323:a, p498:d1324:b) -> e2049:(e2048:(e2046:r797:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2045:(e2044:(e2041:r795:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2040:(e2039:(e2037:r794:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2036:(e2035:(e2032:r792:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2031:"(") e2034:(e2033:r793:a->d1323:a.s73.show=>d321:"std.core.fmt.Display.show"))) e2038:", ")) e2043:(e2042:r796:b->d1324:b.s74.show=>d321:"std.core.fmt.Display.show"))) e2047:")") })
      }
      my d368 mod {
        d369: ('a, 'b, 'c) -> std::text::str::str where 'a: std::core::fmt::Display, 'b: std::core::fmt::Display, 'c: std::core::fmt::Display = e2082:(fn p500:d1325:value -> e2081:case e2052:r798:value->d1325:value { p504:(p501:d1326:a, p502:d1327:b, p503:d1328:c) -> e2080:(e2079:(e2077:r807:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2076:(e2075:(e2072:r805:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2071:(e2070:(e2068:r804:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2067:(e2066:(e2063:r802:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2062:(e2061:(e2059:r801:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2058:(e2057:(e2054:r799:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2053:"(") e2056:(e2055:r800:a->d1326:a.s75.show=>d321:"std.core.fmt.Display.show"))) e2060:", ")) e2065:(e2064:r803:b->d1327:b.s76.show=>d321:"std.core.fmt.Display.show"))) e2069:", ")) e2074:(e2073:r806:c->d1328:c.s77.show=>d321:"std.core.fmt.Display.show"))) e2078:")") })
      }
      my d370 mod {
        d371: ('a, 'b, 'c, 'd) -> std::text::str::str where 'a: std::core::fmt::Display, 'b: std::core::fmt::Display, 'c: std::core::fmt::Display, 'd: std::core::fmt::Display = e2122:(fn p505:d1329:value -> e2121:case e2083:r808:value->d1329:value { p510:(p506:d1330:a, p507:d1331:b, p508:d1332:c, p509:d1333:d) -> e2120:(e2119:(e2117:r820:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2116:(e2115:(e2112:r818:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2111:(e2110:(e2108:r817:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2107:(e2106:(e2103:r815:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2102:(e2101:(e2099:r814:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2098:(e2097:(e2094:r812:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2093:(e2092:(e2090:r811:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2089:(e2088:(e2085:r809:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2084:"(") e2087:(e2086:r810:a->d1330:a.s78.show=>d321:"std.core.fmt.Display.show"))) e2091:", ")) e2096:(e2095:r813:b->d1331:b.s79.show=>d321:"std.core.fmt.Display.show"))) e2100:", ")) e2105:(e2104:r816:c->d1332:c.s80.show=>d321:"std.core.fmt.Display.show"))) e2109:", ")) e2114:(e2113:r819:d->d1333:d.s81.show=>d321:"std.core.fmt.Display.show"))) e2118:")") })
      }
      my d372 mod {
        d373: ('a, 'b, 'c, 'd, 'e) -> std::text::str::str where 'a: std::core::fmt::Display, 'b: std::core::fmt::Display, 'c: std::core::fmt::Display, 'd: std::core::fmt::Display, 'e: std::core::fmt::Display = e2171:(fn p511:d1334:value -> e2170:case e2123:r821:value->d1334:value { p517:(p512:d1335:a, p513:d1336:b, p514:d1337:c, p515:d1338:d, p516:d1339:e) -> e2169:(e2168:(e2166:r836:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2165:(e2164:(e2161:r834:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2160:(e2159:(e2157:r833:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2156:(e2155:(e2152:r831:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2151:(e2150:(e2148:r830:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2147:(e2146:(e2143:r828:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2142:(e2141:(e2139:r827:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2138:(e2137:(e2134:r825:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2133:(e2132:(e2130:r824:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2129:(e2128:(e2125:r822:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2124:"(") e2127:(e2126:r823:a->d1335:a.s82.show=>d321:"std.core.fmt.Display.show"))) e2131:", ")) e2136:(e2135:r826:b->d1336:b.s83.show=>d321:"std.core.fmt.Display.show"))) e2140:", ")) e2145:(e2144:r829:c->d1337:c.s84.show=>d321:"std.core.fmt.Display.show"))) e2149:", ")) e2154:(e2153:r832:d->d1338:d.s85.show=>d321:"std.core.fmt.Display.show"))) e2158:", ")) e2163:(e2162:r835:e->d1339:e.s86.show=>d321:"std.core.fmt.Display.show"))) e2167:")") })
      }
      my d374 mod {
        d375: std::text::str::str -> std::text::str::str = e2181:(fn p518:d1340:x -> e2180:(e2179:(e2177:r839:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2176:(e2175:(e2173:r837:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2172:"\"") e2174:r838:x->d1340:x)) e2178:"\""))
      }
      my d376 mod {
        d377: std::text::char::char -> std::text::str::str = e2193:(fn p519:d1341:x -> e2192:(e2191:(e2189:r843:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2188:(e2187:(e2183:r840:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2182:"'") e2186:(e2184:r841:"std::text::char::to_string"->d674:"std.text.char.to_string" e2185:r842:x->d1341:x))) e2190:"'"))
      }
      my d378 mod {
        d379: () -> std::text::str::str = e2195:(fn p520:d1342:x -> e2194:"()")
      }
      my d380:"std.core.fmt.debug_list_items": std::data::list::list 'a -> std::text::str::str where 'a: std::core::fmt::Debug = e2220:(fn p521:d1343:xs -> e2219:case e2198:(e2196:r844:"std::data::list::view_raw"->d479:"std.data.list.view_raw" e2197:r845:xs->d1343:xs) { p522:r846:"std::data::list::list_view::empty"->d458:"std.data.list.list_view.empty" -> e2199:""; p524:r847:"std::data::list::list_view::leaf"->d459:"std.data.list.list_view.leaf"(p523:d1344:item) -> e2201:(e2200:r848:item->d1344:item.s87.debug=>d325:"std.core.fmt.Debug.debug"); p527:r849:"std::data::list::list_view::node"->d460:"std.data.list.list_view.node"(p525:d1345:left, p526:d1346:right) -> e2218:block { let my p528:d1347:left_text = e2204:(e2202:r850:debug_list_items->d380:"std.core.fmt.debug_list_items" e2203:r851:left->d1345:left); e2217:block { let my p529:d1348:right_text = e2207:(e2205:r852:debug_list_items->d380:"std.core.fmt.debug_list_items" e2206:r853:right->d1346:right); e2216:(e2215:(e2213:r856:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2212:(e2211:(e2209:r855:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2208:r854:left_text->d1347:left_text) e2210:", ")) e2214:r857:right_text->d1348:right_text) } } })
      my d381 mod {
        d382: std::data::list::list 'a -> std::text::str::str where 'a: std::core::fmt::Debug = e2232:(fn p530:d1349:xs -> e2231:(e2230:(e2228:r861:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2227:(e2226:(e2222:r858:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2221:"[") e2225:(e2223:r859:debug_list_items->d380:"std.core.fmt.debug_list_items" e2224:r860:xs->d1349:xs))) e2229:"]"))
      }
      my d383 mod {
        d384: std::data::opt::opt 'a -> std::text::str::str where 'a: std::core::fmt::Debug = e2242:(fn p531:d1350:value -> e2241:case e2233:r862:value->d1350:value { p532:r863:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil" -> e2234:"nil"; p534:r864:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just"(p533:d1351:inner) -> e2240:(e2239:(e2236:r865:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2235:"just ") e2238:(e2237:r866:inner->d1351:inner.s88.debug=>d325:"std.core.fmt.Debug.debug")) })
      }
      my d385 mod {
        d386: std::data::result::result 'a 'b -> std::text::str::str where 'a: std::core::fmt::Debug, 'b: std::core::fmt::Debug = e2257:(fn p535:d1352:value -> e2256:case e2243:r867:value->d1352:value { p537:r868:"std::data::result::result::ok"->d531:"std.data.result.result.ok"(p536:d1353:inner) -> e2249:(e2248:(e2245:r869:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2244:"ok ") e2247:(e2246:r870:inner->d1353:inner.s89.debug=>d325:"std.core.fmt.Debug.debug")); p539:r871:"std::data::result::result::err"->d532:"std.data.result.result.err"(p538:d1354:inner) -> e2255:(e2254:(e2251:r872:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2250:"err ") e2253:(e2252:r873:inner->d1354:inner.s90.debug=>d325:"std.core.fmt.Debug.debug")) })
      }
      my d387 mod {
        d388: ('a, 'b) -> std::text::str::str where 'a: std::core::fmt::Debug, 'b: std::core::fmt::Debug = e2279:(fn p540:d1355:value -> e2278:case e2258:r874:value->d1355:value { p543:(p541:d1356:a, p542:d1357:b) -> e2277:(e2276:(e2274:r880:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2273:(e2272:(e2269:r878:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2268:(e2267:(e2265:r877:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2264:(e2263:(e2260:r875:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2259:"(") e2262:(e2261:r876:a->d1356:a.s91.debug=>d325:"std.core.fmt.Debug.debug"))) e2266:", ")) e2271:(e2270:r879:b->d1357:b.s92.debug=>d325:"std.core.fmt.Debug.debug"))) e2275:")") })
      }
      my d389 mod {
        d390: ('a, 'b, 'c) -> std::text::str::str where 'a: std::core::fmt::Debug, 'b: std::core::fmt::Debug, 'c: std::core::fmt::Debug = e2310:(fn p544:d1358:value -> e2309:case e2280:r881:value->d1358:value { p548:(p545:d1359:a, p546:d1360:b, p547:d1361:c) -> e2308:(e2307:(e2305:r890:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2304:(e2303:(e2300:r888:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2299:(e2298:(e2296:r887:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2295:(e2294:(e2291:r885:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2290:(e2289:(e2287:r884:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2286:(e2285:(e2282:r882:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2281:"(") e2284:(e2283:r883:a->d1359:a.s93.debug=>d325:"std.core.fmt.Debug.debug"))) e2288:", ")) e2293:(e2292:r886:b->d1360:b.s94.debug=>d325:"std.core.fmt.Debug.debug"))) e2297:", ")) e2302:(e2301:r889:c->d1361:c.s95.debug=>d325:"std.core.fmt.Debug.debug"))) e2306:")") })
      }
      my d391 mod {
        d392: ('a, 'b, 'c, 'd) -> std::text::str::str where 'a: std::core::fmt::Debug, 'b: std::core::fmt::Debug, 'c: std::core::fmt::Debug, 'd: std::core::fmt::Debug = e2350:(fn p549:d1362:value -> e2349:case e2311:r891:value->d1362:value { p554:(p550:d1363:a, p551:d1364:b, p552:d1365:c, p553:d1366:d) -> e2348:(e2347:(e2345:r903:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2344:(e2343:(e2340:r901:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2339:(e2338:(e2336:r900:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2335:(e2334:(e2331:r898:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2330:(e2329:(e2327:r897:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2326:(e2325:(e2322:r895:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2321:(e2320:(e2318:r894:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2317:(e2316:(e2313:r892:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2312:"(") e2315:(e2314:r893:a->d1363:a.s96.debug=>d325:"std.core.fmt.Debug.debug"))) e2319:", ")) e2324:(e2323:r896:b->d1364:b.s97.debug=>d325:"std.core.fmt.Debug.debug"))) e2328:", ")) e2333:(e2332:r899:c->d1365:c.s98.debug=>d325:"std.core.fmt.Debug.debug"))) e2337:", ")) e2342:(e2341:r902:d->d1366:d.s99.debug=>d325:"std.core.fmt.Debug.debug"))) e2346:")") })
      }
      my d393 mod {
        d394: ('a, 'b, 'c, 'd, 'e) -> std::text::str::str where 'a: std::core::fmt::Debug, 'b: std::core::fmt::Debug, 'c: std::core::fmt::Debug, 'd: std::core::fmt::Debug, 'e: std::core::fmt::Debug = e2399:(fn p555:d1367:value -> e2398:case e2351:r904:value->d1367:value { p561:(p556:d1368:a, p557:d1369:b, p558:d1370:c, p559:d1371:d, p560:d1372:e) -> e2397:(e2396:(e2394:r919:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2393:(e2392:(e2389:r917:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2388:(e2387:(e2385:r916:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2384:(e2383:(e2380:r914:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2379:(e2378:(e2376:r913:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2375:(e2374:(e2371:r911:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2370:(e2369:(e2367:r910:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2366:(e2365:(e2362:r908:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2361:(e2360:(e2358:r907:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2357:(e2356:(e2353:r905:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2352:"(") e2355:(e2354:r906:a->d1368:a.s100.debug=>d325:"std.core.fmt.Debug.debug"))) e2359:", ")) e2364:(e2363:r909:b->d1369:b.s101.debug=>d325:"std.core.fmt.Debug.debug"))) e2368:", ")) e2373:(e2372:r912:c->d1370:c.s102.debug=>d325:"std.core.fmt.Debug.debug"))) e2377:", ")) e2382:(e2381:r915:d->d1371:d.s103.debug=>d325:"std.core.fmt.Debug.debug"))) e2386:", ")) e2391:(e2390:r918:e->d1372:e.s104.debug=>d325:"std.core.fmt.Debug.debug"))) e2395:")") })
      }
    }
    pub d26:"std.core.ops" mod {
      pub d395:"std.core.ops.#op:nullfix:return": () -> [std::control::flow::sub('a | ())] never = e2403:(fn p562:() -> e2402:(e2400:r920:"std::control::flow::sub::return"->d174:"std.control.flow.sub.return" e2401:()))
      pub d396:"std.core.ops.#op:prefix:return": 'a -> [std::control::flow::sub 'a] never = e2404:r921:"std::control::flow::sub::return"->d174:"std.control.flow.sub.return"
      pub d397:"std.core.ops.#op:prefix:fail": 'a -> ['b] never where 'a: std::control::throw::Throw(throws = 'b) = e2407:(fn p563:d1373:e -> e2406:(e2405:r922:e->d1373:e.s105.throw=>d234:"std.control.throw.Throw.throw"))
      pub d398:"std.core.ops.#op:nullfix:last": () -> [std::control::flow::loop] never = e2411:(fn p564:() -> e2410:(e2408:r923:loop_last->d429:"std.core.ops.loop_last" e2409:()))
      pub d399:"std.core.ops.#op:nullfix:next": () -> [std::control::flow::loop] never = e2415:(fn p565:() -> e2414:(e2412:r924:loop_next->d430:"std.core.ops.loop_next" e2413:()))
      pub d400:"std.core.ops.#op:nullfix:redo": () -> [std::control::flow::loop] never = e2419:(fn p566:() -> e2418:(e2416:r925:loop_redo->d431:"std.core.ops.loop_redo" e2417:()))
      pub d401:"std.core.ops.#op:prefix:last": 'a -> never where 'a: std::control::flow::LoopLabel = e2420:r926:label_last->d432:"std.core.ops.label_last"
      pub d402:"std.core.ops.#op:prefix:next": 'a -> never where 'a: std::control::flow::LoopLabel = e2421:r927:label_next->d433:"std.core.ops.label_next"
      pub d403:"std.core.ops.#op:prefix:redo": 'a -> never where 'a: std::control::flow::LoopLabel = e2422:r928:label_redo->d434:"std.core.ops.label_redo"
      pub d404:"std.core.ops.#op:nullfix:..": () -> std::data::range::range = e2426:(fn p567:() -> e2425:(e2423:r929:"std::data::range::full"->d521:"std.data.range.full" e2424:()))
      pub d405:"std.core.ops.#op:prefix:..": int -> std::data::range::range = e2427:r930:"std::data::range::to_included"->d519:"std.data.range.to_included"
      pub d406:"std.core.ops.#op:prefix:..<": int -> std::data::range::range = e2428:r931:"std::data::range::to_excluded"->d520:"std.data.range.to_excluded"
      pub d407:"std.core.ops.#op:suffix:..": int -> std::data::range::range = e2429:r932:"std::data::range::from_included"->d517:"std.data.range.from_included"
      pub d408:"std.core.ops.#op:suffix:<..": int -> std::data::range::range = e2430:r933:"std::data::range::from_excluded"->d518:"std.data.range.from_excluded"
      pub d409:"std.core.ops.#op:infix:..": int -> int -> std::data::range::range = e2431:r934:"std::data::range::inclusive"->d514:"std.data.range.inclusive"
      pub d410:"std.core.ops.#op:infix:..<": int -> int -> std::data::range::range = e2432:r935:"std::data::range::range"->d513:"std.data.range.range"
      pub d411:"std.core.ops.#op:infix:<..": int -> int -> std::data::range::range = e2433:r936:"std::data::range::from_exclusive_to_inclusive"->d516:"std.data.range.from_exclusive_to_inclusive"
      pub d412:"std.core.ops.#op:infix:<..<": int -> int -> std::data::range::range = e2434:r937:"std::data::range::exclusive"->d515:"std.data.range.exclusive"
      pub d413:"std.core.ops.#op:prefix:not": bool -> bool = e2435:r938:"std::bool::not"->d16:"std.bool.not"
      pub d414:"std.core.ops.#op:prefix:-": int -> int = e2441:(fn p568:d1374:x -> e2440:(e2438:(e2436:r939:"std::int::sub"->d53:"std.int.sub" e2437:0) e2439:r940:x->d1374:x))
      pub d415:"std.core.ops.#op:infix:+": 'a -> 'a -> 'a where 'a: std::num::Add = e2447:(fn p569:d1375:x -> e2446:(fn p570:d1376:y -> e2445:(e2443:(e2442:r941:x->d1375:x.s106.add=>d64:"std.num.Add.add") e2444:r942:y->d1376:y)))
      pub d416:"std.core.ops.#op:infix:-": 'a -> 'a -> 'a where 'a: std::num::Sub = e2453:(fn p571:d1377:x -> e2452:(fn p572:d1378:y -> e2451:(e2449:(e2448:r943:x->d1377:x.s107.sub=>d66:"std.num.Sub.sub") e2450:r944:y->d1378:y)))
      pub d417:"std.core.ops.#op:infix:*": 'a -> 'a -> 'a where 'a: std::num::Mul = e2459:(fn p573:d1379:x -> e2458:(fn p574:d1380:y -> e2457:(e2455:(e2454:r945:x->d1379:x.s108.mul=>d68:"std.num.Mul.mul") e2456:r946:y->d1380:y)))
      pub d418:"std.core.ops.#op:infix:/": 'a -> 'a -> 'b where 'a: std::num::Div(out = 'b) = e2465:(fn p575:d1381:x -> e2464:(fn p576:d1382:y -> e2463:(e2461:(e2460:r947:x->d1381:x.s109.div=>d70:"std.num.Div.div") e2462:r948:y->d1382:y)))
      pub d419:"std.core.ops.#op:infix:div": int -> int -> int = e2466:r949:"std::int::div"->d55:"std.int.div"
      pub d420:"std.core.ops.#op:infix:mod": int -> int -> int = e2467:r950:"std::int::mod"->d46:"std.int.mod"
      pub d421:"std.core.ops.#op:infix:==": 'a -> 'a -> bool where 'a: std::core::cmp::Eq = e2473:(fn p577:d1383:x -> e2472:(fn p578:d1384:y -> e2471:(e2469:(e2468:r951:x->d1383:x.s110.eq=>d250:"std.core.cmp.Eq.eq") e2470:r952:y->d1384:y)))
      pub d422:"std.core.ops.#op:infix:!=": 'a -> 'a -> bool where 'a: std::core::cmp::Eq = e2481:(fn p579:d1385:x -> e2480:(fn p580:d1386:y -> e2479:(e2474:r953:"std::bool::not"->d16:"std.bool.not" e2478:(e2476:(e2475:r954:x->d1385:x.s111.eq=>d250:"std.core.cmp.Eq.eq") e2477:r955:y->d1386:y))))
      pub d423:"std.core.ops.#op:infix:<": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = e2487:(fn p581:d1387:x -> e2486:(fn p582:d1388:y -> e2485:(e2483:(e2482:r956:x->d1387:x.s112.lt=>d252:"std.core.cmp.Ord.lt") e2484:r957:y->d1388:y)))
      pub d424:"std.core.ops.#op:infix:<=": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = e2493:(fn p583:d1389:x -> e2492:(fn p584:d1390:y -> e2491:(e2489:(e2488:r958:x->d1389:x.s113.le=>d253:"std.core.cmp.Ord.le") e2490:r959:y->d1390:y)))
      pub d425:"std.core.ops.#op:infix:>": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = e2499:(fn p585:d1391:x -> e2498:(fn p586:d1392:y -> e2497:(e2495:(e2494:r960:x->d1391:x.s114.gt=>d254:"std.core.cmp.Ord.gt") e2496:r961:y->d1392:y)))
      pub d426:"std.core.ops.#op:infix:>=": 'a -> 'a -> bool where 'a: std::core::cmp::Ord = e2505:(fn p587:d1393:x -> e2504:(fn p588:d1394:y -> e2503:(e2501:(e2500:r962:x->d1393:x.s115.ge=>d255:"std.core.cmp.Ord.ge") e2502:r963:y->d1394:y)))
      pub d427:"std.core.ops.#op:infix:and": (() -> ['a & [std::control::junction::junction; 'a]] bool) -> (() -> ['a] 'b) -> ['a] 'b | bool = e2517:(fn p589:d1395:a -> e2516:(fn p590:d1396:b -> e2515:case e2510:(e2509:r965:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e2508:(e2506:r964:a->d1395:a e2507:())) { p591:true -> e2513:(e2511:r966:b->d1396:b e2512:()); p592:false -> e2514:false }))
      pub d428:"std.core.ops.#op:infix:or": (() -> ['a & [std::control::junction::junction; 'a]] bool) -> (() -> ['a] 'b) -> ['a] 'b | bool = e2529:(fn p593:d1397:a -> e2528:(fn p594:d1398:b -> e2527:case e2522:(e2521:r968:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e2520:(e2518:r967:a->d1397:a e2519:())) { p595:true -> e2523:true; p596:false -> e2526:(e2524:r969:b->d1398:b e2525:()) }))
      my d429:"std.core.ops.loop_last": () -> [std::control::flow::loop] never = e2533:(fn p597:() -> e2532:(e2530:r970:"std::control::flow::loop::last"->d184:"std.control.flow.loop.last" e2531:()))
      my d430:"std.core.ops.loop_next": () -> [std::control::flow::loop] never = e2537:(fn p598:() -> e2536:(e2534:r971:"std::control::flow::loop::next"->d185:"std.control.flow.loop.next" e2535:()))
      my d431:"std.core.ops.loop_redo": () -> [std::control::flow::loop] never = e2541:(fn p599:() -> e2540:(e2538:r972:"std::control::flow::loop::redo"->d186:"std.control.flow.loop.redo" e2539:()))
      my d432:"std.core.ops.label_last": 'a -> never where 'a: std::control::flow::LoopLabel = e2546:(fn p600:d1399:label -> e2545:(e2543:(e2542:r973:label->d1399:label.s116.last=>d193:"std.control.flow.LoopLabel.last") e2544:()))
      my d433:"std.core.ops.label_next": 'a -> never where 'a: std::control::flow::LoopLabel = e2551:(fn p601:d1400:label -> e2550:(e2548:(e2547:r974:label->d1400:label.s117.next=>d194:"std.control.flow.LoopLabel.next") e2549:()))
      my d434:"std.core.ops.label_redo": 'a -> never where 'a: std::control::flow::LoopLabel = e2556:(fn p602:d1401:label -> e2555:(e2553:(e2552:r975:label->d1401:label.s118.redo=>d195:"std.control.flow.LoopLabel.redo") e2554:()))
    }
    pub d27:"std.core.seq" mod {
      pub d435:"std.core.seq.Len" mod {
        pub d436:"std.core.seq.Len.len": 'a -> int where 'a: std::core::seq::Len = <missing>
      }
      pub d437:"std.core.seq.IsEmpty" mod {
        pub d438:"std.core.seq.IsEmpty.is_empty": 'a -> bool where 'a: std::core::seq::IsEmpty = <missing>
      }
      my d439 mod {
        d440: std::text::str::str -> int = e2560:(fn p603:d1402:s -> e2559:(e2557:r976:"std::text::str::len"->d788:"std.text.str.len" e2558:r977:s->d1402:s))
      }
      my d441 mod {
        d442: std::data::list::list 'a -> int = e2564:(fn p604:d1403:xs -> e2563:(e2561:r978:"std::data::list::len"->d481:"std.data.list.len" e2562:r979:xs->d1403:xs))
      }
      my d443 mod {
        d444: std::text::str::str -> bool = e2572:(fn p605:d1404:s -> e2571:(e2569:(e2565:r980:"std::int::eq"->d47:"std.int.eq" e2568:(e2566:r981:"std::text::str::len"->d788:"std.text.str.len" e2567:r982:s->d1404:s)) e2570:0))
      }
      my d445 mod {
        d446: std::data::list::list 'a -> bool = e2580:(fn p606:d1405:xs -> e2579:(e2577:(e2573:r983:"std::int::eq"->d47:"std.int.eq" e2576:(e2574:r984:"std::data::list::len"->d481:"std.data.list.len" e2575:r985:xs->d1405:xs)) e2578:0))
      }
      my d447 mod {
        d448: std::text::bytes::bytes -> bool = e2588:(fn p607:d1406:b -> e2587:(e2585:(e2581:r986:"std::int::eq"->d47:"std.int.eq" e2584:(e2582:r987:"std::text::bytes::len"->d655:"std.text.bytes.len" e2583:r988:b->d1406:b)) e2586:0))
      }
      pub d449:"std.core.seq.len": 'a -> int where 'a: std::core::seq::Len = e2591:(fn p608:d1407:x -> e2590:(e2589:r989:x->d1407:x.s119.len=>d436:"std.core.seq.Len.len"))
    }
    pub d28:"std.core.id": 'a -> 'a = e7:(fn p0:d1013:x -> e6:r1:x->d1013:x)
    pub d29:"std.core.compose": ('a ['b#0[Empty]] -> ['c] 'd) -> ('e -> ['b#0[Empty]] 'a) -> 'e -> ['c#0] 'd#0 = e15:(fn p1:d1014:f -> e14:(fn p2:d1015:g -> e13:(fn p3:d1016:x -> e12:(e8:r2:f->d1014:f e11:(e9:r3:g->d1015:g e10:r4:x->d1016:x)))))
  }
  pub d4:"std.int" mod {
    pub d46:"std.int.mod": int -> int -> int = e26:builtin_op::int_mod
    pub d47:"std.int.eq": int -> int -> bool = e27:builtin_op::int_eq
    pub d48:"std.int.lt": int -> int -> bool = e28:builtin_op::int_lt
    pub d49:"std.int.le": int -> int -> bool = e29:builtin_op::int_le
    pub d50:"std.int.gt": int -> int -> bool = e30:builtin_op::int_gt
    pub d51:"std.int.ge": int -> int -> bool = e31:builtin_op::int_ge
    pub d52:"std.int.add": int -> int -> int = e32:builtin_op::int_add
    pub d53:"std.int.sub": int -> int -> int = e33:builtin_op::int_sub
    pub d54:"std.int.mul": int -> int -> int = e34:builtin_op::int_mul
    pub d55:"std.int.div": int -> int -> int = e35:builtin_op::int_div
    pub d56:"std.int.to_string": int -> std::text::str::str = e36:builtin_op::int_to_string
    pub d57:"std.int.to_hex": int -> std::text::str::str = e37:builtin_op::int_to_hex
    pub d58:"std.int.to_upper_hex": int -> std::text::str::str = e38:builtin_op::int_to_upper_hex
  }
  pub d5:"std.float" mod {
    pub d36:"std.float.eq": float -> float -> bool = e16:builtin_op::float_eq
    pub d37:"std.float.lt": float -> float -> bool = e17:builtin_op::float_lt
    pub d38:"std.float.le": float -> float -> bool = e18:builtin_op::float_le
    pub d39:"std.float.gt": float -> float -> bool = e19:builtin_op::float_gt
    pub d40:"std.float.ge": float -> float -> bool = e20:builtin_op::float_ge
    pub d41:"std.float.add": float -> float -> float = e21:builtin_op::float_add
    pub d42:"std.float.sub": float -> float -> float = e22:builtin_op::float_sub
    pub d43:"std.float.mul": float -> float -> float = e23:builtin_op::float_mul
    pub d44:"std.float.div": float -> float -> float = e24:builtin_op::float_div
    pub d45:"std.float.to_string": float -> std::text::str::str = e25:builtin_op::float_to_string
  }
  pub d6:"std.bool" mod {
    pub d15:"std.bool.eq": bool -> bool -> bool = e3:builtin_op::bool_eq
    pub d16:"std.bool.not": bool -> bool = e4:builtin_op::bool_not
    pub d17:"std.bool.to_string": bool -> std::text::str::str = e5:builtin_op::bool_to_string
  }
  pub d7:"std.num" mod {
    pub d62:"std.num.frac" mod {
      pub d635:"std.num.frac.frac": {num: int, den: int} -> std::num::frac::frac = <missing>
      my d640:"std.num.frac.abs": int -> int = e3706:(fn p943:d1633:x -> e3705:case e3698:(e3697:r1530:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e3696:(e3694:(e3692:r1528:"std::int::lt"->d48:"std.int.lt" e3693:r1529:x->d1633:x) e3695:0)) { p944:true -> e3703:(e3701:(e3699:r1531:"std::int::sub"->d53:"std.int.sub" e3700:0) e3702:r1532:x->d1633:x); p945:false -> e3704:r1533:x->d1633:x })
      my d641:"std.num.frac.gcd_positive": int -> int -> int = e3726:(fn p946:d1634:a -> e3725:(fn p947:d1635:b -> e3724:case e3713:(e3712:r1536:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e3711:(e3709:(e3707:r1534:"std::int::eq"->d47:"std.int.eq" e3708:r1535:b->d1635:b) e3710:0)) { p948:true -> e3714:r1537:a->d1634:a; p949:false -> e3723:(e3717:(e3715:r1538:gcd_positive->d641:"std.num.frac.gcd_positive" e3716:r1539:b->d1635:b) e3722:(e3720:(e3718:r1540:"std::int::mod"->d46:"std.int.mod" e3719:r1541:a->d1634:a) e3721:r1542:b->d1635:b)) }))
      my d642:"std.num.frac.gcd": int -> int -> int = e3737:(fn p950:d1636:a -> e3736:(fn p951:d1637:b -> e3735:(e3731:(e3727:r1543:gcd_positive->d641:"std.num.frac.gcd_positive" e3730:(e3728:r1544:abs->d640:"std.num.frac.abs" e3729:r1545:a->d1636:a)) e3734:(e3732:r1546:abs->d640:"std.num.frac.abs" e3733:r1547:b->d1637:b))))
      pub d643:"std.num.frac.new": int -> int -> std::num::frac::frac = e3783:(fn p952:d1638:n -> e3782:(fn p953:d1639:d -> e3781:block { let my p954:d1640:divisor = e3742:(e3740:(e3738:r1548:gcd->d642:"std.num.frac.gcd" e3739:r1549:n->d1638:n) e3741:r1550:d->d1639:d); e3780:block { let my p955:d1641:normalized_num = e3747:(e3745:(e3743:r1551:"std::int::div"->d55:"std.int.div" e3744:r1552:n->d1638:n) e3746:r1553:divisor->d1640:divisor); e3779:block { let my p956:d1642:normalized_den = e3752:(e3750:(e3748:r1554:"std::int::div"->d55:"std.int.div" e3749:r1555:d->d1639:d) e3751:r1556:divisor->d1640:divisor); e3778:case e3759:(e3758:r1559:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e3757:(e3755:(e3753:r1557:"std::int::lt"->d48:"std.int.lt" e3754:r1558:normalized_den->d1642:normalized_den) e3756:0)) { p957:true -> e3772:(e3760:r1560:frac->d635:"std.num.frac.frac" e3771:{num: e3765:(e3763:(e3761:r1561:"std::int::sub"->d53:"std.int.sub" e3762:0) e3764:r1562:normalized_num->d1641:normalized_num), den: e3770:(e3768:(e3766:r1563:"std::int::sub"->d53:"std.int.sub" e3767:0) e3769:r1564:normalized_den->d1642:normalized_den)}); p958:false -> e3777:(e3773:r1565:frac->d635:"std.num.frac.frac" e3776:{num: e3774:r1566:normalized_num->d1641:normalized_num, den: e3775:r1567:normalized_den->d1642:normalized_den}) } } } }))
      pub d644:"std.num.frac.add": std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e3812:(fn p959:d1643:x -> e3811:(fn p960:d1644:y -> e3810:(e3802:(e3784:r1568:new->d643:"std.num.frac.new" e3801:(e3793:(e3785:r1569:"std::int::add"->d52:"std.int.add" e3792:(e3789:(e3786:r1570:"std::int::mul"->d54:"std.int.mul" e3788:(e3787:r1571:x->d1643:x.s144.num->d636)) e3791:(e3790:r1572:y->d1644:y.s145.den->d638))) e3800:(e3797:(e3794:r1573:"std::int::mul"->d54:"std.int.mul" e3796:(e3795:r1574:y->d1644:y.s146.num->d636)) e3799:(e3798:r1575:x->d1643:x.s147.den->d638)))) e3809:(e3806:(e3803:r1576:"std::int::mul"->d54:"std.int.mul" e3805:(e3804:r1577:x->d1643:x.s148.den->d638)) e3808:(e3807:r1578:y->d1644:y.s149.den->d638)))))
      pub d645:"std.num.frac.sub": std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e3841:(fn p961:d1645:x -> e3840:(fn p962:d1646:y -> e3839:(e3831:(e3813:r1579:new->d643:"std.num.frac.new" e3830:(e3822:(e3814:r1580:"std::int::sub"->d53:"std.int.sub" e3821:(e3818:(e3815:r1581:"std::int::mul"->d54:"std.int.mul" e3817:(e3816:r1582:x->d1645:x.s150.num->d636)) e3820:(e3819:r1583:y->d1646:y.s151.den->d638))) e3829:(e3826:(e3823:r1584:"std::int::mul"->d54:"std.int.mul" e3825:(e3824:r1585:y->d1646:y.s152.num->d636)) e3828:(e3827:r1586:x->d1645:x.s153.den->d638)))) e3838:(e3835:(e3832:r1587:"std::int::mul"->d54:"std.int.mul" e3834:(e3833:r1588:x->d1645:x.s154.den->d638)) e3837:(e3836:r1589:y->d1646:y.s155.den->d638)))))
      pub d646:"std.num.frac.mul": std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e3860:(fn p963:d1647:x -> e3859:(fn p964:d1648:y -> e3858:(e3850:(e3842:r1590:new->d643:"std.num.frac.new" e3849:(e3846:(e3843:r1591:"std::int::mul"->d54:"std.int.mul" e3845:(e3844:r1592:x->d1647:x.s156.num->d636)) e3848:(e3847:r1593:y->d1648:y.s157.num->d636))) e3857:(e3854:(e3851:r1594:"std::int::mul"->d54:"std.int.mul" e3853:(e3852:r1595:x->d1647:x.s158.den->d638)) e3856:(e3855:r1596:y->d1648:y.s159.den->d638)))))
      pub d647:"std.num.frac.div": std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e3879:(fn p965:d1649:x -> e3878:(fn p966:d1650:y -> e3877:(e3869:(e3861:r1597:new->d643:"std.num.frac.new" e3868:(e3865:(e3862:r1598:"std::int::mul"->d54:"std.int.mul" e3864:(e3863:r1599:x->d1649:x.s160.num->d636)) e3867:(e3866:r1600:y->d1650:y.s161.den->d638))) e3876:(e3873:(e3870:r1601:"std::int::mul"->d54:"std.int.mul" e3872:(e3871:r1602:x->d1649:x.s162.den->d638)) e3875:(e3874:r1603:y->d1650:y.s163.num->d636)))))
      pub d648:"std.num.frac.eq": std::num::frac::frac -> std::num::frac::frac -> bool = e3899:(fn p967:d1651:x -> e3898:(fn p968:d1652:y -> e3897:case e3888:(e3887:r1607:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e3886:(e3883:(e3880:r1604:"std::int::eq"->d47:"std.int.eq" e3882:(e3881:r1605:x->d1651:x.s164.num->d636)) e3885:(e3884:r1606:y->d1652:y.s165.num->d636))) { p969:true -> e3895:(e3892:(e3889:r1608:"std::int::eq"->d47:"std.int.eq" e3891:(e3890:r1609:x->d1651:x.s166.den->d638)) e3894:(e3893:r1610:y->d1652:y.s167.den->d638)); p970:false -> e3896:false }))
      pub d649:"std.num.frac.lt": std::num::frac::frac -> std::num::frac::frac -> bool = e3918:(fn p971:d1653:x -> e3917:(fn p972:d1654:y -> e3916:(e3908:(e3900:r1611:"std::int::lt"->d48:"std.int.lt" e3907:(e3904:(e3901:r1612:"std::int::mul"->d54:"std.int.mul" e3903:(e3902:r1613:x->d1653:x.s168.num->d636)) e3906:(e3905:r1614:y->d1654:y.s169.den->d638))) e3915:(e3912:(e3909:r1615:"std::int::mul"->d54:"std.int.mul" e3911:(e3910:r1616:y->d1654:y.s170.num->d636)) e3914:(e3913:r1617:x->d1653:x.s171.den->d638)))))
      pub d650:"std.num.frac.le": std::num::frac::frac -> std::num::frac::frac -> bool = e3934:(fn p973:d1655:x -> e3933:(fn p974:d1656:y -> e3932:case e3925:(e3924:r1621:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e3923:(e3921:(e3919:r1618:lt->d649:"std.num.frac.lt" e3920:r1619:x->d1655:x) e3922:r1620:y->d1656:y)) { p975:true -> e3926:true; p976:false -> e3931:(e3929:(e3927:r1622:eq->d648:"std.num.frac.eq" e3928:r1623:x->d1655:x) e3930:r1624:y->d1656:y) }))
      pub d651:"std.num.frac.gt": std::num::frac::frac -> std::num::frac::frac -> bool = e3941:(fn p977:d1657:x -> e3940:(fn p978:d1658:y -> e3939:(e3937:(e3935:r1625:lt->d649:"std.num.frac.lt" e3936:r1626:y->d1658:y) e3938:r1627:x->d1657:x)))
      pub d652:"std.num.frac.ge": std::num::frac::frac -> std::num::frac::frac -> bool = e3957:(fn p979:d1659:x -> e3956:(fn p980:d1660:y -> e3955:case e3948:(e3947:r1631:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e3946:(e3944:(e3942:r1628:gt->d651:"std.num.frac.gt" e3943:r1629:x->d1659:x) e3945:r1630:y->d1660:y)) { p981:true -> e3949:true; p982:false -> e3954:(e3952:(e3950:r1632:eq->d648:"std.num.frac.eq" e3951:r1633:x->d1659:x) e3953:r1634:y->d1660:y) }))
      pub d653:"std.num.frac.to_float": std::num::frac::frac -> float = e3965:(fn p983:d1661:x -> e3964:(e3961:(e3958:r1635:"std::float::div"->d44:"std.float.div" e3960:(e3959:r1636:x->d1661:x.s172.num->d636)) e3963:(e3962:r1637:x->d1661:x.s173.den->d638)))
      pub d654:"std.num.frac.to_string": std::num::frac::frac -> std::text::str::str = e3994:(fn p984:d1662:x -> e3993:case e3973:(e3972:r1640:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e3971:(e3969:(e3966:r1638:"std::int::eq"->d47:"std.int.eq" e3968:(e3967:r1639:x->d1662:x.s174.den->d638)) e3970:1)) { p985:true -> e3977:(e3974:r1641:"std::int::to_string"->d56:"std.int.to_string" e3976:(e3975:r1642:x->d1662:x.s175.num->d636)); p986:false -> e3992:(e3987:(e3978:r1643:"std::text::str::concat"->d786:"std.text.str.concat" e3986:(e3984:(e3979:r1644:"std::text::str::concat"->d786:"std.text.str.concat" e3983:(e3980:r1645:"std::int::to_string"->d56:"std.int.to_string" e3982:(e3981:r1646:x->d1662:x.s176.num->d636))) e3985:"/")) e3991:(e3988:r1647:"std::int::to_string"->d56:"std.int.to_string" e3990:(e3989:r1648:x->d1662:x.s177.den->d638))) })
    }
    pub d63:"std.num.Add" mod {
      pub d64:"std.num.Add.add": 'a -> 'a -> 'a where 'a: std::num::Add = <missing>
    }
    pub d65:"std.num.Sub" mod {
      pub d66:"std.num.Sub.sub": 'a -> 'a -> 'a where 'a: std::num::Sub = <missing>
    }
    pub d67:"std.num.Mul" mod {
      pub d68:"std.num.Mul.mul": 'a -> 'a -> 'a where 'a: std::num::Mul = <missing>
    }
    pub d69:"std.num.Div" mod {
      pub d70:"std.num.Div.div": 'a -> 'a -> 'b where 'a: std::num::Div(out = 'b) = <missing>
    }
    pub d71:"std.num.LowerHex" mod {
      pub d72:"std.num.LowerHex.lower_hex": 'a -> std::text::str::str where 'a: std::num::LowerHex = <missing>
    }
    pub d73:"std.num.UpperHex" mod {
      pub d74:"std.num.UpperHex.upper_hex": 'a -> std::text::str::str where 'a: std::num::UpperHex = <missing>
    }
    my d75 mod {
      d76: int -> int -> int = e45:(fn p4:d1017:x -> e44:(fn p5:d1018:y -> e43:(e41:(e39:r5:"std::int::add"->d52:"std.int.add" e40:r6:x->d1017:x) e42:r7:y->d1018:y)))
    }
    my d77 mod {
      d78: int -> int -> int = e52:(fn p6:d1019:x -> e51:(fn p7:d1020:y -> e50:(e48:(e46:r8:"std::int::sub"->d53:"std.int.sub" e47:r9:x->d1019:x) e49:r10:y->d1020:y)))
    }
    my d79 mod {
      d80: int -> int -> int = e59:(fn p8:d1021:x -> e58:(fn p9:d1022:y -> e57:(e55:(e53:r11:"std::int::mul"->d54:"std.int.mul" e54:r12:x->d1021:x) e56:r13:y->d1022:y)))
    }
    my d81 mod {
      d82: int -> int -> std::num::frac::frac = e66:(fn p10:d1023:x -> e65:(fn p11:d1024:y -> e64:(e62:(e60:r14:"std::num::frac::new"->d643:"std.num.frac.new" e61:r15:x->d1023:x) e63:r16:y->d1024:y)))
    }
    my d83 mod {
      d84: int -> std::text::str::str = e70:(fn p12:d1025:x -> e69:(e67:r17:"std::int::to_hex"->d57:"std.int.to_hex" e68:r18:x->d1025:x))
    }
    my d85 mod {
      d86: int -> std::text::str::str = e74:(fn p13:d1026:x -> e73:(e71:r19:"std::int::to_upper_hex"->d58:"std.int.to_upper_hex" e72:r20:x->d1026:x))
    }
    my d87 mod {
      d88: float -> float -> float = e81:(fn p14:d1027:x -> e80:(fn p15:d1028:y -> e79:(e77:(e75:r21:"std::float::add"->d41:"std.float.add" e76:r22:x->d1027:x) e78:r23:y->d1028:y)))
    }
    my d89 mod {
      d90: float -> float -> float = e88:(fn p16:d1029:x -> e87:(fn p17:d1030:y -> e86:(e84:(e82:r24:"std::float::sub"->d42:"std.float.sub" e83:r25:x->d1029:x) e85:r26:y->d1030:y)))
    }
    my d91 mod {
      d92: float -> float -> float = e95:(fn p18:d1031:x -> e94:(fn p19:d1032:y -> e93:(e91:(e89:r27:"std::float::mul"->d43:"std.float.mul" e90:r28:x->d1031:x) e92:r29:y->d1032:y)))
    }
    my d93 mod {
      d94: float -> float -> float = e102:(fn p20:d1033:x -> e101:(fn p21:d1034:y -> e100:(e98:(e96:r30:"std::float::div"->d44:"std.float.div" e97:r31:x->d1033:x) e99:r32:y->d1034:y)))
    }
    my d95 mod {
      d96: std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e109:(fn p22:d1035:x -> e108:(fn p23:d1036:y -> e107:(e105:(e103:r33:"std::num::frac::add"->d644:"std.num.frac.add" e104:r34:x->d1035:x) e106:r35:y->d1036:y)))
    }
    my d97 mod {
      d98: std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e116:(fn p24:d1037:x -> e115:(fn p25:d1038:y -> e114:(e112:(e110:r36:"std::num::frac::sub"->d645:"std.num.frac.sub" e111:r37:x->d1037:x) e113:r38:y->d1038:y)))
    }
    my d99 mod {
      d100: std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e123:(fn p26:d1039:x -> e122:(fn p27:d1040:y -> e121:(e119:(e117:r39:"std::num::frac::mul"->d646:"std.num.frac.mul" e118:r40:x->d1039:x) e120:r41:y->d1040:y)))
    }
    my d101 mod {
      d102: std::num::frac::frac -> std::num::frac::frac -> std::num::frac::frac = e130:(fn p28:d1041:x -> e129:(fn p29:d1042:y -> e128:(e126:(e124:r42:"std::num::frac::div"->d647:"std.num.frac.div" e125:r43:x->d1041:x) e127:r44:y->d1042:y)))
    }
    my d103 mod {
      d104: std::text::str::str -> std::text::str::str -> std::text::str::str = e137:(fn p30:d1043:x -> e136:(fn p31:d1044:y -> e135:(e133:(e131:r45:"std::text::str::concat"->d786:"std.text.str.concat" e132:r46:x->d1043:x) e134:r47:y->d1044:y)))
    }
    my d105 mod {
      d106: std::data::list::list 'a -> std::data::list::list 'a -> std::data::list::list 'a = e144:(fn p32:d1045:xs -> e143:(fn p33:d1046:ys -> e142:(e140:(e138:r48:"std::data::list::merge"->d480:"std.data.list.merge" e139:r49:xs->d1045:xs) e141:r50:ys->d1046:ys)))
    }
  }
  pub d8:"std.data" mod {
    pub d30:"std.data.fold" mod {
      pub d450:"std.data.fold.Fold" mod {
        pub d451:"std.data.fold.Fold.fold": 'a -> 'b -> ('b -> 'c -> ['d] 'b) -> ['d] 'b where 'a: std::data::fold::Fold(item = 'c) = <missing>
        pub d452:"std.data.fold.Fold.find": 'a -> ('b -> ['c & [std::control::junction::junction; 'c]] bool) -> ['c] std::data::opt::opt 'b where 'a: std::data::fold::Fold(item = 'b) = e2616:(fn p609:d1408:container -> e2615:(fn p610:d1409:f -> e2614:(e2592:r990:"std::control::flow::sub::sub"->d175:"std.control.flow.sub.sub" e2613:block { let my p611:d1410:nil = e2593:r991:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil"; e2612:(e2597:(e2595:(e2594:r992:container->d1408:container.s120.fold=>d451:"std.data.fold.Fold.fold") e2596:r993:nil->d1410:nil) e2611:(fn p612:_ -> e2610:(fn p613:d1411:x -> e2609:case e2602:(e2601:r996:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e2600:(e2598:r994:f->d1409:f e2599:r995:x->d1411:x)) { p614:true -> e2607:(e2603:r997:"std::control::flow::sub::return"->d174:"std.control.flow.sub.return" e2606:(e2604:r998:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just" e2605:r999:x->d1411:x)); p615:false -> e2608:r1000:nil->d1410:nil }))) })))
        pub d453:"std.data.fold.Fold.contains": 'a -> 'b -> bool where 'a: std::data::fold::Fold(item = 'b), 'b: std::core::cmp::Eq = e2632:(fn p616:d1412:container -> e2631:(fn p617:d1413:target -> e2630:block { let my p618:d1414:found = e2625:(e2618:(e2617:r1001:container->d1412:container.s121.find=>d452:"std.data.fold.Fold.find") e2624:(fn p619:d1415:x -> e2623:(e2622:(e2620:r1003:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e2619:r1002:x->d1415:x) e2621:r1004:target->d1413:target))); e2629:case e2626:r1005:found->d1414:found { p620:r1006:"opt::nil"->d505:"std.data.opt.opt.nil" -> e2627:false; p622:r1007:"opt::just"->d506:"std.data.opt.opt.just"(p621:_) -> e2628:true } }))
        pub d454:"std.data.fold.Fold.each": 'a -> [std::control::nondet::nondet] 'b where 'a: std::data::fold::Fold(item = 'b) = e2636:(fn p623:d1416:container -> e2635:(e2633:r1008:"std::control::nondet::each"->d226:"std.control.nondet.nondet.each" e2634:r1009:container->d1416:container))
      }
    }
    pub d31:"std.data.index" mod {
      pub d455:"std.data.index.Index" mod {
        pub d456:"std.data.index.Index.index": 'a -> 'b -> 'c where 'a: std::data::index::Index('b, value = 'c) = <missing>
      }
    }
    pub d32:"std.data.list" mod {
      pub d457:"std.data.list.list_view" mod {
        pub d458:"std.data.list.list_view.empty": std::data::list::list_view 'a = <missing>
        pub d459:"std.data.list.list_view.leaf": 'a -> std::data::list::list_view 'a = <missing>
        pub d460:"std.data.list.list_view.node": std::data::list::list 'a -> std::data::list::list 'a -> std::data::list::list_view 'a = <missing>
      }
      pub d461:"std.data.list.list" mod {
        pub d462:"std.data.list.list.append": std::data::list::list 'a -> std::data::list::list 'a -> std::data::list::list 'a = e2643:(fn p624:d1417:xs -> e2642:(fn p625:d1418:ys -> e2641:(e2639:(e2637:r1010:"std::data::list::append"->d499:"std.data.list.append" e2638:r1011:xs->d1417:xs) e2640:r1012:ys->d1418:ys)))
        pub d463:"std.data.list.list.map": std::data::list::list 'a -> ('a -> ['b] 'c) -> ['b] std::data::list::list 'c = e2650:(fn p626:d1419:xs -> e2649:(fn p627:d1420:f -> e2648:(e2646:(e2644:r1013:"std::data::list::map"->d497:"std.data.list.map" e2645:r1014:xs->d1419:xs) e2647:r1015:f->d1420:f)))
        pub d464:"std.data.list.list.filter": std::data::list::list 'a -> ('a -> ['b & 'b] bool) -> ['b] std::data::list::list 'a = e2657:(fn p628:d1421:xs -> e2656:(fn p629:d1422:pred -> e2655:(e2653:(e2651:r1016:"std::data::list::filter"->d498:"std.data.list.filter" e2652:r1017:xs->d1421:xs) e2654:r1018:pred->d1422:pred)))
        pub d465:"std.data.list.list.splice": std::data::list::list 'a -> std::data::range::range -> std::data::list::list 'a -> std::data::list::list 'a = e2667:(fn p630:d1423:xs -> e2666:(fn p631:d1424:r -> e2665:(fn p632:d1425:ys -> e2664:(e2662:(e2660:(e2658:r1019:"std::data::list::splice"->d485:"std.data.list.splice" e2659:r1020:xs->d1423:xs) e2661:r1021:r->d1424:r) e2663:r1022:ys->d1425:ys))))
        pub d466:"std.data.list.list.join": std::data::list::list std::text::str::str -> std::text::str::str -> std::text::str::str = e2674:(fn p633:d1426:xs -> e2673:(fn p634:d1427:separator -> e2672:(e2670:(e2668:r1023:"std::text::str::join"->d867:"std.text.str.join" e2669:r1024:xs->d1426:xs) e2671:r1025:separator->d1427:separator)))
        pub d467:"std.data.list.list.is_empty": std::data::list::list 'a -> bool = e2678:(fn p635:d1428:xs -> e2677:(e2675:r1026:"std::data::list::is_empty"->d492:"std.data.list.is_empty" e2676:r1027:xs->d1428:xs))
        pub d468:"std.data.list.list.first": std::data::list::list 'a -> std::data::opt::opt 'a = e2682:(fn p636:d1429:xs -> e2681:(e2679:r1028:"std::data::list::first"->d500:"std.data.list.first" e2680:r1029:xs->d1429:xs))
        pub d469:"std.data.list.list.last": std::data::list::list 'a -> std::data::opt::opt 'a = e2686:(fn p637:d1430:xs -> e2685:(e2683:r1030:"std::data::list::last"->d501:"std.data.list.last" e2684:r1031:xs->d1430:xs))
        pub d470:"std.data.list.list.rev": std::data::list::list 'a -> std::data::list::list 'a = e2690:(fn p638:d1431:xs -> e2689:(e2687:r1032:"std::data::list::rev"->d496:"std.data.list.rev" e2688:r1033:xs->d1431:xs))
        pub d471:"std.data.list.list.sort": std::data::list::list 'a -> std::data::list::list 'a where std::num::Add('b & std::data::list::list 'a), 'a: std::core::cmp::Ord = e2694:(fn p639:d1432:xs -> e2693:(e2691:r1034:"std::data::list::sort"->d503:"std.data.list.sort" e2692:r1035:xs->d1432:xs))
        pub d472:"std.data.list.list.push!": std::control::var::ref('a, std::data::list::list 'b) -> 'b -> ['a] () = e2707:(fn p640:d1433:"&xs" -> e2706:(fn p641:d1434:x -> e2705:(e2695:r1036:"&xs"->d1433:"&xs" := e2704:(e2700:(e2699:(e2697:(e2696:r1037:"&xs"->d1433:"&xs".s122.get->d238) e2698:()).s123.append->d462:"std.data.list.list.append") e2703:(e2702:builtin_op::list_singleton e2701:r1038:x->d1434:x)))))
      }
      my d473 mod {
        d474: std::data::list::list('a & 'b) -> int -> 'a = e2714:(fn p642:d1435:xs -> e2713:(fn p643:d1436:i -> e2712:(e2710:(e2708:r1039:"std::data::list::index_raw"->d482:"std.data.list.index_raw" e2709:r1040:xs->d1435:xs) e2711:r1041:i->d1436:i)))
      }
      my d475 mod {
        d476: std::data::list::list 'a -> std::data::range::range -> std::data::list::list 'a = e2721:(fn p644:d1437:xs -> e2720:(fn p645:d1438:r -> e2719:(e2717:(e2715:r1042:"std::data::list::index_range"->d483:"std.data.list.index_range" e2716:r1043:xs->d1437:xs) e2718:r1044:r->d1438:r)))
      }
      my d477 mod {
        d478: std::control::var::ref('a & 'b, std::data::list::list('c & 'd)) -> int -> std::control::var::ref('b | 'a, 'd | 'c) = e2773:(fn p646:d1439:r -> e2772:(fn p647:d1440:i -> e2771:(e2722:r1045:ref->d237:"std.control.var.ref" e2770:{get: e2731:(fn p648:() -> e2730:(e2728:(e2723:r1046:"std::data::list::index_raw"->d482:"std.data.list.index_raw" e2727:(e2725:(e2724:r1047:r->d1439:r.s124.get->d238) e2726:())) e2729:r1048:i->d1440:i)), update_effect: e2769:(fn p649:() -> e2768:block { let my p650:d1441:loop = e2761:(fn p651:d1442:x -> e2760:catch e2732:r1049:x->d1442:x { std::control::var::ref_update::update p652:d1443:old, p653:d1444:k -> e2759:block { let my p654:d1445:new_item = e2739:(e2733:r1050:"ref_update::update"->d236:"std.control.var.ref_update.update" e2738:(e2736:(e2734:r1051:"std::data::list::index_raw"->d482:"std.data.list.index_raw" e2735:r1052:old->d1443:old) e2737:r1053:i->d1440:i)); e2758:(e2740:r1054:loop->d1441:loop e2757:(e2741:r1055:k->d1444:k e2756:(e2752:(e2746:(e2744:(e2742:r1056:"std::data::list::splice_raw"->d486:"std.data.list.splice_raw" e2743:r1057:old->d1443:old) e2745:r1058:i->d1440:i) e2751:(e2750:(e2748:r1060:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2747:r1059:i->d1440:i) e2749:1)) e2755:(e2754:builtin_op::list_singleton e2753:r1061:new_item->d1445:new_item)))) } }); e2767:(e2762:r1062:loop->d1441:loop e2766:(e2764:(e2763:r1063:r->d1439:r.s125.update_effect->d240) e2765:())) })})))
      }
      pub d479:"std.data.list.view_raw": std::data::list::list 'a -> std::data::list::list_view 'a = e2774:builtin_op::list_view_raw
      pub d480:"std.data.list.merge": std::data::list::list 'a -> std::data::list::list 'a -> std::data::list::list 'a = e2775:builtin_op::list_merge
      pub d481:"std.data.list.len": std::data::list::list 'a -> int = e2776:builtin_op::list_len
      pub d482:"std.data.list.index_raw": std::data::list::list 'a -> int -> 'a = e2777:builtin_op::list_index
      pub d483:"std.data.list.index_range": std::data::list::list 'a -> std::data::range::range -> std::data::list::list 'a = e2778:builtin_op::list_index_range
      pub d484:"std.data.list.index_range_raw": std::data::list::list 'a -> int -> int -> std::data::list::list 'a = e2779:builtin_op::list_index_range_raw
      pub d485:"std.data.list.splice": std::data::list::list 'a -> std::data::range::range -> std::data::list::list 'a -> std::data::list::list 'a = e2780:builtin_op::list_splice
      pub d486:"std.data.list.splice_raw": std::data::list::list 'a -> int -> int -> std::data::list::list 'a -> std::data::list::list 'a = e2781:builtin_op::list_splice_raw
      my d487:"std.data.list.fold_impl": std::data::list::list 'a -> ('b & 'c) -> ('b -> ['d] 'a -> ['e] 'c) -> ['e, 'd] 'c | 'b = e2807:(fn p655:d1446:xs -> e2806:(fn p656:d1447:z -> e2805:(fn p657:d1448:f -> e2804:case e2784:(e2782:r1064:"std::data::list::view_raw"->d479:"std.data.list.view_raw" e2783:r1065:xs->d1446:xs) { p658:r1066:"list_view::empty"->d458:"std.data.list.list_view.empty" -> e2785:r1067:z->d1447:z; p660:r1068:"list_view::leaf"->d459:"std.data.list.list_view.leaf"(p659:d1449:x) -> e2790:(e2788:(e2786:r1069:f->d1448:f e2787:r1070:z->d1447:z) e2789:r1071:x->d1449:x); p663:r1072:"list_view::node"->d460:"std.data.list.list_view.node"(p661:d1450:left, p662:d1451:right) -> e2803:(e2801:(e2793:(e2791:r1073:fold_impl->d487:"std.data.list.fold_impl" e2792:r1074:right->d1451:right) e2800:(e2798:(e2796:(e2794:r1075:fold_impl->d487:"std.data.list.fold_impl" e2795:r1076:left->d1450:left) e2797:r1077:z->d1447:z) e2799:r1078:f->d1448:f)) e2802:r1079:f->d1448:f) })))
      my d488 mod {
        d489: std::data::list::list 'a -> 'b -> ('b -> ['c] ('d | 'a) -> ['c] 'b) -> ['c] 'b = e2817:(fn p664:d1452:xs -> e2816:(fn p665:d1453:z -> e2815:(fn p666:d1454:f -> e2814:(e2812:(e2810:(e2808:r1080:fold_impl->d487:"std.data.list.fold_impl" e2809:r1081:xs->d1452:xs) e2811:r1082:z->d1453:z) e2813:r1083:f->d1454:f))))
      }
      pub d490:"std.data.list.empty": () -> std::data::list::list 'a = e2821:(fn p667:() -> e2820:(e2818:builtin_op::list_empty e2819:()))
      pub d491:"std.data.list.singleton": 'a -> std::data::list::list 'a = e2825:(fn p668:d1455:x -> e2824:(e2823:builtin_op::list_singleton e2822:r1084:x->d1455:x))
      pub d492:"std.data.list.is_empty": std::data::list::list 'a -> bool = e2833:(fn p669:d1456:xs -> e2832:(e2830:(e2826:r1085:"std::int::eq"->d47:"std.int.eq" e2829:(e2827:r1086:"std::data::list::len"->d481:"std.data.list.len" e2828:r1087:xs->d1456:xs)) e2831:0))
      pub d493:"std.data.list.cons": 'a -> std::data::list::list 'a -> std::data::list::list 'a = e2842:(fn p670:d1457:x -> e2841:(fn p671:d1458:xs -> e2840:(e2838:(e2834:r1088:"std::data::list::merge"->d480:"std.data.list.merge" e2837:(e2835:r1089:singleton->d491:"std.data.list.singleton" e2836:r1090:x->d1457:x)) e2839:r1091:xs->d1458:xs)))
      pub d494:"std.data.list.uncons": std::data::list::list 'a -> std::data::opt::opt ('a, std::data::list::list 'a) = e2871:(fn p672:d1459:xs -> e2870:block { let my p673:d1460:n = e2845:(e2843:r1092:"std::data::list::len"->d481:"std.data.list.len" e2844:r1093:xs->d1459:xs); e2869:case e2852:(e2851:r1096:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e2850:(e2848:(e2846:r1094:"std::int::eq"->d47:"std.int.eq" e2847:r1095:n->d1460:n) e2849:0)) { p674:true -> e2853:r1097:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil"; p675:false -> e2868:(e2854:r1098:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just" e2867:(e2859:(e2857:(e2855:r1099:"std::data::list::index_raw"->d482:"std.data.list.index_raw" e2856:r1100:xs->d1459:xs) e2858:0), e2866:(e2864:(e2862:(e2860:r1101:"std::data::list::index_range_raw"->d484:"std.data.list.index_range_raw" e2861:r1102:xs->d1459:xs) e2863:1) e2865:r1103:n->d1460:n))) } })
      pub d495:"std.data.list.fold": std::data::list::list 'a -> ('b & 'c) -> ('b -> ['d] 'a -> ['d] 'c) -> ['d] 'c | 'b = e2881:(fn p676:d1461:xs -> e2880:(fn p677:d1462:z -> e2879:(fn p678:d1463:f -> e2878:(e2876:(e2874:(e2872:r1104:fold_impl->d487:"std.data.list.fold_impl" e2873:r1105:xs->d1461:xs) e2875:r1106:z->d1462:z) e2877:r1107:f->d1463:f))))
      pub d496:"std.data.list.rev": std::data::list::list 'a -> std::data::list::list 'a = e2901:(fn p679:d1464:xs -> e2900:case e2884:(e2882:r1108:"std::data::list::view_raw"->d479:"std.data.list.view_raw" e2883:r1109:xs->d1464:xs) { p680:r1110:"list_view::empty"->d458:"std.data.list.list_view.empty" -> e2887:(e2885:r1111:empty->d490:"std.data.list.empty" e2886:()); p682:r1112:"list_view::leaf"->d459:"std.data.list.list_view.leaf"(p681:d1465:x) -> e2890:(e2888:r1113:singleton->d491:"std.data.list.singleton" e2889:r1114:x->d1465:x); p685:r1115:"list_view::node"->d460:"std.data.list.list_view.node"(p683:d1466:left, p684:d1467:right) -> e2899:(e2895:(e2891:r1116:append->d499:"std.data.list.append" e2894:(e2892:r1117:rev->d496:"std.data.list.rev" e2893:r1118:right->d1467:right)) e2898:(e2896:r1119:rev->d496:"std.data.list.rev" e2897:r1120:left->d1466:left)) })
      pub d497:"std.data.list.map": std::data::list::list 'a -> ('a -> ['b] 'c) -> ['b] std::data::list::list 'c = e2928:(fn p686:d1468:xs -> e2927:(fn p687:d1469:f -> e2926:case e2904:(e2902:r1121:"std::data::list::view_raw"->d479:"std.data.list.view_raw" e2903:r1122:xs->d1468:xs) { p688:r1123:"list_view::empty"->d458:"std.data.list.list_view.empty" -> e2907:(e2905:r1124:empty->d490:"std.data.list.empty" e2906:()); p690:r1125:"list_view::leaf"->d459:"std.data.list.list_view.leaf"(p689:d1470:x) -> e2912:(e2908:r1126:singleton->d491:"std.data.list.singleton" e2911:(e2909:r1127:f->d1469:f e2910:r1128:x->d1470:x)); p693:r1129:"list_view::node"->d460:"std.data.list.list_view.node"(p691:d1471:left, p692:d1472:right) -> e2925:(e2919:(e2913:r1130:append->d499:"std.data.list.append" e2918:(e2916:(e2914:r1131:map->d497:"std.data.list.map" e2915:r1132:left->d1471:left) e2917:r1133:f->d1469:f)) e2924:(e2922:(e2920:r1134:map->d497:"std.data.list.map" e2921:r1135:right->d1472:right) e2923:r1136:f->d1469:f)) }))
      pub d498:"std.data.list.filter": std::data::list::list 'a -> ('a -> ['b & 'b] bool) -> ['b] std::data::list::list 'a = e2962:(fn p694:d1473:xs -> e2961:(fn p695:d1474:pred -> e2960:case e2931:(e2929:r1137:"std::data::list::view_raw"->d479:"std.data.list.view_raw" e2930:r1138:xs->d1473:xs) { p696:r1139:"list_view::empty"->d458:"std.data.list.list_view.empty" -> e2934:(e2932:r1140:empty->d490:"std.data.list.empty" e2933:()); p698:r1141:"list_view::leaf"->d459:"std.data.list.list_view.leaf"(p697:d1475:x) -> e2946:case e2939:(e2938:r1144:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e2937:(e2935:r1142:pred->d1474:pred e2936:r1143:x->d1475:x)) { p699:true -> e2942:(e2940:r1145:singleton->d491:"std.data.list.singleton" e2941:r1146:x->d1475:x); p700:false -> e2945:(e2943:r1147:empty->d490:"std.data.list.empty" e2944:()) }; p703:r1148:"list_view::node"->d460:"std.data.list.list_view.node"(p701:d1476:left, p702:d1477:right) -> e2959:(e2953:(e2947:r1149:append->d499:"std.data.list.append" e2952:(e2950:(e2948:r1150:filter->d498:"std.data.list.filter" e2949:r1151:left->d1476:left) e2951:r1152:pred->d1474:pred)) e2958:(e2956:(e2954:r1153:filter->d498:"std.data.list.filter" e2955:r1154:right->d1477:right) e2957:r1155:pred->d1474:pred)) }))
      pub d499:"std.data.list.append": std::data::list::list 'a -> std::data::list::list 'a -> std::data::list::list 'a = e2969:(fn p704:d1478:xs -> e2968:(fn p705:d1479:ys -> e2967:(e2965:(e2963:r1156:"std::data::list::merge"->d480:"std.data.list.merge" e2964:r1157:xs->d1478:xs) e2966:r1158:ys->d1479:ys)))
      pub d500:"std.data.list.first": std::data::list::list 'a -> std::data::opt::opt 'a = e2978:(fn p706:d1480:xs -> e2977:case e2972:(e2970:r1159:uncons->d494:"std.data.list.uncons" e2971:r1160:xs->d1480:xs) { p707:r1161:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil" -> e2973:r1162:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil"; p711:r1163:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just"(p710:(p708:d1481:head, p709:_)) -> e2976:(e2974:r1164:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just" e2975:r1165:head->d1481:head) })
      pub d501:"std.data.list.last": std::data::list::list 'a -> std::data::opt::opt 'a = e2996:(fn p712:d1482:xs -> e2995:case e2981:(e2979:r1166:uncons->d494:"std.data.list.uncons" e2980:r1167:xs->d1482:xs) { p713:r1168:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil" -> e2982:r1169:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil"; p717:r1170:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just"(p716:(p714:d1483:head, p715:d1484:tail)) -> e2994:case e2987:(e2986:r1173:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e2985:(e2983:r1171:is_empty->d492:"std.data.list.is_empty" e2984:r1172:tail->d1484:tail)) { p718:true -> e2990:(e2988:r1174:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just" e2989:r1175:head->d1483:head); p719:false -> e2993:(e2991:r1176:"std::data::list::last"->d501:"std.data.list.last" e2992:r1177:tail->d1484:tail) } })
      my d502:"std.data.list.sort_split": std::data::list::list('a & 'b) -> 'b -> ('c | std::data::list::list('a & 'b), 'd | std::data::list::list('a & 'b)) where 'c: std::num::Add, 'd: std::num::Add, std::core::cmp::Ord('b | 'a) = e3053:(fn p720:d1485:xs -> e3052:(fn p721:d1486:x -> e3051:case e2999:(e2997:r1178:"std::data::list::view_raw"->d479:"std.data.list.view_raw" e2998:r1179:xs->d1485:xs) { p722:r1180:"list_view::empty"->d458:"std.data.list.list_view.empty" -> e3006:(e3002:(e3000:builtin_op::list_empty e3001:()), e3005:(e3003:builtin_op::list_empty e3004:())); p724:r1181:"list_view::leaf"->d459:"std.data.list.list_view.leaf"(p723:d1487:y) if e3013:(e3012:r1185:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e3011:(e3010:(e3008:r1183:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e3007:r1182:y->d1487:y) e3009:r1184:x->d1486:x)) -> e3020:(e3016:(e3015:builtin_op::list_singleton e3014:r1186:y->d1487:y), e3019:(e3017:builtin_op::list_empty e3018:())); p726:r1187:"list_view::leaf"->d459:"std.data.list.list_view.leaf"(p725:d1488:y) -> e3027:(e3023:(e3021:builtin_op::list_empty e3022:()), e3026:(e3025:builtin_op::list_singleton e3024:r1188:y->d1488:y)); p729:r1189:"list_view::node"->d460:"std.data.list.list_view.node"(p727:d1489:l, p728:d1490:r) -> e3050:block { let my p736:(p732:(p730:d1491:ll, p731:d1492:lr), p735:(p733:d1493:rl, p734:d1494:rr)) = e3038:(e3032:(e3030:(e3028:r1190:sort_split->d502:"std.data.list.sort_split" e3029:r1191:l->d1489:l) e3031:r1192:x->d1486:x), e3037:(e3035:(e3033:r1193:sort_split->d502:"std.data.list.sort_split" e3034:r1194:r->d1490:r) e3036:r1195:x->d1486:x)); e3049:(e3043:(e3042:(e3040:r1197:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3039:r1196:ll->d1491:ll) e3041:r1198:rl->d1493:rl), e3048:(e3047:(e3045:r1200:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3044:r1199:lr->d1492:lr) e3046:r1201:rr->d1494:rr)) } }))
      pub d503:"std.data.list.sort": std::data::list::list 'a -> std::data::list::list 'a where std::num::Add('b & std::data::list::list 'a), 'a: std::core::cmp::Ord = e3080:(fn p737:d1495:xs -> e3079:case e3054:r1202:xs->d1495:xs { p738:[] -> e3057:(e3055:builtin_op::list_empty e3056:()); p741:[p739:d1496:x, ..p740:d1497:xs] -> e3078:block { let my p744:(p742:d1498:l, p743:d1499:r) = e3062:(e3060:(e3058:r1203:sort_split->d502:"std.data.list.sort_split" e3059:r1204:xs->d1497:xs) e3061:r1205:x->d1496:x); e3077:(e3076:(e3075:builtin_op::list_merge e3065:(e3063:r1206:sort->d503:"std.data.list.sort" e3064:r1207:l->d1498:l)) e3074:(e3073:(e3072:builtin_op::list_merge e3068:(e3067:builtin_op::list_singleton e3066:r1208:x->d1496:x)) e3071:(e3069:r1209:sort->d503:"std.data.list.sort" e3070:r1210:r->d1499:r))) } })
    }
    pub d33:"std.data.opt" mod {
      pub d504:"std.data.opt.opt" mod {
        pub d505:"std.data.opt.opt.nil": std::data::opt::opt 'a = <missing>
        pub d506:"std.data.opt.opt.just": 'a -> std::data::opt::opt 'a = <missing>
      }
    }
    pub d34:"std.data.range" mod {
      pub d507:"std.data.range.bound" mod {
        pub d508:"std.data.range.bound.unbounded": std::data::range::bound = <missing>
        pub d509:"std.data.range.bound.included": int -> std::data::range::bound = <missing>
        pub d510:"std.data.range.bound.excluded": int -> std::data::range::bound = <missing>
      }
      pub d511:"std.data.range.range" mod {
        pub d512:"std.data.range.range.within": std::data::range::bound -> std::data::range::bound -> std::data::range::range = <missing>
      }
      pub d513:"std.data.range.range": int -> int -> std::data::range::range = e3091:(fn p745:d1500:start -> e3090:(fn p746:d1501:end -> e3089:(e3085:(e3081:r1211:"range::within"->d512:"std.data.range.range.within" e3084:(e3082:r1212:"bound::included"->d509:"std.data.range.bound.included" e3083:r1213:start->d1500:start)) e3088:(e3086:r1214:"bound::excluded"->d510:"std.data.range.bound.excluded" e3087:r1215:end->d1501:end))))
      pub d514:"std.data.range.inclusive": int -> int -> std::data::range::range = e3102:(fn p747:d1502:start -> e3101:(fn p748:d1503:end -> e3100:(e3096:(e3092:r1216:"range::within"->d512:"std.data.range.range.within" e3095:(e3093:r1217:"bound::included"->d509:"std.data.range.bound.included" e3094:r1218:start->d1502:start)) e3099:(e3097:r1219:"bound::included"->d509:"std.data.range.bound.included" e3098:r1220:end->d1503:end))))
      pub d515:"std.data.range.exclusive": int -> int -> std::data::range::range = e3113:(fn p749:d1504:start -> e3112:(fn p750:d1505:end -> e3111:(e3107:(e3103:r1221:"range::within"->d512:"std.data.range.range.within" e3106:(e3104:r1222:"bound::excluded"->d510:"std.data.range.bound.excluded" e3105:r1223:start->d1504:start)) e3110:(e3108:r1224:"bound::excluded"->d510:"std.data.range.bound.excluded" e3109:r1225:end->d1505:end))))
      pub d516:"std.data.range.from_exclusive_to_inclusive": int -> int -> std::data::range::range = e3124:(fn p751:d1506:start -> e3123:(fn p752:d1507:end -> e3122:(e3118:(e3114:r1226:"range::within"->d512:"std.data.range.range.within" e3117:(e3115:r1227:"bound::excluded"->d510:"std.data.range.bound.excluded" e3116:r1228:start->d1506:start)) e3121:(e3119:r1229:"bound::included"->d509:"std.data.range.bound.included" e3120:r1230:end->d1507:end))))
      pub d517:"std.data.range.from_included": int -> std::data::range::range = e3132:(fn p753:d1508:start -> e3131:(e3129:(e3125:r1231:"range::within"->d512:"std.data.range.range.within" e3128:(e3126:r1232:"bound::included"->d509:"std.data.range.bound.included" e3127:r1233:start->d1508:start)) e3130:r1234:"bound::unbounded"->d508:"std.data.range.bound.unbounded"))
      pub d518:"std.data.range.from_excluded": int -> std::data::range::range = e3140:(fn p754:d1509:start -> e3139:(e3137:(e3133:r1235:"range::within"->d512:"std.data.range.range.within" e3136:(e3134:r1236:"bound::excluded"->d510:"std.data.range.bound.excluded" e3135:r1237:start->d1509:start)) e3138:r1238:"bound::unbounded"->d508:"std.data.range.bound.unbounded"))
      pub d519:"std.data.range.to_included": int -> std::data::range::range = e3148:(fn p755:d1510:end -> e3147:(e3143:(e3141:r1239:"range::within"->d512:"std.data.range.range.within" e3142:r1240:"bound::unbounded"->d508:"std.data.range.bound.unbounded") e3146:(e3144:r1241:"bound::included"->d509:"std.data.range.bound.included" e3145:r1242:end->d1510:end)))
      pub d520:"std.data.range.to_excluded": int -> std::data::range::range = e3156:(fn p756:d1511:end -> e3155:(e3151:(e3149:r1243:"range::within"->d512:"std.data.range.range.within" e3150:r1244:"bound::unbounded"->d508:"std.data.range.bound.unbounded") e3154:(e3152:r1245:"bound::excluded"->d510:"std.data.range.bound.excluded" e3153:r1246:end->d1511:end)))
      pub d521:"std.data.range.full": () -> std::data::range::range = e3162:(fn p757:() -> e3161:(e3159:(e3157:r1247:"range::within"->d512:"std.data.range.range.within" e3158:r1248:"bound::unbounded"->d508:"std.data.range.bound.unbounded") e3160:r1249:"bound::unbounded"->d508:"std.data.range.bound.unbounded"))
      pub d522:"std.data.range.start": std::data::range::range -> std::data::range::bound = e3166:(fn p758:d1512:r -> e3165:case e3163:r1250:r->d1512:r { p761:r1251:"range::within"->d512:"std.data.range.range.within"(p759:d1513:start, p760:_) -> e3164:r1252:start->d1513:start })
      pub d523:"std.data.range.end": std::data::range::range -> std::data::range::bound = e3170:(fn p762:d1514:r -> e3169:case e3167:r1253:r->d1514:r { p765:r1254:"range::within"->d512:"std.data.range.range.within"(p763:_, p764:d1515:end) -> e3168:r1255:end->d1515:end })
      my d524:"std.data.range.first_int": std::data::range::bound -> int = e3180:(fn p766:d1516:b -> e3179:case e3171:r1256:b->d1516:b { p767:r1257:"bound::unbounded"->d508:"std.data.range.bound.unbounded" -> e3172:0; p769:r1258:"bound::included"->d509:"std.data.range.bound.included"(p768:d1517:x) -> e3173:r1259:x->d1517:x; p771:r1260:"bound::excluded"->d510:"std.data.range.bound.excluded"(p770:d1518:x) -> e3178:(e3177:(e3175:r1262:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3174:r1261:x->d1518:x) e3176:1) })
      my d525:"std.data.range.last_exclusive_int": std::data::range::bound -> int = e3190:(fn p772:d1519:b -> e3189:case e3181:r1263:b->d1519:b { p773:r1264:"bound::unbounded"->d508:"std.data.range.bound.unbounded" -> e3182:0; p775:r1265:"bound::included"->d509:"std.data.range.bound.included"(p774:d1520:x) -> e3187:(e3186:(e3184:r1267:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3183:r1266:x->d1520:x) e3185:1); p777:r1268:"bound::excluded"->d510:"std.data.range.bound.excluded"(p776:d1521:x) -> e3188:r1269:x->d1521:x })
      my d526:"std.data.range.fold_ints": ('a -> ['b] int -> ['b] 'a) -> int -> int -> 'a -> ['b] 'a = e3220:(fn p778:d1522:f -> e3219:(fn p779:d1523:i -> e3218:(fn p780:d1524:end -> e3217:(fn p781:d1525:acc -> e3216:case e3197:(e3196:r1273:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e3195:(e3194:(e3192:r1271:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e3191:r1270:i->d1523:i) e3193:r1272:end->d1524:end)) { p782:true -> e3214:(e3208:(e3206:(e3200:(e3198:r1274:fold_ints->d526:"std.data.range.fold_ints" e3199:r1275:f->d1522:f) e3205:(e3204:(e3202:r1277:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3201:r1276:i->d1523:i) e3203:1)) e3207:r1278:end->d1524:end) e3213:(e3211:(e3209:r1279:f->d1522:f e3210:r1280:acc->d1525:acc) e3212:r1281:i->d1523:i)); p783:false -> e3215:r1282:acc->d1525:acc }))))
      my d527:"std.data.range.fold_from": ('a -> ['b] int -> ['b] 'a) -> int -> 'a -> ['b] 'a = e3243:(fn p784:d1526:f -> e3242:(fn p785:d1527:i -> e3241:(fn p786:d1528:acc -> e3240:case e3223:(e3222:r1283:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e3221:true) { p787:true -> e3238:(e3232:(e3226:(e3224:r1284:fold_from->d527:"std.data.range.fold_from" e3225:r1285:f->d1526:f) e3231:(e3230:(e3228:r1287:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3227:r1286:i->d1527:i) e3229:1)) e3237:(e3235:(e3233:r1288:f->d1526:f e3234:r1289:acc->d1528:acc) e3236:r1290:i->d1527:i)); p788:false -> e3239:r1291:acc->d1528:acc })))
      my d528 mod {
        d529: std::data::range::range -> 'a -> ('a -> ['b] int -> ['b] 'a) -> ['b] 'a = e3270:(fn p789:d1529:r -> e3269:(fn p790:d1530:z -> e3268:(fn p791:d1531:f -> e3267:case e3244:r1292:r->d1529:r { p794:r1293:"range::within"->d512:"std.data.range.range.within"(p792:d1532:start, p793:r1294:"bound::unbounded"->d508:"std.data.range.bound.unbounded") -> e3253:(e3251:(e3247:(e3245:r1295:fold_from->d527:"std.data.range.fold_from" e3246:r1296:f->d1531:f) e3250:(e3248:r1297:first_int->d524:"std.data.range.first_int" e3249:r1298:start->d1532:start)) e3252:r1299:z->d1530:z); p797:r1300:"range::within"->d512:"std.data.range.range.within"(p795:d1533:start, p796:d1534:end) -> e3266:(e3264:(e3260:(e3256:(e3254:r1301:fold_ints->d526:"std.data.range.fold_ints" e3255:r1302:f->d1531:f) e3259:(e3257:r1303:first_int->d524:"std.data.range.first_int" e3258:r1304:start->d1533:start)) e3263:(e3261:r1305:last_exclusive_int->d525:"std.data.range.last_exclusive_int" e3262:r1306:end->d1534:end)) e3265:r1307:z->d1530:z) })))
      }
    }
    pub d35:"std.data.result" mod {
      pub d530:"std.data.result.result" mod {
        pub d531:"std.data.result.result.ok": 'a -> std::data::result::result 'a 'b = <missing>
        pub d532:"std.data.result.result.err": 'a -> std::data::result::result 'b 'a = <missing>
        pub d533:"std.data.result.result.map": std::data::result::result 'a 'b -> ('a -> ['c] 'd) -> ['c] std::data::result::result 'd 'b = e3277:(fn p798:d1535:r -> e3276:(fn p799:d1536:f -> e3275:(e3273:(e3271:r1308:"std::data::result::map"->d536:"std.data.result.map" e3272:r1309:r->d1535:r) e3274:r1310:f->d1536:f)))
        pub d534:"std.data.result.result.and_then": std::data::result::result 'a 'b -> ('a -> ['c] std::data::result::result 'd 'b) -> ['c] std::data::result::result 'd 'b = e3284:(fn p800:d1537:r -> e3283:(fn p801:d1538:f -> e3282:(e3280:(e3278:r1311:"std::data::result::and_then"->d537:"std.data.result.and_then" e3279:r1312:r->d1537:r) e3281:r1313:f->d1538:f)))
        pub d535:"std.data.result.result.unwrap_or": std::data::result::result 'a 'b -> 'a -> 'a = e3291:(fn p802:d1539:r -> e3290:(fn p803:d1540:fallback -> e3289:(e3287:(e3285:r1314:"std::data::result::unwrap_or"->d538:"std.data.result.unwrap_or" e3286:r1315:r->d1539:r) e3288:r1316:fallback->d1540:fallback)))
      }
      pub d536:"std.data.result.map": std::data::result::result 'a 'b -> ('a -> ['c] 'd) -> ['c] std::data::result::result 'd 'b = e3303:(fn p804:d1541:r -> e3302:(fn p805:d1542:f -> e3301:case e3292:r1317:r->d1541:r { p807:r1318:"result::ok"->d531:"std.data.result.result.ok"(p806:d1543:value) -> e3297:(e3293:r1319:"result::ok"->d531:"std.data.result.result.ok" e3296:(e3294:r1320:f->d1542:f e3295:r1321:value->d1543:value)); p809:r1322:"result::err"->d532:"std.data.result.result.err"(p808:d1544:err) -> e3300:(e3298:r1323:"result::err"->d532:"std.data.result.result.err" e3299:r1324:err->d1544:err) }))
      pub d537:"std.data.result.and_then": std::data::result::result 'a 'b -> ('a -> ['c] std::data::result::result 'd 'b) -> ['c] std::data::result::result 'd 'b = e3313:(fn p810:d1545:r -> e3312:(fn p811:d1546:f -> e3311:case e3304:r1325:r->d1545:r { p813:r1326:"result::ok"->d531:"std.data.result.result.ok"(p812:d1547:value) -> e3307:(e3305:r1327:f->d1546:f e3306:r1328:value->d1547:value); p815:r1329:"result::err"->d532:"std.data.result.result.err"(p814:d1548:err) -> e3310:(e3308:r1330:"result::err"->d532:"std.data.result.result.err" e3309:r1331:err->d1548:err) }))
      pub d538:"std.data.result.unwrap_or": std::data::result::result 'a 'b -> 'a -> 'a = e3319:(fn p816:d1549:r -> e3318:(fn p817:d1550:fallback -> e3317:case e3314:r1332:r->d1549:r { p819:r1333:"result::ok"->d531:"std.data.result.result.ok"(p818:d1551:value) -> e3315:r1334:value->d1551:value; p821:r1335:"result::err"->d532:"std.data.result.result.err"(p820:_) -> e3316:r1336:fallback->d1550:fallback }))
    }
  }
  pub d9:"std.text" mod {
    pub d112:"std.text.bytes" mod {
      pub d655:"std.text.bytes.len": std::text::bytes::bytes -> int = e3995:builtin_op::bytes_len
      pub d656:"std.text.bytes.eq": std::text::bytes::bytes -> std::text::bytes::bytes -> bool = e3996:builtin_op::bytes_eq
      pub d657:"std.text.bytes.concat": std::text::bytes::bytes -> std::text::bytes::bytes -> std::text::bytes::bytes = e3997:builtin_op::bytes_concat
      pub d658:"std.text.bytes.index_raw": std::text::bytes::bytes -> int -> int = e3998:builtin_op::bytes_index
      pub d659:"std.text.bytes.index_range": std::text::bytes::bytes -> std::data::range::range -> std::text::bytes::bytes = e3999:builtin_op::bytes_index_range
      pub d660:"std.text.bytes.to_utf8_raw": std::text::bytes::bytes -> (std::text::str::str, int) = e4000:builtin_op::bytes_to_utf8_raw
      pub d661:"std.text.bytes.bytes" mod {
        pub d662:"std.text.bytes.bytes.len": std::text::bytes::bytes -> int = e4004:(fn p987:d1663:b -> e4003:(e4001:r1649:"std::text::bytes::len"->d655:"std.text.bytes.len" e4002:r1650:b->d1663:b))
        pub d663:"std.text.bytes.bytes.is_empty": std::text::bytes::bytes -> bool = e4008:(fn p988:d1664:b -> e4007:(e4005:r1651:"std::text::bytes::is_empty"->d667:"std.text.bytes.is_empty" e4006:r1652:b->d1664:b))
        pub d664:"std.text.bytes.bytes.concat": std::text::bytes::bytes -> std::text::bytes::bytes -> std::text::bytes::bytes = e4015:(fn p989:d1665:b -> e4014:(fn p990:d1666:other -> e4013:(e4011:(e4009:r1653:"std::text::bytes::concat"->d657:"std.text.bytes.concat" e4010:r1654:b->d1665:b) e4012:r1655:other->d1666:other)))
        pub d665:"std.text.bytes.bytes.to_utf8_raw": std::text::bytes::bytes -> (std::text::str::str, int) = e4019:(fn p991:d1667:b -> e4018:(e4016:r1656:"std::text::bytes::to_utf8_raw"->d660:"std.text.bytes.to_utf8_raw" e4017:r1657:b->d1667:b))
        pub d666:"std.text.bytes.bytes.to_utf8_lossy": std::text::bytes::bytes -> std::text::str::str = e4023:(fn p992:d1668:b -> e4022:(e4020:r1658:"std::text::bytes::to_utf8_lossy"->d668:"std.text.bytes.to_utf8_lossy" e4021:r1659:b->d1668:b))
      }
      pub d667:"std.text.bytes.is_empty": std::text::bytes::bytes -> bool = e4031:(fn p993:d1669:b -> e4030:(e4028:(e4024:r1660:"std::int::eq"->d47:"std.int.eq" e4027:(e4025:r1661:"std::text::bytes::len"->d655:"std.text.bytes.len" e4026:r1662:b->d1669:b)) e4029:0))
      pub d668:"std.text.bytes.to_utf8_lossy": std::text::bytes::bytes -> std::text::str::str = e4037:(fn p994:d1670:b -> e4036:case e4034:(e4032:r1663:"std::text::bytes::to_utf8_raw"->d660:"std.text.bytes.to_utf8_raw" e4033:r1664:b->d1670:b) { p997:(p995:d1671:text, p996:_) -> e4035:r1665:text->d1671:text })
      my d669 mod {
        d670: std::text::bytes::bytes -> int -> int = e4044:(fn p998:d1672:b -> e4043:(fn p999:d1673:i -> e4042:(e4040:(e4038:r1666:"std::text::bytes::index_raw"->d658:"std.text.bytes.index_raw" e4039:r1667:b->d1672:b) e4041:r1668:i->d1673:i)))
      }
      my d671 mod {
        d672: std::text::bytes::bytes -> std::data::range::range -> std::text::bytes::bytes = e4051:(fn p1000:d1674:b -> e4050:(fn p1001:d1675:r -> e4049:(e4047:(e4045:r1669:"std::text::bytes::index_range"->d659:"std.text.bytes.index_range" e4046:r1670:b->d1674:b) e4048:r1671:r->d1675:r)))
      }
    }
    pub d113:"std.text.char" mod {
      pub d673:"std.text.char.eq": std::text::char::char -> std::text::char::char -> bool = e4052:builtin_op::char_eq
      pub d674:"std.text.char.to_string": std::text::char::char -> std::text::str::str = e4053:builtin_op::char_to_string
      pub d675:"std.text.char.is_whitespace": std::text::char::char -> bool = e4054:builtin_op::char_is_whitespace
      pub d676:"std.text.char.is_punctuation": std::text::char::char -> bool = e4055:builtin_op::char_is_punctuation
      pub d677:"std.text.char.is_word": std::text::char::char -> bool = e4056:builtin_op::char_is_word
      pub d678:"std.text.char.char" mod {
        pub d679:"std.text.char.char.to_string": std::text::char::char -> std::text::str::str = e4060:(fn p1002:d1676:c -> e4059:(e4057:r1672:"std::text::char::to_string"->d674:"std.text.char.to_string" e4058:r1673:c->d1676:c))
        pub d680:"std.text.char.char.is_whitespace": std::text::char::char -> bool = e4064:(fn p1003:d1677:c -> e4063:(e4061:r1674:"std::text::char::is_whitespace"->d675:"std.text.char.is_whitespace" e4062:r1675:c->d1677:c))
        pub d681:"std.text.char.char.is_punctuation": std::text::char::char -> bool = e4068:(fn p1004:d1678:c -> e4067:(e4065:r1676:"std::text::char::is_punctuation"->d676:"std.text.char.is_punctuation" e4066:r1677:c->d1678:c))
        pub d682:"std.text.char.char.is_word": std::text::char::char -> bool = e4072:(fn p1005:d1679:c -> e4071:(e4069:r1678:"std::text::char::is_word"->d677:"std.text.char.is_word" e4070:r1679:c->d1679:c))
      }
    }
    pub d114:"std.text.config" mod {
      pub d683:"std.text.config.section": {name: std::text::str::str, entries: std::data::list::list (std::text::str::str, std::text::str::str)} -> std::text::config::section = <missing>
      pub d688:"std.text.config.config": {sections_: std::data::list::list std::text::config::section} -> std::text::config::config = <missing>
      pub d691:"std.text.config.config" mod {
        pub d692:"std.text.config.config.get": std::text::config::config -> std::text::str::str -> std::text::str::str -> std::data::opt::opt std::text::str::str = e4082:(fn p1006:d1680:c -> e4081:(fn p1007:d1681:section_name -> e4080:(fn p1008:d1682:key -> e4079:(e4077:(e4075:(e4073:r1680:"std::text::config::get"->d708:"std.text.config.get" e4074:r1681:c->d1680:c) e4076:r1682:section_name->d1681:section_name) e4078:r1683:key->d1682:key))))
        pub d693:"std.text.config.config.sections": std::text::config::config -> std::data::list::list std::text::config::section = e4086:(fn p1009:d1683:c -> e4085:(e4083:r1684:"std::text::config::sections"->d696:"std.text.config.sections" e4084:r1685:c->d1683:c))
      }
      my d694:"std.text.config.empty_section": std::text::str::str -> std::text::config::section = e4094:(fn p1010:d1684:name -> e4093:(e4087:r1686:section->d683:"std.text.config.section" e4092:{name: e4088:r1687:name->d1684:name, entries: e4091:(e4089:builtin_op::list_empty e4090:())}))
      my d695:"std.text.config.empty": () -> std::text::config::config = e4103:(fn p1011:() -> e4102:(e4095:r1688:config->d688:"std.text.config.config" e4101:{sections_: e4100:(e4099:builtin_op::list_singleton e4098:(e4096:r1689:empty_section->d694:"std.text.config.empty_section" e4097:""))}))
      pub d696:"std.text.config.sections": std::text::config::config -> std::data::list::list std::text::config::section = e4106:(fn p1012:d1685:c -> e4105:(e4104:r1690:c->d1685:c.s178.sections_->d689))
      my d697:"std.text.config.ensure_section_list": std::data::list::list std::text::config::section -> std::text::str::str -> std::data::list::list std::text::config::section = e4135:(fn p1013:d1686:sections -> e4134:(fn p1014:d1687:name -> e4133:case e4107:r1691:sections->d1686:sections { p1015:[] -> e4112:(e4111:builtin_op::list_singleton e4110:(e4108:r1692:empty_section->d694:"std.text.config.empty_section" e4109:r1693:name->d1687:name)); p1018:[p1016:d1688:head, ..p1017:d1689:tail] if e4120:(e4119:r1697:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4118:(e4117:(e4115:r1695:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e4114:(e4113:r1694:head->d1688:head.s179.name->d684)) e4116:r1696:name->d1687:name)) -> e4121:r1698:sections->d1686:sections; p1021:[p1019:d1690:head, ..p1020:d1691:tail] -> e4132:(e4131:(e4130:builtin_op::list_merge e4124:(e4123:builtin_op::list_singleton e4122:r1699:head->d1690:head)) e4129:(e4127:(e4125:r1700:ensure_section_list->d697:"std.text.config.ensure_section_list" e4126:r1701:tail->d1691:tail) e4128:r1702:name->d1687:name)) }))
      my d698:"std.text.config.ensure_section": std::text::config::config -> std::text::str::str -> std::text::config::config = e4146:(fn p1022:d1692:c -> e4145:(fn p1023:d1693:name -> e4144:(e4136:r1703:config->d688:"std.text.config.config" e4143:{sections_: e4142:(e4140:(e4137:r1704:ensure_section_list->d697:"std.text.config.ensure_section_list" e4139:(e4138:r1705:c->d1692:c.s180.sections_->d689)) e4141:r1706:name->d1693:name)})))
      my d699:"std.text.config.put_entry_list": std::data::list::list std::text::config::section -> std::text::str::str -> (std::text::str::str, std::text::str::str) -> std::data::list::list std::text::config::section = e4200:(fn p1024:d1694:sections -> e4199:(fn p1025:d1695:section_name -> e4198:(fn p1026:d1696:entry -> e4197:case e4147:r1707:sections->d1694:sections { p1027:[] -> e4156:(e4155:builtin_op::list_singleton e4154:(e4148:r1708:section->d683:"std.text.config.section" e4153:{name: e4149:r1709:section_name->d1695:section_name, entries: e4152:(e4151:builtin_op::list_singleton e4150:r1710:entry->d1696:entry)})); p1030:[p1028:d1697:head, ..p1029:d1698:tail] if e4164:(e4163:r1714:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4162:(e4161:(e4159:r1712:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e4158:(e4157:r1711:head->d1697:head.s181.name->d684)) e4160:r1713:section_name->d1695:section_name)) -> e4183:(e4182:(e4181:builtin_op::list_merge e4179:(e4178:builtin_op::list_singleton e4177:(e4165:r1715:section->d683:"std.text.config.section" e4176:{name: e4167:(e4166:r1716:head->d1697:head.s182.name->d684), entries: e4175:(e4174:(e4170:r1718:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4169:(e4168:r1717:head->d1697:head.s183.entries->d686)) e4173:(e4172:builtin_op::list_singleton e4171:r1719:entry->d1696:entry))}))) e4180:r1720:tail->d1698:tail); p1033:[p1031:d1699:head, ..p1032:d1700:tail] -> e4196:(e4195:(e4194:builtin_op::list_merge e4186:(e4185:builtin_op::list_singleton e4184:r1721:head->d1699:head)) e4193:(e4191:(e4189:(e4187:r1722:put_entry_list->d699:"std.text.config.put_entry_list" e4188:r1723:tail->d1700:tail) e4190:r1724:section_name->d1695:section_name) e4192:r1725:entry->d1696:entry)) })))
      my d700:"std.text.config.put_entry": std::text::config::config -> std::text::str::str -> (std::text::str::str, std::text::str::str) -> std::text::config::config = e4214:(fn p1034:d1701:c -> e4213:(fn p1035:d1702:section_name -> e4212:(fn p1036:d1703:entry -> e4211:(e4201:r1726:config->d688:"std.text.config.config" e4210:{sections_: e4209:(e4207:(e4205:(e4202:r1727:put_entry_list->d699:"std.text.config.put_entry_list" e4204:(e4203:r1728:c->d1701:c.s184.sections_->d689)) e4206:r1729:section_name->d1702:section_name) e4208:r1730:entry->d1703:entry)}))))
      my d701:"std.text.config.header_name": std::text::str::str -> std::data::opt::opt std::text::str::str = e4247:(fn p1037:d1704:clean -> e4246:case e4229:(e4228:r1734:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4227:(e4226:(e4219:r1732:"#op:infix:and"->d427:"std.core.ops.#op:infix:and" e4224:(fn p1038:() -> e4218:(e4216:(e4215:r1731:clean->d1704:clean.s185.starts_with->d822:"std.text.str.str.starts_with") e4217:"["))) e4225:(fn p1039:() -> e4223:(e4221:(e4220:r1733:clean->d1704:clean.s186.ends_with->d823:"std.text.str.str.ends_with") e4222:"]")))) { p1040:true -> e4244:(e4230:r1735:just->d506:"std.data.opt.opt.just" e4243:(e4242:(e4235:(e4233:(e4231:r1736:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e4232:r1737:clean->d1704:clean) e4234:1) e4241:(e4240:(e4238:r1739:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e4237:(e4236:r1738:clean->d1704:clean.s187.len->d840:"std.text.str.str.len")) e4239:1)).s188.trim->d828:"std.text.str.str.trim")); p1041:false -> e4245:r1740:nil->d505:"std.data.opt.opt.nil" })
      my d702:"std.text.config.trim_entry": (std::text::str::str, std::text::str::str) -> (std::text::str::str, std::text::str::str) = e4255:(fn p1042:d1705:pair -> e4254:case e4248:r1741:pair->d1705:pair { p1045:(p1043:d1706:key, p1044:d1707:value) -> e4253:(e4250:(e4249:r1742:key->d1706:key.s189.trim->d828:"std.text.str.str.trim"), e4252:(e4251:r1743:value->d1707:value.s190.trim->d828:"std.text.str.str.trim")) })
      my d703:"std.text.config.parse_line": (std::text::config::config, std::text::str::str) -> std::text::str::str -> (std::text::config::config, std::text::str::str) = e4307:(fn p1046:d1708:state -> e4306:(fn p1047:d1709:line -> e4305:case e4256:r1744:state->d1708:state { p1050:(p1048:d1710:cfg, p1049:d1711:current_section) -> e4304:block { let my p1051:d1712:clean = e4258:(e4257:r1745:line->d1709:line.s191.trim->d828:"std.text.str.str.trim"); e4303:case e4265:(e4264:r1748:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4263:(e4262:(e4260:r1747:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e4259:r1746:clean->d1712:clean) e4261:"")) { p1060:true -> e4266:r1749:state->d1708:state; p1061:false -> e4302:case e4272:(e4271:r1751:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4270:(e4268:(e4267:r1750:clean->d1712:clean.s192.starts_with->d822:"std.text.str.str.starts_with") e4269:"#")) { p1058:true -> e4273:r1752:state->d1708:state; p1059:false -> e4301:case e4276:(e4274:r1753:header_name->d701:"std.text.config.header_name" e4275:r1754:clean->d1712:clean) { p1053:r1755:just->d506:"std.data.opt.opt.just"(p1052:d1713:name) -> e4283:(e4281:(e4279:(e4277:r1756:ensure_section->d698:"std.text.config.ensure_section" e4278:r1757:cfg->d1710:cfg) e4280:r1758:name->d1713:name), e4282:r1759:name->d1713:name); p1054:r1760:nil->d505:"std.data.opt.opt.nil" -> e4300:case e4287:(e4285:(e4284:r1761:clean->d1712:clean.s193.split_once->d825:"std.text.str.str.split_once") e4286:"=") { p1056:r1762:just->d506:"std.data.opt.opt.just"(p1055:d1714:pair) -> e4298:(e4296:(e4292:(e4290:(e4288:r1763:put_entry->d700:"std.text.config.put_entry" e4289:r1764:cfg->d1710:cfg) e4291:r1765:current_section->d1711:current_section) e4295:(e4293:r1766:trim_entry->d702:"std.text.config.trim_entry" e4294:r1767:pair->d1714:pair)), e4297:r1768:current_section->d1711:current_section); p1057:r1769:nil->d505:"std.data.opt.opt.nil" -> e4299:r1770:state->d1708:state } } } } } }))
      pub d704:"std.text.config.parse": std::text::str::str -> std::text::config::config = e4323:(fn p1062:d1715:source -> e4322:block { let my p1065:(p1063:d1716:cfg, p1064:_) = e4320:(e4318:(e4312:(e4311:(e4309:(e4308:r1771:source->d1715:source.s194.split->d824:"std.text.str.str.split") e4310:"\n").s195.fold=>d451:"std.data.fold.Fold.fold") e4317:(e4315:(e4313:r1772:empty->d695:"std.text.config.empty" e4314:()), e4316:"")) e4319:r1773:parse_line->d703:"std.text.config.parse_line"); e4321:r1774:cfg->d1716:cfg })
      my d705:"std.text.config.get_entry_rev": std::data::list::list (std::text::str::str, std::text::str::str) -> std::text::str::str -> std::data::opt::opt std::text::str::str = e4343:(fn p1066:d1717:entries -> e4342:(fn p1067:d1718:key -> e4341:case e4324:r1775:entries->d1717:entries { p1068:[] -> e4325:r1776:nil->d505:"std.data.opt.opt.nil"; p1073:[p1071:(p1069:d1719:candidate, p1070:d1720:value), ..p1072:d1721:rest] if e4332:(e4331:r1780:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4330:(e4329:(e4327:r1778:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e4326:r1777:candidate->d1719:candidate) e4328:r1779:key->d1718:key)) -> e4335:(e4333:r1781:just->d506:"std.data.opt.opt.just" e4334:r1782:value->d1720:value); p1076:[p1074:_, ..p1075:d1722:rest] -> e4340:(e4338:(e4336:r1783:get_entry_rev->d705:"std.text.config.get_entry_rev" e4337:r1784:rest->d1722:rest) e4339:r1785:key->d1718:key) }))
      my d706:"std.text.config.get_entry": std::data::list::list (std::text::str::str, std::text::str::str) -> std::text::str::str -> std::data::opt::opt std::text::str::str = e4352:(fn p1077:d1723:entries -> e4351:(fn p1078:d1724:key -> e4350:(e4348:(e4344:r1786:get_entry_rev->d705:"std.text.config.get_entry_rev" e4347:(e4345:r1787:"std::data::list::rev"->d496:"std.data.list.rev" e4346:r1788:entries->d1723:entries)) e4349:r1789:key->d1724:key)))
      my d707:"std.text.config.get_section_rev": std::data::list::list std::text::config::section -> std::text::str::str -> std::text::str::str -> std::data::opt::opt std::text::str::str = e4379:(fn p1079:d1725:sections -> e4378:(fn p1080:d1726:section_name -> e4377:(fn p1081:d1727:key -> e4376:case e4353:r1790:sections->d1725:sections { p1082:[] -> e4354:r1791:nil->d505:"std.data.opt.opt.nil"; p1085:[p1083:d1728:head, ..p1084:d1729:rest] if e4362:(e4361:r1795:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4360:(e4359:(e4357:r1793:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e4356:(e4355:r1792:head->d1728:head.s196.name->d684)) e4358:r1794:section_name->d1726:section_name)) -> e4368:(e4366:(e4363:r1796:get_entry->d706:"std.text.config.get_entry" e4365:(e4364:r1797:head->d1728:head.s197.entries->d686)) e4367:r1798:key->d1727:key); p1088:[p1086:_, ..p1087:d1730:rest] -> e4375:(e4373:(e4371:(e4369:r1799:get_section_rev->d707:"std.text.config.get_section_rev" e4370:r1800:rest->d1730:rest) e4372:r1801:section_name->d1726:section_name) e4374:r1802:key->d1727:key) })))
      pub d708:"std.text.config.get": std::text::config::config -> std::text::str::str -> std::text::str::str -> std::data::opt::opt std::text::str::str = e4392:(fn p1089:d1731:c -> e4391:(fn p1090:d1732:section_name -> e4390:(fn p1091:d1733:key -> e4389:(e4387:(e4385:(e4380:r1803:get_section_rev->d707:"std.text.config.get_section_rev" e4384:(e4381:r1804:"std::data::list::rev"->d496:"std.data.list.rev" e4383:(e4382:r1805:c->d1731:c.s198.sections_->d689))) e4386:r1806:section_name->d1732:section_name) e4388:r1807:key->d1733:key))))
      pub d709:"std.text.config.load": std::text::str::str -> [std::io::file::file, std::io::file::io_err] std::text::config::config = e4402:(fn p1092:d1734:path -> e4401:(e4393:r1808:parse->d704:"std.text.config.parse" e4400:(e4394:r1809:"std::io::file::read_text"->d596:"std.io.file.read_text" e4399:(e4395:r1810:"std::text::path::of_bytes"->d783:"std.text.path.of_bytes" e4398:(e4396:r1811:"std::text::str::to_bytes"->d796:"std.text.str.to_bytes" e4397:r1812:path->d1734:path)))))
    }
    pub d115:"std.text.parse" mod {
      pub d710:"std.text.parse.parse" mod {
      }
      pub d719:"std.text.parse.ParseError" mod {
        pub d720:"std.text.parse.ParseError.merge": 'a -> 'a -> 'a where 'a: std::text::parse::ParseError(item = 'b, pos = 'c) = <missing>
        pub d721:"std.text.parse.ParseError.unexpected": std::data::opt::opt 'a -> 'b -> 'c where 'c: std::text::parse::ParseError(item = 'a, pos = 'b) = <missing>
        pub d722:"std.text.parse.ParseError.expected": std::text::str::str -> 'a -> 'b where 'b: std::text::parse::ParseError(item = 'c, pos = 'a) = <missing>
        pub d723:"std.text.parse.ParseError.label": 'a -> std::text::str::str -> 'a where 'a: std::text::parse::ParseError(item = 'b, pos = 'c) = <missing>
      }
      pub d724:"std.text.parse.str_error": {line: int, column: int, unexpected: std::data::opt::opt std::text::char::char, expected: std::data::list::list std::text::str::str, message: std::data::list::list std::text::str::str} -> std::text::parse::str_error = <missing>
      pub d735:"std.text.parse.str_error" mod {
        my d736 mod {
          d737: std::text::parse::str_error -> std::text::parse::str_error -> std::text::parse::str_error = e4471:(fn p1093:d1735:e -> e4470:(fn p1094:d1736:f -> e4469:case e4411:(e4410:r1816:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4409:(e4408:(e4405:r1814:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e4404:(e4403:r1813:e->d1735:e.s199.line->d725)) e4407:(e4406:r1815:f->d1736:f.s200.line->d725))) { p1101:true -> e4412:r1817:f->d1736:f; p1102:false -> e4468:case e4421:(e4420:r1821:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4419:(e4418:(e4415:r1819:"#op:infix:>"->d425:"std.core.ops.#op:infix:>" e4414:(e4413:r1818:e->d1735:e.s201.line->d725)) e4417:(e4416:r1820:f->d1736:f.s202.line->d725))) { p1099:true -> e4422:r1822:e->d1735:e; p1100:false -> e4467:case e4431:(e4430:r1826:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4429:(e4428:(e4425:r1824:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e4424:(e4423:r1823:e->d1735:e.s203.column->d727)) e4427:(e4426:r1825:f->d1736:f.s204.column->d727))) { p1097:true -> e4432:r1827:f->d1736:f; p1098:false -> e4466:case e4441:(e4440:r1831:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4439:(e4438:(e4435:r1829:"#op:infix:>"->d425:"std.core.ops.#op:infix:>" e4434:(e4433:r1828:e->d1735:e.s205.column->d727)) e4437:(e4436:r1830:f->d1736:f.s206.column->d727))) { p1095:true -> e4442:r1832:e->d1735:e; p1096:false -> e4465:(e4443:r1833:str_error->d724:"std.text.parse.str_error" e4464:{line: e4445:(e4444:r1834:e->d1735:e.s207.line->d725), column: e4447:(e4446:r1835:e->d1735:e.s208.column->d727), unexpected: e4449:(e4448:r1836:e->d1735:e.s209.unexpected->d729), expected: e4456:(e4455:(e4452:r1838:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4451:(e4450:r1837:e->d1735:e.s210.expected->d731)) e4454:(e4453:r1839:f->d1736:f.s211.expected->d731)), message: e4463:(e4462:(e4459:r1841:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4458:(e4457:r1840:e->d1735:e.s212.message->d733)) e4461:(e4460:r1842:f->d1736:f.s213.message->d733))}) } } } }))
          d738: std::data::opt::opt std::text::char::char -> (int, int) -> std::text::parse::str_error = e4485:(fn p1103:d1737:u -> e4484:(fn p1106:(p1104:d1738:l, p1105:d1739:c) -> e4483:(e4472:r1843:str_error->d724:"std.text.parse.str_error" e4482:{line: e4473:r1844:l->d1738:l, column: e4474:r1845:c->d1739:c, unexpected: e4475:r1846:u->d1737:u, expected: e4478:(e4476:builtin_op::list_empty e4477:()), message: e4481:(e4479:builtin_op::list_empty e4480:())})))
          d739: std::text::str::str -> (int, int) -> std::text::parse::str_error = e4499:(fn p1107:d1740:label -> e4498:(fn p1110:(p1108:d1741:l, p1109:d1742:c) -> e4497:(e4486:r1847:str_error->d724:"std.text.parse.str_error" e4496:{line: e4487:r1848:l->d1741:l, column: e4488:r1849:c->d1742:c, unexpected: e4489:r1850:nil->d505:"std.data.opt.opt.nil", expected: e4492:(e4491:builtin_op::list_singleton e4490:r1851:label->d1740:label), message: e4495:(e4493:builtin_op::list_empty e4494:())})))
          d740: std::text::parse::str_error -> std::text::str::str -> std::text::parse::str_error = e4515:(fn p1111:d1743:e -> e4514:(fn p1112:d1744:label -> e4513:(e4500:r1852:str_error->d724:"std.text.parse.str_error" e4512:{line: e4502:(e4501:r1853:e->d1743:e.s214.line->d725), column: e4504:(e4503:r1854:e->d1743:e.s215.column->d727), unexpected: e4506:(e4505:r1855:e->d1743:e.s216.unexpected->d729), expected: e4509:(e4508:builtin_op::list_singleton e4507:r1856:label->d1744:label), message: e4511:(e4510:r1857:e->d1743:e.s217.message->d733)})))
        }
      }
      pub d741:"std.text.parse.prefix_result": {value: 'a, rest: std::text::str::str} -> std::text::parse::prefix_result 'a = <missing>
      pub d746:"std.text.parse.match_result": {value: 'a, start: int, end: int, text: std::text::str::str} -> std::text::parse::match_result 'a = <missing>
      my d755:"std.text.parse.advance_position": std::text::str::str -> int -> int -> int -> (int, int) = e4556:(fn p1113:d1745:input -> e4555:(fn p1114:d1746:count -> e4554:(fn p1115:d1747:line -> e4553:(fn p1116:d1748:column -> e4552:block { let my p1117:d1749:data = e4518:(e4516:r1858:"std::text::str::to_bytes"->d796:"std.text.str.to_bytes" e4517:r1859:input->d1745:input); e4551:case e4528:(e4527:r1864:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4526:(e4525:(e4522:r1862:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e4521:(e4519:r1860:"std::text::bytes::len"->d655:"std.text.bytes.len" e4520:r1861:data->d1749:data)) e4524:(e4523:r1863:input->d1745:input.s218.len->d840:"std.text.str.str.len"))) { p1118:true -> e4539:(e4537:(e4535:(e4533:(e4531:(e4529:r1865:advance_position_ascii_chunks->d756:"std.text.parse.advance_position_ascii_chunks" e4530:r1866:data->d1749:data) e4532:r1867:count->d1746:count) e4534:0) e4536:r1868:line->d1747:line) e4538:r1869:column->d1748:column); p1119:false -> e4550:(e4548:(e4546:(e4544:(e4542:(e4540:r1870:advance_position_slow_chunks->d758:"std.text.parse.advance_position_slow_chunks" e4541:r1871:input->d1745:input) e4543:r1872:count->d1746:count) e4545:0) e4547:r1873:line->d1747:line) e4549:r1874:column->d1748:column) } }))))
      my d756:"std.text.parse.advance_position_ascii_chunks": std::text::bytes::bytes -> int -> int -> int -> int -> (int, int) = e4614:(fn p1120:d1750:data -> e4613:(fn p1121:d1751:count -> e4612:(fn p1122:d1752:i -> e4611:(fn p1123:d1753:line -> e4610:(fn p1124:d1754:column -> e4609:case e4563:(e4562:r1878:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4561:(e4560:(e4558:r1876:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e4557:r1875:i->d1752:i) e4559:r1877:count->d1751:count)) { p1131:true -> e4605:block { let my p1125:d1755:chunk_end = e4581:case e4574:(e4573:r1883:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4572:(e4571:(e4569:r1881:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e4568:(e4567:(e4565:r1880:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4564:r1879:i->d1752:i) e4566:1024)) e4570:r1882:count->d1751:count)) { p1126:true -> e4579:(e4578:(e4576:r1885:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4575:r1884:i->d1752:i) e4577:1024); p1127:false -> e4580:r1886:count->d1751:count }; e4604:case e4592:(e4590:(e4588:(e4586:(e4584:(e4582:r1887:advance_position_ascii_loop->d757:"std.text.parse.advance_position_ascii_loop" e4583:r1888:data->d1750:data) e4585:r1889:chunk_end->d1755:chunk_end) e4587:r1890:i->d1752:i) e4589:r1891:line->d1753:line) e4591:r1892:column->d1754:column) { p1130:(p1128:d1756:line, p1129:d1757:column) -> e4603:(e4601:(e4599:(e4597:(e4595:(e4593:r1893:advance_position_ascii_chunks->d756:"std.text.parse.advance_position_ascii_chunks" e4594:r1894:data->d1750:data) e4596:r1895:count->d1751:count) e4598:r1896:chunk_end->d1755:chunk_end) e4600:r1897:line->d1756:line) e4602:r1898:column->d1757:column) } }; p1132:false -> e4608:(e4606:r1899:line->d1753:line, e4607:r1900:column->d1754:column) })))))
      my d757:"std.text.parse.advance_position_ascii_loop": std::text::bytes::bytes -> int -> int -> int -> int -> (int, int) = e4674:(fn p1133:d1758:data -> e4673:(fn p1134:d1759:count -> e4672:(fn p1135:d1760:i -> e4671:(fn p1136:d1761:line -> e4670:(fn p1137:d1762:column -> e4669:case e4621:(e4620:r1904:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4619:(e4618:(e4616:r1902:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e4615:r1901:i->d1760:i) e4617:r1903:count->d1759:count)) { p1142:true -> e4665:case e4626:(e4624:(e4622:r1905:"std::text::bytes::index_raw"->d658:"std.text.bytes.index_raw" e4623:r1906:data->d1758:data) e4625:r1907:i->d1760:i) { p1140:(p1138:10 | p1139:13) -> e4645:(e4643:(e4637:(e4631:(e4629:(e4627:r1908:advance_position_ascii_loop->d757:"std.text.parse.advance_position_ascii_loop" e4628:r1909:data->d1758:data) e4630:r1910:count->d1759:count) e4636:(e4635:(e4633:r1912:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4632:r1911:i->d1760:i) e4634:1)) e4642:(e4641:(e4639:r1914:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4638:r1913:line->d1761:line) e4640:1)) e4644:1); p1141:_ -> e4664:(e4658:(e4656:(e4650:(e4648:(e4646:r1915:advance_position_ascii_loop->d757:"std.text.parse.advance_position_ascii_loop" e4647:r1916:data->d1758:data) e4649:r1917:count->d1759:count) e4655:(e4654:(e4652:r1919:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4651:r1918:i->d1760:i) e4653:1)) e4657:r1920:line->d1761:line) e4663:(e4662:(e4660:r1922:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4659:r1921:column->d1762:column) e4661:1)) }; p1143:false -> e4668:(e4666:r1923:line->d1761:line, e4667:r1924:column->d1762:column) })))))
      my d758:"std.text.parse.advance_position_slow_chunks": std::text::str::str -> int -> int -> int -> int -> (int, int) = e4732:(fn p1144:d1763:input -> e4731:(fn p1145:d1764:count -> e4730:(fn p1146:d1765:i -> e4729:(fn p1147:d1766:line -> e4728:(fn p1148:d1767:column -> e4727:case e4681:(e4680:r1928:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4679:(e4678:(e4676:r1926:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e4675:r1925:i->d1765:i) e4677:r1927:count->d1764:count)) { p1155:true -> e4723:block { let my p1149:d1768:chunk_end = e4699:case e4692:(e4691:r1933:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4690:(e4689:(e4687:r1931:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e4686:(e4685:(e4683:r1930:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4682:r1929:i->d1765:i) e4684:1024)) e4688:r1932:count->d1764:count)) { p1150:true -> e4697:(e4696:(e4694:r1935:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4693:r1934:i->d1765:i) e4695:1024); p1151:false -> e4698:r1936:count->d1764:count }; e4722:case e4710:(e4708:(e4706:(e4704:(e4702:(e4700:r1937:advance_position_slow_loop->d759:"std.text.parse.advance_position_slow_loop" e4701:r1938:input->d1763:input) e4703:r1939:chunk_end->d1768:chunk_end) e4705:r1940:i->d1765:i) e4707:r1941:line->d1766:line) e4709:r1942:column->d1767:column) { p1154:(p1152:d1769:line, p1153:d1770:column) -> e4721:(e4719:(e4717:(e4715:(e4713:(e4711:r1943:advance_position_slow_chunks->d758:"std.text.parse.advance_position_slow_chunks" e4712:r1944:input->d1763:input) e4714:r1945:count->d1764:count) e4716:r1946:chunk_end->d1768:chunk_end) e4718:r1947:line->d1769:line) e4720:r1948:column->d1770:column) } }; p1156:false -> e4726:(e4724:r1949:line->d1766:line, e4725:r1950:column->d1767:column) })))))
      my d759:"std.text.parse.advance_position_slow_loop": std::text::str::str -> int -> int -> int -> int -> (int, int) = e4795:(fn p1157:d1771:input -> e4794:(fn p1158:d1772:count -> e4793:(fn p1159:d1773:i -> e4792:(fn p1160:d1774:line -> e4791:(fn p1161:d1775:column -> e4790:case e4739:(e4738:r1954:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4737:(e4736:(e4734:r1952:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e4733:r1951:i->d1773:i) e4735:r1953:count->d1772:count)) { p1169:true -> e4786:block { let my p1162:d1776:item = e4744:(e4742:(e4740:r1955:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e4741:r1956:input->d1771:input) e4743:r1957:i->d1773:i); e4785:case e4746:(e4745:r1958:item->d1776:item.s219.to_string->d679:"std.text.char.char.to_string") { p1167:(p1163:"\\r" | p1166:(p1164:"\\r\\n" | p1165:"\\n")) -> e4765:(e4763:(e4757:(e4751:(e4749:(e4747:r1959:advance_position_slow_loop->d759:"std.text.parse.advance_position_slow_loop" e4748:r1960:input->d1771:input) e4750:r1961:count->d1772:count) e4756:(e4755:(e4753:r1963:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4752:r1962:i->d1773:i) e4754:1)) e4762:(e4761:(e4759:r1965:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4758:r1964:line->d1774:line) e4760:1)) e4764:1); p1168:_ -> e4784:(e4778:(e4776:(e4770:(e4768:(e4766:r1966:advance_position_slow_loop->d759:"std.text.parse.advance_position_slow_loop" e4767:r1967:input->d1771:input) e4769:r1968:count->d1772:count) e4775:(e4774:(e4772:r1970:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4771:r1969:i->d1773:i) e4773:1)) e4777:r1971:line->d1774:line) e4783:(e4782:(e4780:r1973:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4779:r1972:column->d1775:column) e4781:1)) } }; p1170:false -> e4789:(e4787:r1974:line->d1774:line, e4788:r1975:column->d1775:column) })))))
      pub d760:"std.text.parse.run_str": std::text::str::str -> int -> int -> 'a [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int); 'b] -> ['b] std::data::result::result 'a std::text::parse::str_error = e4984:(fn p1171:d1777:input -> e4983:(fn p1172:d1778:line -> e4982:(fn p1173:d1779:column -> e4981:(fn p1174:d1780:parser -> e4980:catch e4796:r1976:parser->d1780:parser { std::text::parse::parse::item p1175:_, p1176:d1781:k if e4804:(e4803:r1979:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4802:(e4801:(e4799:r1978:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e4798:(e4797:r1977:input->d1777:input.s220.len->d840:"std.text.str.str.len")) e4800:0)) -> e4818:(e4805:r1980:"result::err"->d532:"std.data.result.result.err" e4817:(e4806:r1981:str_error->d724:"std.text.parse.str_error" e4816:{line: e4807:r1982:line->d1778:line, column: e4808:r1983:column->d1779:column, unexpected: e4809:r1984:nil->d505:"std.data.opt.opt.nil", expected: e4812:(e4810:builtin_op::list_empty e4811:()), message: e4815:(e4813:builtin_op::list_empty e4814:())})); std::text::parse::parse::item p1177:_, p1178:d1782:k -> e4865:block { let my p1179:d1783:item = e4823:(e4821:(e4819:r1985:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e4820:r1986:input->d1777:input) e4822:0); e4864:block { let my p1180:d1784:rest = e4830:(e4826:(e4824:r1987:"std::text::str::index_range"->d792:"std.text.str.index_range" e4825:r1988:input->d1777:input) e4829:(e4827:r1989:"std::data::range::from_excluded"->d518:"std.data.range.from_excluded" e4828:0)); e4863:case e4832:(e4831:r1990:item->d1783:item.s221.to_string->d679:"std.text.char.char.to_string") { p1185:(p1181:"\\r" | p1184:(p1182:"\\r\\n" | p1183:"\\n")) -> e4847:(e4843:(e4841:(e4835:(e4833:r1991:run_str->d760:"std.text.parse.run_str" e4834:r1992:rest->d1784:rest) e4840:(e4839:(e4837:r1994:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4836:r1993:line->d1778:line) e4838:1)) e4842:1) e4846:(e4844:r1995:k->d1782:k e4845:r1996:item->d1783:item)); p1186:_ -> e4862:(e4858:(e4852:(e4850:(e4848:r1997:run_str->d760:"std.text.parse.run_str" e4849:r1998:rest->d1784:rest) e4851:r1999:line->d1778:line) e4857:(e4856:(e4854:r2001:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4853:r2000:column->d1779:column) e4855:1)) e4861:(e4859:r2002:k->d1782:k e4860:r2003:item->d1783:item)) } } }; std::text::parse::parse::fail p1187:d1785:e, p1188:_ -> e4868:(e4866:r2004:"result::err"->d532:"std.data.result.result.err" e4867:r2005:e->d1785:e); std::text::parse::parse::eof p1189:_, p1190:d1786:k -> e4884:(e4875:(e4873:(e4871:(e4869:r2006:run_str->d760:"std.text.parse.run_str" e4870:r2007:input->d1777:input) e4872:r2008:line->d1778:line) e4874:r2009:column->d1779:column) e4883:(e4876:r2010:k->d1786:k e4882:(e4881:(e4879:r2012:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e4878:(e4877:r2011:input->d1777:input.s222.len->d840:"std.text.str.str.len")) e4880:0))); std::text::parse::parse::pos p1191:_, p1192:d1787:k -> e4897:(e4891:(e4889:(e4887:(e4885:r2013:run_str->d760:"std.text.parse.run_str" e4886:r2014:input->d1777:input) e4888:r2015:line->d1778:line) e4890:r2016:column->d1779:column) e4896:(e4892:r2017:k->d1787:k e4895:(e4893:r2018:line->d1778:line, e4894:r2019:column->d1779:column))); std::text::parse::parse::cut p1193:_, p1194:d1788:k -> e4908:(e4904:(e4902:(e4900:(e4898:r2020:run_str->d760:"std.text.parse.run_str" e4899:r2021:input->d1777:input) e4901:r2022:line->d1778:line) e4903:r2023:column->d1779:column) e4907:(e4905:r2024:k->d1788:k e4906:())); std::text::parse::parse::snapshot p1195:_, p1196:d1789:k -> e4922:(e4915:(e4913:(e4911:(e4909:r2025:run_str->d760:"std.text.parse.run_str" e4910:r2026:input->d1777:input) e4912:r2027:line->d1778:line) e4914:r2028:column->d1779:column) e4921:(e4916:r2029:k->d1789:k e4920:(e4917:r2030:input->d1777:input, e4918:r2031:line->d1778:line, e4919:r2032:column->d1779:column))); std::text::parse::parse::restore p1200:(p1197:d1790:input, p1198:d1791:line, p1199:d1792:column), p1201:d1793:k -> e4933:(e4929:(e4927:(e4925:(e4923:r2033:run_str->d760:"std.text.parse.run_str" e4924:r2034:input->d1790:input) e4926:r2035:line->d1791:line) e4928:r2036:column->d1792:column) e4932:(e4930:r2037:k->d1793:k e4931:())); std::text::parse::parse::advance p1202:d1794:count, p1203:d1795:k -> e4976:block { let my p1204:d1796:input_len = e4935:(e4934:r2038:input->d1777:input.s223.len->d840:"std.text.str.str.len"); e4975:block { let my p1205:d1797:end = e4945:case e4942:(e4941:r2042:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4940:(e4939:(e4937:r2040:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e4936:r2039:count->d1794:count) e4938:r2041:input_len->d1796:input_len)) { p1206:true -> e4943:r2043:count->d1794:count; p1207:false -> e4944:r2044:input_len->d1796:input_len }; e4974:block { let my p1208:d1798:rest = e4952:(e4950:(e4948:(e4946:r2045:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e4947:r2046:input->d1777:input) e4949:r2047:end->d1797:end) e4951:r2048:input_len->d1796:input_len); e4973:block { let my p1211:(p1209:d1799:line, p1210:d1800:column) = e4961:(e4959:(e4957:(e4955:(e4953:r2049:advance_position->d755:"std.text.parse.advance_position" e4954:r2050:input->d1777:input) e4956:r2051:end->d1797:end) e4958:r2052:line->d1778:line) e4960:r2053:column->d1779:column); e4972:(e4968:(e4966:(e4964:(e4962:r2054:run_str->d760:"std.text.parse.run_str" e4963:r2055:rest->d1798:rest) e4965:r2056:line->d1799:line) e4967:r2057:column->d1800:column) e4971:(e4969:r2058:k->d1795:k e4970:())) } } } }; p1212:d1801:v -> e4979:(e4977:r2059:"result::ok"->d531:"std.data.result.result.ok" e4978:r2060:v->d1801:v) }))))
      pub d761:"std.text.parse.run_prefix_str": std::text::str::str -> int -> int -> 'a [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int); 'b] -> ['b] std::data::result::result(std::text::parse::prefix_result 'a, std::text::parse::str_error) = e5177:(fn p1213:d1802:input -> e5176:(fn p1214:d1803:line -> e5175:(fn p1215:d1804:column -> e5174:(fn p1216:d1805:parser -> e5173:catch e4985:r2061:parser->d1805:parser { std::text::parse::parse::item p1217:_, p1218:d1806:k if e4993:(e4992:r2064:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4991:(e4990:(e4988:r2063:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e4987:(e4986:r2062:input->d1802:input.s224.len->d840:"std.text.str.str.len")) e4989:0)) -> e5007:(e4994:r2065:"result::err"->d532:"std.data.result.result.err" e5006:(e4995:r2066:str_error->d724:"std.text.parse.str_error" e5005:{line: e4996:r2067:line->d1803:line, column: e4997:r2068:column->d1804:column, unexpected: e4998:r2069:nil->d505:"std.data.opt.opt.nil", expected: e5001:(e4999:builtin_op::list_empty e5000:()), message: e5004:(e5002:builtin_op::list_empty e5003:())})); std::text::parse::parse::item p1219:_, p1220:d1807:k -> e5054:block { let my p1221:d1808:item = e5012:(e5010:(e5008:r2070:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e5009:r2071:input->d1802:input) e5011:0); e5053:block { let my p1222:d1809:rest = e5019:(e5015:(e5013:r2072:"std::text::str::index_range"->d792:"std.text.str.index_range" e5014:r2073:input->d1802:input) e5018:(e5016:r2074:"std::data::range::from_excluded"->d518:"std.data.range.from_excluded" e5017:0)); e5052:case e5021:(e5020:r2075:item->d1808:item.s225.to_string->d679:"std.text.char.char.to_string") { p1227:(p1223:"\\r" | p1226:(p1224:"\\r\\n" | p1225:"\\n")) -> e5036:(e5032:(e5030:(e5024:(e5022:r2076:run_prefix_str->d761:"std.text.parse.run_prefix_str" e5023:r2077:rest->d1809:rest) e5029:(e5028:(e5026:r2079:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e5025:r2078:line->d1803:line) e5027:1)) e5031:1) e5035:(e5033:r2080:k->d1807:k e5034:r2081:item->d1808:item)); p1228:_ -> e5051:(e5047:(e5041:(e5039:(e5037:r2082:run_prefix_str->d761:"std.text.parse.run_prefix_str" e5038:r2083:rest->d1809:rest) e5040:r2084:line->d1803:line) e5046:(e5045:(e5043:r2086:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e5042:r2085:column->d1804:column) e5044:1)) e5050:(e5048:r2087:k->d1807:k e5049:r2088:item->d1808:item)) } } }; std::text::parse::parse::fail p1229:d1810:e, p1230:_ -> e5057:(e5055:r2089:"result::err"->d532:"std.data.result.result.err" e5056:r2090:e->d1810:e); std::text::parse::parse::eof p1231:_, p1232:d1811:k -> e5073:(e5064:(e5062:(e5060:(e5058:r2091:run_prefix_str->d761:"std.text.parse.run_prefix_str" e5059:r2092:input->d1802:input) e5061:r2093:line->d1803:line) e5063:r2094:column->d1804:column) e5072:(e5065:r2095:k->d1811:k e5071:(e5070:(e5068:r2097:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e5067:(e5066:r2096:input->d1802:input.s226.len->d840:"std.text.str.str.len")) e5069:0))); std::text::parse::parse::pos p1233:_, p1234:d1812:k -> e5086:(e5080:(e5078:(e5076:(e5074:r2098:run_prefix_str->d761:"std.text.parse.run_prefix_str" e5075:r2099:input->d1802:input) e5077:r2100:line->d1803:line) e5079:r2101:column->d1804:column) e5085:(e5081:r2102:k->d1812:k e5084:(e5082:r2103:line->d1803:line, e5083:r2104:column->d1804:column))); std::text::parse::parse::cut p1235:_, p1236:d1813:k -> e5097:(e5093:(e5091:(e5089:(e5087:r2105:run_prefix_str->d761:"std.text.parse.run_prefix_str" e5088:r2106:input->d1802:input) e5090:r2107:line->d1803:line) e5092:r2108:column->d1804:column) e5096:(e5094:r2109:k->d1813:k e5095:())); std::text::parse::parse::snapshot p1237:_, p1238:d1814:k -> e5111:(e5104:(e5102:(e5100:(e5098:r2110:run_prefix_str->d761:"std.text.parse.run_prefix_str" e5099:r2111:input->d1802:input) e5101:r2112:line->d1803:line) e5103:r2113:column->d1804:column) e5110:(e5105:r2114:k->d1814:k e5109:(e5106:r2115:input->d1802:input, e5107:r2116:line->d1803:line, e5108:r2117:column->d1804:column))); std::text::parse::parse::restore p1242:(p1239:d1815:input, p1240:d1816:line, p1241:d1817:column), p1243:d1818:k -> e5122:(e5118:(e5116:(e5114:(e5112:r2118:run_prefix_str->d761:"std.text.parse.run_prefix_str" e5113:r2119:input->d1815:input) e5115:r2120:line->d1816:line) e5117:r2121:column->d1817:column) e5121:(e5119:r2122:k->d1818:k e5120:())); std::text::parse::parse::advance p1244:d1819:count, p1245:d1820:k -> e5165:block { let my p1246:d1821:input_len = e5124:(e5123:r2123:input->d1802:input.s227.len->d840:"std.text.str.str.len"); e5164:block { let my p1247:d1822:end = e5134:case e5131:(e5130:r2127:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e5129:(e5128:(e5126:r2125:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e5125:r2124:count->d1819:count) e5127:r2126:input_len->d1821:input_len)) { p1248:true -> e5132:r2128:count->d1819:count; p1249:false -> e5133:r2129:input_len->d1821:input_len }; e5163:block { let my p1250:d1823:rest = e5141:(e5139:(e5137:(e5135:r2130:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5136:r2131:input->d1802:input) e5138:r2132:end->d1822:end) e5140:r2133:input_len->d1821:input_len); e5162:block { let my p1253:(p1251:d1824:line, p1252:d1825:column) = e5150:(e5148:(e5146:(e5144:(e5142:r2134:advance_position->d755:"std.text.parse.advance_position" e5143:r2135:input->d1802:input) e5145:r2136:end->d1822:end) e5147:r2137:line->d1803:line) e5149:r2138:column->d1804:column); e5161:(e5157:(e5155:(e5153:(e5151:r2139:run_prefix_str->d761:"std.text.parse.run_prefix_str" e5152:r2140:rest->d1823:rest) e5154:r2141:line->d1824:line) e5156:r2142:column->d1825:column) e5160:(e5158:r2143:k->d1820:k e5159:())) } } } }; p1254:d1826:v -> e5172:(e5166:r2144:"result::ok"->d531:"std.data.result.result.ok" e5171:(e5167:r2145:prefix_result->d741:"std.text.parse.prefix_result" e5170:{value: e5168:r2146:v->d1826:v, rest: e5169:r2147:input->d1802:input})) }))))
      pub d762:"std.text.parse.read_prefix": std::text::str::str -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] 'a) -> std::data::result::result(std::text::parse::prefix_result 'a, std::text::parse::str_error) = e5190:(fn p1255:d1827:source -> e5189:(fn p1256:d1828:parser -> e5188:(e5184:(e5182:(e5180:(e5178:r2148:run_prefix_str->d761:"std.text.parse.run_prefix_str" e5179:r2149:source->d1827:source) e5181:1) e5183:1) e5187:(e5185:r2150:parser->d1828:parser e5186:()))))
      my d763:"std.text.parse.find_from": std::text::str::str -> int -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] 'a) -> std::data::opt::opt(std::text::parse::match_result 'a) = e5291:(fn p1257:d1829:source -> e5290:(fn p1258:d1830:start -> e5289:(fn p1259:d1831:parser -> e5288:case e5198:(e5197:r2154:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e5196:(e5195:(e5192:r2152:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e5191:r2151:start->d1830:start) e5194:(e5193:r2153:source->d1829:source.s228.len->d840:"std.text.str.str.len"))) { p1268:true -> e5286:block { let my p1260:d1832:rest = e5206:(e5203:(e5201:(e5199:r2155:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5200:r2156:source->d1829:source) e5202:r2157:start->d1830:start) e5205:(e5204:r2158:source->d1829:source.s229.len->d840:"std.text.str.str.len")); e5285:case e5221:(e5217:(e5211:(e5209:(e5207:r2159:run_prefix_str->d761:"std.text.parse.run_prefix_str" e5208:r2160:rest->d1832:rest) e5210:1) e5216:(e5215:(e5213:r2162:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e5212:r2161:start->d1830:start) e5214:1)) e5220:(e5218:r2163:parser->d1831:parser e5219:())) { p1262:r2164:"result::ok"->d531:"std.data.result.result.ok"(p1261:d1833:found) -> e5273:block { let my p1263:d1834:consumed = e5229:(e5228:(e5224:r2166:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e5223:(e5222:r2165:rest->d1832:rest.s230.len->d840:"std.text.str.str.len")) e5227:(e5226:(e5225:r2167:found->d1833:found.s231.rest->d744).s232.len->d840:"std.text.str.str.len")); e5272:case e5236:(e5235:r2170:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e5234:(e5233:(e5231:r2169:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e5230:r2168:consumed->d1834:consumed) e5232:0)) { p1264:true -> e5247:(e5245:(e5239:(e5237:r2171:find_from->d763:"std.text.parse.find_from" e5238:r2172:source->d1829:source) e5244:(e5243:(e5241:r2174:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e5240:r2173:start->d1830:start) e5242:1)) e5246:r2175:parser->d1831:parser); p1265:false -> e5271:(e5248:r2176:just->d506:"std.data.opt.opt.just" e5270:(e5249:r2177:match_result->d746:"std.text.parse.match_result" e5269:{value: e5251:(e5250:r2178:found->d1833:found.s233.value->d742), start: e5252:r2179:start->d1830:start, end: e5257:(e5256:(e5254:r2181:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e5253:r2180:start->d1830:start) e5255:r2182:consumed->d1834:consumed), text: e5268:(e5262:(e5260:(e5258:r2183:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5259:r2184:source->d1829:source) e5261:r2185:start->d1830:start) e5267:(e5266:(e5264:r2187:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e5263:r2186:start->d1830:start) e5265:r2188:consumed->d1834:consumed))})) } }; p1267:r2189:"result::err"->d532:"std.data.result.result.err"(p1266:_) -> e5284:(e5282:(e5276:(e5274:r2190:find_from->d763:"std.text.parse.find_from" e5275:r2191:source->d1829:source) e5281:(e5280:(e5278:r2193:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e5277:r2192:start->d1830:start) e5279:1)) e5283:r2194:parser->d1831:parser) } }; p1269:false -> e5287:r2195:nil->d505:"std.data.opt.opt.nil" })))
      pub d764:"std.text.parse.find": std::text::str::str -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] 'a) -> std::data::opt::opt(std::text::parse::match_result 'a) = e5300:(fn p1270:d1835:source -> e5299:(fn p1271:d1836:parser -> e5298:(e5296:(e5294:(e5292:r2196:find_from->d763:"std.text.parse.find_from" e5293:r2197:source->d1835:source) e5295:0) e5297:r2198:parser->d1836:parser)))
      pub d765:"std.text.parse.edit_once": std::text::str::str -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] 'a) -> ('a -> ['b] std::text::str::str) -> ['b] std::text::str::str = e5339:(fn p1272:d1837:source -> e5338:(fn p1273:d1838:parser -> e5337:(fn p1274:d1839:replacement -> e5336:case e5307:(e5305:(e5303:(e5301:r2199:find_from->d763:"std.text.parse.find_from" e5302:r2200:source->d1837:source) e5304:0) e5306:r2201:parser->d1838:parser) { p1276:r2202:just->d506:"std.data.opt.opt.just"(p1275:d1840:found) -> e5334:(e5324:(e5308:r2203:"std::text::str::concat"->d786:"std.text.str.concat" e5323:(e5318:(e5309:r2204:"std::text::str::concat"->d786:"std.text.str.concat" e5317:(e5314:(e5312:(e5310:r2205:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5311:r2206:source->d1837:source) e5313:0) e5316:(e5315:r2207:found->d1840:found.s234.start->d749))) e5322:(e5319:r2208:replacement->d1839:replacement e5321:(e5320:r2209:found->d1840:found.s235.value->d747)))) e5333:(e5330:(e5327:(e5325:r2210:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5326:r2211:source->d1837:source) e5329:(e5328:r2212:found->d1840:found.s236.end->d751)) e5332:(e5331:r2213:source->d1837:source.s237.len->d840:"std.text.str.str.len"))); p1277:r2214:nil->d505:"std.data.opt.opt.nil" -> e5335:r2215:source->d1837:source })))
      pub d766:"std.text.parse.edit": std::text::str::str -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] 'a) -> ('a -> ['b] std::text::str::str) -> ['b] std::text::str::str = e5394:(fn p1278:d1841:source -> e5393:(fn p1279:d1842:parser -> e5392:(fn p1280:d1843:replacement -> e5391:block { let my p1281:d1844:loop = e5385:(fn p1282:d1845:start -> e5384:(fn p1283:d1846:out -> e5383:case e5346:(e5344:(e5342:(e5340:r2216:find_from->d763:"std.text.parse.find_from" e5341:r2217:source->d1841:source) e5343:r2218:start->d1845:start) e5345:r2219:parser->d1842:parser) { p1285:r2220:just->d506:"std.data.opt.opt.just"(p1284:d1847:found) -> e5370:(e5350:(e5347:r2221:loop->d1844:loop e5349:(e5348:r2222:found->d1847:found.s238.end->d751)) e5369:(e5364:(e5351:r2223:"std::text::str::concat"->d786:"std.text.str.concat" e5363:(e5354:(e5352:r2224:"std::text::str::concat"->d786:"std.text.str.concat" e5353:r2225:out->d1846:out) e5362:(e5359:(e5357:(e5355:r2226:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5356:r2227:source->d1841:source) e5358:r2228:start->d1845:start) e5361:(e5360:r2229:found->d1847:found.s239.start->d749)))) e5368:(e5365:r2230:replacement->d1843:replacement e5367:(e5366:r2231:found->d1847:found.s240.value->d747)))); p1286:r2232:nil->d505:"std.data.opt.opt.nil" -> e5382:(e5373:(e5371:r2233:"std::text::str::concat"->d786:"std.text.str.concat" e5372:r2234:out->d1846:out) e5381:(e5378:(e5376:(e5374:r2235:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5375:r2236:source->d1841:source) e5377:r2237:start->d1845:start) e5380:(e5379:r2238:source->d1841:source.s241.len->d840:"std.text.str.str.len"))) })); e5390:(e5388:(e5386:r2239:loop->d1844:loop e5387:0) e5389:"") })))
      pub d767:"std.text.parse.replace_once": std::text::str::str -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] any) -> std::text::str::str -> std::text::str::str = e5430:(fn p1287:d1848:source -> e5429:(fn p1288:d1849:parser -> e5428:(fn p1289:d1850:replacement -> e5427:case e5401:(e5399:(e5397:(e5395:r2240:find_from->d763:"std.text.parse.find_from" e5396:r2241:source->d1848:source) e5398:0) e5400:r2242:parser->d1849:parser) { p1291:r2243:just->d506:"std.data.opt.opt.just"(p1290:d1851:found) -> e5425:(e5415:(e5402:r2244:"std::text::str::concat"->d786:"std.text.str.concat" e5414:(e5412:(e5403:r2245:"std::text::str::concat"->d786:"std.text.str.concat" e5411:(e5408:(e5406:(e5404:r2246:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5405:r2247:source->d1848:source) e5407:0) e5410:(e5409:r2248:found->d1851:found.s242.start->d749))) e5413:r2249:replacement->d1850:replacement)) e5424:(e5421:(e5418:(e5416:r2250:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5417:r2251:source->d1848:source) e5420:(e5419:r2252:found->d1851:found.s243.end->d751)) e5423:(e5422:r2253:source->d1848:source.s244.len->d840:"std.text.str.str.len"))); p1292:r2254:nil->d505:"std.data.opt.opt.nil" -> e5426:r2255:source->d1848:source })))
      pub d768:"std.text.parse.replace": std::text::str::str -> (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] any) -> std::text::str::str -> std::text::str::str = e5482:(fn p1293:d1852:source -> e5481:(fn p1294:d1853:parser -> e5480:(fn p1295:d1854:replacement -> e5479:block { let my p1296:d1855:loop = e5473:(fn p1297:d1856:start -> e5472:(fn p1298:d1857:out -> e5471:case e5437:(e5435:(e5433:(e5431:r2256:find_from->d763:"std.text.parse.find_from" e5432:r2257:source->d1852:source) e5434:r2258:start->d1856:start) e5436:r2259:parser->d1853:parser) { p1300:r2260:just->d506:"std.data.opt.opt.just"(p1299:d1858:found) -> e5458:(e5441:(e5438:r2261:loop->d1855:loop e5440:(e5439:r2262:found->d1858:found.s245.end->d751)) e5457:(e5455:(e5442:r2263:"std::text::str::concat"->d786:"std.text.str.concat" e5454:(e5445:(e5443:r2264:"std::text::str::concat"->d786:"std.text.str.concat" e5444:r2265:out->d1857:out) e5453:(e5450:(e5448:(e5446:r2266:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5447:r2267:source->d1852:source) e5449:r2268:start->d1856:start) e5452:(e5451:r2269:found->d1858:found.s246.start->d749)))) e5456:r2270:replacement->d1854:replacement)); p1301:r2271:nil->d505:"std.data.opt.opt.nil" -> e5470:(e5461:(e5459:r2272:"std::text::str::concat"->d786:"std.text.str.concat" e5460:r2273:out->d1857:out) e5469:(e5466:(e5464:(e5462:r2274:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5463:r2275:source->d1852:source) e5465:r2276:start->d1856:start) e5468:(e5467:r2277:source->d1852:source.s247.len->d840:"std.text.str.str.len"))) })); e5478:(e5476:(e5474:r2278:loop->d1855:loop e5475:0) e5477:"") })))
      pub d769:"std.text.parse.translate": (() -> [std::text::parse::parse std::text::char::char std::text::parse::str_error (int, int) (std::text::str::str, int, int)] 'a) -> ('a -> ['b] std::text::str::str) -> std::text::str::str -> ['b] std::text::str::str = e5492:(fn p1302:d1859:parser -> e5491:(fn p1303:d1860:replacement -> e5490:(fn p1304:d1861:source -> e5489:(e5487:(e5485:(e5483:r2279:edit->d766:"std.text.parse.edit" e5484:r2280:source->d1861:source) e5486:r2281:parser->d1859:parser) e5488:r2282:replacement->d1860:replacement))))
      pub d770:"std.text.parse.choice": (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> () -> [std::text::parse::parse 'a 'b 'c 'd] 'e where 'b: std::text::parse::ParseError(item = 'f, pos = 'g) = e5528:(fn p1305:d1862:p -> e5527:(fn p1306:d1863:q -> e5526:(fn p1307:() -> e5525:block { let my p1308:d1864:snap = e5495:(e5493:r2283:"parse::snapshot"->d716:"std.text.parse.parse.snapshot" e5494:()); e5524:catch e5498:(e5496:r2284:p->d1862:p e5497:()) { std::text::parse::parse::cut p1309:_, p1310:d1865:k -> e5509:block { e5501:(e5499:r2285:"parse::cut"->d715:"std.text.parse.parse.cut" e5500:()); e5508:catch e5504:(e5502:r2286:k->d1865:k e5503:()) { std::text::parse::parse::fail p1311:d1866:e, p1312:_ -> e5507:(e5505:r2287:"parse::fail"->d712:"std.text.parse.parse.fail" e5506:r2288:e->d1866:e) } }; std::text::parse::parse::fail p1313:d1867:e1, p1314:_ -> e5523:block { e5512:(e5510:r2289:"parse::restore"->d717:"std.text.parse.parse.restore" e5511:r2290:snap->d1864:snap); e5522:catch e5515:(e5513:r2291:q->d1863:q e5514:()) { std::text::parse::parse::fail p1315:d1868:e2, p1316:_ -> e5521:(e5516:r2292:"parse::fail"->d712:"std.text.parse.parse.fail" e5520:(e5518:(e5517:r2293:e1->d1867:e1.s248.merge=>d720:"std.text.parse.ParseError.merge") e5519:r2294:e2->d1868:e2)) } } } })))
      pub d771:"std.text.parse.satisfy": ('a -> ['b & 'b] bool) -> () -> [std::text::parse::parse('a & 'c, 'd | 'e, 'g & 'f, 'h), 'b] 'a where std::text::parse::ParseError('e & 'd, item = 'a | 'c, pos = 'g | 'f) = e5567:(fn p1317:d1869:p -> e5566:(fn p1318:() -> e5565:block { let my p1319:d1870:pos = e5531:(e5529:r2295:"parse::pos"->d714:"std.text.parse.parse.pos" e5530:()); e5564:case e5536:(e5535:r2297:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e5534:(e5532:r2296:"parse::eof"->d713:"std.text.parse.parse.eof" e5533:())) { p1323:true -> e5543:(e5537:r2298:"parse::fail"->d712:"std.text.parse.parse.fail" e5542:(e5540:(e5538:r2299:"ParseError::unexpected"->d721:"std.text.parse.ParseError.unexpected" e5539:r2300:nil->d505:"std.data.opt.opt.nil") e5541:r2301:pos->d1870:pos)); p1324:false -> e5563:block { let my p1320:d1871:item = e5546:(e5544:r2302:"parse::item"->d711:"std.text.parse.parse.item" e5545:()); e5562:case e5551:(e5550:r2305:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e5549:(e5547:r2303:p->d1869:p e5548:r2304:item->d1871:item)) { p1321:true -> e5552:r2306:item->d1871:item; p1322:false -> e5561:(e5553:r2307:"parse::fail"->d712:"std.text.parse.parse.fail" e5560:(e5558:(e5554:r2308:"ParseError::unexpected"->d721:"std.text.parse.ParseError.unexpected" e5557:(e5555:r2309:just->d506:"std.data.opt.opt.just" e5556:r2310:item->d1871:item)) e5559:r2311:pos->d1870:pos)) } } } }))
      pub d772:"std.text.parse.token": std::text::str::str -> () -> [std::text::parse::parse(std::text::char::char, 'a | 'b, 'c, 'd & (std::text::str::str, any, any))] () where std::text::parse::ParseError('b & 'a, item = 'e, pos = 'f) = e5620:(fn p1325:d1872:expected -> e5619:(fn p1326:() -> e5618:block { let my p1330:(p1327:d1873:input, p1328:_, p1329:_) = e5570:(e5568:r2312:"parse::snapshot"->d716:"std.text.parse.parse.snapshot" e5569:()); e5617:case e5579:(e5578:r2316:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e5577:(e5576:(e5573:r2314:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e5572:(e5571:r2313:expected->d1872:expected.s249.len->d840:"std.text.str.str.len")) e5575:(e5574:r2315:input->d1873:input.s250.len->d840:"std.text.str.str.len"))) { p1333:true -> e5607:case e5593:(e5592:r2322:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e5591:(e5590:(e5588:r2320:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e5587:(e5584:(e5582:(e5580:r2317:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5581:r2318:input->d1873:input) e5583:0) e5586:(e5585:r2319:expected->d1872:expected.s251.len->d840:"std.text.str.str.len"))) e5589:r2321:expected->d1872:expected)) { p1331:true -> e5597:(e5594:r2323:"parse::advance"->d718:"std.text.parse.parse.advance" e5596:(e5595:r2324:expected->d1872:expected.s252.len->d840:"std.text.str.str.len")); p1332:false -> e5606:(e5598:r2325:"parse::fail"->d712:"std.text.parse.parse.fail" e5605:(e5601:(e5599:r2326:"ParseError::expected"->d722:"std.text.parse.ParseError.expected" e5600:r2327:expected->d1872:expected) e5604:(e5602:r2328:"parse::pos"->d714:"std.text.parse.parse.pos" e5603:()))) }; p1334:false -> e5616:(e5608:r2329:"parse::fail"->d712:"std.text.parse.parse.fail" e5615:(e5611:(e5609:r2330:"ParseError::expected"->d722:"std.text.parse.ParseError.expected" e5610:r2331:expected->d1872:expected) e5614:(e5612:r2332:"parse::pos"->d714:"std.text.parse.parse.pos" e5613:()))) } }))
      pub d773:"std.text.parse.rest": () -> [std::text::parse::parse std::text::char::char 'a (int, int) (std::text::str::str, int, int)] std::text::str::str = e5631:(fn p1335:() -> e5630:block { let my p1339:(p1336:d1874:input, p1337:_, p1338:_) = e5623:(e5621:r2333:"parse::snapshot"->d716:"std.text.parse.parse.snapshot" e5622:()); e5629:block { e5627:(e5624:r2334:"parse::advance"->d718:"std.text.parse.parse.advance" e5626:(e5625:r2335:input->d1874:input.s253.len->d840:"std.text.str.str.len")); e5628:r2336:input->d1874:input } })
      pub d774:"std.text.parse.optional": (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> () -> [std::text::parse::parse 'a 'b 'c 'd] std::data::opt::opt 'e where 'b: std::text::parse::ParseError(item = 'f, pos = 'g) = e5646:(fn p1340:d1875:p -> e5645:(fn p1341:() -> e5644:(e5642:(e5639:(e5632:r2337:choice->d770:"std.text.parse.choice" e5638:(fn p1342:() -> e5637:(e5633:r2338:just->d506:"std.data.opt.opt.just" e5636:(e5634:r2339:p->d1875:p e5635:())))) e5641:(fn p1343:() -> e5640:r2340:nil->d505:"std.data.opt.opt.nil")) e5643:())))
      pub d775:"std.text.parse.many": (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> () -> [std::text::parse::parse 'a 'b 'c 'd] std::data::list::list 'e where 'b: std::text::parse::ParseError(item = 'f, pos = 'g) = e5671:(fn p1344:d1876:p -> e5670:(fn p1345:() -> e5669:(e5667:(e5662:(e5647:r2341:choice->d770:"std.text.parse.choice" e5661:(fn p1346:() -> e5660:(e5659:(e5658:builtin_op::list_merge e5652:(e5651:builtin_op::list_singleton e5650:(e5648:r2342:p->d1876:p e5649:()))) e5657:(e5655:(e5653:r2343:many->d775:"std.text.parse.many" e5654:r2344:p->d1876:p) e5656:())))) e5666:(fn p1347:() -> e5665:(e5663:builtin_op::list_empty e5664:()))) e5668:())))
      pub d776:"std.text.parse.some": (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> () -> [std::text::parse::parse 'a 'b 'c 'd] std::data::list::list 'e where 'b: std::text::parse::ParseError(item = 'f, pos = 'g) = e5686:(fn p1348:d1877:p -> e5685:(fn p1349:() -> e5684:(e5683:(e5682:builtin_op::list_merge e5676:(e5675:builtin_op::list_singleton e5674:(e5672:r2345:p->d1877:p e5673:()))) e5681:(e5679:(e5677:r2346:many->d775:"std.text.parse.many" e5678:r2347:p->d1877:p) e5680:()))))
      pub d777:"std.text.parse.label": (() -> [std::text::parse::parse 'a 'b 'c 'd] 'e) -> std::text::str::str -> () -> [std::text::parse::parse 'a 'b 'c 'd] 'e where 'b: std::text::parse::ParseError(item = 'f, pos = 'g) = e5699:(fn p1350:d1878:p -> e5698:(fn p1351:d1879:label_text -> e5697:(fn p1352:() -> e5696:catch e5689:(e5687:r2348:p->d1878:p e5688:()) { std::text::parse::parse::fail p1353:d1880:e, p1354:_ -> e5695:(e5690:r2349:"parse::fail"->d712:"std.text.parse.parse.fail" e5694:(e5692:(e5691:r2350:e->d1880:e.s254.label=>d723:"std.text.parse.ParseError.label") e5693:r2351:label_text->d1879:label_text)) })))
      pub d778:"std.text.parse.word": () -> [std::text::parse::parse(std::text::char::char, 'a | 'b, (int, int), (std::text::str::str, int, int))] std::text::str::str where std::text::parse::ParseError('b & 'a, item = 'c, pos = 'd) = e5734:(fn p1355:() -> e5733:block { let my p1359:(p1356:d1881:input, p1357:_, p1358:_) = e5702:(e5700:r2352:"parse::snapshot"->d716:"std.text.parse.parse.snapshot" e5701:()); e5732:block { let my p1360:d1882:found = e5707:(e5705:(e5703:r2353:"std::text::str::word_prefix_at"->d881:"std.text.str.word_prefix_at" e5704:r2354:input->d1881:input) e5706:0); e5731:case e5715:(e5714:r2357:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e5713:(e5712:(e5710:r2356:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e5709:(e5708:r2355:found->d1882:found.s255.len->d840:"std.text.str.str.len")) e5711:0)) { p1361:true -> e5724:(e5716:r2358:"parse::fail"->d712:"std.text.parse.parse.fail" e5723:(e5719:(e5717:r2359:"ParseError::expected"->d722:"std.text.parse.ParseError.expected" e5718:"word") e5722:(e5720:r2360:"parse::pos"->d714:"std.text.parse.parse.pos" e5721:()))); p1362:false -> e5730:block { e5728:(e5725:r2361:"parse::advance"->d718:"std.text.parse.parse.advance" e5727:(e5726:r2362:found->d1882:found.s256.len->d840:"std.text.str.str.len")); e5729:r2363:found->d1882:found } } } })
    }
    pub d116:"std.text.path" mod {
      pub d779:"std.text.path.of_bytes_raw": std::text::bytes::bytes -> std::text::path::path = e5735:builtin_op::bytes_to_path
      pub d780:"std.text.path.to_bytes": std::text::path::path -> std::text::bytes::bytes = e5736:builtin_op::path_to_bytes
      pub d781:"std.text.path.path" mod {
        pub d782:"std.text.path.path.to_bytes": std::text::path::path -> std::text::bytes::bytes = e5740:(fn p1363:d1883:p -> e5739:(e5737:r2364:"std::text::path::to_bytes"->d780:"std.text.path.to_bytes" e5738:r2365:p->d1883:p))
      }
      pub d783:"std.text.path.of_bytes": std::text::bytes::bytes -> std::text::path::path = e5744:(fn p1364:d1884:b -> e5743:(e5741:r2366:"std::text::path::of_bytes_raw"->d779:"std.text.path.of_bytes_raw" e5742:r2367:b->d1884:b))
      my d784 mod {
        d785: std::text::path::path -> std::text::str::str = e5750:(fn p1365:d1885:p -> e5749:(e5745:r2368:"std::text::bytes::to_utf8_lossy"->d668:"std.text.bytes.to_utf8_lossy" e5748:(e5746:r2369:"std::text::path::to_bytes"->d780:"std.text.path.to_bytes" e5747:r2370:p->d1885:p)))
      }
    }
    pub d117:"std.text.str" mod {
      pub d786:"std.text.str.concat": std::text::str::str -> std::text::str::str -> std::text::str::str = e5751:builtin_op::string_concat
      pub d787:"std.text.str.eq": std::text::str::str -> std::text::str::str -> bool = e5752:builtin_op::string_eq
      pub d788:"std.text.str.len": std::text::str::str -> int = e5753:builtin_op::string_len
      pub d789:"std.text.str.line_count": std::text::str::str -> int = e5754:builtin_op::string_line_count
      pub d790:"std.text.str.line_range": std::text::str::str -> int -> std::data::range::range = e5755:builtin_op::string_line_range
      pub d791:"std.text.str.index_raw": std::text::str::str -> int -> std::text::char::char = e5756:builtin_op::string_index
      pub d792:"std.text.str.index_range": std::text::str::str -> std::data::range::range -> std::text::str::str = e5757:builtin_op::string_index_range
      pub d793:"std.text.str.index_range_raw": std::text::str::str -> int -> int -> std::text::str::str = e5758:builtin_op::string_index_range_raw
      pub d794:"std.text.str.splice": std::text::str::str -> std::data::range::range -> std::text::str::str -> std::text::str::str = e5759:builtin_op::string_splice
      pub d795:"std.text.str.splice_raw": std::text::str::str -> int -> int -> std::text::str::str -> std::text::str::str = e5760:builtin_op::string_splice_raw
      pub d796:"std.text.str.to_bytes": std::text::str::str -> std::text::bytes::bytes = e5761:builtin_op::string_to_bytes
      pub d797:"std.text.str.lines": {source: std::text::str::str} -> std::text::str::lines = <missing>
      pub d800:"std.text.str.lines" mod {
      }
      pub d801:"std.text.str.ref_lines": {source: std::control::var::ref 'a std::text::str::str} -> std::text::str::ref_lines 'a = <missing>
      pub d804:"std.text.str.ref_lines" mod {
        pub d805:"std.text.str.ref_lines.index": std::text::str::ref_lines('a & 'b) -> int -> std::control::var::ref('b | 'a, 'c | std::text::str::str) = e5823:(fn p1366:d1886:ls -> e5822:(fn p1367:d1887:i -> e5821:(e5762:r2371:ref->d237:"std.control.var.ref" e5820:{get: e5782:(fn p1368:() -> e5781:block { let my p1369:d1888:line_range = e5771:(e5769:(e5763:r2372:"std::text::str::line_range"->d790:"std.text.str.line_range" e5768:(e5766:(e5765:(e5764:r2373:ls->d1886:ls.s257.source->d802).s258.get->d238) e5767:())) e5770:r2374:i->d1887:i); e5780:(e5778:(e5772:r2375:"std::text::str::index_range"->d792:"std.text.str.index_range" e5777:(e5775:(e5774:(e5773:r2376:ls->d1886:ls.s259.source->d802).s260.get->d238) e5776:())) e5779:r2377:line_range->d1888:line_range) }), update_effect: e5819:(fn p1370:() -> e5818:block { let my p1371:d1889:loop = e5810:(fn p1372:d1890:x -> e5809:catch e5783:r2378:x->d1890:x { std::control::var::ref_update::update p1373:d1891:old, p1374:d1892:k -> e5808:block { let my p1375:d1893:line_range = e5788:(e5786:(e5784:r2379:"std::text::str::line_range"->d790:"std.text.str.line_range" e5785:r2380:old->d1891:old) e5787:r2381:i->d1887:i); e5807:block { let my p1376:d1894:new_item = e5795:(e5789:r2382:"ref_update::update"->d236:"std.control.var.ref_update.update" e5794:(e5792:(e5790:r2383:"std::text::str::index_range"->d792:"std.text.str.index_range" e5791:r2384:old->d1891:old) e5793:r2385:line_range->d1893:line_range)); e5806:(e5796:r2386:loop->d1889:loop e5805:(e5797:r2387:k->d1892:k e5804:(e5802:(e5800:(e5798:r2388:"std::text::str::splice"->d794:"std.text.str.splice" e5799:r2389:old->d1891:old) e5801:r2390:line_range->d1893:line_range) e5803:r2391:new_item->d1894:new_item))) } } }); e5817:(e5811:r2392:loop->d1889:loop e5816:(e5814:(e5813:(e5812:r2393:ls->d1886:ls.s261.source->d802).s262.update_effect->d240) e5815:())) })})))
      }
      pub d806:"std.text.str.str_line_view": std::text::str::str -> std::text::str::lines = e5828:(fn p1377:d1895:source -> e5827:(e5824:r2394:lines->d797:"std.text.str.lines" e5826:{source: e5825:r2395:source->d1895:source}))
      pub d807:"std.text.str.line_view": std::control::var::ref 'a std::text::str::str -> std::text::str::ref_lines 'a = e5833:(fn p1378:d1896:source -> e5832:(e5829:r2396:ref_lines->d801:"std.text.str.ref_lines" e5831:{source: e5830:r2397:source->d1896:source}))
      my d808 mod {
        d809: std::text::str::lines -> int -> std::text::str::str = e5848:(fn p1379:d1897:ls -> e5847:(fn p1380:d1898:i -> e5846:block { let my p1381:d1899:line_range = e5839:(e5837:(e5834:r2398:"std::text::str::line_range"->d790:"std.text.str.line_range" e5836:(e5835:r2399:ls->d1897:ls.s263.source->d798)) e5838:r2400:i->d1898:i); e5845:(e5843:(e5840:r2401:"std::text::str::index_range"->d792:"std.text.str.index_range" e5842:(e5841:r2402:ls->d1897:ls.s264.source->d798)) e5844:r2403:line_range->d1899:line_range) }))
      }
      my d810 mod {
        d811: std::text::str::ref_lines('a & 'b) -> int -> std::control::var::ref('b | 'a, 'c | std::text::str::str) = e5910:(fn p1382:d1900:ls -> e5909:(fn p1383:d1901:i -> e5908:(e5849:r2404:ref->d237:"std.control.var.ref" e5907:{get: e5869:(fn p1384:() -> e5868:block { let my p1385:d1902:line_range = e5858:(e5856:(e5850:r2405:"std::text::str::line_range"->d790:"std.text.str.line_range" e5855:(e5853:(e5852:(e5851:r2406:ls->d1900:ls.s265.source->d802).s266.get->d238) e5854:())) e5857:r2407:i->d1901:i); e5867:(e5865:(e5859:r2408:"std::text::str::index_range"->d792:"std.text.str.index_range" e5864:(e5862:(e5861:(e5860:r2409:ls->d1900:ls.s267.source->d802).s268.get->d238) e5863:())) e5866:r2410:line_range->d1902:line_range) }), update_effect: e5906:(fn p1386:() -> e5905:block { let my p1387:d1903:loop = e5897:(fn p1388:d1904:x -> e5896:catch e5870:r2411:x->d1904:x { std::control::var::ref_update::update p1389:d1905:old, p1390:d1906:k -> e5895:block { let my p1391:d1907:line_range = e5875:(e5873:(e5871:r2412:"std::text::str::line_range"->d790:"std.text.str.line_range" e5872:r2413:old->d1905:old) e5874:r2414:i->d1901:i); e5894:block { let my p1392:d1908:new_item = e5882:(e5876:r2415:"ref_update::update"->d236:"std.control.var.ref_update.update" e5881:(e5879:(e5877:r2416:"std::text::str::index_range"->d792:"std.text.str.index_range" e5878:r2417:old->d1905:old) e5880:r2418:line_range->d1907:line_range)); e5893:(e5883:r2419:loop->d1903:loop e5892:(e5884:r2420:k->d1906:k e5891:(e5889:(e5887:(e5885:r2421:"std::text::str::splice"->d794:"std.text.str.splice" e5886:r2422:old->d1905:old) e5888:r2423:line_range->d1907:line_range) e5890:r2424:new_item->d1908:new_item))) } } }); e5904:(e5898:r2425:loop->d1903:loop e5903:(e5901:(e5900:(e5899:r2426:ls->d1900:ls.s269.source->d802).s270.update_effect->d240) e5902:())) })})))
      }
      my d812:"std.text.str.fold_lines": std::text::str::lines -> int -> int -> 'a -> ('a -> ['b] std::text::str::str -> ['c] 'a) -> ['c, 'b] 'a = e5946:(fn p1393:d1909:ls -> e5945:(fn p1394:d1910:i -> e5944:(fn p1395:d1911:end -> e5943:(fn p1396:d1912:acc -> e5942:(fn p1397:d1913:f -> e5941:case e5917:(e5916:r2430:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e5915:(e5914:(e5912:r2428:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e5911:r2427:i->d1910:i) e5913:r2429:end->d1911:end)) { p1398:true -> e5939:(e5937:(e5928:(e5926:(e5920:(e5918:r2431:fold_lines->d812:"std.text.str.fold_lines" e5919:r2432:ls->d1909:ls) e5925:(e5924:(e5922:r2434:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e5921:r2433:i->d1910:i) e5923:1)) e5927:r2435:end->d1911:end) e5936:(e5931:(e5929:r2436:f->d1913:f e5930:r2437:acc->d1912:acc) e5935:(e5933:(e5932:r2438:ls->d1909:ls.s271.index=>d456:"std.data.index.Index.index") e5934:r2439:i->d1910:i))) e5938:r2440:f->d1913:f); p1399:false -> e5940:r2441:acc->d1912:acc })))))
      my d813:"std.text.str.fold_ref_lines": std::text::str::ref_lines('a & 'b) -> int -> int -> 'c -> ('c -> ['d] std::control::var::ref('b | 'a, 'e | std::text::str::str) -> ['f] 'c) -> ['f, 'd] 'c = e5982:(fn p1400:d1914:ls -> e5981:(fn p1401:d1915:i -> e5980:(fn p1402:d1916:end -> e5979:(fn p1403:d1917:acc -> e5978:(fn p1404:d1918:f -> e5977:case e5953:(e5952:r2445:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e5951:(e5950:(e5948:r2443:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e5947:r2442:i->d1915:i) e5949:r2444:end->d1916:end)) { p1405:true -> e5975:(e5973:(e5964:(e5962:(e5956:(e5954:r2446:fold_ref_lines->d813:"std.text.str.fold_ref_lines" e5955:r2447:ls->d1914:ls) e5961:(e5960:(e5958:r2449:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e5957:r2448:i->d1915:i) e5959:1)) e5963:r2450:end->d1916:end) e5972:(e5967:(e5965:r2451:f->d1918:f e5966:r2452:acc->d1917:acc) e5971:(e5969:(e5968:r2453:ls->d1914:ls.s272.index->d805:"std.text.str.ref_lines.index") e5970:r2454:i->d1915:i))) e5974:r2455:f->d1918:f); p1406:false -> e5976:r2456:acc->d1917:acc })))))
      my d814 mod {
        d815: std::text::str::lines -> 'a -> ('a -> ['b] std::text::str::str -> ['b] 'a) -> ['b] 'a = e5999:(fn p1407:d1919:ls -> e5998:(fn p1408:d1920:z -> e5997:(fn p1409:d1921:f -> e5996:(e5994:(e5992:(e5987:(e5985:(e5983:r2457:fold_lines->d812:"std.text.str.fold_lines" e5984:r2458:ls->d1919:ls) e5986:0) e5991:(e5988:r2459:"std::text::str::line_count"->d789:"std.text.str.line_count" e5990:(e5989:r2460:ls->d1919:ls.s273.source->d798))) e5993:r2461:z->d1920:z) e5995:r2462:f->d1921:f))))
      }
      my d816 mod {
        d817: std::text::str::ref_lines('a & 'b) -> 'c -> ('c -> ['a & 'b] std::control::var::ref('b | 'a, 'd | std::text::str::str) -> ['a & 'b] 'c) -> ['a] 'c = e6019:(fn p1410:d1922:ls -> e6018:(fn p1411:d1923:z -> e6017:(fn p1412:d1924:f -> e6016:(e6014:(e6012:(e6004:(e6002:(e6000:r2463:fold_ref_lines->d813:"std.text.str.fold_ref_lines" e6001:r2464:ls->d1922:ls) e6003:0) e6011:(e6005:r2465:"std::text::str::line_count"->d789:"std.text.str.line_count" e6010:(e6008:(e6007:(e6006:r2466:ls->d1922:ls.s274.source->d802).s275.get->d238) e6009:()))) e6013:r2467:z->d1923:z) e6015:r2468:f->d1924:f))))
      }
      pub d818:"std.text.str.str" mod {
        pub d819:"std.text.str.str.splice": std::text::str::str -> std::data::range::range -> std::text::str::str -> std::text::str::str = e6029:(fn p1413:d1925:s -> e6028:(fn p1414:d1926:r -> e6027:(fn p1415:d1927:insert -> e6026:(e6024:(e6022:(e6020:r2469:"std::text::str::splice"->d794:"std.text.str.splice" e6021:r2470:s->d1925:s) e6023:r2471:r->d1926:r) e6025:r2472:insert->d1927:insert))))
        pub d820:"std.text.str.str.find": std::text::str::str -> std::text::str::str -> std::data::opt::opt std::data::range::range = e6036:(fn p1416:d1928:s -> e6035:(fn p1417:d1929:needle -> e6034:(e6032:(e6030:r2473:"std::text::str::find"->d854:"std.text.str.find" e6031:r2474:s->d1928:s) e6033:r2475:needle->d1929:needle)))
        pub d821:"std.text.str.str.contains": std::text::str::str -> std::text::str::str -> bool = e6043:(fn p1418:d1930:s -> e6042:(fn p1419:d1931:needle -> e6041:(e6039:(e6037:r2476:"std::text::str::contains"->d855:"std.text.str.contains" e6038:r2477:s->d1930:s) e6040:r2478:needle->d1931:needle)))
        pub d822:"std.text.str.str.starts_with": std::text::str::str -> std::text::str::str -> bool = e6050:(fn p1420:d1932:s -> e6049:(fn p1421:d1933:prefix -> e6048:(e6046:(e6044:r2479:"std::text::str::starts_with"->d856:"std.text.str.starts_with" e6045:r2480:s->d1932:s) e6047:r2481:prefix->d1933:prefix)))
        pub d823:"std.text.str.str.ends_with": std::text::str::str -> std::text::str::str -> bool = e6057:(fn p1422:d1934:s -> e6056:(fn p1423:d1935:suffix -> e6055:(e6053:(e6051:r2482:"std::text::str::ends_with"->d857:"std.text.str.ends_with" e6052:r2483:s->d1934:s) e6054:r2484:suffix->d1935:suffix)))
        pub d824:"std.text.str.str.split": std::text::str::str -> std::text::str::str -> std::data::list::list std::text::str::str = e6064:(fn p1424:d1936:s -> e6063:(fn p1425:d1937:separator -> e6062:(e6060:(e6058:r2485:"std::text::str::split"->d859:"std.text.str.split" e6059:r2486:s->d1936:s) e6061:r2487:separator->d1937:separator)))
        pub d825:"std.text.str.str.split_once": std::text::str::str -> std::text::str::str -> std::data::opt::opt (std::text::str::str, std::text::str::str) = e6071:(fn p1426:d1938:s -> e6070:(fn p1427:d1939:separator -> e6069:(e6067:(e6065:r2488:"std::text::str::split_once"->d865:"std.text.str.split_once" e6066:r2489:s->d1938:s) e6068:r2490:separator->d1939:separator)))
        pub d826:"std.text.str.str.replace_once": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e6081:(fn p1428:d1940:s -> e6080:(fn p1429:d1941:from -> e6079:(fn p1430:d1942:to -> e6078:(e6076:(e6074:(e6072:r2491:"std::text::str::replace_once"->d877:"std.text.str.replace_once" e6073:r2492:s->d1940:s) e6075:r2493:from->d1941:from) e6077:r2494:to->d1942:to))))
        pub d827:"std.text.str.str.replace": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e6091:(fn p1431:d1943:s -> e6090:(fn p1432:d1944:from -> e6089:(fn p1433:d1945:to -> e6088:(e6086:(e6084:(e6082:r2495:"std::text::str::replace_all"->d879:"std.text.str.replace_all" e6083:r2496:s->d1943:s) e6085:r2497:from->d1944:from) e6087:r2498:to->d1945:to))))
        pub d828:"std.text.str.str.trim": std::text::str::str -> std::text::str::str = e6095:(fn p1434:d1946:s -> e6094:(e6092:r2499:"std::text::str::trim"->d872:"std.text.str.trim" e6093:r2500:s->d1946:s))
        pub d829:"std.text.str.str.trim_start": std::text::str::str -> std::text::str::str = e6099:(fn p1435:d1947:s -> e6098:(e6096:r2501:"std::text::str::trim_start"->d870:"std.text.str.trim_start" e6097:r2502:s->d1947:s))
        pub d830:"std.text.str.str.trim_end": std::text::str::str -> std::text::str::str = e6103:(fn p1436:d1948:s -> e6102:(e6100:r2503:"std::text::str::trim_end"->d871:"std.text.str.trim_end" e6101:r2504:s->d1948:s))
        pub d831:"std.text.str.str.replace_once!": std::control::var::ref 'a std::text::str::str -> std::text::str::str -> std::text::str::str -> ['a] () = e6117:(fn p1437:d1949:"&r" -> e6116:(fn p1438:d1950:pattern -> e6115:(fn p1439:d1951:replacement -> e6114:(e6105:(e6104:r2505:"&r"->d1949:"&r".s276.update->d243:"std.control.var.ref.update") e6113:(fn p1440:d1952:s -> e6112:(e6110:(e6108:(e6106:r2506:"std::text::str::replace_once"->d877:"std.text.str.replace_once" e6107:r2507:s->d1952:s) e6109:r2508:pattern->d1950:pattern) e6111:r2509:replacement->d1951:replacement))))))
        pub d832:"std.text.str.str.replace!": std::control::var::ref 'a std::text::str::str -> std::text::str::str -> std::text::str::str -> ['a] () = e6131:(fn p1441:d1953:"&r" -> e6130:(fn p1442:d1954:pattern -> e6129:(fn p1443:d1955:replacement -> e6128:(e6119:(e6118:r2510:"&r"->d1953:"&r".s277.update->d243:"std.control.var.ref.update") e6127:(fn p1444:d1956:s -> e6126:(e6124:(e6122:(e6120:r2511:"std::text::str::replace"->d878:"std.text.str.replace" e6121:r2512:s->d1956:s) e6123:r2513:pattern->d1954:pattern) e6125:r2514:replacement->d1955:replacement))))))
        pub d833:"std.text.str.str.replace_all!": std::control::var::ref 'a std::text::str::str -> std::text::str::str -> std::text::str::str -> ['a] () = e6145:(fn p1445:d1957:"&r" -> e6144:(fn p1446:d1958:pattern -> e6143:(fn p1447:d1959:replacement -> e6142:(e6133:(e6132:r2515:"&r"->d1957:"&r".s278.update->d243:"std.control.var.ref.update") e6141:(fn p1448:d1960:s -> e6140:(e6138:(e6136:(e6134:r2516:"std::text::str::replace_all"->d879:"std.text.str.replace_all" e6135:r2517:s->d1960:s) e6137:r2518:pattern->d1958:pattern) e6139:r2519:replacement->d1959:replacement))))))
        pub d834:"std.text.str.str.splice!": std::control::var::ref 'a std::text::str::str -> std::data::range::range -> std::text::str::str -> ['a] () = e6159:(fn p1449:d1961:"&r" -> e6158:(fn p1450:d1962:range -> e6157:(fn p1451:d1963:replacement -> e6156:(e6147:(e6146:r2520:"&r"->d1961:"&r".s279.update->d243:"std.control.var.ref.update") e6155:(fn p1452:d1964:s -> e6154:(e6152:(e6150:(e6148:r2521:"std::text::str::splice"->d794:"std.text.str.splice" e6149:r2522:s->d1964:s) e6151:r2523:range->d1962:range) e6153:r2524:replacement->d1963:replacement))))))
        pub d835:"std.text.str.str.trim!": std::control::var::ref 'a std::text::str::str -> ['a] () = e6167:(fn p1453:d1965:"&r" -> e6166:(e6161:(e6160:r2525:"&r"->d1965:"&r".s280.update->d243:"std.control.var.ref.update") e6165:(fn p1454:d1966:s -> e6164:(e6162:r2526:"std::text::str::trim"->d872:"std.text.str.trim" e6163:r2527:s->d1966:s))))
        pub d836:"std.text.str.str.trim_start!": std::control::var::ref 'a std::text::str::str -> ['a] () = e6175:(fn p1455:d1967:"&r" -> e6174:(e6169:(e6168:r2528:"&r"->d1967:"&r".s281.update->d243:"std.control.var.ref.update") e6173:(fn p1456:d1968:s -> e6172:(e6170:r2529:"std::text::str::trim_start"->d870:"std.text.str.trim_start" e6171:r2530:s->d1968:s))))
        pub d837:"std.text.str.str.trim_end!": std::control::var::ref 'a std::text::str::str -> ['a] () = e6183:(fn p1457:d1969:"&r" -> e6182:(e6177:(e6176:r2531:"&r"->d1969:"&r".s282.update->d243:"std.control.var.ref.update") e6181:(fn p1458:d1970:s -> e6180:(e6178:r2532:"std::text::str::trim_end"->d871:"std.text.str.trim_end" e6179:r2533:s->d1970:s))))
        pub d838:"std.text.str.str.repeat": std::text::str::str -> int -> std::text::str::str = e6190:(fn p1459:d1971:s -> e6189:(fn p1460:d1972:count -> e6188:(e6186:(e6184:r2534:"std::text::str::repeat"->d873:"std.text.str.repeat" e6185:r2535:s->d1971:s) e6187:r2536:count->d1972:count)))
        pub d839:"std.text.str.str.to_int": std::text::str::str -> std::data::opt::opt int = e6194:(fn p1461:d1973:s -> e6193:(e6191:r2537:"std::text::str::to_int"->d876:"std.text.str.to_int" e6192:r2538:s->d1973:s))
        pub d840:"std.text.str.str.len": std::text::str::str -> int = e6198:(fn p1462:d1974:s -> e6197:(e6195:r2539:"std::text::str::len"->d788:"std.text.str.len" e6196:r2540:s->d1974:s))
        pub d841:"std.text.str.str.is_empty": std::text::str::str -> bool = e6202:(fn p1463:d1975:s -> e6201:(e6199:r2541:"std::text::str::is_empty"->d848:"std.text.str.is_empty" e6200:r2542:s->d1975:s))
        pub d842:"std.text.str.str.lines": std::text::str::str -> std::text::str::lines = e6206:(fn p1464:d1976:s -> e6205:(e6203:r2543:str_line_view->d806:"std.text.str.str_line_view" e6204:r2544:s->d1976:s))
        pub d843:"std.text.str.str.lines!": std::control::var::ref 'a std::text::str::str -> std::text::str::ref_lines 'a = e6210:(fn p1465:d1977:"&s" -> e6209:(e6207:r2545:line_view->d807:"std.text.str.line_view" e6208:r2546:"&s"->d1977:"&s"))
        pub d844:"std.text.str.str.print": std::text::str::str -> [std::io::console::out] () = e6214:(fn p1466:d1978:s -> e6213:(e6211:r2547:"std::io::print"->d541:"std.io.console.print" e6212:r2548:s->d1978:s))
        pub d845:"std.text.str.str.println": std::text::str::str -> [std::io::console::out] () = e6218:(fn p1467:d1979:s -> e6217:(e6215:r2549:"std::io::println"->d543:"std.io.console.println" e6216:r2550:s->d1979:s))
        pub d846:"std.text.str.str.eprint": std::text::str::str -> [std::io::console::err] () = e6222:(fn p1468:d1980:s -> e6221:(e6219:r2551:"std::io::eprint"->d547:"std.io.console.eprint" e6220:r2552:s->d1980:s))
        pub d847:"std.text.str.str.eprintln": std::text::str::str -> [std::io::console::err] () = e6226:(fn p1469:d1981:s -> e6225:(e6223:r2553:"std::io::eprintln"->d548:"std.io.console.eprintln" e6224:r2554:s->d1981:s))
      }
      pub d848:"std.text.str.is_empty": std::text::str::str -> bool = e6234:(fn p1470:d1982:s -> e6233:(e6231:(e6227:r2555:"std::int::eq"->d47:"std.int.eq" e6230:(e6228:r2556:"std::text::str::len"->d788:"std.text.str.len" e6229:r2557:s->d1982:s)) e6232:0))
      my d849:"std.text.str.starts_with_at_len": std::text::str::str -> int -> std::text::str::str -> int -> int -> bool = e6265:(fn p1471:d1983:source -> e6264:(fn p1472:d1984:source_len -> e6263:(fn p1473:d1985:needle -> e6262:(fn p1474:d1986:needle_len -> e6261:(fn p1475:d1987:start -> e6260:block { let my p1476:d1988:end = e6239:(e6237:(e6235:r2558:"std::int::add"->d52:"std.int.add" e6236:r2559:start->d1987:start) e6238:r2560:needle_len->d1986:needle_len); e6259:case e6246:(e6245:r2564:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6244:(e6242:(e6240:r2561:"std::int::le"->d49:"std.int.le" e6241:r2562:end->d1988:end) e6243:r2563:source_len->d1984:source_len)) { p1477:true -> e6257:(e6256:(e6254:r2569:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e6253:(e6251:(e6249:(e6247:r2565:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e6248:r2566:source->d1983:source) e6250:r2567:start->d1987:start) e6252:r2568:end->d1988:end)) e6255:r2570:needle->d1985:needle); p1478:false -> e6258:false } })))))
      my d850:"std.text.str.starts_with_at": std::text::str::str -> std::text::str::str -> int -> bool = e6283:(fn p1479:d1989:source -> e6282:(fn p1480:d1990:needle -> e6281:(fn p1481:d1991:start -> e6280:(e6278:(e6274:(e6272:(e6268:(e6266:r2571:starts_with_at_len->d849:"std.text.str.starts_with_at_len" e6267:r2572:source->d1989:source) e6271:(e6269:r2573:"std::text::str::len"->d788:"std.text.str.len" e6270:r2574:source->d1989:source)) e6273:r2575:needle->d1990:needle) e6277:(e6275:r2576:"std::text::str::len"->d788:"std.text.str.len" e6276:r2577:needle->d1990:needle)) e6279:r2578:start->d1991:start))))
      my d851:"std.text.str.find_at_len": std::text::str::str -> int -> std::text::str::str -> int -> int -> std::data::opt::opt int = e6316:(fn p1482:d1992:source -> e6315:(fn p1483:d1993:source_len -> e6314:(fn p1484:d1994:needle -> e6313:(fn p1485:d1995:needle_len -> e6312:(fn p1486:d1996:start -> e6311:case e6290:(e6289:r2581:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6288:(e6286:(e6284:r2579:"std::int::eq"->d47:"std.int.eq" e6285:r2580:needle_len->d1995:needle_len) e6287:0)) { p1487:true -> e6293:(e6291:r2582:just->d506:"std.data.opt.opt.just" e6292:r2583:start->d1996:start); p1488:false -> e6310:(e6308:(e6302:(e6300:(e6298:(e6296:(e6294:r2584:find_at_loop->d852:"std.text.str.find_at_loop" e6295:r2585:source->d1992:source) e6297:r2586:source_len->d1993:source_len) e6299:r2587:needle->d1994:needle) e6301:r2588:needle_len->d1995:needle_len) e6307:(e6305:(e6303:r2589:"std::int::sub"->d53:"std.int.sub" e6304:r2590:source_len->d1993:source_len) e6306:r2591:needle_len->d1995:needle_len)) e6309:r2592:start->d1996:start) })))))
      my d852:"std.text.str.find_at_loop": std::text::str::str -> int -> std::text::str::str -> int -> int -> int -> std::data::opt::opt int = e6365:(fn p1489:d1997:source -> e6364:(fn p1490:d1998:source_len -> e6363:(fn p1491:d1999:needle -> e6362:(fn p1492:d2000:needle_len -> e6361:(fn p1493:d2001:limit -> e6360:(fn p1494:d2002:i -> e6359:case e6323:(e6322:r2596:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6321:(e6319:(e6317:r2593:"std::int::le"->d49:"std.int.le" e6318:r2594:i->d2002:i) e6320:r2595:limit->d2001:limit)) { p1497:true -> e6357:case e6336:(e6335:r2603:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6334:(e6332:(e6330:(e6328:(e6326:(e6324:r2597:starts_with_at_len->d849:"std.text.str.starts_with_at_len" e6325:r2598:source->d1997:source) e6327:r2599:source_len->d1998:source_len) e6329:r2600:needle->d1999:needle) e6331:r2601:needle_len->d2000:needle_len) e6333:r2602:i->d2002:i)) { p1495:true -> e6339:(e6337:r2604:just->d506:"std.data.opt.opt.just" e6338:r2605:i->d2002:i); p1496:false -> e6356:(e6350:(e6348:(e6346:(e6344:(e6342:(e6340:r2606:find_at_loop->d852:"std.text.str.find_at_loop" e6341:r2607:source->d1997:source) e6343:r2608:source_len->d1998:source_len) e6345:r2609:needle->d1999:needle) e6347:r2610:needle_len->d2000:needle_len) e6349:r2611:limit->d2001:limit) e6355:(e6353:(e6351:r2612:"std::int::add"->d52:"std.int.add" e6352:r2613:i->d2002:i) e6354:1)) }; p1498:false -> e6358:r2614:nil->d505:"std.data.opt.opt.nil" }))))))
      my d853:"std.text.str.find_at": std::text::str::str -> std::text::str::str -> int -> std::data::opt::opt int = e6383:(fn p1499:d2003:source -> e6382:(fn p1500:d2004:needle -> e6381:(fn p1501:d2005:start -> e6380:(e6378:(e6374:(e6372:(e6368:(e6366:r2615:find_at_len->d851:"std.text.str.find_at_len" e6367:r2616:source->d2003:source) e6371:(e6369:r2617:"std::text::str::len"->d788:"std.text.str.len" e6370:r2618:source->d2003:source)) e6373:r2619:needle->d2004:needle) e6377:(e6375:r2620:"std::text::str::len"->d788:"std.text.str.len" e6376:r2621:needle->d2004:needle)) e6379:r2622:start->d2005:start))))
      pub d854:"std.text.str.find": std::text::str::str -> std::text::str::str -> std::data::opt::opt std::data::range::range = e6407:(fn p1502:d2006:source -> e6406:(fn p1503:d2007:needle -> e6405:case e6390:(e6388:(e6386:(e6384:r2623:find_at->d853:"std.text.str.find_at" e6385:r2624:source->d2006:source) e6387:r2625:needle->d2007:needle) e6389:0) { p1505:r2626:just->d506:"std.data.opt.opt.just"(p1504:d2008:i) -> e6403:(e6391:r2627:just->d506:"std.data.opt.opt.just" e6402:(e6394:(e6392:r2628:range->d513:"std.data.range.range" e6393:r2629:i->d2008:i) e6401:(e6397:(e6395:r2630:"std::int::add"->d52:"std.int.add" e6396:r2631:i->d2008:i) e6400:(e6398:r2632:"std::text::str::len"->d788:"std.text.str.len" e6399:r2633:needle->d2007:needle)))); p1506:r2634:nil->d505:"std.data.opt.opt.nil" -> e6404:r2635:nil->d505:"std.data.opt.opt.nil" }))
      pub d855:"std.text.str.contains": std::text::str::str -> std::text::str::str -> bool = e6419:(fn p1507:d2009:source -> e6418:(fn p1508:d2010:needle -> e6417:case e6414:(e6412:(e6410:(e6408:r2636:find_at->d853:"std.text.str.find_at" e6409:r2637:source->d2009:source) e6411:r2638:needle->d2010:needle) e6413:0) { p1510:r2639:just->d506:"std.data.opt.opt.just"(p1509:_) -> e6415:true; p1511:r2640:nil->d505:"std.data.opt.opt.nil" -> e6416:false }))
      pub d856:"std.text.str.starts_with": std::text::str::str -> std::text::str::str -> bool = e6428:(fn p1512:d2011:source -> e6427:(fn p1513:d2012:prefix -> e6426:(e6424:(e6422:(e6420:r2641:starts_with_at->d850:"std.text.str.starts_with_at" e6421:r2642:source->d2011:source) e6423:r2643:prefix->d2012:prefix) e6425:0)))
      pub d857:"std.text.str.ends_with": std::text::str::str -> std::text::str::str -> bool = e6458:(fn p1514:d2013:source -> e6457:(fn p1515:d2014:suffix -> e6456:block { let my p1516:d2015:source_len = e6431:(e6429:r2644:"std::text::str::len"->d788:"std.text.str.len" e6430:r2645:source->d2013:source); e6455:block { let my p1517:d2016:suffix_len = e6434:(e6432:r2646:"std::text::str::len"->d788:"std.text.str.len" e6433:r2647:suffix->d2014:suffix); e6454:case e6441:(e6440:r2651:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6439:(e6437:(e6435:r2648:"std::int::le"->d49:"std.int.le" e6436:r2649:suffix_len->d2016:suffix_len) e6438:r2650:source_len->d2015:source_len)) { p1518:true -> e6452:(e6446:(e6444:(e6442:r2652:starts_with_at->d850:"std.text.str.starts_with_at" e6443:r2653:source->d2013:source) e6445:r2654:suffix->d2014:suffix) e6451:(e6449:(e6447:r2655:"std::int::sub"->d53:"std.int.sub" e6448:r2656:source_len->d2015:source_len) e6450:r2657:suffix_len->d2016:suffix_len)); p1519:false -> e6453:false } } }))
      my d858:"std.text.str.split_newline_byte_scan_min": int = e6459:2
      pub d859:"std.text.str.split": std::text::str::str -> std::text::str::str -> std::data::list::list std::text::str::str = e6528:(fn p1520:d2017:source -> e6527:(fn p1521:d2018:separator -> e6526:block { let my p1522:d2019:source_len = e6462:(e6460:r2658:"std::text::str::len"->d788:"std.text.str.len" e6461:r2659:source->d2017:source); e6525:block { let my p1523:d2020:separator_len = e6465:(e6463:r2660:"std::text::str::len"->d788:"std.text.str.len" e6464:r2661:separator->d2018:separator); e6524:case e6472:(e6471:r2664:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6470:(e6468:(e6466:r2662:"std::int::eq"->d47:"std.int.eq" e6467:r2663:separator_len->d2020:separator_len) e6469:0)) { p1531:true -> e6475:(e6474:builtin_op::list_singleton e6473:r2665:source->d2017:source); p1532:false -> e6523:case e6482:(e6481:r2668:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6480:(e6479:(e6477:r2667:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e6476:r2666:separator->d2018:separator) e6478:"\n")) { p1529:true -> e6513:case e6489:(e6488:r2672:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6487:(e6486:(e6484:r2670:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e6483:r2669:source_len->d2019:source_len) e6485:r2671:split_newline_byte_scan_min->d858:"std.text.str.split_newline_byte_scan_min")) { p1527:true -> e6498:(e6496:(e6494:(e6492:(e6490:r2673:split_generic->d860:"std.text.str.split_generic" e6491:r2674:source->d2017:source) e6493:r2675:source_len->d2019:source_len) e6495:r2676:separator->d2018:separator) e6497:r2677:separator_len->d2020:separator_len); p1528:false -> e6512:case e6501:(e6499:r2678:split_newline_bytes->d862:"std.text.str.split_newline_bytes" e6500:r2679:source->d2017:source) { p1525:r2680:just->d506:"std.data.opt.opt.just"(p1524:d2021:parts) -> e6502:r2681:parts->d2021:parts; p1526:r2682:nil->d505:"std.data.opt.opt.nil" -> e6511:(e6509:(e6507:(e6505:(e6503:r2683:split_generic->d860:"std.text.str.split_generic" e6504:r2684:source->d2017:source) e6506:r2685:source_len->d2019:source_len) e6508:r2686:separator->d2018:separator) e6510:r2687:separator_len->d2020:separator_len) } }; p1530:false -> e6522:(e6520:(e6518:(e6516:(e6514:r2688:split_generic->d860:"std.text.str.split_generic" e6515:r2689:source->d2017:source) e6517:r2690:source_len->d2019:source_len) e6519:r2691:separator->d2018:separator) e6521:r2692:separator_len->d2020:separator_len) } } } }))
      my d860:"std.text.str.split_generic": std::text::str::str -> int -> std::text::str::str -> int -> std::data::list::list std::text::str::str = e6547:(fn p1533:d2022:source -> e6546:(fn p1534:d2023:source_len -> e6545:(fn p1535:d2024:separator -> e6544:(fn p1536:d2025:separator_len -> e6543:(e6539:(e6537:(e6535:(e6533:(e6531:(e6529:r2693:split_generic_loop->d861:"std.text.str.split_generic_loop" e6530:r2694:source->d2022:source) e6532:r2695:source_len->d2023:source_len) e6534:r2696:separator->d2024:separator) e6536:r2697:separator_len->d2025:separator_len) e6538:0) e6542:(e6540:builtin_op::list_empty e6541:()))))))
      my d861:"std.text.str.split_generic_loop": std::text::str::str -> int -> std::text::str::str -> int -> int -> std::data::list::list std::text::str::str -> std::data::list::list std::text::str::str = e6607:(fn p1537:d2026:source -> e6606:(fn p1538:d2027:source_len -> e6605:(fn p1539:d2028:separator -> e6604:(fn p1540:d2029:separator_len -> e6603:(fn p1541:d2030:start -> e6602:(fn p1542:d2031:out -> e6601:case e6558:(e6556:(e6554:(e6552:(e6550:(e6548:r2698:find_at_len->d851:"std.text.str.find_at_len" e6549:r2699:source->d2026:source) e6551:r2700:source_len->d2027:source_len) e6553:r2701:separator->d2028:separator) e6555:r2702:separator_len->d2029:separator_len) e6557:r2703:start->d2030:start) { p1544:r2704:just->d506:"std.data.opt.opt.just"(p1543:d2032:i) -> e6587:block { let my p1545:d2033:piece = e6565:(e6563:(e6561:(e6559:r2705:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e6560:r2706:source->d2026:source) e6562:r2707:start->d2030:start) e6564:r2708:i->d2032:i); e6586:(e6580:(e6574:(e6572:(e6570:(e6568:(e6566:r2709:split_generic_loop->d861:"std.text.str.split_generic_loop" e6567:r2710:source->d2026:source) e6569:r2711:source_len->d2027:source_len) e6571:r2712:separator->d2028:separator) e6573:r2713:separator_len->d2029:separator_len) e6579:(e6577:(e6575:r2714:"std::int::add"->d52:"std.int.add" e6576:r2715:i->d2032:i) e6578:r2716:separator_len->d2029:separator_len)) e6585:(e6583:(e6581:r2717:"std::data::list::cons"->d493:"std.data.list.cons" e6582:r2718:piece->d2033:piece) e6584:r2719:out->d2031:out)) }; p1546:r2720:nil->d505:"std.data.opt.opt.nil" -> e6600:(e6588:r2721:"std::data::list::rev"->d496:"std.data.list.rev" e6599:(e6597:(e6589:r2722:"std::data::list::cons"->d493:"std.data.list.cons" e6596:(e6594:(e6592:(e6590:r2723:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e6591:r2724:source->d2026:source) e6593:r2725:start->d2030:start) e6595:r2726:source_len->d2027:source_len)) e6598:r2727:out->d2031:out)) }))))))
      my d862:"std.text.str.split_newline_bytes": std::text::str::str -> std::data::opt::opt(std::data::list::list std::text::str::str) = e6674:(fn p1547:d2034:source -> e6673:block { let my p1548:d2035:data = e6610:(e6608:r2728:"std::text::str::to_bytes"->d796:"std.text.str.to_bytes" e6609:r2729:source->d2034:source); e6672:block { let my p1549:d2036:end = e6613:(e6611:r2730:"std::text::bytes::len"->d655:"std.text.bytes.len" e6612:r2731:data->d2035:data); e6671:block { let my p1550:d2037:chunk_count = e6622:(e6620:(e6614:r2732:"std::int::div"->d55:"std.int.div" e6619:(e6618:(e6616:r2734:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e6615:r2733:end->d2036:end) e6617:1023)) e6621:1024); e6670:block { let my p1551:d2038:scan = e6647:(e6635:(e6628:(e6627:(e6626:(e6624:r2735:"#op:infix:..<"->d410:"std.core.ops.#op:infix:..<" e6623:0) e6625:r2736:chunk_count->d2037:chunk_count).s283.fold=>d451:"std.data.fold.Fold.fold") e6634:(e6629:0, e6632:(e6630:builtin_op::list_empty e6631:()), e6633:true)) e6646:(fn p1552:d2039:state -> e6645:(fn p1553:d2040:chunk -> e6644:(e6642:(e6640:(e6638:(e6636:r2737:split_newline_bytes_chunk->d863:"std.text.str.split_newline_bytes_chunk" e6637:r2738:data->d2035:data) e6639:r2739:end->d2036:end) e6641:r2740:state->d2039:state) e6643:r2741:chunk->d2040:chunk)))); e6669:case e6648:r2742:scan->d2038:scan { p1557:(p1554:d2041:start, p1555:d2042:out, p1556:true) -> e6667:(e6649:r2743:just->d506:"std.data.opt.opt.just" e6666:(e6650:r2744:"std::data::list::rev"->d496:"std.data.list.rev" e6665:(e6663:(e6651:r2745:"std::data::list::cons"->d493:"std.data.list.cons" e6662:(e6652:r2746:"std::text::bytes::to_utf8_lossy"->d668:"std.text.bytes.to_utf8_lossy" e6661:(e6655:(e6653:r2747:"std::text::bytes::index_range"->d659:"std.text.bytes.index_range" e6654:r2748:data->d2035:data) e6660:(e6658:(e6656:r2749:"std::data::range::range"->d513:"std.data.range.range" e6657:r2750:start->d2041:start) e6659:r2751:end->d2036:end)))) e6664:r2752:out->d2042:out))); p1558:_ -> e6668:r2753:nil->d505:"std.data.opt.opt.nil" } } } } })
      my d863:"std.text.str.split_newline_bytes_chunk": std::text::bytes::bytes -> int -> (int, std::data::list::list std::text::str::str, bool) -> int -> (int, std::data::list::list std::text::str::str, bool) = e6724:(fn p1559:d2043:data -> e6723:(fn p1560:d2044:end -> e6722:(fn p1561:d2045:state -> e6721:(fn p1562:d2046:chunk -> e6720:case e6675:r2754:state->d2045:state { p1566:(p1563:_, p1564:_, p1565:false) -> e6676:r2755:state->d2045:state; p1567:_ -> e6719:block { let my p1568:d2047:i = e6681:(e6680:(e6678:r2757:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e6677:r2756:chunk->d2046:chunk) e6679:1024); e6718:block { let my p1569:d2048:chunk_end = e6699:case e6692:(e6691:r2762:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6690:(e6689:(e6687:r2760:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e6686:(e6685:(e6683:r2759:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e6682:r2758:i->d2047:i) e6684:1024)) e6688:r2761:end->d2044:end)) { p1570:true -> e6697:(e6696:(e6694:r2764:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e6693:r2763:i->d2047:i) e6695:1024); p1571:false -> e6698:r2765:end->d2044:end }; e6717:(e6707:(e6705:(e6704:(e6702:(e6700:r2766:"std::data::range::range"->d513:"std.data.range.range" e6701:r2767:i->d2047:i) e6703:r2768:chunk_end->d2048:chunk_end).s284.fold=>d451:"std.data.fold.Fold.fold") e6706:r2769:state->d2045:state) e6716:(fn p1572:d2049:state -> e6715:(fn p1573:d2050:j -> e6714:(e6712:(e6710:(e6708:r2770:split_newline_bytes_step->d864:"std.text.str.split_newline_bytes_step" e6709:r2771:data->d2043:data) e6711:r2772:state->d2049:state) e6713:r2773:j->d2050:j)))) } } }))))
      my d864:"std.text.str.split_newline_bytes_step": std::text::bytes::bytes -> (int, std::data::list::list std::text::str::str, bool) -> int -> (int, std::data::list::list std::text::str::str, bool) = e6765:(fn p1574:d2051:data -> e6764:(fn p1575:d2052:state -> e6763:(fn p1576:d2053:i -> e6762:case e6725:r2774:state->d2052:state { p1580:(p1577:d2054:start, p1578:d2055:out, p1579:true) -> e6760:case e6730:(e6728:(e6726:r2775:"std::text::bytes::index_raw"->d658:"std.text.bytes.index_raw" e6727:r2776:data->d2051:data) e6729:r2777:i->d2053:i) { p1581:10 -> e6754:block { let my p1582:d2056:piece = e6741:(e6731:r2778:"std::text::bytes::to_utf8_lossy"->d668:"std.text.bytes.to_utf8_lossy" e6740:(e6734:(e6732:r2779:"std::text::bytes::index_range"->d659:"std.text.bytes.index_range" e6733:r2780:data->d2051:data) e6739:(e6737:(e6735:r2781:"std::data::range::range"->d513:"std.data.range.range" e6736:r2782:start->d2054:start) e6738:r2783:i->d2053:i))); e6753:(e6746:(e6745:(e6743:r2785:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e6742:r2784:i->d2053:i) e6744:1), e6751:(e6749:(e6747:r2786:"std::data::list::cons"->d493:"std.data.list.cons" e6748:r2787:piece->d2056:piece) e6750:r2788:out->d2055:out), e6752:true) }; p1583:13 -> e6758:(e6755:r2789:start->d2054:start, e6756:r2790:out->d2055:out, e6757:false); p1584:_ -> e6759:r2791:state->d2052:state }; p1585:_ -> e6761:r2792:state->d2052:state })))
      pub d865:"std.text.str.split_once": std::text::str::str -> std::text::str::str -> std::data::opt::opt (std::text::str::str, std::text::str::str) = e6809:(fn p1586:d2057:source -> e6808:(fn p1587:d2058:separator -> e6807:block { let my p1588:d2059:source_len = e6768:(e6766:r2793:"std::text::str::len"->d788:"std.text.str.len" e6767:r2794:source->d2057:source); e6806:block { let my p1589:d2060:separator_len = e6771:(e6769:r2795:"std::text::str::len"->d788:"std.text.str.len" e6770:r2796:separator->d2058:separator); e6805:case e6782:(e6780:(e6778:(e6776:(e6774:(e6772:r2797:find_at_len->d851:"std.text.str.find_at_len" e6773:r2798:source->d2057:source) e6775:r2799:source_len->d2059:source_len) e6777:r2800:separator->d2058:separator) e6779:r2801:separator_len->d2060:separator_len) e6781:0) { p1591:r2802:just->d506:"std.data.opt.opt.just"(p1590:d2061:i) -> e6803:(e6783:r2803:just->d506:"std.data.opt.opt.just" e6802:(e6790:(e6788:(e6786:(e6784:r2804:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e6785:r2805:source->d2057:source) e6787:0) e6789:r2806:i->d2061:i), e6801:(e6799:(e6793:(e6791:r2807:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e6792:r2808:source->d2057:source) e6798:(e6796:(e6794:r2809:"std::int::add"->d52:"std.int.add" e6795:r2810:i->d2061:i) e6797:r2811:separator_len->d2060:separator_len)) e6800:r2812:source_len->d2059:source_len))); p1592:r2813:nil->d505:"std.data.opt.opt.nil" -> e6804:r2814:nil->d505:"std.data.opt.opt.nil" } } }))
      my d866:"std.text.str.join_tail": std::data::list::list std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e6832:(fn p1593:d2062:parts -> e6831:(fn p1594:d2063:separator -> e6830:(fn p1595:d2064:out -> e6829:case e6812:(e6810:r2815:"std::data::list::uncons"->d494:"std.data.list.uncons" e6811:r2816:parts->d2062:parts) { p1596:r2817:nil->d505:"std.data.opt.opt.nil" -> e6813:r2818:out->d2064:out; p1600:r2819:just->d506:"std.data.opt.opt.just"(p1599:(p1597:d2065:part, p1598:d2066:rest)) -> e6828:(e6818:(e6816:(e6814:r2820:join_tail->d866:"std.text.str.join_tail" e6815:r2821:rest->d2066:rest) e6817:r2822:separator->d2063:separator) e6827:(e6825:(e6819:r2823:"std::text::str::concat"->d786:"std.text.str.concat" e6824:(e6822:(e6820:r2824:"std::text::str::concat"->d786:"std.text.str.concat" e6821:r2825:out->d2064:out) e6823:r2826:separator->d2063:separator)) e6826:r2827:part->d2065:part)) })))
      pub d867:"std.text.str.join": std::data::list::list std::text::str::str -> std::text::str::str -> std::text::str::str = e6846:(fn p1601:d2067:parts -> e6845:(fn p1602:d2068:separator -> e6844:case e6835:(e6833:r2828:"std::data::list::uncons"->d494:"std.data.list.uncons" e6834:r2829:parts->d2067:parts) { p1603:r2830:nil->d505:"std.data.opt.opt.nil" -> e6836:""; p1607:r2831:just->d506:"std.data.opt.opt.just"(p1606:(p1604:d2069:head, p1605:d2070:tail)) -> e6843:(e6841:(e6839:(e6837:r2832:join_tail->d866:"std.text.str.join_tail" e6838:r2833:tail->d2070:tail) e6840:r2834:separator->d2068:separator) e6842:r2835:head->d2069:head) }))
      my d868:"std.text.str.trim_start_index": std::text::str::str -> int -> int = e6879:(fn p1608:d2071:source -> e6878:(fn p1609:d2072:i -> e6877:case e6855:(e6854:r2840:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6853:(e6849:(e6847:r2836:"std::int::lt"->d48:"std.int.lt" e6848:r2837:i->d2072:i) e6852:(e6850:r2838:"std::text::str::len"->d788:"std.text.str.len" e6851:r2839:source->d2071:source))) { p1612:true -> e6875:case e6864:(e6863:r2845:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6862:(e6856:r2841:"std::text::char::is_whitespace"->d675:"std.text.char.is_whitespace" e6861:(e6859:(e6857:r2842:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e6858:r2843:source->d2071:source) e6860:r2844:i->d2072:i))) { p1610:true -> e6873:(e6867:(e6865:r2846:trim_start_index->d868:"std.text.str.trim_start_index" e6866:r2847:source->d2071:source) e6872:(e6870:(e6868:r2848:"std::int::add"->d52:"std.int.add" e6869:r2849:i->d2072:i) e6871:1)); p1611:false -> e6874:r2850:i->d2072:i }; p1613:false -> e6876:r2851:i->d2072:i }))
      my d869:"std.text.str.trim_end_index": std::text::str::str -> int -> int = e6912:(fn p1614:d2073:source -> e6911:(fn p1615:d2074:end -> e6910:case e6886:(e6885:r2854:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6884:(e6882:(e6880:r2852:"std::int::gt"->d50:"std.int.gt" e6881:r2853:end->d2074:end) e6883:0)) { p1619:true -> e6908:block { let my p1616:d2075:previous = e6891:(e6889:(e6887:r2855:"std::int::sub"->d53:"std.int.sub" e6888:r2856:end->d2074:end) e6890:1); e6907:case e6900:(e6899:r2861:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6898:(e6892:r2857:"std::text::char::is_whitespace"->d675:"std.text.char.is_whitespace" e6897:(e6895:(e6893:r2858:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e6894:r2859:source->d2073:source) e6896:r2860:previous->d2075:previous))) { p1617:true -> e6905:(e6903:(e6901:r2862:trim_end_index->d869:"std.text.str.trim_end_index" e6902:r2863:source->d2073:source) e6904:r2864:previous->d2075:previous); p1618:false -> e6906:r2865:end->d2074:end } }; p1620:false -> e6909:r2866:end->d2074:end }))
      pub d870:"std.text.str.trim_start": std::text::str::str -> std::text::str::str = e6926:(fn p1621:d2076:source -> e6925:(e6921:(e6915:(e6913:r2867:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e6914:r2868:source->d2076:source) e6920:(e6918:(e6916:r2869:trim_start_index->d868:"std.text.str.trim_start_index" e6917:r2870:source->d2076:source) e6919:0)) e6924:(e6922:r2871:"std::text::str::len"->d788:"std.text.str.len" e6923:r2872:source->d2076:source)))
      pub d871:"std.text.str.trim_end": std::text::str::str -> std::text::str::str = e6940:(fn p1622:d2077:source -> e6939:(e6931:(e6929:(e6927:r2873:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e6928:r2874:source->d2077:source) e6930:0) e6938:(e6934:(e6932:r2875:trim_end_index->d869:"std.text.str.trim_end_index" e6933:r2876:source->d2077:source) e6937:(e6935:r2877:"std::text::str::len"->d788:"std.text.str.len" e6936:r2878:source->d2077:source))))
      pub d872:"std.text.str.trim": std::text::str::str -> std::text::str::str = e6971:(fn p1623:d2078:source -> e6970:block { let my p1624:d2079:start = e6945:(e6943:(e6941:r2879:trim_start_index->d868:"std.text.str.trim_start_index" e6942:r2880:source->d2078:source) e6944:0); e6969:block { let my p1625:d2080:end = e6952:(e6948:(e6946:r2881:trim_end_index->d869:"std.text.str.trim_end_index" e6947:r2882:source->d2078:source) e6951:(e6949:r2883:"std::text::str::len"->d788:"std.text.str.len" e6950:r2884:source->d2078:source)); e6968:case e6959:(e6958:r2888:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6957:(e6955:(e6953:r2885:"std::int::le"->d49:"std.int.le" e6954:r2886:start->d2079:start) e6956:r2887:end->d2080:end)) { p1626:true -> e6966:(e6964:(e6962:(e6960:r2889:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e6961:r2890:source->d2078:source) e6963:r2891:start->d2079:start) e6965:r2892:end->d2080:end); p1627:false -> e6967:"" } } })
      pub d873:"std.text.str.repeat": std::text::str::str -> int -> std::text::str::str = e7012:(fn p1628:d2081:source -> e7011:(fn p1629:d2082:count -> e7010:block { let my p1630:d2083:loop = e6995:(fn p1631:d2084:i -> e6994:(fn p1632:d2085:out -> e6993:case e6978:(e6977:r2896:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6976:(e6974:(e6972:r2893:"std::int::lt"->d48:"std.int.lt" e6973:r2894:i->d2084:i) e6975:r2895:count->d2082:count)) { p1633:true -> e6991:(e6985:(e6979:r2897:loop->d2083:loop e6984:(e6982:(e6980:r2898:"std::int::add"->d52:"std.int.add" e6981:r2899:i->d2084:i) e6983:1)) e6990:(e6988:(e6986:r2900:"std::text::str::concat"->d786:"std.text.str.concat" e6987:r2901:out->d2085:out) e6989:r2902:source->d2081:source)); p1634:false -> e6992:r2903:out->d2085:out })); e7009:case e7002:(e7001:r2906:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7000:(e6998:(e6996:r2904:"std::int::le"->d49:"std.int.le" e6997:r2905:count->d2082:count) e6999:0)) { p1635:true -> e7003:""; p1636:false -> e7008:(e7006:(e7004:r2907:loop->d2083:loop e7005:0) e7007:"") } }))
      my d874:"std.text.str.digit_value": std::text::char::char -> std::data::opt::opt int = e7048:(fn p1637:d2086:item -> e7047:case e7015:(e7013:r2908:"std::text::char::to_string"->d674:"std.text.char.to_string" e7014:r2909:item->d2086:item) { p1638:"0" -> e7018:(e7016:r2910:just->d506:"std.data.opt.opt.just" e7017:0); p1639:"1" -> e7021:(e7019:r2911:just->d506:"std.data.opt.opt.just" e7020:1); p1640:"2" -> e7024:(e7022:r2912:just->d506:"std.data.opt.opt.just" e7023:2); p1641:"3" -> e7027:(e7025:r2913:just->d506:"std.data.opt.opt.just" e7026:3); p1642:"4" -> e7030:(e7028:r2914:just->d506:"std.data.opt.opt.just" e7029:4); p1643:"5" -> e7033:(e7031:r2915:just->d506:"std.data.opt.opt.just" e7032:5); p1644:"6" -> e7036:(e7034:r2916:just->d506:"std.data.opt.opt.just" e7035:6); p1645:"7" -> e7039:(e7037:r2917:just->d506:"std.data.opt.opt.just" e7038:7); p1646:"8" -> e7042:(e7040:r2918:just->d506:"std.data.opt.opt.just" e7041:8); p1647:"9" -> e7045:(e7043:r2919:just->d506:"std.data.opt.opt.just" e7044:9); p1648:_ -> e7046:r2920:nil->d505:"std.data.opt.opt.nil" })
      my d875:"std.text.str.parse_unsigned_int": std::text::str::str -> int -> int -> int -> std::data::opt::opt int = e7104:(fn p1649:d2087:source -> e7103:(fn p1650:d2088:start -> e7102:(fn p1651:d2089:i -> e7101:(fn p1652:d2090:acc -> e7100:case e7057:(e7056:r2925:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7055:(e7051:(e7049:r2921:"std::int::lt"->d48:"std.int.lt" e7050:r2922:i->d2089:i) e7054:(e7052:r2923:"std::text::str::len"->d788:"std.text.str.len" e7053:r2924:source->d2087:source))) { p1658:true -> e7087:case e7064:(e7058:r2926:digit_value->d874:"std.text.str.digit_value" e7063:(e7061:(e7059:r2927:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e7060:r2928:source->d2087:source) e7062:r2929:i->d2089:i)) { p1654:r2930:just->d506:"std.data.opt.opt.just"(p1653:d2091:digit) -> e7085:(e7075:(e7069:(e7067:(e7065:r2931:parse_unsigned_int->d875:"std.text.str.parse_unsigned_int" e7066:r2932:source->d2087:source) e7068:r2933:start->d2088:start) e7074:(e7072:(e7070:r2934:"std::int::add"->d52:"std.int.add" e7071:r2935:i->d2089:i) e7073:1)) e7084:(e7082:(e7076:r2936:"std::int::add"->d52:"std.int.add" e7081:(e7079:(e7077:r2937:"std::int::mul"->d54:"std.int.mul" e7078:r2938:acc->d2090:acc) e7080:10)) e7083:r2939:digit->d2091:digit)); p1655:r2940:nil->d505:"std.data.opt.opt.nil" -> e7086:r2941:nil->d505:"std.data.opt.opt.nil" }; p1659:false -> e7099:case e7094:(e7093:r2945:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7092:(e7090:(e7088:r2942:"std::int::eq"->d47:"std.int.eq" e7089:r2943:i->d2089:i) e7091:r2944:start->d2088:start)) { p1656:true -> e7095:r2946:nil->d505:"std.data.opt.opt.nil"; p1657:false -> e7098:(e7096:r2947:just->d506:"std.data.opt.opt.just" e7097:r2948:acc->d2090:acc) } }))))
      pub d876:"std.text.str.to_int": std::text::str::str -> std::data::opt::opt int = e7160:(fn p1660:d2092:source -> e7159:case e7113:(e7112:r2952:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7111:(e7109:(e7105:r2949:"std::int::eq"->d47:"std.int.eq" e7108:(e7106:r2950:"std::text::str::len"->d788:"std.text.str.len" e7107:r2951:source->d2092:source)) e7110:0)) { p1667:true -> e7114:r2953:nil->d505:"std.data.opt.opt.nil"; p1668:false -> e7158:case e7121:(e7115:r2954:"std::text::char::to_string"->d674:"std.text.char.to_string" e7120:(e7118:(e7116:r2955:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e7117:r2956:source->d2092:source) e7119:0)) { p1661:"-" -> e7139:case e7130:(e7128:(e7126:(e7124:(e7122:r2957:parse_unsigned_int->d875:"std.text.str.parse_unsigned_int" e7123:r2958:source->d2092:source) e7125:1) e7127:1) e7129:0) { p1663:r2959:just->d506:"std.data.opt.opt.just"(p1662:d2093:value) -> e7137:(e7131:r2960:just->d506:"std.data.opt.opt.just" e7136:(e7134:(e7132:r2961:"std::int::sub"->d53:"std.int.sub" e7133:0) e7135:r2962:value->d2093:value)); p1664:r2963:nil->d505:"std.data.opt.opt.nil" -> e7138:r2964:nil->d505:"std.data.opt.opt.nil" }; p1665:"+" -> e7148:(e7146:(e7144:(e7142:(e7140:r2965:parse_unsigned_int->d875:"std.text.str.parse_unsigned_int" e7141:r2966:source->d2092:source) e7143:1) e7145:1) e7147:0); p1666:_ -> e7157:(e7155:(e7153:(e7151:(e7149:r2967:parse_unsigned_int->d875:"std.text.str.parse_unsigned_int" e7150:r2968:source->d2092:source) e7152:0) e7154:0) e7156:0) } })
      pub d877:"std.text.str.replace_once": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e7212:(fn p1669:d2094:source -> e7211:(fn p1670:d2095:from -> e7210:(fn p1671:d2096:to -> e7209:case e7169:(e7168:r2972:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7167:(e7165:(e7161:r2969:"std::int::eq"->d47:"std.int.eq" e7164:(e7162:r2970:"std::text::str::len"->d788:"std.text.str.len" e7163:r2971:from->d2095:from)) e7166:0)) { p1675:true -> e7170:r2973:source->d2094:source; p1676:false -> e7208:case e7177:(e7175:(e7173:(e7171:r2974:find_at->d853:"std.text.str.find_at" e7172:r2975:source->d2094:source) e7174:r2976:from->d2095:from) e7176:0) { p1673:r2977:just->d506:"std.data.opt.opt.just"(p1672:d2097:i) -> e7206:(e7190:(e7178:r2978:"std::text::str::concat"->d786:"std.text.str.concat" e7189:(e7187:(e7179:r2979:"std::text::str::concat"->d786:"std.text.str.concat" e7186:(e7184:(e7182:(e7180:r2980:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e7181:r2981:source->d2094:source) e7183:0) e7185:r2982:i->d2097:i)) e7188:r2983:to->d2096:to)) e7205:(e7201:(e7193:(e7191:r2984:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e7192:r2985:source->d2094:source) e7200:(e7196:(e7194:r2986:"std::int::add"->d52:"std.int.add" e7195:r2987:i->d2097:i) e7199:(e7197:r2988:"std::text::str::len"->d788:"std.text.str.len" e7198:r2989:from->d2095:from))) e7204:(e7202:r2990:"std::text::str::len"->d788:"std.text.str.len" e7203:r2991:source->d2094:source))); p1674:r2992:nil->d505:"std.data.opt.opt.nil" -> e7207:r2993:source->d2094:source } })))
      pub d878:"std.text.str.replace": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e7222:(fn p1677:d2098:source -> e7221:(fn p1678:d2099:from -> e7220:(fn p1679:d2100:to -> e7219:(e7217:(e7215:(e7213:r2994:replace_all->d879:"std.text.str.replace_all" e7214:r2995:source->d2098:source) e7216:r2996:from->d2099:from) e7218:r2997:to->d2100:to))))
      pub d879:"std.text.str.replace_all": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e7292:(fn p1680:d2101:source -> e7291:(fn p1681:d2102:from -> e7290:(fn p1682:d2103:to -> e7289:case e7231:(e7230:r3001:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7229:(e7227:(e7223:r2998:"std::int::eq"->d47:"std.int.eq" e7226:(e7224:r2999:"std::text::str::len"->d788:"std.text.str.len" e7225:r3000:from->d2102:from)) e7228:0)) { p1690:true -> e7232:r3002:source->d2101:source; p1691:false -> e7288:block { let my p1683:d2104:loop = e7282:(fn p1684:d2105:start -> e7281:(fn p1685:d2106:out -> e7280:case e7239:(e7237:(e7235:(e7233:r3003:find_at->d853:"std.text.str.find_at" e7234:r3004:source->d2101:source) e7236:r3005:from->d2102:from) e7238:r3006:start->d2105:start) { p1687:r3007:just->d506:"std.data.opt.opt.just"(p1686:d2107:i) -> e7266:block { let my p1688:d2108:prefix = e7246:(e7244:(e7242:(e7240:r3008:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e7241:r3009:source->d2101:source) e7243:r3010:start->d2105:start) e7245:r3011:i->d2107:i); e7265:(e7255:(e7247:r3012:loop->d2104:loop e7254:(e7250:(e7248:r3013:"std::int::add"->d52:"std.int.add" e7249:r3014:i->d2107:i) e7253:(e7251:r3015:"std::text::str::len"->d788:"std.text.str.len" e7252:r3016:from->d2102:from))) e7264:(e7262:(e7256:r3017:"std::text::str::concat"->d786:"std.text.str.concat" e7261:(e7259:(e7257:r3018:"std::text::str::concat"->d786:"std.text.str.concat" e7258:r3019:out->d2106:out) e7260:r3020:prefix->d2108:prefix)) e7263:r3021:to->d2103:to)) }; p1689:r3022:nil->d505:"std.data.opt.opt.nil" -> e7279:(e7269:(e7267:r3023:"std::text::str::concat"->d786:"std.text.str.concat" e7268:r3024:out->d2106:out) e7278:(e7274:(e7272:(e7270:r3025:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e7271:r3026:source->d2101:source) e7273:r3027:start->d2105:start) e7277:(e7275:r3028:"std::text::str::len"->d788:"std.text.str.len" e7276:r3029:source->d2101:source))) })); e7287:(e7285:(e7283:r3030:loop->d2104:loop e7284:0) e7286:"") } })))
      my d880:"std.text.str.word_prefix_small_scan_limit": int = e7293:512
      pub d881:"std.text.str.word_prefix_at": std::text::str::str -> int -> std::text::str::str = e7387:(fn p1692:d2109:source -> e7386:(fn p1693:d2110:start -> e7385:block { let my p1694:d2111:source_len = e7296:(e7294:r3031:"std::text::str::len"->d788:"std.text.str.len" e7295:r3032:source->d2109:source); e7384:block { let my p1695:d2112:remaining = e7301:(e7300:(e7298:r3034:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e7297:r3033:source_len->d2111:source_len) e7299:r3035:start->d2110:start); e7383:case e7308:(e7307:r3039:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7306:(e7305:(e7303:r3037:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e7302:r3036:remaining->d2112:remaining) e7304:r3038:word_prefix_small_scan_limit->d880:"std.text.str.word_prefix_small_scan_limit")) { p1706:true -> e7354:block { let my p1696:d2113:loop = e7350:(fn p1697:d2114:i -> e7349:case e7315:(e7314:r3043:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7313:(e7312:(e7310:r3041:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e7309:r3040:i->d2114:i) e7311:r3042:source_len->d2111:source_len)) { p1701:true -> e7341:block { let my p1698:d2115:item = e7320:(e7318:(e7316:r3044:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e7317:r3045:source->d2109:source) e7319:r3046:i->d2114:i); e7340:case e7325:(e7324:r3049:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7323:(e7321:r3047:"std::text::char::is_word"->d677:"std.text.char.is_word" e7322:r3048:item->d2115:item)) { p1699:true -> e7332:(e7326:r3050:loop->d2113:loop e7331:(e7330:(e7328:r3052:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7327:r3051:i->d2114:i) e7329:1)); p1700:false -> e7339:(e7337:(e7335:(e7333:r3053:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e7334:r3054:source->d2109:source) e7336:r3055:start->d2110:start) e7338:r3056:i->d2114:i) } }; p1702:false -> e7348:(e7346:(e7344:(e7342:r3057:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e7343:r3058:source->d2109:source) e7345:r3059:start->d2110:start) e7347:r3060:i->d2114:i) }); e7353:(e7351:r3061:loop->d2113:loop e7352:r3062:start->d2110:start) }; p1707:false -> e7382:block { let my p1703:d2116:end = e7374:case e7361:(e7360:r3065:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7359:(e7358:(e7356:r3064:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e7355:r3063:start->d2110:start) e7357:0)) { p1704:true -> e7366:(e7364:(e7362:r3066:word_prefix_ascii_or_slow_end->d882:"std.text.str.word_prefix_ascii_or_slow_end" e7363:r3067:source->d2109:source) e7365:r3068:source_len->d2111:source_len); p1705:false -> e7373:(e7371:(e7369:(e7367:r3069:word_prefix_slow_end->d886:"std.text.str.word_prefix_slow_end" e7368:r3070:source->d2109:source) e7370:r3071:source_len->d2111:source_len) e7372:r3072:start->d2110:start) }; e7381:(e7379:(e7377:(e7375:r3073:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e7376:r3074:source->d2109:source) e7378:r3075:start->d2110:start) e7380:r3076:end->d2116:end) } } } }))
      my d882:"std.text.str.word_prefix_ascii_or_slow_end": std::text::str::str -> int -> int = e7440:(fn p1708:d2117:source -> e7439:(fn p1709:d2118:source_len -> e7438:block { let my p1710:d2119:data = e7390:(e7388:r3077:"std::text::str::to_bytes"->d796:"std.text.str.to_bytes" e7389:r3078:source->d2117:source); e7437:block { let my p1711:d2120:data_len = e7393:(e7391:r3079:"std::text::bytes::len"->d655:"std.text.bytes.len" e7392:r3080:data->d2119:data); e7436:block { let my p1712:d2121:chunk_count = e7402:(e7400:(e7394:r3081:"std::int::div"->d55:"std.int.div" e7399:(e7398:(e7396:r3083:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7395:r3082:data_len->d2120:data_len) e7397:1023)) e7401:1024); e7435:block { let my p1713:d2122:scan = e7424:(e7412:(e7408:(e7407:(e7406:(e7404:r3084:"#op:infix:..<"->d410:"std.core.ops.#op:infix:..<" e7403:0) e7405:r3085:chunk_count->d2121:chunk_count).s285.fold=>d451:"std.data.fold.Fold.fold") e7411:(e7409:0, e7410:0)) e7423:(fn p1714:d2123:state -> e7422:(fn p1715:d2124:chunk -> e7421:(e7419:(e7417:(e7415:(e7413:r3086:word_prefix_ascii_chunk->d883:"std.text.str.word_prefix_ascii_chunk" e7414:r3087:data->d2119:data) e7416:r3088:data_len->d2120:data_len) e7418:r3089:state->d2123:state) e7420:r3090:chunk->d2124:chunk)))); e7434:case e7425:r3091:scan->d2122:scan { p1718:(p1716:d2125:end, p1717:2) -> e7432:(e7430:(e7428:(e7426:r3092:word_prefix_slow_end->d886:"std.text.str.word_prefix_slow_end" e7427:r3093:source->d2117:source) e7429:r3094:source_len->d2118:source_len) e7431:r3095:end->d2125:end); p1721:(p1719:d2126:end, p1720:_) -> e7433:r3096:end->d2126:end } } } } }))
      my d883:"std.text.str.word_prefix_ascii_chunk": std::text::bytes::bytes -> int -> (int, int) -> int -> (int, int) = e7490:(fn p1722:d2127:data -> e7489:(fn p1723:d2128:data_len -> e7488:(fn p1724:d2129:state -> e7487:(fn p1725:d2130:chunk -> e7486:case e7441:r3097:state->d2129:state { p1728:(p1726:_, p1727:0) -> e7484:block { let my p1729:d2131:i = e7446:(e7445:(e7443:r3099:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e7442:r3098:chunk->d2130:chunk) e7444:1024); e7483:block { let my p1730:d2132:chunk_end = e7464:case e7457:(e7456:r3104:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7455:(e7454:(e7452:r3102:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e7451:(e7450:(e7448:r3101:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7447:r3100:i->d2131:i) e7449:1024)) e7453:r3103:data_len->d2128:data_len)) { p1731:true -> e7462:(e7461:(e7459:r3106:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7458:r3105:i->d2131:i) e7460:1024); p1732:false -> e7463:r3107:data_len->d2128:data_len }; e7482:(e7472:(e7470:(e7469:(e7467:(e7465:r3108:"std::data::range::range"->d513:"std.data.range.range" e7466:r3109:i->d2131:i) e7468:r3110:chunk_end->d2132:chunk_end).s286.fold=>d451:"std.data.fold.Fold.fold") e7471:r3111:state->d2129:state) e7481:(fn p1733:d2133:state -> e7480:(fn p1734:d2134:j -> e7479:(e7477:(e7475:(e7473:r3112:word_prefix_ascii_step->d884:"std.text.str.word_prefix_ascii_step" e7474:r3113:data->d2127:data) e7476:r3114:state->d2133:state) e7478:r3115:j->d2134:j)))) } }; p1735:_ -> e7485:r3116:state->d2129:state }))))
      my d884:"std.text.str.word_prefix_ascii_step": std::text::bytes::bytes -> (int, int) -> int -> (int, int) = e7529:(fn p1736:d2135:data -> e7528:(fn p1737:d2136:state -> e7527:(fn p1738:d2137:i -> e7526:case e7491:r3117:state->d2136:state { p1741:(p1739:d2138:end, p1740:0) -> e7524:block { let my p1742:d2139:byte = e7496:(e7494:(e7492:r3118:"std::text::bytes::index_raw"->d658:"std.text.bytes.index_raw" e7493:r3119:data->d2135:data) e7495:r3120:i->d2137:i); e7523:case e7501:(e7500:r3123:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7499:(e7497:r3121:ascii_word_byte->d885:"std.text.str.ascii_word_byte" e7498:r3122:byte->d2139:byte)) { p1745:true -> e7508:(e7506:(e7505:(e7503:r3125:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7502:r3124:i->d2137:i) e7504:1), e7507:0); p1746:false -> e7522:case e7515:(e7514:r3128:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7513:(e7512:(e7510:r3127:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e7509:r3126:byte->d2139:byte) e7511:128)) { p1743:true -> e7518:(e7516:r3129:i->d2137:i, e7517:1); p1744:false -> e7521:(e7519:r3130:i->d2137:i, e7520:2) } } }; p1747:_ -> e7525:r3131:state->d2136:state })))
      my d885:"std.text.str.ascii_word_byte": int -> bool = e7595:(fn p1748:d2140:byte -> e7594:(e7593:(e7575:r3146:"#op:infix:or"->d428:"std.core.ops.#op:infix:or" e7591:(fn p1759:() -> e7574:(e7573:(e7555:r3140:"#op:infix:or"->d428:"std.core.ops.#op:infix:or" e7571:(fn p1755:() -> e7554:(e7553:(e7535:r3134:"#op:infix:or"->d428:"std.core.ops.#op:infix:or" e7551:(fn p1751:() -> e7534:(e7533:(e7531:r3133:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e7530:r3132:byte->d2140:byte) e7532:95))) e7552:(fn p1752:() -> e7550:(e7549:(e7541:r3137:"#op:infix:and"->d427:"std.core.ops.#op:infix:and" e7547:(fn p1749:() -> e7540:(e7539:(e7537:r3135:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e7536:48) e7538:r3136:byte->d2140:byte))) e7548:(fn p1750:() -> e7546:(e7545:(e7543:r3139:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e7542:r3138:byte->d2140:byte) e7544:57))))))) e7572:(fn p1756:() -> e7570:(e7569:(e7561:r3143:"#op:infix:and"->d427:"std.core.ops.#op:infix:and" e7567:(fn p1753:() -> e7560:(e7559:(e7557:r3141:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e7556:65) e7558:r3142:byte->d2140:byte))) e7568:(fn p1754:() -> e7566:(e7565:(e7563:r3145:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e7562:r3144:byte->d2140:byte) e7564:90))))))) e7592:(fn p1760:() -> e7590:(e7589:(e7581:r3149:"#op:infix:and"->d427:"std.core.ops.#op:infix:and" e7587:(fn p1757:() -> e7580:(e7579:(e7577:r3147:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e7576:97) e7578:r3148:byte->d2140:byte))) e7588:(fn p1758:() -> e7586:(e7585:(e7583:r3151:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e7582:r3150:byte->d2140:byte) e7584:122))))))
      my d886:"std.text.str.word_prefix_slow_end": std::text::str::str -> int -> int -> int = e7642:(fn p1761:d2141:source -> e7641:(fn p1762:d2142:source_len -> e7640:(fn p1763:d2143:i -> e7639:block { let my p1764:d2144:count = e7600:(e7599:(e7597:r3153:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e7596:r3152:source_len->d2142:source_len) e7598:r3154:i->d2143:i); e7638:block { let my p1765:d2145:chunk_count = e7609:(e7607:(e7601:r3155:"std::int::div"->d55:"std.int.div" e7606:(e7605:(e7603:r3157:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7602:r3156:count->d2144:count) e7604:1023)) e7608:1024); e7637:block { let my p1766:d2146:scan = e7633:(e7619:(e7615:(e7614:(e7613:(e7611:r3158:"#op:infix:..<"->d410:"std.core.ops.#op:infix:..<" e7610:0) e7612:r3159:chunk_count->d2145:chunk_count).s287.fold=>d451:"std.data.fold.Fold.fold") e7618:(e7616:r3160:i->d2143:i, e7617:true)) e7632:(fn p1767:d2147:state -> e7631:(fn p1768:d2148:chunk -> e7630:(e7628:(e7626:(e7624:(e7622:(e7620:r3161:word_prefix_slow_chunk->d887:"std.text.str.word_prefix_slow_chunk" e7621:r3162:source->d2141:source) e7623:r3163:source_len->d2142:source_len) e7625:r3164:state->d2147:state) e7627:r3165:i->d2143:i) e7629:r3166:chunk->d2148:chunk)))); e7636:case e7634:r3167:scan->d2146:scan { p1771:(p1769:d2149:end, p1770:_) -> e7635:r3168:end->d2149:end } } } })))
      my d887:"std.text.str.word_prefix_slow_chunk": std::text::str::str -> int -> (int, bool) -> int -> int -> (int, bool) = e7697:(fn p1772:d2150:source -> e7696:(fn p1773:d2151:source_len -> e7695:(fn p1774:d2152:state -> e7694:(fn p1775:d2153:start -> e7693:(fn p1776:d2154:chunk -> e7692:case e7643:r3169:state->d2152:state { p1779:(p1777:_, p1778:true) -> e7690:block { let my p1780:d2155:i = e7652:(e7651:(e7645:r3171:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7644:r3170:start->d2153:start) e7650:(e7649:(e7647:r3173:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e7646:r3172:chunk->d2154:chunk) e7648:1024)); e7689:block { let my p1781:d2156:chunk_end = e7670:case e7663:(e7662:r3178:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7661:(e7660:(e7658:r3176:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e7657:(e7656:(e7654:r3175:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7653:r3174:i->d2155:i) e7655:1024)) e7659:r3177:source_len->d2151:source_len)) { p1782:true -> e7668:(e7667:(e7665:r3180:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7664:r3179:i->d2155:i) e7666:1024); p1783:false -> e7669:r3181:source_len->d2151:source_len }; e7688:(e7678:(e7676:(e7675:(e7673:(e7671:r3182:"std::data::range::range"->d513:"std.data.range.range" e7672:r3183:i->d2155:i) e7674:r3184:chunk_end->d2156:chunk_end).s288.fold=>d451:"std.data.fold.Fold.fold") e7677:r3185:state->d2152:state) e7687:(fn p1784:d2157:state -> e7686:(fn p1785:d2158:index -> e7685:(e7683:(e7681:(e7679:r3186:word_prefix_slow_step->d888:"std.text.str.word_prefix_slow_step" e7680:r3187:source->d2150:source) e7682:r3188:state->d2157:state) e7684:r3189:index->d2158:index)))) } }; p1786:_ -> e7691:r3190:state->d2152:state })))))
      my d888:"std.text.str.word_prefix_slow_step": std::text::str::str -> (int, bool) -> int -> (int, bool) = e7723:(fn p1787:d2159:source -> e7722:(fn p1788:d2160:state -> e7721:(fn p1789:d2161:i -> e7720:case e7698:r3191:state->d2160:state { p1792:(p1790:d2162:end, p1791:true) -> e7718:case e7707:(e7706:r3196:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7705:(e7699:r3192:"std::text::char::is_word"->d677:"std.text.char.is_word" e7704:(e7702:(e7700:r3193:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e7701:r3194:source->d2159:source) e7703:r3195:i->d2161:i))) { p1793:true -> e7714:(e7712:(e7711:(e7709:r3198:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7708:r3197:i->d2161:i) e7710:1), e7713:true); p1794:false -> e7717:(e7715:r3199:i->d2161:i, e7716:false) }; p1795:_ -> e7719:r3200:state->d2160:state })))
      my d889 mod {
        d890: std::text::str::str -> int -> std::text::char::char = e7730:(fn p1796:d2163:s -> e7729:(fn p1797:d2164:i -> e7728:(e7726:(e7724:r3201:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e7725:r3202:s->d2163:s) e7727:r3203:i->d2164:i)))
      }
      my d891 mod {
        d892: std::text::str::str -> std::data::range::range -> std::text::str::str = e7737:(fn p1798:d2165:s -> e7736:(fn p1799:d2166:r -> e7735:(e7733:(e7731:r3204:"std::text::str::index_range"->d792:"std.text.str.index_range" e7732:r3205:s->d2165:s) e7734:r3206:r->d2166:r)))
      }
      my d893 mod {
        d894: std::control::var::ref('a & 'b, std::text::str::str) -> std::data::range::range -> std::control::var::ref('b | 'a, 'c | std::text::str::str) = e7781:(fn p1800:d2167:r -> e7780:(fn p1801:d2168:i -> e7779:(e7738:r3207:ref->d237:"std.control.var.ref" e7778:{get: e7747:(fn p1802:() -> e7746:(e7744:(e7739:r3208:"std::text::str::index_range"->d792:"std.text.str.index_range" e7743:(e7741:(e7740:r3209:r->d2167:r.s289.get->d238) e7742:())) e7745:r3210:i->d2168:i)), update_effect: e7777:(fn p1803:() -> e7776:block { let my p1804:d2169:loop = e7769:(fn p1805:d2170:x -> e7768:catch e7748:r3211:x->d2170:x { std::control::var::ref_update::update p1806:d2171:old, p1807:d2172:k -> e7767:block { let my p1808:d2173:new_item = e7755:(e7749:r3212:"ref_update::update"->d236:"std.control.var.ref_update.update" e7754:(e7752:(e7750:r3213:"std::text::str::index_range"->d792:"std.text.str.index_range" e7751:r3214:old->d2171:old) e7753:r3215:i->d2168:i)); e7766:(e7756:r3216:loop->d2169:loop e7765:(e7757:r3217:k->d2172:k e7764:(e7762:(e7760:(e7758:r3218:"std::text::str::splice"->d794:"std.text.str.splice" e7759:r3219:old->d2171:old) e7761:r3220:i->d2168:i) e7763:r3221:new_item->d2173:new_item))) } }); e7775:(e7770:r3222:loop->d2169:loop e7774:(e7772:(e7771:r3223:r->d2167:r.s290.update_effect->d240) e7773:())) })})))
      }
      my d895 mod {
        d896: std::control::var::ref('a & 'b, std::text::str::str) -> int -> std::control::var::ref('b | 'a, 'c | std::text::char::char) = e7837:(fn p1809:d2174:r -> e7836:(fn p1810:d2175:i -> e7835:(e7782:r3224:ref->d237:"std.control.var.ref" e7834:{get: e7791:(fn p1811:() -> e7790:(e7788:(e7783:r3225:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e7787:(e7785:(e7784:r3226:r->d2174:r.s291.get->d238) e7786:())) e7789:r3227:i->d2175:i)), update_effect: e7833:(fn p1812:() -> e7832:block { let my p1813:d2176:loop = e7825:(fn p1814:d2177:x -> e7824:catch e7792:r3228:x->d2177:x { std::control::var::ref_update::update p1815:d2178:old, p1816:d2179:k -> e7823:block { let my p1817:d2180:new_item = e7799:(e7793:r3229:"ref_update::update"->d236:"std.control.var.ref_update.update" e7798:(e7796:(e7794:r3230:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e7795:r3231:old->d2178:old) e7797:r3232:i->d2175:i)); e7822:block { let my p1818:d2181:replacement = e7802:(e7800:r3233:"std::text::char::to_string"->d674:"std.text.char.to_string" e7801:r3234:new_item->d2180:new_item); e7821:(e7803:r3235:loop->d2176:loop e7820:(e7804:r3236:k->d2179:k e7819:(e7817:(e7807:(e7805:r3237:"std::text::str::splice"->d794:"std.text.str.splice" e7806:r3238:old->d2178:old) e7816:(e7810:(e7808:r3239:range->d513:"std.data.range.range" e7809:r3240:i->d2175:i) e7815:(e7814:(e7812:r3242:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7811:r3241:i->d2175:i) e7813:1))) e7818:r3243:replacement->d2181:replacement))) } } }); e7831:(e7826:r3244:loop->d2176:loop e7830:(e7828:(e7827:r3245:r->d2174:r.s292.update_effect->d240) e7829:())) })})))
      }
    }
    pub d118:"std.text.yumark" mod {
      pub d897:"std.text.yumark.yumark_algebra": {nil: () -> 'a, cons: 'a -> 'a -> 'a, text: std::text::str::str -> 'a, paragraph: 'a -> 'a, heading: std::text::str::str -> int -> 'a -> 'a, blank_line: std::text::str::str -> 'a, section_close: std::text::str::str -> 'a -> 'a, list_block: bool -> 'a -> 'a, list_item: std::text::str::str -> 'a -> 'a, list_item_body: 'a -> 'a, code_fence: std::text::str::str -> std::text::str::str -> 'a, quote_block: 'a -> 'a, emphasis: 'a -> 'a, strong: 'a -> 'a} -> std::text::yumark::yumark_algebra 'a = <missing>
      pub d926:"std.text.yumark.html_format": {marker: std::text::str::str} -> std::text::yumark::html_format = <missing>
      pub d929:"std.text.yumark.markdown_format": {marker: std::text::str::str} -> std::text::yumark::markdown_format = <missing>
      pub d932:"std.text.yumark.html_node": {tag: std::text::str::str, body: std::text::str::str} -> std::text::yumark::html_node = <missing>
      pub d937:"std.text.yumark.YumarkFormat" mod {
        d938:"std.text.yumark.YumarkFormat.yumark_algebra": 'a -> () -> std::text::yumark::yumark_algebra 'b where 'a: std::text::yumark::YumarkFormat(repr = 'b) = <missing>
      }
      pub d939:"std.text.yumark.nil": any -> std::text::yumark::yumark_algebra 'a -> 'a = e7843:(fn p1819:d2182:format -> e7842:(fn p1820:d2183:algebra -> e7841:(e7839:(e7838:r3246:algebra->d2183:algebra.s293.nil->d898) e7840:())))
      pub d940:"std.text.yumark.cons": ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7861:(fn p1821:d2184:head -> e7860:(fn p1822:d2185:tail -> e7859:(fn p1823:d2186:format -> e7858:(fn p1824:d2187:algebra -> e7857:(e7851:(e7845:(e7844:r3247:algebra->d2187:algebra.s294.cons->d900) e7850:(e7848:(e7846:r3248:head->d2184:head e7847:r3249:format->d2186:format) e7849:r3250:algebra->d2187:algebra)) e7856:(e7854:(e7852:r3251:tail->d2185:tail e7853:r3252:format->d2186:format) e7855:r3253:algebra->d2187:algebra))))))
      pub d941:"std.text.yumark.text": std::text::str::str -> any -> std::text::yumark::yumark_algebra 'a -> 'a = e7868:(fn p1825:d2188:value -> e7867:(fn p1826:d2189:format -> e7866:(fn p1827:d2190:algebra -> e7865:(e7863:(e7862:r3254:algebra->d2190:algebra.s295.text->d902) e7864:r3255:value->d2188:value))))
      pub d942:"std.text.yumark.paragraph": ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7879:(fn p1828:d2191:children -> e7878:(fn p1829:d2192:format -> e7877:(fn p1830:d2193:algebra -> e7876:(e7870:(e7869:r3256:algebra->d2193:algebra.s296.paragraph->d904) e7875:(e7873:(e7871:r3257:children->d2191:children e7872:r3258:format->d2192:format) e7874:r3259:algebra->d2193:algebra)))))
      pub d943:"std.text.yumark.heading": std::text::str::str -> int -> ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7896:(fn p1831:d2194:marker -> e7895:(fn p1832:d2195:level -> e7894:(fn p1833:d2196:children -> e7893:(fn p1834:d2197:format -> e7892:(fn p1835:d2198:algebra -> e7891:(e7885:(e7883:(e7881:(e7880:r3260:algebra->d2198:algebra.s297.heading->d906) e7882:r3261:marker->d2194:marker) e7884:r3262:level->d2195:level) e7890:(e7888:(e7886:r3263:children->d2196:children e7887:r3264:format->d2197:format) e7889:r3265:algebra->d2198:algebra)))))))
      pub d944:"std.text.yumark.blank_line": std::text::str::str -> any -> std::text::yumark::yumark_algebra 'a -> 'a = e7903:(fn p1836:d2199:marker -> e7902:(fn p1837:d2200:format -> e7901:(fn p1838:d2201:algebra -> e7900:(e7898:(e7897:r3266:algebra->d2201:algebra.s298.blank_line->d908) e7899:r3267:marker->d2199:marker))))
      pub d945:"std.text.yumark.section_close": std::text::str::str -> ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7917:(fn p1839:d2202:marker -> e7916:(fn p1840:d2203:children -> e7915:(fn p1841:d2204:format -> e7914:(fn p1842:d2205:algebra -> e7913:(e7907:(e7905:(e7904:r3268:algebra->d2205:algebra.s299.section_close->d910) e7906:r3269:marker->d2202:marker) e7912:(e7910:(e7908:r3270:children->d2203:children e7909:r3271:format->d2204:format) e7911:r3272:algebra->d2205:algebra))))))
      pub d946:"std.text.yumark.list_block": bool -> ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7931:(fn p1843:d2206:ordered -> e7930:(fn p1844:d2207:items -> e7929:(fn p1845:d2208:format -> e7928:(fn p1846:d2209:algebra -> e7927:(e7921:(e7919:(e7918:r3273:algebra->d2209:algebra.s300.list_block->d912) e7920:r3274:ordered->d2206:ordered) e7926:(e7924:(e7922:r3275:items->d2207:items e7923:r3276:format->d2208:format) e7925:r3277:algebra->d2209:algebra))))))
      pub d947:"std.text.yumark.list_item": std::text::str::str -> ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7945:(fn p1847:d2210:marker -> e7944:(fn p1848:d2211:children -> e7943:(fn p1849:d2212:format -> e7942:(fn p1850:d2213:algebra -> e7941:(e7935:(e7933:(e7932:r3278:algebra->d2213:algebra.s301.list_item->d914) e7934:r3279:marker->d2210:marker) e7940:(e7938:(e7936:r3280:children->d2211:children e7937:r3281:format->d2212:format) e7939:r3282:algebra->d2213:algebra))))))
      pub d948:"std.text.yumark.list_item_body": ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7956:(fn p1851:d2214:children -> e7955:(fn p1852:d2215:format -> e7954:(fn p1853:d2216:algebra -> e7953:(e7947:(e7946:r3283:algebra->d2216:algebra.s302.list_item_body->d916) e7952:(e7950:(e7948:r3284:children->d2214:children e7949:r3285:format->d2215:format) e7951:r3286:algebra->d2216:algebra)))))
      pub d949:"std.text.yumark.code_fence": std::text::str::str -> std::text::str::str -> any -> std::text::yumark::yumark_algebra 'a -> 'a = e7966:(fn p1854:d2217:info -> e7965:(fn p1855:d2218:body -> e7964:(fn p1856:d2219:format -> e7963:(fn p1857:d2220:algebra -> e7962:(e7960:(e7958:(e7957:r3287:algebra->d2220:algebra.s303.code_fence->d918) e7959:r3288:info->d2217:info) e7961:r3289:body->d2218:body)))))
      pub d950:"std.text.yumark.quote_block": ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7977:(fn p1858:d2221:children -> e7976:(fn p1859:d2222:format -> e7975:(fn p1860:d2223:algebra -> e7974:(e7968:(e7967:r3290:algebra->d2223:algebra.s304.quote_block->d920) e7973:(e7971:(e7969:r3291:children->d2221:children e7970:r3292:format->d2222:format) e7972:r3293:algebra->d2223:algebra)))))
      pub d951:"std.text.yumark.emphasis": ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7988:(fn p1861:d2224:children -> e7987:(fn p1862:d2225:format -> e7986:(fn p1863:d2226:algebra -> e7985:(e7979:(e7978:r3294:algebra->d2226:algebra.s305.emphasis->d922) e7984:(e7982:(e7980:r3295:children->d2224:children e7981:r3296:format->d2225:format) e7983:r3297:algebra->d2226:algebra)))))
      pub d952:"std.text.yumark.strong": ('a -> std::text::yumark::yumark_algebra 'b -> 'b) -> 'a -> std::text::yumark::yumark_algebra 'b -> 'b = e7999:(fn p1864:d2227:children -> e7998:(fn p1865:d2228:format -> e7997:(fn p1866:d2229:algebra -> e7996:(e7990:(e7989:r3298:algebra->d2229:algebra.s306.strong->d924) e7995:(e7993:(e7991:r3299:children->d2227:children e7992:r3300:format->d2228:format) e7994:r3301:algebra->d2229:algebra)))))
      pub d953:"std.text.yumark.html_format_value": () -> std::text::yumark::html_format = e8004:(fn p1867:() -> e8003:(e8000:r3302:html_format->d926:"std.text.yumark.html_format" e8002:{marker: e8001:"html"}))
      pub d954:"std.text.yumark.markdown_format_value": () -> std::text::yumark::markdown_format = e8009:(fn p1868:() -> e8008:(e8005:r3303:markdown_format->d929:"std.text.yumark.markdown_format" e8007:{marker: e8006:"markdown"}))
      pub d955:"std.text.yumark.html_tag": std::text::yumark::html_node -> std::text::str::str = e8043:(fn p1869:d2230:node -> e8042:case e8017:(e8016:r3306:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e8015:(e8014:(e8012:r3305:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e8011:(e8010:r3304:node->d2230:node.s307.tag->d933)) e8013:"fragment")) { p1870:true -> e8019:(e8018:r3307:node->d2230:node.s308.body->d935); p1871:false -> e8041:(e8034:(e8032:(e8029:(e8020:r3308:cat4->d991:"std.text.yumark.cat4" e8028:(e8026:(e8023:(e8021:r3309:cat3->d990:"std.text.yumark.cat3" e8022:"<") e8025:(e8024:r3310:node->d2230:node.s309.tag->d933)) e8027:">")) e8031:(e8030:r3311:node->d2230:node.s310.body->d935)) e8033:"</") e8040:(e8038:(e8035:r3312:cat2->d989:"std.text.yumark.cat2" e8037:(e8036:r3313:node->d2230:node.s311.tag->d933)) e8039:">")) })
      pub d956:"std.text.yumark.html_algebra": () -> std::text::yumark::yumark_algebra std::text::yumark::html_node = e8061:(fn p1872:() -> e8060:(e8044:r3314:yumark_algebra->d897:"std.text.yumark.yumark_algebra" e8059:{nil: e8045:r3315:html_nil->d961:"std.text.yumark.html_nil", cons: e8046:r3316:html_cons->d962:"std.text.yumark.html_cons", text: e8047:r3317:html_text->d963:"std.text.yumark.html_text", paragraph: e8048:r3318:html_paragraph->d964:"std.text.yumark.html_paragraph", heading: e8049:r3319:html_heading->d965:"std.text.yumark.html_heading", blank_line: e8050:r3320:html_blank_line->d966:"std.text.yumark.html_blank_line", section_close: e8051:r3321:html_section_close->d967:"std.text.yumark.html_section_close", list_block: e8052:r3322:html_list_block->d968:"std.text.yumark.html_list_block", list_item: e8053:r3323:html_list_item->d969:"std.text.yumark.html_list_item", list_item_body: e8054:r3324:html_list_item_body->d970:"std.text.yumark.html_list_item_body", code_fence: e8055:r3325:html_code_fence->d971:"std.text.yumark.html_code_fence", quote_block: e8056:r3326:html_quote_block->d972:"std.text.yumark.html_quote_block", emphasis: e8057:r3327:html_emphasis->d973:"std.text.yumark.html_emphasis", strong: e8058:r3328:html_strong->d974:"std.text.yumark.html_strong"}))
      pub d957:"std.text.yumark.markdown_algebra": () -> std::text::yumark::yumark_algebra std::text::str::str = e8079:(fn p1873:() -> e8078:(e8062:r3329:yumark_algebra->d897:"std.text.yumark.yumark_algebra" e8077:{nil: e8063:r3330:markdown_nil->d975:"std.text.yumark.markdown_nil", cons: e8064:r3331:markdown_cons->d976:"std.text.yumark.markdown_cons", text: e8065:r3332:markdown_text->d977:"std.text.yumark.markdown_text", paragraph: e8066:r3333:markdown_paragraph->d978:"std.text.yumark.markdown_paragraph", heading: e8067:r3334:markdown_heading->d979:"std.text.yumark.markdown_heading", blank_line: e8068:r3335:markdown_blank_line->d980:"std.text.yumark.markdown_blank_line", section_close: e8069:r3336:markdown_section_close->d981:"std.text.yumark.markdown_section_close", list_block: e8070:r3337:markdown_list_block->d982:"std.text.yumark.markdown_list_block", list_item: e8071:r3338:markdown_list_item->d983:"std.text.yumark.markdown_list_item", list_item_body: e8072:r3339:markdown_list_item_body->d984:"std.text.yumark.markdown_list_item_body", code_fence: e8073:r3340:markdown_code_fence->d985:"std.text.yumark.markdown_code_fence", quote_block: e8074:r3341:markdown_quote_block->d986:"std.text.yumark.markdown_quote_block", emphasis: e8075:r3342:markdown_emphasis->d987:"std.text.yumark.markdown_emphasis", strong: e8076:r3343:markdown_strong->d988:"std.text.yumark.markdown_strong"}))
      pub d958:"std.text.yumark.run_yumark": 'a -> ('a -> ['b] std::text::yumark::yumark_algebra 'c -> ['d] 'e) -> ['d, 'b] 'e where 'a: std::text::yumark::YumarkFormat(repr = 'c) = e8089:(fn p1874:d2231:format -> e8088:(fn p1875:d2232:document -> e8087:(e8082:(e8080:r3344:document->d2232:document e8081:r3345:format->d2231:format) e8086:(e8084:(e8083:r3346:format->d2231:format.s312.yumark_algebra=>d938:"std.text.yumark.YumarkFormat.yumark_algebra") e8085:()))))
      pub d959:"std.text.yumark.render_html_doc": (std::text::yumark::html_format -> ['a] std::text::yumark::yumark_algebra std::text::yumark::html_node -> ['a] std::text::yumark::html_node) -> ['a] std::text::yumark::html_node = e8097:(fn p1876:d2233:document -> e8096:(e8094:(e8090:r3347:run_yumark->d958:"std.text.yumark.run_yumark" e8093:(e8091:r3348:html_format_value->d953:"std.text.yumark.html_format_value" e8092:())) e8095:r3349:document->d2233:document))
      pub d960:"std.text.yumark.render_markdown_doc": (std::text::yumark::markdown_format -> ['a] std::text::yumark::yumark_algebra std::text::str::str -> ['a] std::text::str::str) -> ['a] std::text::str::str = e8105:(fn p1877:d2234:document -> e8104:(e8102:(e8098:r3350:run_yumark->d958:"std.text.yumark.run_yumark" e8101:(e8099:r3351:markdown_format_value->d954:"std.text.yumark.markdown_format_value" e8100:())) e8103:r3352:document->d2234:document))
      my d961:"std.text.yumark.html_nil": () -> std::text::yumark::html_node = e8111:(fn p1878:() -> e8110:(e8106:r3353:html_node->d932:"std.text.yumark.html_node" e8109:{tag: e8107:"fragment", body: e8108:""}))
      my d962:"std.text.yumark.html_cons": std::text::yumark::html_node -> std::text::yumark::html_node -> std::text::yumark::html_node = e8126:(fn p1879:d2235:head -> e8125:(fn p1880:d2236:tail -> e8124:(e8112:r3354:html_node->d932:"std.text.yumark.html_node" e8123:{tag: e8113:"fragment", body: e8122:(e8118:(e8114:r3355:cat2->d989:"std.text.yumark.cat2" e8117:(e8115:r3356:html_tag->d955:"std.text.yumark.html_tag" e8116:r3357:head->d2235:head)) e8121:(e8119:r3358:html_tag->d955:"std.text.yumark.html_tag" e8120:r3359:tail->d2236:tail))})))
      my d963:"std.text.yumark.html_text": std::text::str::str -> std::text::yumark::html_node = e8132:(fn p1881:d2237:value -> e8131:(e8127:r3360:html_node->d932:"std.text.yumark.html_node" e8130:{tag: e8128:"span", body: e8129:r3361:value->d2237:value}))
      my d964:"std.text.yumark.html_paragraph": std::text::yumark::html_node -> std::text::yumark::html_node = e8140:(fn p1882:d2238:children -> e8139:(e8133:r3362:html_node->d932:"std.text.yumark.html_node" e8138:{tag: e8134:"p", body: e8137:(e8135:r3363:html_tag->d955:"std.text.yumark.html_tag" e8136:r3364:children->d2238:children)}))
      my d965:"std.text.yumark.html_heading": std::text::str::str -> int -> std::text::yumark::html_node -> std::text::yumark::html_node = e8156:(fn p1883:d2239:marker -> e8155:(fn p1884:d2240:level -> e8154:(fn p1885:d2241:children -> e8153:(e8141:r3365:html_node->d932:"std.text.yumark.html_node" e8152:{tag: e8148:(e8144:(e8142:r3366:cat2->d989:"std.text.yumark.cat2" e8143:"h") e8147:(e8145:r3367:"std::int::to_string"->d56:"std.int.to_string" e8146:r3368:level->d2240:level)), body: e8151:(e8149:r3369:html_tag->d955:"std.text.yumark.html_tag" e8150:r3370:children->d2241:children)}))))
      my d966:"std.text.yumark.html_blank_line": std::text::str::str -> std::text::yumark::html_node = e8162:(fn p1886:d2242:marker -> e8161:(e8157:r3371:html_node->d932:"std.text.yumark.html_node" e8160:{tag: e8158:"br", body: e8159:r3372:marker->d2242:marker}))
      my d967:"std.text.yumark.html_section_close": std::text::str::str -> std::text::yumark::html_node -> std::text::yumark::html_node = e8175:(fn p1887:d2243:marker -> e8174:(fn p1888:d2244:children -> e8173:(e8163:r3373:html_node->d932:"std.text.yumark.html_node" e8172:{tag: e8164:"section-close", body: e8171:(e8167:(e8165:r3374:cat2->d989:"std.text.yumark.cat2" e8166:r3375:marker->d2243:marker) e8170:(e8168:r3376:html_tag->d955:"std.text.yumark.html_tag" e8169:r3377:children->d2244:children))})))
      my d968:"std.text.yumark.html_list_block": bool -> std::text::yumark::html_node -> std::text::yumark::html_node = e8189:(fn p1889:d2245:ordered -> e8188:(fn p1890:d2246:items -> e8187:(e8176:r3378:html_node->d932:"std.text.yumark.html_node" e8186:{tag: e8182:case e8179:(e8178:r3380:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e8177:r3379:ordered->d2245:ordered) { p1891:true -> e8180:"ol"; p1892:false -> e8181:"ul" }, body: e8185:(e8183:r3381:html_tag->d955:"std.text.yumark.html_tag" e8184:r3382:items->d2246:items)})))
      my d969:"std.text.yumark.html_list_item": std::text::str::str -> std::text::yumark::html_node -> std::text::yumark::html_node = e8198:(fn p1893:d2247:marker -> e8197:(fn p1894:d2248:children -> e8196:(e8190:r3383:html_node->d932:"std.text.yumark.html_node" e8195:{tag: e8191:"li", body: e8194:(e8192:r3384:html_tag->d955:"std.text.yumark.html_tag" e8193:r3385:children->d2248:children)})))
      my d970:"std.text.yumark.html_list_item_body": std::text::yumark::html_node -> std::text::yumark::html_node = e8206:(fn p1895:d2249:children -> e8205:(e8199:r3386:html_node->d932:"std.text.yumark.html_node" e8204:{tag: e8200:"item-body", body: e8203:(e8201:r3387:html_tag->d955:"std.text.yumark.html_tag" e8202:r3388:children->d2249:children)}))
      my d971:"std.text.yumark.html_code_fence": std::text::str::str -> std::text::str::str -> std::text::yumark::html_node = e8233:(fn p1896:d2250:info -> e8232:(fn p1897:d2251:body -> e8231:block { let my p1898:d2252:info_node = e8211:(e8207:r3389:html_node->d932:"std.text.yumark.html_node" e8210:{tag: e8208:"code-info", body: e8209:r3390:info->d2250:info}); e8230:block { let my p1899:d2253:body_node = e8216:(e8212:r3391:html_node->d932:"std.text.yumark.html_node" e8215:{tag: e8213:"code", body: e8214:r3392:body->d2251:body}); e8229:(e8217:r3393:html_node->d932:"std.text.yumark.html_node" e8228:{tag: e8218:"pre", body: e8227:(e8223:(e8219:r3394:cat2->d989:"std.text.yumark.cat2" e8222:(e8220:r3395:html_tag->d955:"std.text.yumark.html_tag" e8221:r3396:info_node->d2252:info_node)) e8226:(e8224:r3397:html_tag->d955:"std.text.yumark.html_tag" e8225:r3398:body_node->d2253:body_node))}) } }))
      my d972:"std.text.yumark.html_quote_block": std::text::yumark::html_node -> std::text::yumark::html_node = e8241:(fn p1900:d2254:children -> e8240:(e8234:r3399:html_node->d932:"std.text.yumark.html_node" e8239:{tag: e8235:"blockquote", body: e8238:(e8236:r3400:html_tag->d955:"std.text.yumark.html_tag" e8237:r3401:children->d2254:children)}))
      my d973:"std.text.yumark.html_emphasis": std::text::yumark::html_node -> std::text::yumark::html_node = e8249:(fn p1901:d2255:children -> e8248:(e8242:r3402:html_node->d932:"std.text.yumark.html_node" e8247:{tag: e8243:"em", body: e8246:(e8244:r3403:html_tag->d955:"std.text.yumark.html_tag" e8245:r3404:children->d2255:children)}))
      my d974:"std.text.yumark.html_strong": std::text::yumark::html_node -> std::text::yumark::html_node = e8257:(fn p1902:d2256:children -> e8256:(e8250:r3405:html_node->d932:"std.text.yumark.html_node" e8255:{tag: e8251:"strong", body: e8254:(e8252:r3406:html_tag->d955:"std.text.yumark.html_tag" e8253:r3407:children->d2256:children)}))
      my d975:"std.text.yumark.markdown_nil": () -> std::text::str::str = e8259:(fn p1903:() -> e8258:"")
      my d976:"std.text.yumark.markdown_cons": std::text::str::str -> std::text::str::str -> std::text::str::str = e8266:(fn p1904:d2257:head -> e8265:(fn p1905:d2258:tail -> e8264:(e8262:(e8260:r3408:cat2->d989:"std.text.yumark.cat2" e8261:r3409:head->d2257:head) e8263:r3410:tail->d2258:tail)))
      my d977:"std.text.yumark.markdown_text": std::text::str::str -> std::text::str::str = e8268:(fn p1906:d2259:value -> e8267:r3411:value->d2259:value)
      my d978:"std.text.yumark.markdown_paragraph": std::text::str::str -> std::text::str::str = e8274:(fn p1907:d2260:children -> e8273:(e8271:(e8269:r3412:cat2->d989:"std.text.yumark.cat2" e8270:r3413:children->d2260:children) e8272:"\n\n"))
      my d979:"std.text.yumark.markdown_heading": std::text::str::str -> int -> std::text::str::str -> std::text::str::str = e8284:(fn p1908:d2261:marker -> e8283:(fn p1909:d2262:level -> e8282:(fn p1910:d2263:children -> e8281:(e8279:(e8277:(e8275:r3414:cat3->d990:"std.text.yumark.cat3" e8276:r3415:marker->d2261:marker) e8278:r3416:children->d2263:children) e8280:"\n\n"))))
      my d980:"std.text.yumark.markdown_blank_line": std::text::str::str -> std::text::str::str = e8286:(fn p1911:d2264:marker -> e8285:r3417:marker->d2264:marker)
      my d981:"std.text.yumark.markdown_section_close": std::text::str::str -> std::text::str::str -> std::text::str::str = e8295:(fn p1912:d2265:marker -> e8294:(fn p1913:d2266:children -> e8293:(e8291:(e8289:(e8287:r3418:cat3->d990:"std.text.yumark.cat3" e8288:r3419:marker->d2265:marker) e8290:r3420:children->d2266:children) e8292:"\n")))
      my d982:"std.text.yumark.markdown_list_block": bool -> std::text::str::str -> std::text::str::str = e8302:(fn p1914:d2267:ordered -> e8301:(fn p1915:d2268:items -> e8300:(e8298:(e8296:r3421:cat2->d989:"std.text.yumark.cat2" e8297:r3422:items->d2268:items) e8299:"\n")))
      my d983:"std.text.yumark.markdown_list_item": std::text::str::str -> std::text::str::str -> std::text::str::str = e8311:(fn p1916:d2269:marker -> e8310:(fn p1917:d2270:children -> e8309:(e8307:(e8305:(e8303:r3423:cat3->d990:"std.text.yumark.cat3" e8304:r3424:marker->d2269:marker) e8306:r3425:children->d2270:children) e8308:"\n")))
      my d984:"std.text.yumark.markdown_list_item_body": std::text::str::str -> std::text::str::str = e8313:(fn p1918:d2271:children -> e8312:r3426:children->d2271:children)
      my d985:"std.text.yumark.markdown_code_fence": std::text::str::str -> std::text::str::str -> std::text::str::str = e8328:(fn p1919:d2272:info -> e8327:(fn p1920:d2273:body -> e8326:(e8324:(e8314:r3427:cat2->d989:"std.text.yumark.cat2" e8323:(e8321:(e8319:(e8317:(e8315:r3428:cat4->d991:"std.text.yumark.cat4" e8316:"```") e8318:r3429:info->d2272:info) e8320:"\n") e8322:r3430:body->d2273:body)) e8325:"\n```\n\n")))
      my d986:"std.text.yumark.markdown_quote_block": std::text::str::str -> std::text::str::str = e8336:(fn p1921:d2274:children -> e8335:(e8333:(e8331:(e8329:r3431:cat3->d990:"std.text.yumark.cat3" e8330:"> ") e8332:r3432:children->d2274:children) e8334:"\n"))
      my d987:"std.text.yumark.markdown_emphasis": std::text::str::str -> std::text::str::str = e8344:(fn p1922:d2275:children -> e8343:(e8341:(e8339:(e8337:r3433:cat3->d990:"std.text.yumark.cat3" e8338:"*") e8340:r3434:children->d2275:children) e8342:"*"))
      my d988:"std.text.yumark.markdown_strong": std::text::str::str -> std::text::str::str = e8352:(fn p1923:d2276:children -> e8351:(e8349:(e8347:(e8345:r3435:cat3->d990:"std.text.yumark.cat3" e8346:"**") e8348:r3436:children->d2276:children) e8350:"**"))
      my d989:"std.text.yumark.cat2": std::text::str::str -> std::text::str::str -> std::text::str::str = e8359:(fn p1924:d2277:left -> e8358:(fn p1925:d2278:right -> e8357:(e8355:(e8353:r3437:"std::text::str::concat"->d786:"std.text.str.concat" e8354:r3438:left->d2277:left) e8356:r3439:right->d2278:right)))
      my d990:"std.text.yumark.cat3": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e8371:(fn p1926:d2279:a -> e8370:(fn p1927:d2280:b -> e8369:(fn p1928:d2281:c -> e8368:(e8366:(e8360:r3440:cat2->d989:"std.text.yumark.cat2" e8365:(e8363:(e8361:r3441:cat2->d989:"std.text.yumark.cat2" e8362:r3442:a->d2279:a) e8364:r3443:b->d2280:b)) e8367:r3444:c->d2281:c))))
      my d991:"std.text.yumark.cat4": std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str -> std::text::str::str = e8386:(fn p1929:d2282:a -> e8385:(fn p1930:d2283:b -> e8384:(fn p1931:d2284:c -> e8383:(fn p1932:d2285:d -> e8382:(e8380:(e8372:r3445:cat2->d989:"std.text.yumark.cat2" e8379:(e8377:(e8375:(e8373:r3446:cat3->d990:"std.text.yumark.cat3" e8374:r3447:a->d2282:a) e8376:r3448:b->d2283:b) e8378:r3449:c->d2284:c)) e8381:r3450:d->d2285:d)))))
      my d992 mod {
        d993: std::text::yumark::html_format -> () -> std::text::yumark::yumark_algebra std::text::yumark::html_node = e8391:(fn p1933:d2286:format -> e8390:(fn p1934:_ -> e8389:(e8387:r3451:html_algebra->d956:"std.text.yumark.html_algebra" e8388:())))
      }
      my d994 mod {
        d995: std::text::yumark::markdown_format -> () -> std::text::yumark::yumark_algebra std::text::str::str = e8396:(fn p1935:d2287:format -> e8395:(fn p1936:_ -> e8394:(e8392:r3452:markdown_algebra->d957:"std.text.yumark.markdown_algebra" e8393:())))
      }
    }
  }
  pub d10:"std.control" mod {
    pub d18:"std.control.flow" mod {
      pub d173:"std.control.flow.sub" mod {
        pub d175:"std.control.flow.sub.sub": 'a [std::control::flow::sub('b & 'a); 'c] -> ['c] 'a | 'b = e932:(fn p145:d1133:x -> e931:catch e928:r346:x->d1133:x { std::control::flow::sub::return p146:d1134:a, p147:_ -> e929:r347:a->d1134:a; p148:d1135:a -> e930:r348:a->d1135:a })
      }
      pub d176:"std.control.flow.label_sub" mod {
        pub d178:"std.control.flow.label_sub.label": {marker: ()} -> std::control::flow::label_sub::label = <missing>
        d181:"std.control.flow.label_sub.control_label": std::control::flow::label_sub::label = e936:(e933:r349:label->d178:"std.control.flow.label_sub.label" e935:{marker: e934:()})
        pub d182:"std.control.flow.label_sub.sub": 'a [std::control::flow::label_sub('b & 'a & 'c), std::control::flow::sub('c & 'a & 'b); 'd] -> ['d] 'a | 'b | 'c = e942:(fn p149:d1136:x -> e941:catch e937:r350:x->d1136:x { std::control::flow::label_sub::return p150:d1137:a, p151:_ -> e938:r351:a->d1137:a; std::control::flow::sub::return p152:d1138:a, p153:_ -> e939:r352:a->d1138:a; p154:d1139:a -> e940:r353:a->d1139:a })
      }
      pub d183:"std.control.flow.loop" mod {
        my d187:"std.control.flow.loop.last" mod {
          d189:"std.control.flow.loop.last.judge": any [std::control::flow::loop::last; 'a] -> ['a] bool = e947:(fn p155:d1140:x -> e946:catch e943:r354:x->d1140:x { std::control::flow::loop::last::break p156:_, p157:_ -> e944:true; p158:_ -> e945:false })
          d190:"std.control.flow.loop.last.sub": any [std::control::flow::loop::last; 'a] -> ['a] () = e952:(fn p159:d1141:x -> e951:catch e948:r355:x->d1141:x { std::control::flow::loop::last::break p160:_, p161:_ -> e949:(); p162:_ -> e950:() })
        }
        pub d191:"std.control.flow.loop.for_in": 'a -> ('b -> [std::control::flow::loop; 'c] any) -> ['c] () where 'a: std::data::fold::Fold(item = 'b) = e1025:(fn p179:d1146:xs -> e1024:(fn p180:d1147:f -> e1023:(e973:r360:"last::sub"->d190:"std.control.flow.loop.last.sub" e1022:(e977:(e975:(e974:r361:xs->d1146:xs.s36.fold=>d451:"std.data.fold.Fold.fold") e976:()) e1021:(fn p181:() -> e1020:(fn p182:d1148:x -> e1019:(e978:r362:"next::sub"->d1007:"std.control.flow.loop.next.sub" e1018:block { e1014:block { let my p183:d1149:loop = e1012:(fn p184:d1150:b -> e1011:case e981:(e980:r364:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e979:r363:b->d1150:b) { p197:true -> e1009:block { e1007:(e982:r365:loop->d1149:loop e1006:(e983:r366:"redo::judge"->d998:"std.control.flow.loop.redo.judge" e1005:catch e986:(e984:r367:f->d1147:f e985:r368:x->d1148:x) { std::control::flow::loop::last p185:_, p186:_ -> e989:(e987:r369:"last::break"->d188:"std.control.flow.loop.last.break" e988:()); std::control::flow::loop::next p187:_, p188:_ -> e992:(e990:r370:"next::break"->d1005:"std.control.flow.loop.next.break" e991:()); std::control::flow::loop::redo p189:_, p190:_ -> e995:(e993:r371:"redo::break"->d997:"std.control.flow.loop.redo.break" e994:()); std::control::flow::loop::last p191:_, p192:_ -> e998:(e996:r372:"last::break"->d188:"std.control.flow.loop.last.break" e997:()); std::control::flow::loop::next p193:_, p194:_ -> e1001:(e999:r373:"next::break"->d1005:"std.control.flow.loop.next.break" e1000:()); std::control::flow::loop::redo p195:_, p196:_ -> e1004:(e1002:r374:"redo::break"->d997:"std.control.flow.loop.redo.break" e1003:()) })); e1008:() }; p198:false -> e1010:() }); e1013:() }; e1017:(e1015:r375:loop->d1149:loop e1016:true) })))))))
        my d996:"std.control.flow.loop.redo" mod {
          d998:"std.control.flow.loop.redo.judge": any [std::control::flow::loop::redo; 'a] -> ['a] bool = e967:(fn p171:d1144:x -> e966:catch e963:r358:x->d1144:x { std::control::flow::loop::redo::break p172:_, p173:_ -> e964:true; p174:_ -> e965:false })
          d999:"std.control.flow.loop.redo.sub": any [std::control::flow::loop::redo; 'a] -> ['a] () = e972:(fn p175:d1145:x -> e971:catch e968:r359:x->d1145:x { std::control::flow::loop::redo::break p176:_, p177:_ -> e969:(); p178:_ -> e970:() })
        }
        my d1004:"std.control.flow.loop.next" mod {
          d1006:"std.control.flow.loop.next.judge": any [std::control::flow::loop::next; 'a] -> ['a] bool = e957:(fn p163:d1142:x -> e956:catch e953:r356:x->d1142:x { std::control::flow::loop::next::break p164:_, p165:_ -> e954:true; p166:_ -> e955:false })
          d1007:"std.control.flow.loop.next.sub": any [std::control::flow::loop::next; 'a] -> ['a] () = e962:(fn p167:d1143:x -> e961:catch e958:r357:x->d1143:x { std::control::flow::loop::next::break p168:_, p169:_ -> e959:(); p170:_ -> e960:() })
        }
      }
      pub d192:"std.control.flow.LoopLabel" mod {
        pub d193:"std.control.flow.LoopLabel.last": 'a -> () -> never where 'a: std::control::flow::LoopLabel = <missing>
        pub d194:"std.control.flow.LoopLabel.next": 'a -> () -> never where 'a: std::control::flow::LoopLabel = <missing>
        pub d195:"std.control.flow.LoopLabel.redo": 'a -> () -> never where 'a: std::control::flow::LoopLabel = <missing>
      }
      pub d196:"std.control.flow.label_loop" mod {
        pub d200:"std.control.flow.label_loop.label": {last: () -> [std::control::flow::label_loop] never, next: () -> [std::control::flow::label_loop] never, redo: () -> [std::control::flow::label_loop] never} -> std::control::flow::label_loop::label = <missing>
        my d207:"std.control.flow.label_loop.last" mod {
          d209:"std.control.flow.label_loop.last.judge": any [std::control::flow::label_loop::last; 'a] -> ['a] bool = e1030:(fn p199:d1151:x -> e1029:catch e1026:r376:x->d1151:x { std::control::flow::label_loop::last::break p200:_, p201:_ -> e1027:true; p202:_ -> e1028:false })
          d210:"std.control.flow.label_loop.last.sub": any [std::control::flow::label_loop::last; 'a] -> ['a] () = e1035:(fn p203:d1152:x -> e1034:catch e1031:r377:x->d1152:x { std::control::flow::label_loop::last::break p204:_, p205:_ -> e1032:(); p206:_ -> e1033:() })
        }
        my d211:"std.control.flow.label_loop.control_label": std::control::flow::label_loop::label = e1061:(e1056:r382:"label_loop::label"->d200:"std.control.flow.label_loop.label" e1060:{last: e1057:r383:"label_loop::last"->d197:"std.control.flow.label_loop.last", next: e1058:r384:"label_loop::next"->d198:"std.control.flow.label_loop.next", redo: e1059:r385:"label_loop::redo"->d199:"std.control.flow.label_loop.redo"})
        pub d212:"std.control.flow.label_loop.for_in": 'a -> (std::control::flow::label_loop::label -> 'b -> [std::control::flow::label_loop, std::control::flow::loop; 'c] any) -> ['c] () where 'a: std::data::fold::Fold(item = 'b) = e1116:(fn p223:d1157:xs -> e1115:(fn p224:d1158:f -> e1114:(e1062:r386:"last::sub"->d210:"std.control.flow.label_loop.last.sub" e1113:(e1066:(e1064:(e1063:r387:xs->d1157:xs.s37.fold=>d451:"std.data.fold.Fold.fold") e1065:()) e1112:(fn p225:() -> e1111:(fn p226:d1159:x -> e1110:(e1067:r388:"next::sub"->d1003:"std.control.flow.label_loop.next.sub" e1109:block { e1105:block { let my p227:d1160:loop = e1103:(fn p228:d1161:b -> e1102:case e1070:(e1069:r390:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1068:r389:b->d1161:b) { p241:true -> e1100:block { e1098:(e1071:r391:loop->d1160:loop e1097:(e1072:r392:"redo::judge"->d1010:"std.control.flow.label_loop.redo.judge" e1096:catch e1077:(e1075:(e1073:r393:f->d1158:f e1074:r394:control_label->d211:"std.control.flow.label_loop.control_label") e1076:r395:x->d1159:x) { std::control::flow::label_loop::last p229:_, p230:_ -> e1080:(e1078:r396:"last::break"->d208:"std.control.flow.label_loop.last.break" e1079:()); std::control::flow::label_loop::next p231:_, p232:_ -> e1083:(e1081:r397:"next::break"->d1001:"std.control.flow.label_loop.next.break" e1082:()); std::control::flow::label_loop::redo p233:_, p234:_ -> e1086:(e1084:r398:"redo::break"->d1009:"std.control.flow.label_loop.redo.break" e1085:()); std::control::flow::loop::last p235:_, p236:_ -> e1089:(e1087:r399:"last::break"->d208:"std.control.flow.label_loop.last.break" e1088:()); std::control::flow::loop::next p237:_, p238:_ -> e1092:(e1090:r400:"next::break"->d1001:"std.control.flow.label_loop.next.break" e1091:()); std::control::flow::loop::redo p239:_, p240:_ -> e1095:(e1093:r401:"redo::break"->d1009:"std.control.flow.label_loop.redo.break" e1094:()) })); e1099:() }; p242:false -> e1101:() }); e1104:() }; e1108:(e1106:r402:loop->d1160:loop e1107:true) })))))))
        my d1000:"std.control.flow.label_loop.next" mod {
          d1002:"std.control.flow.label_loop.next.judge": any [std::control::flow::label_loop::next; 'a] -> ['a] bool = e1040:(fn p207:d1153:x -> e1039:catch e1036:r378:x->d1153:x { std::control::flow::label_loop::next::break p208:_, p209:_ -> e1037:true; p210:_ -> e1038:false })
          d1003:"std.control.flow.label_loop.next.sub": any [std::control::flow::label_loop::next; 'a] -> ['a] () = e1045:(fn p211:d1154:x -> e1044:catch e1041:r379:x->d1154:x { std::control::flow::label_loop::next::break p212:_, p213:_ -> e1042:(); p214:_ -> e1043:() })
        }
        my d1008:"std.control.flow.label_loop.redo" mod {
          d1010:"std.control.flow.label_loop.redo.judge": any [std::control::flow::label_loop::redo; 'a] -> ['a] bool = e1050:(fn p215:d1155:x -> e1049:catch e1046:r380:x->d1155:x { std::control::flow::label_loop::redo::break p216:_, p217:_ -> e1047:true; p218:_ -> e1048:false })
          d1011:"std.control.flow.label_loop.redo.sub": any [std::control::flow::label_loop::redo; 'a] -> ['a] () = e1055:(fn p219:d1156:x -> e1054:catch e1051:r381:x->d1156:x { std::control::flow::label_loop::redo::break p220:_, p221:_ -> e1052:(); p222:_ -> e1053:() })
        }
      }
    }
    pub d19:"std.control.junction" mod {
      pub d213:"std.control.junction.junction" mod {
        pub d217:"std.control.junction.junction.any": 'a -> [std::control::junction::junction] 'b where 'a: std::data::fold::Fold(item = 'b) = e1138:(fn p243:d1162:xs -> e1137:(e1117:r403:"sub::sub"->d175:"std.control.flow.sub.sub" e1136:block { e1132:(e1121:(e1119:(e1118:r404:xs->d1162:xs.s38.fold=>d451:"std.data.fold.Fold.fold") e1120:()) e1131:(fn p244:() -> e1130:(fn p245:d1163:x -> e1129:case e1124:(e1122:r405:or->d214:"std.control.junction.junction.or" e1123:()) { p246:true -> e1127:(e1125:r406:"sub::return"->d174:"std.control.flow.sub.return" e1126:r407:x->d1163:x); p247:false -> e1128:() }))); e1135:(e1133:r408:ret->d216:"std.control.junction.junction.ret" e1134:false) }))
        pub d218:"std.control.junction.junction.all": 'a -> [std::control::junction::junction] 'b where 'a: std::data::fold::Fold(item = 'b) = e1160:(fn p248:d1164:xs -> e1159:(e1139:r409:"sub::sub"->d175:"std.control.flow.sub.sub" e1158:block { e1154:(e1143:(e1141:(e1140:r410:xs->d1164:xs.s39.fold=>d451:"std.data.fold.Fold.fold") e1142:()) e1153:(fn p249:() -> e1152:(fn p250:d1165:x -> e1151:case e1146:(e1144:r411:and->d215:"std.control.junction.junction.and" e1145:()) { p251:true -> e1149:(e1147:r412:"sub::return"->d174:"std.control.flow.sub.return" e1148:r413:x->d1165:x); p252:false -> e1150:() }))); e1157:(e1155:r414:ret->d216:"std.control.junction.junction.ret" e1156:true) }))
        pub d219:"std.control.junction.junction.junction": bool [std::control::junction::junction; 'a] -> ['a] bool = e1188:(fn p253:d1166:x -> e1187:catch e1161:r415:x->d1166:x { std::control::junction::junction::or p254:_, p255:d1167:k -> e1173:case e1166:(e1162:r416:junction->d219:"std.control.junction.junction.junction" e1165:(e1163:r417:k->d1167:k e1164:true)) { p256:true -> e1167:true; p257:_ -> e1172:(e1168:r418:junction->d219:"std.control.junction.junction.junction" e1171:(e1169:r419:k->d1167:k e1170:false)) }; std::control::junction::junction::and p258:_, p259:d1168:k -> e1185:case e1178:(e1174:r420:junction->d219:"std.control.junction.junction.junction" e1177:(e1175:r421:k->d1168:k e1176:true)) { p260:true -> e1183:(e1179:r422:junction->d219:"std.control.junction.junction.junction" e1182:(e1180:r423:k->d1168:k e1181:false)); p261:_ -> e1184:false }; std::control::junction::junction::ret p262:d1169:b, p263:_ -> e1186:r424:b->d1169:b })
      }
      pub d220:"std.control.junction.any": 'a -> [std::control::junction::junction] 'b where 'a: std::data::fold::Fold(item = 'b) = e1192:(fn p264:d1170:xs -> e1191:(e1189:r425:"junction::any"->d217:"std.control.junction.junction.any" e1190:r426:xs->d1170:xs))
      pub d221:"std.control.junction.all": 'a -> [std::control::junction::junction] 'b where 'a: std::data::fold::Fold(item = 'b) = e1196:(fn p265:d1171:xs -> e1195:(e1193:r427:"junction::all"->d218:"std.control.junction.junction.all" e1194:r428:xs->d1171:xs))
    }
    pub d20:"std.control.throw" mod {
      pub d233:"std.control.throw.Throw" mod {
        pub d234:"std.control.throw.Throw.throw": 'a -> ['b] never where 'a: std::control::throw::Throw(throws = 'b) = <missing>
      }
    }
    pub d21:"std.control.nondet" mod {
      pub d222:"std.control.nondet.nondet" mod {
        pub d225:"std.control.nondet.nondet.guard": bool -> [std::control::nondet::nondet] () = e1205:(fn p266:d1172:b -> e1204:case e1199:(e1198:r430:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1197:r429:b->d1172:b) { p267:true -> e1200:(); p268:false -> e1203:(e1201:r431:reject->d224:"std.control.nondet.nondet.reject" e1202:()) })
        pub d226:"std.control.nondet.nondet.each": 'a -> [std::control::nondet::nondet] 'b where 'a: std::data::fold::Fold(item = 'b) = e1229:(fn p269:d1173:xs -> e1228:(e1206:r432:"sub::sub"->d175:"std.control.flow.sub.sub" e1227:block { e1223:(e1210:(e1208:(e1207:r433:xs->d1173:xs.s40.fold=>d451:"std.data.fold.Fold.fold") e1209:()) e1222:(fn p270:() -> e1221:(fn p271:d1174:x -> e1220:case e1215:(e1214:r435:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1213:(e1211:r434:branch->d223:"std.control.nondet.nondet.branch" e1212:())) { p272:true -> e1218:(e1216:r436:"sub::return"->d174:"std.control.flow.sub.return" e1217:r437:x->d1174:x); p273:false -> e1219:() }))); e1226:(e1224:r438:reject->d224:"std.control.nondet.nondet.reject" e1225:()) }))
        pub d227:"std.control.nondet.nondet.#act-method:list:227": 'a [std::control::nondet::nondet; 'b] -> ['b] std::data::list::list 'a = e1249:(fn p274:d1175:x -> e1248:catch e1230:r439:x->d1175:x { std::control::nondet::nondet::branch p275:_, p276:d1176:k -> e1241:(e1236:(e1231:r440:"std::data::list::merge"->d480:"std.data.list.merge" e1235:(e1234:(e1232:r441:k->d1176:k e1233:true).s41.list->d227:"std.control.nondet.nondet.#act-method:list:227")) e1240:(e1239:(e1237:r442:k->d1176:k e1238:false).s42.list->d227:"std.control.nondet.nondet.#act-method:list:227")); std::control::nondet::nondet::reject p277:_, p278:_ -> e1244:(e1242:builtin_op::list_empty e1243:()); p279:d1177:v -> e1247:(e1246:builtin_op::list_singleton e1245:r443:v->d1177:v) })
        pub d228:"std.control.nondet.nondet.logic": any [std::control::nondet::nondet; 'a] -> ['a] std::data::list::list 'b = e1324:(fn p280:d1178:x -> e1323:block { e1311:block { let my p281:d1179:loop = e1309:(fn p282:d1180:x -> e1308:(fn p283:d1181:queue -> e1307:(fn p284:d1182:res -> e1306:catch e1250:r444:x->d1180:x { std::control::nondet::nondet::branch p285:_, p286:d1183:k -> e1265:(e1263:(e1255:(e1251:r445:loop->d1179:loop e1254:(e1252:r446:k->d1183:k e1253:true)) e1262:(e1258:(e1256:r447:"std::data::list::append"->d499:"std.data.list.append" e1257:r448:queue->d1181:queue) e1261:(e1260:builtin_op::list_singleton e1259:r449:k->d1183:k))) e1264:r450:res->d1182:res); std::control::nondet::nondet::reject p287:_, p288:_ -> e1279:case e1268:(e1266:r451:"std::data::list::uncons"->d494:"std.data.list.uncons" e1267:r452:queue->d1181:queue) { p289:r453:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil" -> e1269:r454:res->d1182:res; p293:r455:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just"(p292:(p290:d1184:k, p291:d1185:queue)) -> e1278:(e1276:(e1274:(e1270:r456:loop->d1179:loop e1273:(e1271:r457:k->d1184:k e1272:false)) e1275:r458:queue->d1185:queue) e1277:r459:res->d1182:res) }; p294:d1186:v -> e1305:case e1282:(e1280:r460:"std::data::list::uncons"->d494:"std.data.list.uncons" e1281:r461:queue->d1181:queue) { p295:r462:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil" -> e1289:(e1285:(e1283:r463:"std::data::list::append"->d499:"std.data.list.append" e1284:r464:res->d1182:res) e1288:(e1287:builtin_op::list_singleton e1286:r465:v->d1186:v)); p299:r466:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just"(p298:(p296:d1187:k, p297:d1188:queue)) -> e1304:(e1296:(e1294:(e1290:r467:loop->d1179:loop e1293:(e1291:r468:k->d1187:k e1292:false)) e1295:r469:queue->d1188:queue) e1303:(e1299:(e1297:r470:"std::data::list::append"->d499:"std.data.list.append" e1298:r471:res->d1182:res) e1302:(e1301:builtin_op::list_singleton e1300:r472:v->d1186:v))) } }))); e1310:() }; e1322:(e1318:(e1314:(e1312:r473:loop->d1179:loop e1313:r474:x->d1178:x) e1317:(e1315:builtin_op::list_empty e1316:())) e1321:(e1319:builtin_op::list_empty e1320:())) })
        pub d229:"std.control.nondet.nondet.once": 'a [std::control::nondet::nondet; 'b] -> ['b] std::data::opt::opt 'a = e1367:(fn p300:d1189:x -> e1366:block { e1358:block { let my p301:d1190:loop = e1356:(fn p302:d1191:x -> e1355:(fn p303:d1192:queue -> e1354:catch e1325:r475:x->d1191:x { std::control::nondet::nondet::branch p304:_, p305:d1193:k -> e1338:(e1330:(e1326:r476:loop->d1190:loop e1329:(e1327:r477:k->d1193:k e1328:true)) e1337:(e1333:(e1331:r478:"std::data::list::append"->d499:"std.data.list.append" e1332:r479:queue->d1192:queue) e1336:(e1335:builtin_op::list_singleton e1334:r480:k->d1193:k))); std::control::nondet::nondet::reject p306:_, p307:_ -> e1350:case e1341:(e1339:r481:"std::data::list::uncons"->d494:"std.data.list.uncons" e1340:r482:queue->d1192:queue) { p308:r483:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil" -> e1342:r484:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil"; p312:r485:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just"(p311:(p309:d1194:k, p310:d1195:queue)) -> e1349:(e1347:(e1343:r486:loop->d1190:loop e1346:(e1344:r487:k->d1194:k e1345:false)) e1348:r488:queue->d1195:queue) }; p313:d1196:v -> e1353:(e1351:r489:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just" e1352:r490:v->d1196:v) })); e1357:() }; e1365:(e1361:(e1359:r491:loop->d1190:loop e1360:r492:x->d1189:x) e1364:(e1362:builtin_op::list_empty e1363:())) })
        pub d230:"std.control.nondet.nondet.#act-method:logic:230": any [std::control::nondet::nondet; 'a] -> ['a] std::data::list::list 'b = e1371:(fn p314:d1197:x -> e1370:(e1368:r493:logic->d228:"std.control.nondet.nondet.logic" e1369:r494:x->d1197:x))
        pub d231:"std.control.nondet.nondet.#act-method:once:231": 'a [std::control::nondet::nondet; 'b] -> ['b] std::data::opt::opt 'a = e1375:(fn p315:d1198:x -> e1374:(e1372:r495:once->d229:"std.control.nondet.nondet.once" e1373:r496:x->d1198:x))
        pub d232:"std.control.nondet.nondet.#act-method:guard:232": 'a ['b] -> ('a ['b] -> ['c] bool) -> [std::control::nondet::nondet, 'b, 'c] 'a = e1384:(fn p316:d1199:x -> e1383:(fn p317:d1200:f -> e1382:block { e1380:(e1376:r497:guard->d225:"std.control.nondet.nondet.guard" e1379:(e1377:r498:f->d1200:f e1378:r499:x->d1199:x)); e1381:r500:x->d1199:x }))
      }
    }
    pub d22:"std.control.var" mod {
      pub d235:"std.control.var.ref_update" mod {
      }
      pub d237:"std.control.var.ref": {get: () -> ['a] 'b, update_effect: () -> [std::control::var::ref_update 'b; 'c] ()} -> std::control::var::ref('a | 'c, 'b) = <missing>
      pub d242:"std.control.var.ref" mod {
        pub d243:"std.control.var.ref.update": std::control::var::ref('a & 'b, 'c) -> ('c -> ['b] 'c) -> ['b, 'a] () = e1403:(fn p318:d1201:r -> e1402:(fn p319:d1202:f -> e1401:block { let my p320:d1203:loop = e1394:(fn p321:d1204:x -> e1393:catch e1385:r501:x->d1204:x { std::control::var::ref_update::update p322:d1205:v, p323:d1206:k -> e1392:(e1386:r502:loop->d1203:loop e1391:(e1387:r503:k->d1206:k e1390:(e1388:r504:f->d1202:f e1389:r505:v->d1205:v))) }); e1400:(e1395:r506:loop->d1203:loop e1399:(e1397:(e1396:r507:r->d1201:r.s43.update_effect->d240) e1398:())) }))
      }
      pub d244:"std.control.var.var" mod {
        my d247:"std.control.var.var.var_ref": () -> std::control::var::ref '[std::control::var::var 'a] 'a = e1419:(fn p324:() -> e1418:(e1404:r508:ref->d237:"std.control.var.ref" e1417:{get: e1408:(fn p325:() -> e1407:(e1405:r509:get->d245:"std.control.var.var.get" e1406:())), update_effect: e1416:(fn p326:() -> e1415:(e1409:r510:set->d246:"std.control.var.var.set" e1414:(e1410:r511:"ref_update::update"->d236:"std.control.var.ref_update.update" e1413:(e1411:r512:get->d245:"std.control.var.var.get" e1412:()))))}))
        my d248:"std.control.var.var.run": 'a -> 'b [std::control::var::var 'a; 'c] -> ['c] 'b = e1437:(fn p327:d1207:v -> e1436:(fn p328:d1208:x -> e1435:catch e1420:r513:x->d1208:x { std::control::var::var::get p329:_, p330:d1209:k -> e1427:(e1423:(e1421:r514:run->d248:"std.control.var.var.run" e1422:r515:v->d1207:v) e1426:(e1424:r516:k->d1209:k e1425:r517:v->d1207:v)); std::control::var::var::set p331:d1210:v, p332:d1211:k -> e1434:(e1430:(e1428:r518:run->d248:"std.control.var.var.run" e1429:r519:v->d1210:v) e1433:(e1431:r520:k->d1211:k e1432:())) }))
      }
    }
  }
  pub d11:"std.io" mod {
    pub d59:"std.io.console" mod {
      pub d539:"std.io.console.out" mod {
      }
      pub d541:"std.io.console.print": std::text::str::str -> [std::io::console::out] () = e3323:(fn p822:d1552:value -> e3322:(e3320:r1337:"out::write"->d540:"std.io.console.out.write" e3321:r1338:value->d1552:value))
      pub d542:"std.io.console.say": 'a -> [std::io::console::out] () where 'a: std::core::fmt::Display = e3332:(fn p823:d1553:value -> e3331:(e3324:r1339:"out::write"->d540:"std.io.console.out.write" e3330:(e3329:(e3327:r1341:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3326:(e3325:r1340:value->d1553:value.s126.show=>d321:"std.core.fmt.Display.show")) e3328:"\n")))
      pub d543:"std.io.console.println": std::text::str::str -> [std::io::console::out] () = e3340:(fn p824:d1554:value -> e3339:(e3333:r1342:"out::write"->d540:"std.io.console.out.write" e3338:(e3337:(e3335:r1344:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3334:r1343:value->d1554:value) e3336:"\n")))
      pub d544:"std.io.console.err" mod {
      }
      pub d546:"std.io.console.note": 'a -> [std::io::console::err] () where 'a: std::core::fmt::Display = e3349:(fn p825:d1555:value -> e3348:(e3341:r1345:"err::write"->d545:"std.io.console.err.write" e3347:(e3346:(e3344:r1347:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3343:(e3342:r1346:value->d1555:value.s127.show=>d321:"std.core.fmt.Display.show")) e3345:"\n")))
      pub d547:"std.io.console.eprint": std::text::str::str -> [std::io::console::err] () = e3353:(fn p826:d1556:value -> e3352:(e3350:r1348:"err::write"->d545:"std.io.console.err.write" e3351:r1349:value->d1556:value))
      pub d548:"std.io.console.eprintln": std::text::str::str -> [std::io::console::err] () = e3361:(fn p827:d1557:value -> e3360:(e3354:r1350:"err::write"->d545:"std.io.console.err.write" e3359:(e3358:(e3356:r1352:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3355:r1351:value->d1557:value) e3357:"\n")))
      pub d549:"std.io.console.dd": 'a -> [std::io::console::err] () where 'a: std::core::fmt::Debug = e3370:(fn p828:d1558:value -> e3369:(e3362:r1353:"err::write"->d545:"std.io.console.err.write" e3368:(e3367:(e3365:r1355:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3364:(e3363:r1354:value->d1558:value.s128.debug=>d325:"std.core.fmt.Debug.debug")) e3366:"\n")))
      pub d550:"std.io.console.warn" mod {
      }
      pub d552:"std.io.console.die" mod {
      }
    }
    pub d60:"std.io.file" mod {
      pub d554:"std.io.file.file_kind" mod {
        pub d555:"std.io.file.file_kind.missing": std::io::file::file_kind = <missing>
        pub d556:"std.io.file.file_kind.denied": std::io::file::file_kind = <missing>
        pub d557:"std.io.file.file_kind.file": std::io::file::file_kind = <missing>
        pub d558:"std.io.file.file_kind.dir": std::io::file::file_kind = <missing>
        pub d559:"std.io.file.file_kind.symlink": std::io::file::file_kind = <missing>
        pub d560:"std.io.file.file_kind.other": std::io::file::file_kind = <missing>
      }
      pub d561:"std.io.file.file_meta": {kind: std::io::file::file_kind, size: int, readonly: bool, modified: std::data::opt::opt std::time::instant} -> std::io::file::file_meta = <missing>
      pub d570:"std.io.file.file" mod {
      }
      pub d579:"std.io.file.io_err" mod {
        pub d580:"std.io.file.io_err.not_found": std::text::path::path -> std::io::file::io_err = <missing>
        pub d582:"std.io.file.io_err.denied": std::text::path::path -> std::io::file::io_err = <missing>
        pub d584:"std.io.file.io_err.invalid_path": std::text::path::path -> std::io::file::io_err = <missing>
        pub d586:"std.io.file.io_err.failed": std::text::path::path -> std::text::str::str -> std::io::file::io_err = <missing>
      }
      my d589:"std.io.file.unwrap_io": std::data::result::result 'a 'b -> ['c] 'a where 'b: std::control::throw::Throw(throws = 'c) = e3461:(fn p861:d1582:result -> e3460:case e3456:r1403:result->d1582:result { p863:r1404:"result::ok"->d531:"std.data.result.result.ok"(p862:d1583:value) -> e3457:r1405:value->d1583:value; p865:r1406:"result::err"->d532:"std.data.result.result.err"(p864:d1584:err) -> e3459:(e3458:r1407:err->d1584:err.s134.throw=>d234:"std.control.throw.Throw.throw") })
      pub d590:"std.io.file.meta": std::text::path::path -> [std::io::file::file] std::io::file::file_meta = e3465:(fn p866:d1585:path -> e3464:(e3462:r1408:"file::meta"->d573:"std.io.file.file.meta" e3463:r1409:path->d1585:path))
      pub d591:"std.io.file.exists": std::text::path::path -> [std::io::file::file] bool = e3474:(fn p867:d1586:path -> e3473:case e3469:(e3468:(e3466:r1410:meta->d590:"std.io.file.meta" e3467:r1411:path->d1586:path).s135.kind->d562) { p868:r1412:"file_kind::missing"->d555:"std.io.file.file_kind.missing" -> e3470:false; p869:r1413:"file_kind::denied"->d556:"std.io.file.file_kind.denied" -> e3471:false; p870:_ -> e3472:true })
      pub d592:"std.io.file.is_file": std::text::path::path -> [std::io::file::file] bool = e3482:(fn p871:d1587:path -> e3481:case e3478:(e3477:(e3475:r1414:meta->d590:"std.io.file.meta" e3476:r1415:path->d1587:path).s136.kind->d562) { p872:r1416:"file_kind::file"->d557:"std.io.file.file_kind.file" -> e3479:true; p873:_ -> e3480:false })
      pub d593:"std.io.file.is_dir": std::text::path::path -> [std::io::file::file] bool = e3490:(fn p874:d1588:path -> e3489:case e3486:(e3485:(e3483:r1417:meta->d590:"std.io.file.meta" e3484:r1418:path->d1588:path).s137.kind->d562) { p875:r1419:"file_kind::dir"->d558:"std.io.file.file_kind.dir" -> e3487:true; p876:_ -> e3488:false })
      pub d594:"std.io.file.read_at": std::text::path::path -> std::data::range::range -> [std::io::file::file, std::io::file::io_err] (std::text::str::str, std::data::range::range) = e3499:(fn p877:d1589:path -> e3498:(fn p878:d1590:r -> e3497:(e3491:r1420:unwrap_io->d589:"std.io.file.unwrap_io" e3496:(e3492:r1421:"file::read_at"->d577:"std.io.file.file.read_at" e3495:(e3493:r1422:path->d1589:path, e3494:r1423:r->d1590:r)))))
      pub d595:"std.io.file.write_at": std::text::path::path -> std::data::range::range -> std::text::str::str -> [std::io::file::file, std::io::file::io_err] () = e3510:(fn p879:d1591:path -> e3509:(fn p880:d1592:r -> e3508:(fn p881:d1593:text -> e3507:(e3500:r1424:unwrap_io->d589:"std.io.file.unwrap_io" e3506:(e3501:r1425:"file::write_at"->d578:"std.io.file.file.write_at" e3505:(e3502:r1426:path->d1591:path, e3503:r1427:r->d1592:r, e3504:r1428:text->d1593:text))))))
      pub d596:"std.io.file.read_text": std::text::path::path -> [std::io::file::file, std::io::file::io_err] std::text::str::str = e3516:(fn p882:d1594:path -> e3515:(e3511:r1429:unwrap_io->d589:"std.io.file.unwrap_io" e3514:(e3512:r1430:"file::load"->d571:"std.io.file.file.load" e3513:r1431:path->d1594:path)))
      pub d597:"std.io.file.write_text": std::text::path::path -> std::text::str::str -> [std::io::file::file, std::io::file::io_err] () = e3525:(fn p883:d1595:path -> e3524:(fn p884:d1596:text -> e3523:(e3517:r1432:unwrap_io->d589:"std.io.file.unwrap_io" e3522:(e3518:r1433:"file::store"->d572:"std.io.file.file.store" e3521:(e3519:r1434:path->d1595:path, e3520:r1435:text->d1596:text)))))
      pub d598:"std.io.file.text": std::text::path::path -> [std::io::file::file, std::io::file::io_err] std::control::var::ref '[std::io::file::file] std::text::str::str = e3549:(fn p885:d1597:path -> e3548:block { e3530:(e3526:r1436:unwrap_io->d589:"std.io.file.unwrap_io" e3529:(e3527:r1437:"file::ambient_touch"->d574:"std.io.file.file.ambient_touch" e3528:r1438:path->d1597:path)); e3547:(e3531:r1439:ref->d237:"std.control.var.ref" e3546:{get: e3535:(fn p886:() -> e3534:(e3532:r1440:"file::ambient_get"->d575:"std.io.file.file.ambient_get" e3533:r1441:path->d1597:path)), update_effect: e3545:(fn p887:() -> e3544:(e3536:r1442:"file::ambient_set"->d576:"std.io.file.file.ambient_set" e3543:(e3537:r1443:path->d1597:path, e3542:(e3538:r1444:"ref_update::update"->d236:"std.control.var.ref_update.update" e3541:(e3539:r1445:"file::ambient_get"->d575:"std.io.file.file.ambient_get" e3540:r1446:path->d1597:path)))))}) })
      pub d599:"std.io.file.text_with": std::text::path::path -> (std::text::str::str -> ['a] ('b, std::text::str::str)) -> [std::io::file::file, std::io::file::io_err, 'a] 'b = e3570:(fn p888:d1598:path -> e3569:(fn p889:d1599:f -> e3568:block { let my p890:d1600:initial = e3554:(e3550:r1447:unwrap_io->d589:"std.io.file.unwrap_io" e3553:(e3551:r1448:"file::load"->d571:"std.io.file.file.load" e3552:r1449:path->d1598:path)); e3567:block { let my p893:(p891:d1601:result, p892:d1602:final) = e3557:(e3555:r1450:f->d1599:f e3556:r1451:initial->d1600:initial); e3566:block { e3564:(e3558:r1452:unwrap_io->d589:"std.io.file.unwrap_io" e3563:(e3559:r1453:"file::store"->d572:"std.io.file.file.store" e3562:(e3560:r1454:path->d1598:path, e3561:r1455:final->d1602:final))); e3565:r1456:result->d1601:result } } }))
    }
    pub d61:"std.io.net" mod {
      pub d600:"std.io.net.request": {meta: std::io::net::request_meta, payload: std::text::bytes::bytes, slot: std::io::net::respond_slot} -> std::io::net::request = <missing>
      pub d607:"std.io.net.net_err" mod {
        pub d608:"std.io.net.net_err.unreachable": std::text::str::str -> std::io::net::net_err = <missing>
        pub d610:"std.io.net.net_err.refused": std::text::str::str -> std::io::net::net_err = <missing>
        pub d612:"std.io.net.net_err.already_bound": std::text::str::str -> std::io::net::net_err = <missing>
        pub d614:"std.io.net.net_err.closed": std::io::net::net_err = <missing>
        pub d616:"std.io.net.net_err.timeout": std::io::net::net_err = <missing>
        pub d618:"std.io.net.net_err.failed": std::text::str::str -> std::io::net::net_err = <missing>
      }
      pub d621:"std.io.net.net" mod {
      }
      pub d624:"std.io.net.server" mod {
      }
      my d627:"std.io.net.unwrap_net": std::data::result::result 'a 'b -> ['c] 'a where 'b: std::control::throw::Throw(throws = 'c) = e3658:(fn p930:d1623:result -> e3657:case e3653:r1508:result->d1623:result { p932:r1509:"result::ok"->d531:"std.data.result.result.ok"(p931:d1624:value) -> e3654:r1510:value->d1624:value; p934:r1511:"result::err"->d532:"std.data.result.result.err"(p933:d1625:err) -> e3656:(e3655:r1512:err->d1625:err.s142.throw=>d234:"std.control.throw.Throw.throw") })
      pub d628:"std.io.net.listen": int -> [std::io::net::net, std::io::net::net_err] std::io::net::listener = e3664:(fn p935:d1626:port -> e3663:(e3659:r1513:unwrap_net->d627:"std.io.net.unwrap_net" e3662:(e3660:r1514:"net::listen"->d622:"std.io.net.net.listen" e3661:r1515:port->d1626:port)))
      pub d629:"std.io.net.serve": int -> [std::io::net::net, std::io::net::net_err, std::io::net::server] std::io::net::request = e3672:(fn p936:d1627:port -> e3671:block { let my p937:d1628:listener = e3667:(e3665:r1516:listen->d628:"std.io.net.listen" e3666:r1517:port->d1627:port); e3670:(e3668:r1518:"server::accept"->d625:"std.io.net.server.accept" e3669:r1519:listener->d1628:listener) })
      pub d630:"std.io.net.listener" mod {
        pub d631:"std.io.net.listener.accept": std::io::net::listener -> () -> [std::io::net::server] std::io::net::request = e3677:(fn p938:d1629:l -> e3676:(fn p939:() -> e3675:(e3673:r1520:"server::accept"->d625:"std.io.net.server.accept" e3674:r1521:l->d1629:l)))
        pub d632:"std.io.net.listener.port": std::io::net::listener -> [std::io::net::net] int = e3681:(fn p940:d1630:l -> e3680:(e3678:r1522:"net::port"->d623:"std.io.net.net.port" e3679:r1523:l->d1630:l))
      }
      pub d633:"std.io.net.request" mod {
        pub d634:"std.io.net.request.respond": std::io::net::request -> std::text::bytes::bytes -> [std::io::net::net_err, std::io::net::server] () = e3691:(fn p941:d1631:req -> e3690:(fn p942:d1632:res -> e3689:(e3682:r1524:unwrap_net->d627:"std.io.net.unwrap_net" e3688:(e3683:r1525:"server::respond"->d626:"std.io.net.server.respond" e3687:(e3685:(e3684:r1526:req->d1631:req.s143.slot->d605), e3686:r1527:res->d1632:res)))))
      }
    }
  }
  pub d12:"std.time" mod {
    pub d119:"std.time.instant": {epoch_nanos: int} -> std::time::instant = <missing>
    pub d122:"std.time.duration": {nanos: int} -> std::time::duration = <missing>
    pub d125:"std.time.clock" mod {
    }
    pub d127:"std.time.instant_add": std::time::instant -> std::time::duration -> std::time::instant = e173:(fn p39:d1052:t -> e172:(fn p40:d1053:delta -> e171:(e162:r58:instant->d119:"std.time.instant" e170:{epoch_nanos: e169:(e166:(e163:r59:"std::int::add"->d52:"std.int.add" e165:(e164:r60:t->d1052:t.s2.epoch_nanos->d120)) e168:(e167:r61:delta->d1053:delta.s3.nanos->d123))})))
    pub d128:"std.time.instant_sub": std::time::instant -> std::time::duration -> std::time::instant = e185:(fn p41:d1054:t -> e184:(fn p42:d1055:delta -> e183:(e174:r62:instant->d119:"std.time.instant" e182:{epoch_nanos: e181:(e178:(e175:r63:"std::int::sub"->d53:"std.int.sub" e177:(e176:r64:t->d1054:t.s4.epoch_nanos->d120)) e180:(e179:r65:delta->d1055:delta.s5.nanos->d123))})))
    pub d129:"std.time.instant_since": std::time::instant -> std::time::instant -> std::time::duration = e197:(fn p43:d1056:later -> e196:(fn p44:d1057:earlier -> e195:(e186:r66:duration->d122:"std.time.duration" e194:{nanos: e193:(e190:(e187:r67:"std::int::sub"->d53:"std.int.sub" e189:(e188:r68:later->d1056:later.s6.epoch_nanos->d120)) e192:(e191:r69:earlier->d1057:earlier.s7.epoch_nanos->d120))})))
    pub d130:"std.time.duration_add": std::time::duration -> std::time::duration -> std::time::duration = e209:(fn p45:d1058:x -> e208:(fn p46:d1059:y -> e207:(e198:r70:duration->d122:"std.time.duration" e206:{nanos: e205:(e202:(e199:r71:"std::int::add"->d52:"std.int.add" e201:(e200:r72:x->d1058:x.s8.nanos->d123)) e204:(e203:r73:y->d1059:y.s9.nanos->d123))})))
    pub d131:"std.time.duration_sub": std::time::duration -> std::time::duration -> std::time::duration = e221:(fn p47:d1060:x -> e220:(fn p48:d1061:y -> e219:(e210:r74:duration->d122:"std.time.duration" e218:{nanos: e217:(e214:(e211:r75:"std::int::sub"->d53:"std.int.sub" e213:(e212:r76:x->d1060:x.s10.nanos->d123)) e216:(e215:r77:y->d1061:y.s11.nanos->d123))})))
    pub d132:"std.time.nanos": int -> std::time::duration = e226:(fn p49:d1062:count -> e225:(e222:r78:duration->d122:"std.time.duration" e224:{nanos: e223:r79:count->d1062:count}))
    pub d133:"std.time.micros": int -> std::time::duration = e234:(fn p50:d1063:count -> e233:(e227:r80:nanos->d132:"std.time.nanos" e232:(e230:(e228:r81:"std::int::mul"->d54:"std.int.mul" e229:r82:count->d1063:count) e231:1000)))
    pub d134:"std.time.millis": int -> std::time::duration = e242:(fn p51:d1064:count -> e241:(e235:r83:micros->d133:"std.time.micros" e240:(e238:(e236:r84:"std::int::mul"->d54:"std.int.mul" e237:r85:count->d1064:count) e239:1000)))
    pub d135:"std.time.secs": int -> std::time::duration = e250:(fn p52:d1065:count -> e249:(e243:r86:millis->d134:"std.time.millis" e248:(e246:(e244:r87:"std::int::mul"->d54:"std.int.mul" e245:r88:count->d1065:count) e247:1000)))
    pub d136:"std.time.mins": int -> std::time::duration = e258:(fn p53:d1066:count -> e257:(e251:r89:secs->d135:"std.time.secs" e256:(e254:(e252:r90:"std::int::mul"->d54:"std.int.mul" e253:r91:count->d1066:count) e255:60)))
    pub d137:"std.time.hours": int -> std::time::duration = e266:(fn p54:d1067:count -> e265:(e259:r92:mins->d136:"std.time.mins" e264:(e262:(e260:r93:"std::int::mul"->d54:"std.int.mul" e261:r94:count->d1067:count) e263:60)))
    pub d138:"std.time.days": int -> std::time::duration = e274:(fn p55:d1068:count -> e273:(e267:r95:hours->d137:"std.time.hours" e272:(e270:(e268:r96:"std::int::mul"->d54:"std.int.mul" e269:r97:count->d1068:count) e271:24)))
    my d139:"std.time.floor_div": int -> int -> int = e302:(fn p56:d1069:x -> e301:(fn p57:d1070:y -> e300:block { let my p58:d1071:q = e279:(e278:(e276:r99:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e275:r98:x->d1069:x) e277:r100:y->d1070:y); e299:block { let my p59:d1072:r = e284:(e283:(e281:r102:"#op:infix:mod"->d420:"std.core.ops.#op:infix:mod" e280:r101:x->d1069:x) e282:r103:y->d1070:y); e298:case e291:(e290:r106:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e289:(e288:(e286:r105:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e285:r104:r->d1072:r) e287:0)) { p60:true -> e296:(e295:(e293:r108:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e292:r107:q->d1071:q) e294:1); p61:false -> e297:r109:q->d1071:q } } }))
    my d140:"std.time.floor_mod": int -> int -> int = e317:(fn p62:d1073:x -> e316:(fn p63:d1074:y -> e315:(e314:(e304:r111:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e303:r110:x->d1073:x) e313:(e312:(e310:r115:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e309:(e307:(e305:r112:floor_div->d139:"std.time.floor_div" e306:r113:x->d1073:x) e308:r114:y->d1074:y)) e311:r116:y->d1074:y))))
    my d141:"std.time.civil_from_epoch_days": int -> (int, int, int) = e476:(fn p64:d1075:days_since_epoch -> e475:block { let my p65:d1076:z = e322:(e321:(e319:r118:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e318:r117:days_since_epoch->d1075:days_since_epoch) e320:719468); e474:block { let my p66:d1077:era = e327:(e325:(e323:r119:floor_div->d139:"std.time.floor_div" e324:r120:z->d1076:z) e326:146097); e473:block { let my p67:d1078:doe = e336:(e335:(e329:r122:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e328:r121:z->d1076:z) e334:(e333:(e331:r124:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e330:r123:era->d1077:era) e332:146097)); e472:block { let my p68:d1079:yoe = e365:(e364:(e362:r135:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e361:(e360:(e354:r132:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e353:(e352:(e346:r129:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e345:(e344:(e338:r126:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e337:r125:doe->d1078:doe) e343:(e342:(e340:r128:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e339:r127:doe->d1078:doe) e341:1460))) e351:(e350:(e348:r131:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e347:r130:doe->d1078:doe) e349:36524))) e359:(e358:(e356:r134:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e355:r133:doe->d1078:doe) e357:146096))) e363:365); e471:block { let my p69:d1080:year = e374:(e373:(e367:r137:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e366:r136:yoe->d1079:yoe) e372:(e371:(e369:r139:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e368:r138:era->d1077:era) e370:400)); e470:block { let my p70:d1081:doy = e399:(e398:(e376:r141:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e375:r140:doe->d1078:doe) e397:(e396:(e390:r147:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e389:(e388:(e382:r144:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e381:(e380:(e378:r142:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e377:365) e379:r143:yoe->d1079:yoe)) e387:(e386:(e384:r146:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e383:r145:yoe->d1079:yoe) e385:4))) e395:(e394:(e392:r149:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e391:r148:yoe->d1079:yoe) e393:100))); e469:block { let my p71:d1082:mp = e412:(e411:(e409:r153:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e408:(e407:(e405:r152:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e404:(e403:(e401:r150:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e400:5) e402:r151:doy->d1081:doy)) e406:2)) e410:153); e468:block { let my p72:d1083:day = e433:(e432:(e430:r160:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e429:(e428:(e414:r155:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e413:r154:doy->d1081:doy) e427:(e426:(e424:r159:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e423:(e422:(e420:r158:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e419:(e418:(e416:r156:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e415:153) e417:r157:mp->d1082:mp)) e421:2)) e425:5))) e431:1); e467:block { let my p73:d1084:month = e449:(e448:(e435:r162:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e434:r161:mp->d1082:mp) e447:case e442:(e441:r165:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e440:(e439:(e437:r164:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e436:r163:mp->d1082:mp) e438:10)) { p74:true -> e443:3; p75:false -> e446:(e444:r166:"#op:prefix:-"->d414:"std.core.ops.#op:prefix:-" e445:9) }); e466:(e463:case e456:(e455:r169:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e454:(e453:(e451:r168:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e450:r167:month->d1084:month) e452:2)) { p76:true -> e461:(e460:(e458:r171:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e457:r170:year->d1080:year) e459:1); p77:false -> e462:r172:year->d1080:year }, e464:r173:month->d1084:month, e465:r174:day->d1083:day) } } } } } } } } })
    my d142:"std.time.pad2": int -> std::text::str::str = e495:(fn p78:d1085:n -> e494:case e483:(e482:r177:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e481:(e480:(e478:r176:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e477:r175:n->d1085:n) e479:10)) { p79:true -> e490:(e489:(e485:r178:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e484:"0") e488:(e486:r179:"std::int::to_string"->d56:"std.int.to_string" e487:r180:n->d1085:n)); p80:false -> e493:(e491:r181:"std::int::to_string"->d56:"std.int.to_string" e492:r182:n->d1085:n) })
    my d143:"std.time.pad3": int -> std::text::str::str = e529:(fn p81:d1086:n -> e528:case e502:(e501:r185:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e500:(e499:(e497:r184:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e496:r183:n->d1086:n) e498:10)) { p84:true -> e509:(e508:(e504:r186:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e503:"00") e507:(e505:r187:"std::int::to_string"->d56:"std.int.to_string" e506:r188:n->d1086:n)); p85:false -> e527:case e516:(e515:r191:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e514:(e513:(e511:r190:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e510:r189:n->d1086:n) e512:100)) { p82:true -> e523:(e522:(e518:r192:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e517:"0") e521:(e519:r193:"std::int::to_string"->d56:"std.int.to_string" e520:r194:n->d1086:n)); p83:false -> e526:(e524:r195:"std::int::to_string"->d56:"std.int.to_string" e525:r196:n->d1086:n) } })
    my d144:"std.time.pad4": int -> std::text::str::str = e578:(fn p86:d1087:n -> e577:case e536:(e535:r199:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e534:(e533:(e531:r198:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e530:r197:n->d1087:n) e532:10)) { p91:true -> e543:(e542:(e538:r200:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e537:"000") e541:(e539:r201:"std::int::to_string"->d56:"std.int.to_string" e540:r202:n->d1087:n)); p92:false -> e576:case e550:(e549:r205:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e548:(e547:(e545:r204:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e544:r203:n->d1087:n) e546:100)) { p89:true -> e557:(e556:(e552:r206:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e551:"00") e555:(e553:r207:"std::int::to_string"->d56:"std.int.to_string" e554:r208:n->d1087:n)); p90:false -> e575:case e564:(e563:r211:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e562:(e561:(e559:r210:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e558:r209:n->d1087:n) e560:1000)) { p87:true -> e571:(e570:(e566:r212:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e565:"0") e569:(e567:r213:"std::int::to_string"->d56:"std.int.to_string" e568:r214:n->d1087:n)); p88:false -> e574:(e572:r215:"std::int::to_string"->d56:"std.int.to_string" e573:r216:n->d1087:n) } } })
    my d145:"std.time.pad9": int -> std::text::str::str = e610:(fn p93:d1088:n -> e609:(e608:(e600:r225:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e599:(e598:(e586:r220:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e585:(e579:r217:pad3->d143:"std.time.pad3" e584:(e583:(e581:r219:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e580:r218:n->d1088:n) e582:1000000))) e597:(e587:r221:pad3->d143:"std.time.pad3" e596:(e595:(e593:r224:"#op:infix:mod"->d420:"std.core.ops.#op:infix:mod" e592:(e591:(e589:r223:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e588:r222:n->d1088:n) e590:1000)) e594:1000)))) e607:(e601:r226:pad3->d143:"std.time.pad3" e606:(e605:(e603:r228:"#op:infix:mod"->d420:"std.core.ops.#op:infix:mod" e602:r227:n->d1088:n) e604:1000))))
    my d146:"std.time.trim_trailing_zeros": std::text::str::str -> std::text::str::str = e654:(fn p94:d1089:text -> e653:block { let my p95:d1090:len = e613:(e611:r229:"std::text::str::len"->d788:"std.text.str.len" e612:r230:text->d1089:text); e652:case e620:(e619:r233:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e618:(e617:(e615:r232:"#op:infix:<="->d424:"std.core.ops.#op:infix:<=" e614:r231:len->d1090:len) e616:0)) { p99:true -> e621:r234:text->d1089:text; p100:false -> e651:block { let my p96:d1091:end = e626:(e625:(e623:r236:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e622:r235:len->d1090:len) e624:1); e650:case e639:(e638:r242:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e637:(e636:(e634:r241:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e633:(e631:(e629:(e627:r237:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e628:r238:text->d1089:text) e630:r239:end->d1091:end) e632:r240:len->d1090:len)) e635:"0")) { p97:true -> e648:(e640:r243:trim_trailing_zeros->d146:"std.time.trim_trailing_zeros" e647:(e645:(e643:(e641:r244:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e642:r245:text->d1089:text) e644:0) e646:r246:end->d1091:end)); p98:false -> e649:r247:text->d1089:text } } } })
    my d147:"std.time.fraction_text": int -> std::text::str::str = e673:(fn p101:d1092:nanos_in_second -> e672:case e661:(e660:r250:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e659:(e658:(e656:r249:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e655:r248:nanos_in_second->d1092:nanos_in_second) e657:0)) { p102:true -> e662:""; p103:false -> e671:(e670:(e664:r251:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e663:".") e669:(e665:r252:trim_trailing_zeros->d146:"std.time.trim_trailing_zeros" e668:(e666:r253:pad9->d145:"std.time.pad9" e667:r254:nanos_in_second->d1092:nanos_in_second))) })
    my d148:"std.time.instant_rfc3339_utc": std::time::instant -> std::text::str::str = e793:(fn p104:d1093:x -> e792:block { let my p105:d1094:seconds = e679:(e677:(e674:r255:floor_div->d139:"std.time.floor_div" e676:(e675:r256:x->d1093:x.s12.epoch_nanos->d120)) e678:1000000000); e791:block { let my p106:d1095:nanos_in_second = e685:(e683:(e680:r257:floor_mod->d140:"std.time.floor_mod" e682:(e681:r258:x->d1093:x.s13.epoch_nanos->d120)) e684:1000000000); e790:block { let my p107:d1096:days = e690:(e688:(e686:r259:floor_div->d139:"std.time.floor_div" e687:r260:seconds->d1094:seconds) e689:86400); e789:block { let my p108:d1097:second_of_day = e695:(e693:(e691:r261:floor_mod->d140:"std.time.floor_mod" e692:r262:seconds->d1094:seconds) e694:86400); e788:block { let my p112:(p109:d1098:year, p110:d1099:month, p111:d1100:day) = e698:(e696:r263:civil_from_epoch_days->d141:"std.time.civil_from_epoch_days" e697:r264:days->d1096:days); e787:block { let my p113:d1101:hour = e703:(e702:(e700:r266:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e699:r265:second_of_day->d1097:second_of_day) e701:3600); e786:block { let my p114:d1102:minute = e712:(e711:(e709:r269:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e708:(e707:(e705:r268:"#op:infix:mod"->d420:"std.core.ops.#op:infix:mod" e704:r267:second_of_day->d1097:second_of_day) e706:3600)) e710:60); e785:block { let my p115:d1103:second = e717:(e716:(e714:r271:"#op:infix:mod"->d420:"std.core.ops.#op:infix:mod" e713:r270:second_of_day->d1097:second_of_day) e715:60); e784:block { let my p116:d1104:date = e740:(e739:(e735:r279:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e734:(e733:(e731:r278:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e730:(e729:(e725:r275:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e724:(e723:(e721:r274:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e720:(e718:r272:pad4->d144:"std.time.pad4" e719:r273:year->d1098:year)) e722:"-")) e728:(e726:r276:pad2->d142:"std.time.pad2" e727:r277:month->d1099:month))) e732:"-")) e738:(e736:r280:pad2->d142:"std.time.pad2" e737:r281:day->d1100:day)); e783:block { let my p117:d1105:clock = e763:(e762:(e758:r289:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e757:(e756:(e754:r288:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e753:(e752:(e748:r285:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e747:(e746:(e744:r284:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e743:(e741:r282:pad2->d142:"std.time.pad2" e742:r283:hour->d1101:hour)) e745:":")) e751:(e749:r286:pad2->d142:"std.time.pad2" e750:r287:minute->d1102:minute))) e755:":")) e761:(e759:r290:pad2->d142:"std.time.pad2" e760:r291:second->d1103:second)); e782:(e781:(e779:r299:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e778:(e777:(e773:r296:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e772:(e771:(e769:r294:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e768:(e767:(e765:r293:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e764:r292:date->d1104:date) e766:"T")) e770:r295:clock->d1105:clock)) e776:(e774:r297:fraction_text->d147:"std.time.fraction_text" e775:r298:nanos_in_second->d1095:nanos_in_second))) e780:"Z") } } } } } } } } } })
    my d149 mod {
      d150: std::time::instant -> std::time::instant -> bool = e802:(fn p118:d1106:x -> e801:(fn p119:d1107:y -> e800:(e797:(e794:r300:"std::int::eq"->d47:"std.int.eq" e796:(e795:r301:x->d1106:x.s14.epoch_nanos->d120)) e799:(e798:r302:y->d1107:y.s15.epoch_nanos->d120))))
    }
    my d151 mod {
      d152: std::time::instant -> std::time::instant -> bool = e811:(fn p120:d1108:x -> e810:(fn p121:d1109:y -> e809:(e806:(e803:r303:"std::int::lt"->d48:"std.int.lt" e805:(e804:r304:x->d1108:x.s16.epoch_nanos->d120)) e808:(e807:r305:y->d1109:y.s17.epoch_nanos->d120))))
      d153: std::time::instant -> std::time::instant -> bool = e820:(fn p122:d1110:x -> e819:(fn p123:d1111:y -> e818:(e815:(e812:r306:"std::int::le"->d49:"std.int.le" e814:(e813:r307:x->d1110:x.s18.epoch_nanos->d120)) e817:(e816:r308:y->d1111:y.s19.epoch_nanos->d120))))
      d154: std::time::instant -> std::time::instant -> bool = e829:(fn p124:d1112:x -> e828:(fn p125:d1113:y -> e827:(e824:(e821:r309:"std::int::gt"->d50:"std.int.gt" e823:(e822:r310:x->d1112:x.s20.epoch_nanos->d120)) e826:(e825:r311:y->d1113:y.s21.epoch_nanos->d120))))
      d155: std::time::instant -> std::time::instant -> bool = e838:(fn p126:d1114:x -> e837:(fn p127:d1115:y -> e836:(e833:(e830:r312:"std::int::ge"->d51:"std.int.ge" e832:(e831:r313:x->d1114:x.s22.epoch_nanos->d120)) e835:(e834:r314:y->d1115:y.s23.epoch_nanos->d120))))
    }
    my d156 mod {
      d157: std::time::duration -> std::time::duration -> bool = e847:(fn p128:d1116:x -> e846:(fn p129:d1117:y -> e845:(e842:(e839:r315:"std::int::eq"->d47:"std.int.eq" e841:(e840:r316:x->d1116:x.s24.nanos->d123)) e844:(e843:r317:y->d1117:y.s25.nanos->d123))))
    }
    my d158 mod {
      d159: std::time::duration -> std::time::duration -> bool = e856:(fn p130:d1118:x -> e855:(fn p131:d1119:y -> e854:(e851:(e848:r318:"std::int::lt"->d48:"std.int.lt" e850:(e849:r319:x->d1118:x.s26.nanos->d123)) e853:(e852:r320:y->d1119:y.s27.nanos->d123))))
      d160: std::time::duration -> std::time::duration -> bool = e865:(fn p132:d1120:x -> e864:(fn p133:d1121:y -> e863:(e860:(e857:r321:"std::int::le"->d49:"std.int.le" e859:(e858:r322:x->d1120:x.s28.nanos->d123)) e862:(e861:r323:y->d1121:y.s29.nanos->d123))))
      d161: std::time::duration -> std::time::duration -> bool = e874:(fn p134:d1122:x -> e873:(fn p135:d1123:y -> e872:(e869:(e866:r324:"std::int::gt"->d50:"std.int.gt" e868:(e867:r325:x->d1122:x.s30.nanos->d123)) e871:(e870:r326:y->d1123:y.s31.nanos->d123))))
      d162: std::time::duration -> std::time::duration -> bool = e883:(fn p136:d1124:x -> e882:(fn p137:d1125:y -> e881:(e878:(e875:r327:"std::int::ge"->d51:"std.int.ge" e877:(e876:r328:x->d1124:x.s32.nanos->d123)) e880:(e879:r329:y->d1125:y.s33.nanos->d123))))
    }
    my d163 mod {
      d164: std::time::instant -> std::text::str::str = e896:(fn p138:d1126:x -> e895:(e894:(e892:r333:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e891:(e890:(e885:r330:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e884:"instant { epoch_nanos: ") e889:(e886:r331:"std::int::to_string"->d56:"std.int.to_string" e888:(e887:r332:x->d1126:x.s34.epoch_nanos->d120)))) e893:" }"))
    }
    my d165 mod {
      d166: std::time::duration -> std::text::str::str = e909:(fn p139:d1127:x -> e908:(e907:(e905:r337:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e904:(e903:(e898:r334:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e897:"duration { nanos: ") e902:(e899:r335:"std::int::to_string"->d56:"std.int.to_string" e901:(e900:r336:x->d1127:x.s35.nanos->d123)))) e906:" }"))
    }
    my d167 mod {
      d168: std::time::instant -> std::text::str::str = e913:(fn p140:d1128:x -> e912:(e910:r338:instant_rfc3339_utc->d148:"std.time.instant_rfc3339_utc" e911:r339:x->d1128:x))
    }
    my d169 mod {
      d170: std::time::duration -> std::time::duration -> std::time::duration = e920:(fn p141:d1129:x -> e919:(fn p142:d1130:y -> e918:(e916:(e914:r340:duration_add->d130:"std.time.duration_add" e915:r341:x->d1129:x) e917:r342:y->d1130:y)))
    }
    my d171 mod {
      d172: std::time::duration -> std::time::duration -> std::time::duration = e927:(fn p143:d1131:x -> e926:(fn p144:d1132:y -> e925:(e923:(e921:r343:duration_sub->d131:"std.time.duration_sub" e922:r344:x->d1131:x) e924:r345:y->d1132:y)))
    }
  }
  pub d13:"std.testing" mod {
    pub d107:"std.testing.#op:prefix:assert": (() -> bool) -> [std::testing::assertion] () = e145:r51:"assertion::assert"->d110:"std.testing.assertion.assert"
    pub d108:"std.testing.#op:infix:assert_eq": (() -> 'a) -> (() -> 'a) -> [std::testing::assertion] () where 'a: std::core::cmp::Eq, 'a: std::core::fmt::Debug = e161:(fn p34:d1047:left -> e160:(fn p35:d1048:right -> e159:(e146:r52:"assertion::assert_eq"->d111:"std.testing.assertion.assert_eq" e158:(e147:r53:left->d1047:left, e148:r54:right->d1048:right, e154:(fn p36:d1049:expected -> e153:(fn p37:d1050:actual -> e152:(e150:(e149:r55:expected->d1049:expected.s0.eq=>d250:"std.core.cmp.Eq.eq") e151:r56:actual->d1050:actual))), e157:(fn p38:d1051:value -> e156:(e155:r57:value->d1051:value.s1.debug=>d325:"std.core.fmt.Debug.debug"))))))
    pub d109:"std.testing.assertion" mod {
    }
  }
  pub d14:"std.prelude" mod {
  }
}
d1:ping mod {
}
runtime roots d181:"std.control.flow.label_sub.control_label" d211:"std.control.flow.label_loop.control_label"
detached {
  d2:"ping.get": () -> [ping] int = <missing>
  pub d110:"std.testing.assertion.assert": (() -> bool) -> [std::testing::assertion] () = <missing>
  pub d111:"std.testing.assertion.assert_eq": (() -> 'a, () -> 'a, 'a -> 'a -> bool, 'a -> std::text::str::str) -> [std::testing::assertion] () = <missing>
  pub d120: std::time::instant -> int = <missing>
  pub d121: std::control::var::ref 'a std::time::instant -> std::control::var::ref 'a int = <missing>
  pub d123: std::time::duration -> int = <missing>
  pub d124: std::control::var::ref 'a std::time::duration -> std::control::var::ref 'a int = <missing>
  pub d126:"std.time.clock.now": () -> [std::time::clock] std::time::instant = <missing>
  pub d174:"std.control.flow.sub.return": 'a -> [std::control::flow::sub 'a] never = <missing>
  pub d177:"std.control.flow.label_sub.return": 'a -> [std::control::flow::label_sub 'a] never = <missing>
  pub d179: std::control::flow::label_sub::label -> () = <missing>
  pub d180: std::control::var::ref 'a std::control::flow::label_sub::label -> std::control::var::ref 'a () = <missing>
  pub d184:"std.control.flow.loop.last": () -> [std::control::flow::loop] never = <missing>
  pub d185:"std.control.flow.loop.next": () -> [std::control::flow::loop] never = <missing>
  pub d186:"std.control.flow.loop.redo": () -> [std::control::flow::loop] never = <missing>
  d188:"std.control.flow.loop.last.break": () -> [std::control::flow::loop::last] never = <missing>
  pub d197:"std.control.flow.label_loop.last": () -> [std::control::flow::label_loop] never = <missing>
  pub d198:"std.control.flow.label_loop.next": () -> [std::control::flow::label_loop] never = <missing>
  pub d199:"std.control.flow.label_loop.redo": () -> [std::control::flow::label_loop] never = <missing>
  pub d201: std::control::flow::label_loop::label -> () -> [std::control::flow::label_loop] never = <missing>
  pub d202: std::control::var::ref 'a std::control::flow::label_loop::label -> std::control::var::ref('a, () ['[]] -> ['[std::control::flow::label_loop]] never) = <missing>
  pub d203: std::control::flow::label_loop::label -> () -> [std::control::flow::label_loop] never = <missing>
  pub d204: std::control::var::ref 'a std::control::flow::label_loop::label -> std::control::var::ref('a, () ['[]] -> ['[std::control::flow::label_loop]] never) = <missing>
  pub d205: std::control::flow::label_loop::label -> () -> [std::control::flow::label_loop] never = <missing>
  pub d206: std::control::var::ref 'a std::control::flow::label_loop::label -> std::control::var::ref('a, () ['[]] -> ['[std::control::flow::label_loop]] never) = <missing>
  d208:"std.control.flow.label_loop.last.break": () -> [std::control::flow::label_loop::last] never = <missing>
  my d214:"std.control.junction.junction.or": () -> [std::control::junction::junction] bool = <missing>
  my d215:"std.control.junction.junction.and": () -> [std::control::junction::junction] bool = <missing>
  my d216:"std.control.junction.junction.ret": bool -> [std::control::junction::junction] never = <missing>
  pub d223:"std.control.nondet.nondet.branch": () -> [std::control::nondet::nondet] bool = <missing>
  pub d224:"std.control.nondet.nondet.reject": () -> [std::control::nondet::nondet] never = <missing>
  pub d236:"std.control.var.ref_update.update": 'a -> [std::control::var::ref_update 'a] 'a = <missing>
  pub d238: std::control::var::ref 'a 'b -> () -> ['a] 'b = <missing>
  pub d239: std::control::var::ref('a, std::control::var::ref 'b 'c) -> std::control::var::ref('a, () ['[]] -> ['b] 'c) = <missing>
  pub d240: std::control::var::ref 'a 'b -> () -> [std::control::var::ref_update 'b, 'a#0[AllExcept(std::control::var::ref_update)]] () = <missing>
  pub d241: std::control::var::ref('a, std::control::var::ref 'b 'c) -> std::control::var::ref('a, () ['[]] -> ['[std::control::var::ref_update 'c, 'b] <: 'b & '[std::control::var::ref_update 'c; 'b]] ()) = <missing>
  pub d245:"std.control.var.var.get": () -> [std::control::var::var 'a] 'a = <missing>
  pub d246:"std.control.var.var.set": 'a -> [std::control::var::var 'a] () = <missing>
  my d287:"#cast": std::text::path::path -> std::text::bytes::bytes = e1596:(fn p389:d1256:p -> e1595:(e1593:r593:"std::text::path::to_bytes"->d780:"std.text.path.to_bytes" e1594:r594:p->d1256:p))
  my d288:"#cast": int -> std::num::frac::frac = e1602:(fn p390:d1257:x -> e1601:(e1599:(e1597:r595:"std::num::frac::new"->d643:"std.num.frac.new" e1598:r596:x->d1257:x) e1600:1))
  my d289:"#cast": int -> float = e1606:(fn p391:d1258:x -> e1605:(e1603:builtin_op::int_to_float e1604:r597:x->d1258:x))
  my d290:"#cast": std::num::frac::frac -> float = e1610:(fn p392:d1259:x -> e1609:(e1607:r598:"std::num::frac::to_float"->d653:"std.num.frac.to_float" e1608:r599:x->d1259:x))
  pub d304: std::core::fmt::format_spec -> std::core::fmt::format_kind = <missing>
  pub d305: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref 'a std::core::fmt::format_kind = <missing>
  pub d306: std::core::fmt::format_spec -> std::data::opt::opt std::core::fmt::format_align = <missing>
  pub d307: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref('a, std::data::opt::opt std::core::fmt::format_align) = <missing>
  pub d308: std::core::fmt::format_spec -> std::data::opt::opt std::core::fmt::format_sign = <missing>
  pub d309: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref('a, std::data::opt::opt std::core::fmt::format_sign) = <missing>
  pub d310: std::core::fmt::format_spec -> std::data::opt::opt std::text::str::str = <missing>
  pub d311: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref('a, std::data::opt::opt std::text::str::str) = <missing>
  pub d312: std::core::fmt::format_spec -> std::data::opt::opt int = <missing>
  pub d313: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref('a, std::data::opt::opt int) = <missing>
  pub d314: std::core::fmt::format_spec -> std::data::opt::opt int = <missing>
  pub d315: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref('a, std::data::opt::opt int) = <missing>
  pub d316: std::core::fmt::format_spec -> bool = <missing>
  pub d317: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref 'a bool = <missing>
  pub d318: std::core::fmt::format_spec -> bool = <missing>
  pub d319: std::control::var::ref 'a std::core::fmt::format_spec -> std::control::var::ref 'a bool = <missing>
  pub d540:"std.io.console.out.write": std::text::str::str -> [std::io::console::out] () = <missing>
  pub d545:"std.io.console.err.write": std::text::str::str -> [std::io::console::err] () = <missing>
  pub d551:"std.io.console.warn.warn": std::text::str::str -> [std::io::console::warn] () = <missing>
  pub d553:"std.io.console.die.die": std::text::str::str -> [std::io::console::die] never = <missing>
  pub d562: std::io::file::file_meta -> std::io::file::file_kind = <missing>
  pub d563: std::control::var::ref 'a std::io::file::file_meta -> std::control::var::ref 'a std::io::file::file_kind = <missing>
  pub d564: std::io::file::file_meta -> int = <missing>
  pub d565: std::control::var::ref 'a std::io::file::file_meta -> std::control::var::ref 'a int = <missing>
  pub d566: std::io::file::file_meta -> bool = <missing>
  pub d567: std::control::var::ref 'a std::io::file::file_meta -> std::control::var::ref 'a bool = <missing>
  pub d568: std::io::file::file_meta -> std::data::opt::opt std::time::instant = <missing>
  pub d569: std::control::var::ref 'a std::io::file::file_meta -> std::control::var::ref('a, std::data::opt::opt std::time::instant) = <missing>
  pub d571:"std.io.file.file.load": std::text::path::path -> [std::io::file::file] std::data::result::result std::text::str::str std::io::file::io_err = <missing>
  pub d572:"std.io.file.file.store": (std::text::path::path, std::text::str::str) -> [std::io::file::file] std::data::result::result () std::io::file::io_err = <missing>
  pub d573:"std.io.file.file.meta": std::text::path::path -> [std::io::file::file] std::io::file::file_meta = <missing>
  pub d574:"std.io.file.file.ambient_touch": std::text::path::path -> [std::io::file::file] std::data::result::result () std::io::file::io_err = <missing>
  pub d575:"std.io.file.file.ambient_get": std::text::path::path -> [std::io::file::file] std::text::str::str = <missing>
  pub d576:"std.io.file.file.ambient_set": (std::text::path::path, std::text::str::str) -> [std::io::file::file] () = <missing>
  pub d577:"std.io.file.file.read_at": (std::text::path::path, std::data::range::range) -> [std::io::file::file] std::data::result::result (std::text::str::str, std::data::range::range) std::io::file::io_err = <missing>
  pub d578:"std.io.file.file.write_at": (std::text::path::path, std::data::range::range, std::text::str::str) -> [std::io::file::file] std::data::result::result () std::io::file::io_err = <missing>
  my d581: std::text::path::path -> [std::io::file::io_err] never = <missing>
  my d583: std::text::path::path -> [std::io::file::io_err] never = <missing>
  my d585: std::text::path::path -> [std::io::file::io_err] never = <missing>
  my d587: (std::text::path::path, std::text::str::str) -> [std::io::file::io_err] never = <missing>
  pub d588:"std.io.file.io_err.wrap": 'a [std::io::file::io_err; 'b] -> ['b] std::data::result::result('a, 'c | std::io::file::io_err) = e3455:(fn p849:d1575:action -> e3454:catch e3428:r1387:action->d1575:action { std::io::file::io_err::not_found p850:d1576:__error_payload_0_0, p851:_ -> e3433:(e3429:r1388:"std::data::result::result::err"->d532:"std.data.result.result.err" e3432:(e3430:r1389:not_found->d580:"std.io.file.io_err.not_found" e3431:r1390:__error_payload_0_0->d1576:__error_payload_0_0)); std::io::file::io_err::denied p852:d1577:__error_payload_1_0, p853:_ -> e3438:(e3434:r1391:"std::data::result::result::err"->d532:"std.data.result.result.err" e3437:(e3435:r1392:denied->d582:"std.io.file.io_err.denied" e3436:r1393:__error_payload_1_0->d1577:__error_payload_1_0)); std::io::file::io_err::invalid_path p854:d1578:__error_payload_2_0, p855:_ -> e3443:(e3439:r1394:"std::data::result::result::err"->d532:"std.data.result.result.err" e3442:(e3440:r1395:invalid_path->d584:"std.io.file.io_err.invalid_path" e3441:r1396:__error_payload_2_0->d1578:__error_payload_2_0)); std::io::file::io_err::failed p858:(p856:d1579:__error_payload_3_0, p857:d1580:__error_payload_3_1), p859:_ -> e3450:(e3444:r1397:"std::data::result::result::err"->d532:"std.data.result.result.err" e3449:(e3447:(e3445:r1398:failed->d586:"std.io.file.io_err.failed" e3446:r1399:__error_payload_3_0->d1579:__error_payload_3_0) e3448:r1400:__error_payload_3_1->d1580:__error_payload_3_1)); p860:d1581:value -> e3453:(e3451:r1401:"std::data::result::result::ok"->d531:"std.data.result.result.ok" e3452:r1402:value->d1581:value) })
  pub d601: std::io::net::request -> std::io::net::request_meta = <missing>
  pub d602: std::control::var::ref 'a std::io::net::request -> std::control::var::ref 'a std::io::net::request_meta = <missing>
  pub d603: std::io::net::request -> std::text::bytes::bytes = <missing>
  pub d604: std::control::var::ref 'a std::io::net::request -> std::control::var::ref 'a std::text::bytes::bytes = <missing>
  pub d605: std::io::net::request -> std::io::net::respond_slot = <missing>
  pub d606: std::control::var::ref 'a std::io::net::request -> std::control::var::ref 'a std::io::net::respond_slot = <missing>
  my d609: std::text::str::str -> [std::io::net::net_err] never = <missing>
  my d611: std::text::str::str -> [std::io::net::net_err] never = <missing>
  my d613: std::text::str::str -> [std::io::net::net_err] never = <missing>
  my d615: () -> [std::io::net::net_err] never = <missing>
  my d617: () -> [std::io::net::net_err] never = <missing>
  my d619: std::text::str::str -> [std::io::net::net_err] never = <missing>
  pub d620:"std.io.net.net_err.wrap": 'a [std::io::net::net_err; 'b] -> ['b] std::data::result::result('a, 'c | std::io::net::net_err) = e3652:(fn p916:d1617:action -> e3651:catch e3621:r1489:action->d1617:action { std::io::net::net_err::unreachable p917:d1618:__error_payload_0_0, p918:_ -> e3626:(e3622:r1490:"std::data::result::result::err"->d532:"std.data.result.result.err" e3625:(e3623:r1491:unreachable->d608:"std.io.net.net_err.unreachable" e3624:r1492:__error_payload_0_0->d1618:__error_payload_0_0)); std::io::net::net_err::refused p919:d1619:__error_payload_1_0, p920:_ -> e3631:(e3627:r1493:"std::data::result::result::err"->d532:"std.data.result.result.err" e3630:(e3628:r1494:refused->d610:"std.io.net.net_err.refused" e3629:r1495:__error_payload_1_0->d1619:__error_payload_1_0)); std::io::net::net_err::already_bound p921:d1620:__error_payload_2_0, p922:_ -> e3636:(e3632:r1496:"std::data::result::result::err"->d532:"std.data.result.result.err" e3635:(e3633:r1497:already_bound->d612:"std.io.net.net_err.already_bound" e3634:r1498:__error_payload_2_0->d1620:__error_payload_2_0)); std::io::net::net_err::closed p923:_, p924:_ -> e3639:(e3637:r1499:"std::data::result::result::err"->d532:"std.data.result.result.err" e3638:r1500:closed->d614:"std.io.net.net_err.closed"); std::io::net::net_err::timeout p925:_, p926:_ -> e3642:(e3640:r1501:"std::data::result::result::err"->d532:"std.data.result.result.err" e3641:r1502:timeout->d616:"std.io.net.net_err.timeout"); std::io::net::net_err::failed p927:d1621:__error_payload_5_0, p928:_ -> e3647:(e3643:r1503:"std::data::result::result::err"->d532:"std.data.result.result.err" e3646:(e3644:r1504:failed->d618:"std.io.net.net_err.failed" e3645:r1505:__error_payload_5_0->d1621:__error_payload_5_0)); p929:d1622:value -> e3650:(e3648:r1506:"std::data::result::result::ok"->d531:"std.data.result.result.ok" e3649:r1507:value->d1622:value) })
  pub d622:"std.io.net.net.listen": int -> [std::io::net::net] std::data::result::result std::io::net::listener std::io::net::net_err = <missing>
  pub d623:"std.io.net.net.port": std::io::net::listener -> [std::io::net::net] int = <missing>
  pub d625:"std.io.net.server.accept": std::io::net::listener -> [std::io::net::server] std::io::net::request = <missing>
  pub d626:"std.io.net.server.respond": (std::io::net::respond_slot, std::text::bytes::bytes) -> [std::io::net::server] std::data::result::result () std::io::net::net_err = <missing>
  pub d636: std::num::frac::frac -> int = <missing>
  pub d637: std::control::var::ref 'a std::num::frac::frac -> std::control::var::ref 'a int = <missing>
  pub d638: std::num::frac::frac -> int = <missing>
  pub d639: std::control::var::ref 'a std::num::frac::frac -> std::control::var::ref 'a int = <missing>
  pub d684: std::text::config::section -> std::text::str::str = <missing>
  pub d685: std::control::var::ref 'a std::text::config::section -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d686: std::text::config::section -> std::data::list::list (std::text::str::str, std::text::str::str) = <missing>
  pub d687: std::control::var::ref 'a std::text::config::section -> std::control::var::ref('a, std::data::list::list (std::text::str::str, std::text::str::str)) = <missing>
  pub d689: std::text::config::config -> std::data::list::list std::text::config::section = <missing>
  pub d690: std::control::var::ref 'a std::text::config::config -> std::control::var::ref('a, std::data::list::list std::text::config::section) = <missing>
  pub d711:"std.text.parse.parse.item": () -> [std::text::parse::parse 'a 'b 'c 'd] 'a = <missing>
  pub d712:"std.text.parse.parse.fail": 'a -> [std::text::parse::parse 'b 'a 'c 'd] never = <missing>
  pub d713:"std.text.parse.parse.eof": () -> [std::text::parse::parse 'a 'b 'c 'd] bool = <missing>
  pub d714:"std.text.parse.parse.pos": () -> [std::text::parse::parse 'a 'b 'c 'd] 'c = <missing>
  pub d715:"std.text.parse.parse.cut": () -> [std::text::parse::parse 'a 'b 'c 'd] () = <missing>
  pub d716:"std.text.parse.parse.snapshot": () -> [std::text::parse::parse 'a 'b 'c 'd] 'd = <missing>
  pub d717:"std.text.parse.parse.restore": 'a -> [std::text::parse::parse 'b 'c 'd 'a] () = <missing>
  pub d718:"std.text.parse.parse.advance": int -> [std::text::parse::parse 'a 'b 'c 'd] () = <missing>
  pub d725: std::text::parse::str_error -> int = <missing>
  pub d726: std::control::var::ref 'a std::text::parse::str_error -> std::control::var::ref 'a int = <missing>
  pub d727: std::text::parse::str_error -> int = <missing>
  pub d728: std::control::var::ref 'a std::text::parse::str_error -> std::control::var::ref 'a int = <missing>
  pub d729: std::text::parse::str_error -> std::data::opt::opt std::text::char::char = <missing>
  pub d730: std::control::var::ref 'a std::text::parse::str_error -> std::control::var::ref('a, std::data::opt::opt std::text::char::char) = <missing>
  pub d731: std::text::parse::str_error -> std::data::list::list std::text::str::str = <missing>
  pub d732: std::control::var::ref 'a std::text::parse::str_error -> std::control::var::ref('a, std::data::list::list std::text::str::str) = <missing>
  pub d733: std::text::parse::str_error -> std::data::list::list std::text::str::str = <missing>
  pub d734: std::control::var::ref 'a std::text::parse::str_error -> std::control::var::ref('a, std::data::list::list std::text::str::str) = <missing>
  pub d742: std::text::parse::prefix_result 'a -> 'a = <missing>
  pub d743: std::control::var::ref('a, std::text::parse::prefix_result 'b) -> std::control::var::ref 'a 'b = <missing>
  pub d744: std::text::parse::prefix_result 'a -> std::text::str::str = <missing>
  pub d745: std::control::var::ref('a, std::text::parse::prefix_result 'b) -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d747: std::text::parse::match_result 'a -> 'a = <missing>
  pub d748: std::control::var::ref('a, std::text::parse::match_result 'b) -> std::control::var::ref 'a 'b = <missing>
  pub d749: std::text::parse::match_result 'a -> int = <missing>
  pub d750: std::control::var::ref('a, std::text::parse::match_result 'b) -> std::control::var::ref 'a int = <missing>
  pub d751: std::text::parse::match_result 'a -> int = <missing>
  pub d752: std::control::var::ref('a, std::text::parse::match_result 'b) -> std::control::var::ref 'a int = <missing>
  pub d753: std::text::parse::match_result 'a -> std::text::str::str = <missing>
  pub d754: std::control::var::ref('a, std::text::parse::match_result 'b) -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d798: std::text::str::lines -> std::text::str::str = <missing>
  pub d799: std::control::var::ref 'a std::text::str::lines -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d802: std::text::str::ref_lines 'a -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d803: std::control::var::ref('a, std::text::str::ref_lines 'b) -> std::control::var::ref('a, std::control::var::ref 'b std::text::str::str) = <missing>
  pub d898: std::text::yumark::yumark_algebra 'a -> () -> 'a = <missing>
  pub d899: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, () ['[]] -> ['[]] 'b) = <missing>
  pub d900: std::text::yumark::yumark_algebra 'a -> 'a -> 'a -> 'a = <missing>
  pub d901: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b ['[]] -> ['[]] 'b) = <missing>
  pub d902: std::text::yumark::yumark_algebra 'a -> std::text::str::str -> 'a = <missing>
  pub d903: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, std::text::str::str ['[]] -> ['[]] 'b) = <missing>
  pub d904: std::text::yumark::yumark_algebra 'a -> 'a -> 'a = <missing>
  pub d905: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  pub d906: std::text::yumark::yumark_algebra 'a -> std::text::str::str -> int -> 'a -> 'a = <missing>
  pub d907: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, std::text::str::str ['[]] -> ['[]] int ['[]] -> ['[]] 'b ['[]] -> ['[]] 'b) = <missing>
  pub d908: std::text::yumark::yumark_algebra 'a -> std::text::str::str -> 'a = <missing>
  pub d909: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, std::text::str::str ['[]] -> ['[]] 'b) = <missing>
  pub d910: std::text::yumark::yumark_algebra 'a -> std::text::str::str -> 'a -> 'a = <missing>
  pub d911: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, std::text::str::str ['[]] -> ['[]] 'b ['[]] -> ['[]] 'b) = <missing>
  pub d912: std::text::yumark::yumark_algebra 'a -> bool -> 'a -> 'a = <missing>
  pub d913: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, bool ['[]] -> ['[]] 'b ['[]] -> ['[]] 'b) = <missing>
  pub d914: std::text::yumark::yumark_algebra 'a -> std::text::str::str -> 'a -> 'a = <missing>
  pub d915: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, std::text::str::str ['[]] -> ['[]] 'b ['[]] -> ['[]] 'b) = <missing>
  pub d916: std::text::yumark::yumark_algebra 'a -> 'a -> 'a = <missing>
  pub d917: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  pub d918: std::text::yumark::yumark_algebra 'a -> std::text::str::str -> std::text::str::str -> 'a = <missing>
  pub d919: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, std::text::str::str ['[]] -> ['[]] std::text::str::str ['[]] -> ['[]] 'b) = <missing>
  pub d920: std::text::yumark::yumark_algebra 'a -> 'a -> 'a = <missing>
  pub d921: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  pub d922: std::text::yumark::yumark_algebra 'a -> 'a -> 'a = <missing>
  pub d923: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  pub d924: std::text::yumark::yumark_algebra 'a -> 'a -> 'a = <missing>
  pub d925: std::control::var::ref('a, std::text::yumark::yumark_algebra 'b) -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  pub d927: std::text::yumark::html_format -> std::text::str::str = <missing>
  pub d928: std::control::var::ref 'a std::text::yumark::html_format -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d930: std::text::yumark::markdown_format -> std::text::str::str = <missing>
  pub d931: std::control::var::ref 'a std::text::yumark::markdown_format -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d933: std::text::yumark::html_node -> std::text::str::str = <missing>
  pub d934: std::control::var::ref 'a std::text::yumark::html_node -> std::control::var::ref 'a std::text::str::str = <missing>
  pub d935: std::text::yumark::html_node -> std::text::str::str = <missing>
  pub d936: std::control::var::ref 'a std::text::yumark::html_node -> std::control::var::ref 'a std::text::str::str = <missing>
  d997:"std.control.flow.loop.redo.break": () -> [std::control::flow::loop::redo] never = <missing>
  d1001:"std.control.flow.label_loop.next.break": () -> [std::control::flow::label_loop::next] never = <missing>
  d1005:"std.control.flow.loop.next.break": () -> [std::control::flow::loop::next] never = <missing>
  d1009:"std.control.flow.label_loop.redo.break": () -> [std::control::flow::label_loop::redo] never = <missing>
  d1013:x arg
  d1014:f arg
  d1015:g arg
  d1016:x arg
  d1017:x arg
  d1018:y arg
  d1019:x arg
  d1020:y arg
  d1021:x arg
  d1022:y arg
  d1023:x arg
  d1024:y arg
  d1025:x arg
  d1026:x arg
  d1027:x arg
  d1028:y arg
  d1029:x arg
  d1030:y arg
  d1031:x arg
  d1032:y arg
  d1033:x arg
  d1034:y arg
  d1035:x arg
  d1036:y arg
  d1037:x arg
  d1038:y arg
  d1039:x arg
  d1040:y arg
  d1041:x arg
  d1042:y arg
  d1043:x arg
  d1044:y arg
  d1045:xs arg
  d1046:ys arg
  d1047:left arg
  d1048:right arg
  d1049:expected arg
  d1050:actual arg
  d1051:value arg
  d1052:t arg
  d1053:delta arg
  d1054:t arg
  d1055:delta arg
  d1056:later arg
  d1057:earlier arg
  d1058:x arg
  d1059:y arg
  d1060:x arg
  d1061:y arg
  d1062:count arg
  d1063:count arg
  d1064:count arg
  d1065:count arg
  d1066:count arg
  d1067:count arg
  d1068:count arg
  d1069:x arg
  d1070:y arg
  my d1071:q: 'a = e279:(e278:(e276:r99:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e275:r98:x->d1069:x) e277:r100:y->d1070:y)
  my d1072:r: 'a = e284:(e283:(e281:r102:"#op:infix:mod"->d420:"std.core.ops.#op:infix:mod" e280:r101:x->d1069:x) e282:r103:y->d1070:y)
  d1073:x arg
  d1074:y arg
  d1075:days_since_epoch arg
  my d1076:z: 'a = e322:(e321:(e319:r118:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e318:r117:days_since_epoch->d1075:days_since_epoch) e320:719468)
  my d1077:era: 'a = e327:(e325:(e323:r119:floor_div->d139:"std.time.floor_div" e324:r120:z->d1076:z) e326:146097)
  my d1078:doe: 'a = e336:(e335:(e329:r122:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e328:r121:z->d1076:z) e334:(e333:(e331:r124:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e330:r123:era->d1077:era) e332:146097))
  my d1079:yoe: 'a = e365:(e364:(e362:r135:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e361:(e360:(e354:r132:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e353:(e352:(e346:r129:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e345:(e344:(e338:r126:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e337:r125:doe->d1078:doe) e343:(e342:(e340:r128:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e339:r127:doe->d1078:doe) e341:1460))) e351:(e350:(e348:r131:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e347:r130:doe->d1078:doe) e349:36524))) e359:(e358:(e356:r134:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e355:r133:doe->d1078:doe) e357:146096))) e363:365)
  my d1080:year: 'a = e374:(e373:(e367:r137:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e366:r136:yoe->d1079:yoe) e372:(e371:(e369:r139:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e368:r138:era->d1077:era) e370:400))
  my d1081:doy: 'a = e399:(e398:(e376:r141:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e375:r140:doe->d1078:doe) e397:(e396:(e390:r147:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e389:(e388:(e382:r144:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e381:(e380:(e378:r142:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e377:365) e379:r143:yoe->d1079:yoe)) e387:(e386:(e384:r146:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e383:r145:yoe->d1079:yoe) e385:4))) e395:(e394:(e392:r149:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e391:r148:yoe->d1079:yoe) e393:100)))
  my d1082:mp: 'a = e412:(e411:(e409:r153:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e408:(e407:(e405:r152:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e404:(e403:(e401:r150:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e400:5) e402:r151:doy->d1081:doy)) e406:2)) e410:153)
  my d1083:day: 'a = e433:(e432:(e430:r160:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e429:(e428:(e414:r155:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e413:r154:doy->d1081:doy) e427:(e426:(e424:r159:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e423:(e422:(e420:r158:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e419:(e418:(e416:r156:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e415:153) e417:r157:mp->d1082:mp)) e421:2)) e425:5))) e431:1)
  my d1084:month: 'a = e449:(e448:(e435:r162:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e434:r161:mp->d1082:mp) e447:case e442:(e441:r165:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e440:(e439:(e437:r164:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e436:r163:mp->d1082:mp) e438:10)) { p74:true -> e443:3; p75:false -> e446:(e444:r166:"#op:prefix:-"->d414:"std.core.ops.#op:prefix:-" e445:9) })
  d1085:n arg
  d1086:n arg
  d1087:n arg
  d1088:n arg
  d1089:text arg
  my d1090:len: 'a = e613:(e611:r229:"std::text::str::len"->d788:"std.text.str.len" e612:r230:text->d1089:text)
  my d1091:end: 'a = e626:(e625:(e623:r236:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e622:r235:len->d1090:len) e624:1)
  d1092:nanos_in_second arg
  d1093:x arg
  my d1094:seconds: 'a = e679:(e677:(e674:r255:floor_div->d139:"std.time.floor_div" e676:(e675:r256:x->d1093:x.s12.epoch_nanos->d120)) e678:1000000000)
  my d1095:nanos_in_second: 'a = e685:(e683:(e680:r257:floor_mod->d140:"std.time.floor_mod" e682:(e681:r258:x->d1093:x.s13.epoch_nanos->d120)) e684:1000000000)
  my d1096:days: 'a = e690:(e688:(e686:r259:floor_div->d139:"std.time.floor_div" e687:r260:seconds->d1094:seconds) e689:86400)
  my d1097:second_of_day: 'a = e695:(e693:(e691:r261:floor_mod->d140:"std.time.floor_mod" e692:r262:seconds->d1094:seconds) e694:86400)
  d1098:year arg
  d1099:month arg
  d1100:day arg
  my d1101:hour: 'a = e703:(e702:(e700:r266:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e699:r265:second_of_day->d1097:second_of_day) e701:3600)
  my d1102:minute: 'a = e712:(e711:(e709:r269:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e708:(e707:(e705:r268:"#op:infix:mod"->d420:"std.core.ops.#op:infix:mod" e704:r267:second_of_day->d1097:second_of_day) e706:3600)) e710:60)
  my d1103:second: 'a = e717:(e716:(e714:r271:"#op:infix:mod"->d420:"std.core.ops.#op:infix:mod" e713:r270:second_of_day->d1097:second_of_day) e715:60)
  my d1104:date: 'a = e740:(e739:(e735:r279:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e734:(e733:(e731:r278:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e730:(e729:(e725:r275:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e724:(e723:(e721:r274:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e720:(e718:r272:pad4->d144:"std.time.pad4" e719:r273:year->d1098:year)) e722:"-")) e728:(e726:r276:pad2->d142:"std.time.pad2" e727:r277:month->d1099:month))) e732:"-")) e738:(e736:r280:pad2->d142:"std.time.pad2" e737:r281:day->d1100:day))
  my d1105:clock: 'a = e763:(e762:(e758:r289:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e757:(e756:(e754:r288:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e753:(e752:(e748:r285:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e747:(e746:(e744:r284:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e743:(e741:r282:pad2->d142:"std.time.pad2" e742:r283:hour->d1101:hour)) e745:":")) e751:(e749:r286:pad2->d142:"std.time.pad2" e750:r287:minute->d1102:minute))) e755:":")) e761:(e759:r290:pad2->d142:"std.time.pad2" e760:r291:second->d1103:second))
  d1106:x arg
  d1107:y arg
  d1108:x arg
  d1109:y arg
  d1110:x arg
  d1111:y arg
  d1112:x arg
  d1113:y arg
  d1114:x arg
  d1115:y arg
  d1116:x arg
  d1117:y arg
  d1118:x arg
  d1119:y arg
  d1120:x arg
  d1121:y arg
  d1122:x arg
  d1123:y arg
  d1124:x arg
  d1125:y arg
  d1126:x arg
  d1127:x arg
  d1128:x arg
  d1129:x arg
  d1130:y arg
  d1131:x arg
  d1132:y arg
  d1133:x arg
  d1134:a arg
  d1135:a arg
  d1136:x arg
  d1137:a arg
  d1138:a arg
  d1139:a arg
  d1140:x arg
  d1141:x arg
  d1142:x arg
  d1143:x arg
  d1144:x arg
  d1145:x arg
  d1146:xs arg
  d1147:f arg
  d1148:x arg
  my d1149:loop: any -> ['a] () = e1012:(fn p184:d1150:b -> e1011:case e981:(e980:r364:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e979:r363:b->d1150:b) { p197:true -> e1009:block { e1007:(e982:r365:loop->d1149:loop e1006:(e983:r366:"redo::judge"->d998:"std.control.flow.loop.redo.judge" e1005:catch e986:(e984:r367:f->d1147:f e985:r368:x->d1148:x) { std::control::flow::loop::last p185:_, p186:_ -> e989:(e987:r369:"last::break"->d188:"std.control.flow.loop.last.break" e988:()); std::control::flow::loop::next p187:_, p188:_ -> e992:(e990:r370:"next::break"->d1005:"std.control.flow.loop.next.break" e991:()); std::control::flow::loop::redo p189:_, p190:_ -> e995:(e993:r371:"redo::break"->d997:"std.control.flow.loop.redo.break" e994:()); std::control::flow::loop::last p191:_, p192:_ -> e998:(e996:r372:"last::break"->d188:"std.control.flow.loop.last.break" e997:()); std::control::flow::loop::next p193:_, p194:_ -> e1001:(e999:r373:"next::break"->d1005:"std.control.flow.loop.next.break" e1000:()); std::control::flow::loop::redo p195:_, p196:_ -> e1004:(e1002:r374:"redo::break"->d997:"std.control.flow.loop.redo.break" e1003:()) })); e1008:() }; p198:false -> e1010:() })
  d1150:b arg
  d1151:x arg
  d1152:x arg
  d1153:x arg
  d1154:x arg
  d1155:x arg
  d1156:x arg
  d1157:xs arg
  d1158:f arg
  d1159:x arg
  my d1160:loop: any -> ['a] () = e1103:(fn p228:d1161:b -> e1102:case e1070:(e1069:r390:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1068:r389:b->d1161:b) { p241:true -> e1100:block { e1098:(e1071:r391:loop->d1160:loop e1097:(e1072:r392:"redo::judge"->d1010:"std.control.flow.label_loop.redo.judge" e1096:catch e1077:(e1075:(e1073:r393:f->d1158:f e1074:r394:control_label->d211:"std.control.flow.label_loop.control_label") e1076:r395:x->d1159:x) { std::control::flow::label_loop::last p229:_, p230:_ -> e1080:(e1078:r396:"last::break"->d208:"std.control.flow.label_loop.last.break" e1079:()); std::control::flow::label_loop::next p231:_, p232:_ -> e1083:(e1081:r397:"next::break"->d1001:"std.control.flow.label_loop.next.break" e1082:()); std::control::flow::label_loop::redo p233:_, p234:_ -> e1086:(e1084:r398:"redo::break"->d1009:"std.control.flow.label_loop.redo.break" e1085:()); std::control::flow::loop::last p235:_, p236:_ -> e1089:(e1087:r399:"last::break"->d208:"std.control.flow.label_loop.last.break" e1088:()); std::control::flow::loop::next p237:_, p238:_ -> e1092:(e1090:r400:"next::break"->d1001:"std.control.flow.label_loop.next.break" e1091:()); std::control::flow::loop::redo p239:_, p240:_ -> e1095:(e1093:r401:"redo::break"->d1009:"std.control.flow.label_loop.redo.break" e1094:()) })); e1099:() }; p242:false -> e1101:() })
  d1161:b arg
  d1162:xs arg
  d1163:x arg
  d1164:xs arg
  d1165:x arg
  d1166:x arg
  d1167:k arg
  d1168:k arg
  d1169:b arg
  d1170:xs arg
  d1171:xs arg
  d1172:b arg
  d1173:xs arg
  d1174:x arg
  d1175:x arg
  d1176:k arg
  d1177:v arg
  d1178:x arg
  my d1179:loop: any [std::control::nondet::nondet; 'a] -> any -> 'b -> ['a] 'b = e1309:(fn p282:d1180:x -> e1308:(fn p283:d1181:queue -> e1307:(fn p284:d1182:res -> e1306:catch e1250:r444:x->d1180:x { std::control::nondet::nondet::branch p285:_, p286:d1183:k -> e1265:(e1263:(e1255:(e1251:r445:loop->d1179:loop e1254:(e1252:r446:k->d1183:k e1253:true)) e1262:(e1258:(e1256:r447:"std::data::list::append"->d499:"std.data.list.append" e1257:r448:queue->d1181:queue) e1261:(e1260:builtin_op::list_singleton e1259:r449:k->d1183:k))) e1264:r450:res->d1182:res); std::control::nondet::nondet::reject p287:_, p288:_ -> e1279:case e1268:(e1266:r451:"std::data::list::uncons"->d494:"std.data.list.uncons" e1267:r452:queue->d1181:queue) { p289:r453:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil" -> e1269:r454:res->d1182:res; p293:r455:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just"(p292:(p290:d1184:k, p291:d1185:queue)) -> e1278:(e1276:(e1274:(e1270:r456:loop->d1179:loop e1273:(e1271:r457:k->d1184:k e1272:false)) e1275:r458:queue->d1185:queue) e1277:r459:res->d1182:res) }; p294:d1186:v -> e1305:case e1282:(e1280:r460:"std::data::list::uncons"->d494:"std.data.list.uncons" e1281:r461:queue->d1181:queue) { p295:r462:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil" -> e1289:(e1285:(e1283:r463:"std::data::list::append"->d499:"std.data.list.append" e1284:r464:res->d1182:res) e1288:(e1287:builtin_op::list_singleton e1286:r465:v->d1186:v)); p299:r466:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just"(p298:(p296:d1187:k, p297:d1188:queue)) -> e1304:(e1296:(e1294:(e1290:r467:loop->d1179:loop e1293:(e1291:r468:k->d1187:k e1292:false)) e1295:r469:queue->d1188:queue) e1303:(e1299:(e1297:r470:"std::data::list::append"->d499:"std.data.list.append" e1298:r471:res->d1182:res) e1302:(e1301:builtin_op::list_singleton e1300:r472:v->d1186:v))) } })))
  d1180:x arg
  d1181:queue arg
  d1182:res arg
  d1183:k arg
  d1184:k arg
  d1185:queue arg
  d1186:v arg
  d1187:k arg
  d1188:queue arg
  d1189:x arg
  my d1190:loop: any [std::control::nondet::nondet; 'a] -> any -> ['a] never = e1356:(fn p302:d1191:x -> e1355:(fn p303:d1192:queue -> e1354:catch e1325:r475:x->d1191:x { std::control::nondet::nondet::branch p304:_, p305:d1193:k -> e1338:(e1330:(e1326:r476:loop->d1190:loop e1329:(e1327:r477:k->d1193:k e1328:true)) e1337:(e1333:(e1331:r478:"std::data::list::append"->d499:"std.data.list.append" e1332:r479:queue->d1192:queue) e1336:(e1335:builtin_op::list_singleton e1334:r480:k->d1193:k))); std::control::nondet::nondet::reject p306:_, p307:_ -> e1350:case e1341:(e1339:r481:"std::data::list::uncons"->d494:"std.data.list.uncons" e1340:r482:queue->d1192:queue) { p308:r483:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil" -> e1342:r484:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil"; p312:r485:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just"(p311:(p309:d1194:k, p310:d1195:queue)) -> e1349:(e1347:(e1343:r486:loop->d1190:loop e1346:(e1344:r487:k->d1194:k e1345:false)) e1348:r488:queue->d1195:queue) }; p313:d1196:v -> e1353:(e1351:r489:"std::data::opt::opt::just"->d506:"std.data.opt.opt.just" e1352:r490:v->d1196:v) }))
  d1191:x arg
  d1192:queue arg
  d1193:k arg
  d1194:k arg
  d1195:queue arg
  d1196:v arg
  d1197:x arg
  d1198:x arg
  d1199:x arg
  d1200:f arg
  d1201:r arg
  d1202:f arg
  my d1203:loop: 'a [[['b & 'c] & 'd] & [std::control::var::ref_update('e | 'f | 'g | 'h | 'i <: 'e & 'f & 'g & 'i & 'h); [[['j & 'k] & 'l] & 'm] & 'n]] -> ['p#0[AllExcept([std::control::var::ref_update 'e])], 'k, 'j, 'n, 'o, 'm, 'l] 'a = e1394:(fn p321:d1204:x -> e1393:catch e1385:r501:x->d1204:x { std::control::var::ref_update::update p322:d1205:v, p323:d1206:k -> e1392:(e1386:r502:loop->d1203:loop e1391:(e1387:r503:k->d1206:k e1390:(e1388:r504:f->d1202:f e1389:r505:v->d1205:v))) })
  d1204:x arg
  d1205:v arg
  d1206:k arg
  d1207:v arg
  d1208:x arg
  d1209:k arg
  d1210:v arg
  d1211:k arg
  d1212:x arg
  d1213:y arg
  d1214:x arg
  d1215:y arg
  d1216:x arg
  d1217:y arg
  d1218:x arg
  d1219:y arg
  d1220:x arg
  d1221:y arg
  d1222:x arg
  d1223:y arg
  d1224:x arg
  d1225:y arg
  d1226:x arg
  d1227:y arg
  d1228:x arg
  d1229:y arg
  d1230:x arg
  d1231:y arg
  d1232:x arg
  d1233:y arg
  d1234:x arg
  d1235:y arg
  d1236:x arg
  d1237:y arg
  d1238:x arg
  d1239:y arg
  d1240:x arg
  d1241:y arg
  d1242:x arg
  d1243:y arg
  d1244:x arg
  d1245:y arg
  d1246:x arg
  d1247:y arg
  d1248:xs arg
  d1249:ys arg
  d1250:x arg
  d1251:y arg
  d1252:xl arg
  d1253:xr arg
  d1254:yl arg
  d1255:yr arg
  d1256:p arg
  d1257:x arg
  d1258:x arg
  d1259:x arg
  d1260:a arg
  d1261:a arg
  d1262:a arg
  d1263:text arg
  d1264:count arg
  d1265:spec arg
  d1266:fill arg
  d1267:spec arg
  d1268:body arg
  d1269:limit arg
  d1270:body arg
  d1271:spec arg
  d1272:head arg
  d1273:body arg
  d1274:spec arg
  d1275:head arg
  d1276:body arg
  my d1277:clipped: 'a = e1745:(e1743:(e1741:r658:format_body->d329:"std.core.fmt.format_body" e1742:r659:spec->d1274:spec) e1744:r660:body->d1276:body)
  my d1278:body_prefix: 'a = e1752:(e1750:(e1748:(e1746:r661:format_sign_prefix->d331:"std.core.fmt.format_sign_prefix" e1747:r662:spec->d1274:spec) e1749:r663:head->d1275:head) e1751:r664:clipped->d1277:clipped)
  d1279:width arg
  my d1280:clipped: 'a = e1764:(e1762:(e1760:r669:format_body->d329:"std.core.fmt.format_body" e1761:r670:spec->d1274:spec) e1763:r671:body->d1276:body)
  my d1281:body_prefix: 'a = e1771:(e1769:(e1767:(e1765:r672:format_sign_prefix->d331:"std.core.fmt.format_sign_prefix" e1766:r673:spec->d1274:spec) e1768:r674:head->d1275:head) e1770:r675:clipped->d1280:clipped)
  my d1282:text: 'a = e1776:(e1775:(e1773:r677:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1772:r676:body_prefix->d1281:body_prefix) e1774:r678:clipped->d1280:clipped)
  my d1283:missing: 'a = e1782:(e1781:(e1778:r680:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e1777:r679:width->d1279:width) e1780:(e1779:r681:text->d1282:text.s56.len->d840:"std.text.str.str.len"))
  my d1284:fill: 'a = e1793:(e1791:r686:format_fill->d328:"std.core.fmt.format_fill" e1792:r687:spec->d1274:spec)
  my d1285:left: 'a = e1809:(e1808:(e1806:r699:"#op:infix:div"->d419:"std.core.ops.#op:infix:div" e1805:r698:missing->d1283:missing) e1807:2)
  my d1286:right: 'a = e1814:(e1813:(e1811:r701:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e1810:r700:missing->d1283:missing) e1812:r702:left->d1285:left)
  my d1287:padding: 'a = e1842:(e1840:(e1838:r714:repeat->d327:"std.core.fmt.repeat" e1839:r715:fill->d1284:fill) e1841:r716:missing->d1283:missing)
  my d1288:padded_prefix: 'a = e1847:(e1846:(e1844:r718:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e1843:r717:body_prefix->d1281:body_prefix) e1845:r719:padding->d1287:padding)
  d1289:spec arg
  d1290:value arg
  d1291:spec arg
  d1292:value arg
  d1293:spec arg
  d1294:value arg
  my d1295:head: 'a | std::text::str::str = e1902:case e1899:(e1898:r735:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1897:(e1896:r734:spec->d1293:spec.s61.alternate->d316)) { p459:true -> e1900:"0x"; p460:false -> e1901:"" }
  d1296:spec arg
  d1297:value arg
  my d1298:head: 'a | std::text::str::str = e1920:case e1917:(e1916:r741:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e1915:(e1914:r740:spec->d1296:spec.s63.alternate->d316)) { p464:true -> e1918:"0X"; p465:false -> e1919:"" }
  d1299:x arg
  d1300:x arg
  d1301:x arg
  d1302:x arg
  d1303:x arg
  d1304:x arg
  d1305:x arg
  d1306:x arg
  d1307:x arg
  d1308:x arg
  d1309:x arg
  d1310:xs arg
  d1311:item arg
  d1312:left arg
  d1313:right arg
  my d1314:left_text: 'a | 'b | 'c = e1976:(e1974:r767:show_list_items->d359:"std.core.fmt.show_list_items" e1975:r768:left->d1312:left)
  my d1315:right_text: 'a | 'b | 'c = e1979:(e1977:r769:show_list_items->d359:"std.core.fmt.show_list_items" e1978:r770:right->d1313:right)
  d1316:xs arg
  d1317:value arg
  d1318:inner arg
  d1319:value arg
  d1320:inner arg
  d1321:inner arg
  d1322:value arg
  d1323:a arg
  d1324:b arg
  d1325:value arg
  d1326:a arg
  d1327:b arg
  d1328:c arg
  d1329:value arg
  d1330:a arg
  d1331:b arg
  d1332:c arg
  d1333:d arg
  d1334:value arg
  d1335:a arg
  d1336:b arg
  d1337:c arg
  d1338:d arg
  d1339:e arg
  d1340:x arg
  d1341:x arg
  d1342:x arg
  d1343:xs arg
  d1344:item arg
  d1345:left arg
  d1346:right arg
  my d1347:left_text: 'a | 'b | 'c = e2204:(e2202:r850:debug_list_items->d380:"std.core.fmt.debug_list_items" e2203:r851:left->d1345:left)
  my d1348:right_text: 'a | 'b | 'c = e2207:(e2205:r852:debug_list_items->d380:"std.core.fmt.debug_list_items" e2206:r853:right->d1346:right)
  d1349:xs arg
  d1350:value arg
  d1351:inner arg
  d1352:value arg
  d1353:inner arg
  d1354:inner arg
  d1355:value arg
  d1356:a arg
  d1357:b arg
  d1358:value arg
  d1359:a arg
  d1360:b arg
  d1361:c arg
  d1362:value arg
  d1363:a arg
  d1364:b arg
  d1365:c arg
  d1366:d arg
  d1367:value arg
  d1368:a arg
  d1369:b arg
  d1370:c arg
  d1371:d arg
  d1372:e arg
  d1373:e arg
  d1374:x arg
  d1375:x arg
  d1376:y arg
  d1377:x arg
  d1378:y arg
  d1379:x arg
  d1380:y arg
  d1381:x arg
  d1382:y arg
  d1383:x arg
  d1384:y arg
  d1385:x arg
  d1386:y arg
  d1387:x arg
  d1388:y arg
  d1389:x arg
  d1390:y arg
  d1391:x arg
  d1392:y arg
  d1393:x arg
  d1394:y arg
  d1395:a arg
  d1396:b arg
  d1397:a arg
  d1398:b arg
  d1399:label arg
  d1400:label arg
  d1401:label arg
  d1402:s arg
  d1403:xs arg
  d1404:s arg
  d1405:xs arg
  d1406:b arg
  d1407:x arg
  d1408:container arg
  d1409:f arg
  my d1410:nil: never = e2593:r991:"std::data::opt::opt::nil"->d505:"std.data.opt.opt.nil"
  d1411:x arg
  d1412:container arg
  d1413:target arg
  my d1414:found: 'a = e2625:(e2618:(e2617:r1001:container->d1412:container.s121.find=>d452:"std.data.fold.Fold.find") e2624:(fn p619:d1415:x -> e2623:(e2622:(e2620:r1003:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e2619:r1002:x->d1415:x) e2621:r1004:target->d1413:target)))
  d1415:x arg
  d1416:container arg
  d1417:xs arg
  d1418:ys arg
  d1419:xs arg
  d1420:f arg
  d1421:xs arg
  d1422:pred arg
  d1423:xs arg
  d1424:r arg
  d1425:ys arg
  d1426:xs arg
  d1427:separator arg
  d1428:xs arg
  d1429:xs arg
  d1430:xs arg
  d1431:xs arg
  d1432:xs arg
  d1433:"&xs" arg
  d1434:x arg
  d1435:xs arg
  d1436:i arg
  d1437:xs arg
  d1438:r arg
  d1439:r arg
  d1440:i arg
  my d1441:loop: 'a [std::control::var::ref_update 'b; 'c] -> [std::control::var::ref_update 'd, 'c] 'a = e2761:(fn p651:d1442:x -> e2760:catch e2732:r1049:x->d1442:x { std::control::var::ref_update::update p652:d1443:old, p653:d1444:k -> e2759:block { let my p654:d1445:new_item = e2739:(e2733:r1050:"ref_update::update"->d236:"std.control.var.ref_update.update" e2738:(e2736:(e2734:r1051:"std::data::list::index_raw"->d482:"std.data.list.index_raw" e2735:r1052:old->d1443:old) e2737:r1053:i->d1440:i)); e2758:(e2740:r1054:loop->d1441:loop e2757:(e2741:r1055:k->d1444:k e2756:(e2752:(e2746:(e2744:(e2742:r1056:"std::data::list::splice_raw"->d486:"std.data.list.splice_raw" e2743:r1057:old->d1443:old) e2745:r1058:i->d1440:i) e2751:(e2750:(e2748:r1060:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e2747:r1059:i->d1440:i) e2749:1)) e2755:(e2754:builtin_op::list_singleton e2753:r1061:new_item->d1445:new_item)))) } })
  d1442:x arg
  d1443:old arg
  d1444:k arg
  my d1445:new_item: 'a = e2739:(e2733:r1050:"ref_update::update"->d236:"std.control.var.ref_update.update" e2738:(e2736:(e2734:r1051:"std::data::list::index_raw"->d482:"std.data.list.index_raw" e2735:r1052:old->d1443:old) e2737:r1053:i->d1440:i))
  d1446:xs arg
  d1447:z arg
  d1448:f arg
  d1449:x arg
  d1450:left arg
  d1451:right arg
  d1452:xs arg
  d1453:z arg
  d1454:f arg
  d1455:x arg
  d1456:xs arg
  d1457:x arg
  d1458:xs arg
  d1459:xs arg
  my d1460:n: 'a = e2845:(e2843:r1092:"std::data::list::len"->d481:"std.data.list.len" e2844:r1093:xs->d1459:xs)
  d1461:xs arg
  d1462:z arg
  d1463:f arg
  d1464:xs arg
  d1465:x arg
  d1466:left arg
  d1467:right arg
  d1468:xs arg
  d1469:f arg
  d1470:x arg
  d1471:left arg
  d1472:right arg
  d1473:xs arg
  d1474:pred arg
  d1475:x arg
  d1476:left arg
  d1477:right arg
  d1478:xs arg
  d1479:ys arg
  d1480:xs arg
  d1481:head arg
  d1482:xs arg
  d1483:head arg
  d1484:tail arg
  d1485:xs arg
  d1486:x arg
  d1487:y arg
  d1488:y arg
  d1489:l arg
  d1490:r arg
  d1491:ll arg
  d1492:lr arg
  d1493:rl arg
  d1494:rr arg
  d1495:xs arg
  d1496:x arg
  d1497:xs arg
  d1498:l arg
  d1499:r arg
  d1500:start arg
  d1501:end arg
  d1502:start arg
  d1503:end arg
  d1504:start arg
  d1505:end arg
  d1506:start arg
  d1507:end arg
  d1508:start arg
  d1509:start arg
  d1510:end arg
  d1511:end arg
  d1512:r arg
  d1513:start arg
  d1514:r arg
  d1515:end arg
  d1516:b arg
  d1517:x arg
  d1518:x arg
  d1519:b arg
  d1520:x arg
  d1521:x arg
  d1522:f arg
  d1523:i arg
  d1524:end arg
  d1525:acc arg
  d1526:f arg
  d1527:i arg
  d1528:acc arg
  d1529:r arg
  d1530:z arg
  d1531:f arg
  d1532:start arg
  d1533:start arg
  d1534:end arg
  d1535:r arg
  d1536:f arg
  d1537:r arg
  d1538:f arg
  d1539:r arg
  d1540:fallback arg
  d1541:r arg
  d1542:f arg
  d1543:value arg
  d1544:err arg
  d1545:r arg
  d1546:f arg
  d1547:value arg
  d1548:err arg
  d1549:r arg
  d1550:fallback arg
  d1551:value arg
  d1552:value arg
  d1553:value arg
  d1554:value arg
  d1555:value arg
  d1556:value arg
  d1557:value arg
  d1558:value arg
  my d1559 mod {
    d1560:"io_err::throw#error": std::io::file::io_err -> [std::io::file::io_err] never = e3387:(fn p829:d1561:error -> e3386:case e3371:r1356:error->d1561:error { p831:r1357:not_found->d580:"std.io.file.io_err.not_found"(p830:d1562:__error_payload_0_0) -> e3374:(e3372:r1358:"std::io::file::io_err::not_found"->d581 e3373:r1359:__error_payload_0_0->d1562:__error_payload_0_0); p833:r1360:denied->d582:"std.io.file.io_err.denied"(p832:d1563:__error_payload_1_0) -> e3377:(e3375:r1361:"std::io::file::io_err::denied"->d583 e3376:r1362:__error_payload_1_0->d1563:__error_payload_1_0); p835:r1363:invalid_path->d584:"std.io.file.io_err.invalid_path"(p834:d1564:__error_payload_2_0) -> e3380:(e3378:r1364:"std::io::file::io_err::invalid_path"->d585 e3379:r1365:__error_payload_2_0->d1564:__error_payload_2_0); p838:r1366:failed->d586:"std.io.file.io_err.failed"(p836:d1565:__error_payload_3_0, p837:d1566:__error_payload_3_1) -> e3385:(e3381:r1367:"std::io::file::io_err::failed"->d587 e3384:(e3382:r1368:__error_payload_3_0->d1565:__error_payload_3_0, e3383:r1369:__error_payload_3_1->d1566:__error_payload_3_1)) })
  }
  d1561:error arg
  d1562:__error_payload_0_0 arg
  d1563:__error_payload_1_0 arg
  d1564:__error_payload_2_0 arg
  d1565:__error_payload_3_0 arg
  d1566:__error_payload_3_1 arg
  my d1567 mod {
    d1568:"io_err::show#error": std::io::file::io_err -> std::text::str::str = e3427:(fn p839:d1569:__error_value -> e3426:case e3388:r1370:__error_value->d1569:__error_value { p841:r1371:not_found->d580:"std.io.file.io_err.not_found"(p840:d1570:__error_payload_0_0) -> e3394:(e3393:(e3390:r1372:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3389:"not_found: ") e3392:(e3391:r1373:__error_payload_0_0->d1570:__error_payload_0_0.s129.show=>d321:"std.core.fmt.Display.show")); p843:r1374:denied->d582:"std.io.file.io_err.denied"(p842:d1571:__error_payload_1_0) -> e3400:(e3399:(e3396:r1375:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3395:"denied: ") e3398:(e3397:r1376:__error_payload_1_0->d1571:__error_payload_1_0.s130.show=>d321:"std.core.fmt.Display.show")); p845:r1377:invalid_path->d584:"std.io.file.io_err.invalid_path"(p844:d1572:__error_payload_2_0) -> e3406:(e3405:(e3402:r1378:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3401:"invalid_path: ") e3404:(e3403:r1379:__error_payload_2_0->d1572:__error_payload_2_0.s131.show=>d321:"std.core.fmt.Display.show")); p848:r1380:failed->d586:"std.io.file.io_err.failed"(p846:d1573:__error_payload_3_0, p847:d1574:__error_payload_3_1) -> e3425:(e3424:(e3422:r1386:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3421:(e3420:(e3417:r1384:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3416:(e3415:(e3413:r1383:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3412:(e3411:(e3408:r1381:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3407:"failed(") e3410:(e3409:r1382:__error_payload_3_0->d1573:__error_payload_3_0.s132.show=>d321:"std.core.fmt.Display.show"))) e3414:", ")) e3419:(e3418:r1385:__error_payload_3_1->d1574:__error_payload_3_1.s133.show=>d321:"std.core.fmt.Display.show"))) e3423:")") })
  }
  d1569:__error_value arg
  d1570:__error_payload_0_0 arg
  d1571:__error_payload_1_0 arg
  d1572:__error_payload_2_0 arg
  d1573:__error_payload_3_0 arg
  d1574:__error_payload_3_1 arg
  d1575:action arg
  d1576:__error_payload_0_0 arg
  d1577:__error_payload_1_0 arg
  d1578:__error_payload_2_0 arg
  d1579:__error_payload_3_0 arg
  d1580:__error_payload_3_1 arg
  d1581:value arg
  d1582:result arg
  d1583:value arg
  d1584:err arg
  d1585:path arg
  d1586:path arg
  d1587:path arg
  d1588:path arg
  d1589:path arg
  d1590:r arg
  d1591:path arg
  d1592:r arg
  d1593:text arg
  d1594:path arg
  d1595:path arg
  d1596:text arg
  d1597:path arg
  d1598:path arg
  d1599:f arg
  my d1600:initial: 'a = e3554:(e3550:r1447:unwrap_io->d589:"std.io.file.unwrap_io" e3553:(e3551:r1448:"file::load"->d571:"std.io.file.file.load" e3552:r1449:path->d1598:path))
  d1601:result arg
  d1602:final arg
  my d1603 mod {
    d1604:"net_err::throw#error": std::io::net::net_err -> [std::io::net::net_err] never = e3591:(fn p894:d1605:error -> e3590:case e3571:r1457:error->d1605:error { p896:r1458:unreachable->d608:"std.io.net.net_err.unreachable"(p895:d1606:__error_payload_0_0) -> e3574:(e3572:r1459:"std::io::net::net_err::unreachable"->d609 e3573:r1460:__error_payload_0_0->d1606:__error_payload_0_0); p898:r1461:refused->d610:"std.io.net.net_err.refused"(p897:d1607:__error_payload_1_0) -> e3577:(e3575:r1462:"std::io::net::net_err::refused"->d611 e3576:r1463:__error_payload_1_0->d1607:__error_payload_1_0); p900:r1464:already_bound->d612:"std.io.net.net_err.already_bound"(p899:d1608:__error_payload_2_0) -> e3580:(e3578:r1465:"std::io::net::net_err::already_bound"->d613 e3579:r1466:__error_payload_2_0->d1608:__error_payload_2_0); p901:r1467:closed->d614:"std.io.net.net_err.closed" -> e3583:(e3581:r1468:"std::io::net::net_err::closed"->d615 e3582:()); p902:r1469:timeout->d616:"std.io.net.net_err.timeout" -> e3586:(e3584:r1470:"std::io::net::net_err::timeout"->d617 e3585:()); p904:r1471:failed->d618:"std.io.net.net_err.failed"(p903:d1609:__error_payload_5_0) -> e3589:(e3587:r1472:"std::io::net::net_err::failed"->d619 e3588:r1473:__error_payload_5_0->d1609:__error_payload_5_0) })
  }
  d1605:error arg
  d1606:__error_payload_0_0 arg
  d1607:__error_payload_1_0 arg
  d1608:__error_payload_2_0 arg
  d1609:__error_payload_5_0 arg
  my d1610 mod {
    d1611:"net_err::show#error": std::io::net::net_err -> std::text::str::str = e3620:(fn p905:d1612:__error_value -> e3619:case e3592:r1474:__error_value->d1612:__error_value { p907:r1475:unreachable->d608:"std.io.net.net_err.unreachable"(p906:d1613:__error_payload_0_0) -> e3598:(e3597:(e3594:r1476:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3593:"unreachable: ") e3596:(e3595:r1477:__error_payload_0_0->d1613:__error_payload_0_0.s138.show=>d321:"std.core.fmt.Display.show")); p909:r1478:refused->d610:"std.io.net.net_err.refused"(p908:d1614:__error_payload_1_0) -> e3604:(e3603:(e3600:r1479:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3599:"refused: ") e3602:(e3601:r1480:__error_payload_1_0->d1614:__error_payload_1_0.s139.show=>d321:"std.core.fmt.Display.show")); p911:r1481:already_bound->d612:"std.io.net.net_err.already_bound"(p910:d1615:__error_payload_2_0) -> e3610:(e3609:(e3606:r1482:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3605:"already_bound: ") e3608:(e3607:r1483:__error_payload_2_0->d1615:__error_payload_2_0.s140.show=>d321:"std.core.fmt.Display.show")); p912:r1484:closed->d614:"std.io.net.net_err.closed" -> e3611:"closed"; p913:r1485:timeout->d616:"std.io.net.net_err.timeout" -> e3612:"timeout"; p915:r1486:failed->d618:"std.io.net.net_err.failed"(p914:d1616:__error_payload_5_0) -> e3618:(e3617:(e3614:r1487:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e3613:"failed: ") e3616:(e3615:r1488:__error_payload_5_0->d1616:__error_payload_5_0.s141.show=>d321:"std.core.fmt.Display.show")) })
  }
  d1612:__error_value arg
  d1613:__error_payload_0_0 arg
  d1614:__error_payload_1_0 arg
  d1615:__error_payload_2_0 arg
  d1616:__error_payload_5_0 arg
  d1617:action arg
  d1618:__error_payload_0_0 arg
  d1619:__error_payload_1_0 arg
  d1620:__error_payload_2_0 arg
  d1621:__error_payload_5_0 arg
  d1622:value arg
  d1623:result arg
  d1624:value arg
  d1625:err arg
  d1626:port arg
  d1627:port arg
  my d1628:listener: 'a = e3667:(e3665:r1516:listen->d628:"std.io.net.listen" e3666:r1517:port->d1627:port)
  d1629:l arg
  d1630:l arg
  d1631:req arg
  d1632:res arg
  d1633:x arg
  d1634:a arg
  d1635:b arg
  d1636:a arg
  d1637:b arg
  d1638:n arg
  d1639:d arg
  my d1640:divisor: 'a = e3742:(e3740:(e3738:r1548:gcd->d642:"std.num.frac.gcd" e3739:r1549:n->d1638:n) e3741:r1550:d->d1639:d)
  my d1641:normalized_num: 'a = e3747:(e3745:(e3743:r1551:"std::int::div"->d55:"std.int.div" e3744:r1552:n->d1638:n) e3746:r1553:divisor->d1640:divisor)
  my d1642:normalized_den: 'a = e3752:(e3750:(e3748:r1554:"std::int::div"->d55:"std.int.div" e3749:r1555:d->d1639:d) e3751:r1556:divisor->d1640:divisor)
  d1643:x arg
  d1644:y arg
  d1645:x arg
  d1646:y arg
  d1647:x arg
  d1648:y arg
  d1649:x arg
  d1650:y arg
  d1651:x arg
  d1652:y arg
  d1653:x arg
  d1654:y arg
  d1655:x arg
  d1656:y arg
  d1657:x arg
  d1658:y arg
  d1659:x arg
  d1660:y arg
  d1661:x arg
  d1662:x arg
  d1663:b arg
  d1664:b arg
  d1665:b arg
  d1666:other arg
  d1667:b arg
  d1668:b arg
  d1669:b arg
  d1670:b arg
  d1671:text arg
  d1672:b arg
  d1673:i arg
  d1674:b arg
  d1675:r arg
  d1676:c arg
  d1677:c arg
  d1678:c arg
  d1679:c arg
  d1680:c arg
  d1681:section_name arg
  d1682:key arg
  d1683:c arg
  d1684:name arg
  d1685:c arg
  d1686:sections arg
  d1687:name arg
  d1688:head arg
  d1689:tail arg
  d1690:head arg
  d1691:tail arg
  d1692:c arg
  d1693:name arg
  d1694:sections arg
  d1695:section_name arg
  d1696:entry arg
  d1697:head arg
  d1698:tail arg
  d1699:head arg
  d1700:tail arg
  d1701:c arg
  d1702:section_name arg
  d1703:entry arg
  d1704:clean arg
  d1705:pair arg
  d1706:key arg
  d1707:value arg
  d1708:state arg
  d1709:line arg
  d1710:cfg arg
  d1711:current_section arg
  my d1712:clean = e4258:(e4257:r1745:line->d1709:line.s191.trim->d828:"std.text.str.str.trim")
  d1713:name arg
  d1714:pair arg
  d1715:source arg
  d1716:cfg arg
  d1717:entries arg
  d1718:key arg
  d1719:candidate arg
  d1720:value arg
  d1721:rest arg
  d1722:rest arg
  d1723:entries arg
  d1724:key arg
  d1725:sections arg
  d1726:section_name arg
  d1727:key arg
  d1728:head arg
  d1729:rest arg
  d1730:rest arg
  d1731:c arg
  d1732:section_name arg
  d1733:key arg
  d1734:path arg
  d1735:e arg
  d1736:f arg
  d1737:u arg
  d1738:l arg
  d1739:c arg
  d1740:label arg
  d1741:l arg
  d1742:c arg
  d1743:e arg
  d1744:label arg
  d1745:input arg
  d1746:count arg
  d1747:line arg
  d1748:column arg
  my d1749:data: 'a = e4518:(e4516:r1858:"std::text::str::to_bytes"->d796:"std.text.str.to_bytes" e4517:r1859:input->d1745:input)
  d1750:data arg
  d1751:count arg
  d1752:i arg
  d1753:line arg
  d1754:column arg
  my d1755:chunk_end: 'a | 'b | 'c | int = e4581:case e4574:(e4573:r1883:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4572:(e4571:(e4569:r1881:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e4568:(e4567:(e4565:r1880:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4564:r1879:i->d1752:i) e4566:1024)) e4570:r1882:count->d1751:count)) { p1126:true -> e4579:(e4578:(e4576:r1885:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4575:r1884:i->d1752:i) e4577:1024); p1127:false -> e4580:r1886:count->d1751:count }
  d1756:line arg
  d1757:column arg
  d1758:data arg
  d1759:count arg
  d1760:i arg
  d1761:line arg
  d1762:column arg
  d1763:input arg
  d1764:count arg
  d1765:i arg
  d1766:line arg
  d1767:column arg
  my d1768:chunk_end: 'a | 'b | 'c | int = e4699:case e4692:(e4691:r1933:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4690:(e4689:(e4687:r1931:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e4686:(e4685:(e4683:r1930:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4682:r1929:i->d1765:i) e4684:1024)) e4688:r1932:count->d1764:count)) { p1150:true -> e4697:(e4696:(e4694:r1935:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e4693:r1934:i->d1765:i) e4695:1024); p1151:false -> e4698:r1936:count->d1764:count }
  d1769:line arg
  d1770:column arg
  d1771:input arg
  d1772:count arg
  d1773:i arg
  d1774:line arg
  d1775:column arg
  my d1776:item: 'a = e4744:(e4742:(e4740:r1955:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e4741:r1956:input->d1771:input) e4743:r1957:i->d1773:i)
  d1777:input arg
  d1778:line arg
  d1779:column arg
  d1780:parser arg
  d1781:k arg
  d1782:k arg
  my d1783:item: 'a = e4823:(e4821:(e4819:r1985:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e4820:r1986:input->d1777:input) e4822:0)
  my d1784:rest: 'a = e4830:(e4826:(e4824:r1987:"std::text::str::index_range"->d792:"std.text.str.index_range" e4825:r1988:input->d1777:input) e4829:(e4827:r1989:"std::data::range::from_excluded"->d518:"std.data.range.from_excluded" e4828:0))
  d1785:e arg
  d1786:k arg
  d1787:k arg
  d1788:k arg
  d1789:k arg
  d1790:input arg
  d1791:line arg
  d1792:column arg
  d1793:k arg
  d1794:count arg
  d1795:k arg
  my d1796:input_len = e4935:(e4934:r2038:input->d1777:input.s223.len->d840:"std.text.str.str.len")
  my d1797:end: 'a | 'b | 'c | int = e4945:case e4942:(e4941:r2042:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e4940:(e4939:(e4937:r2040:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e4936:r2039:count->d1794:count) e4938:r2041:input_len->d1796:input_len)) { p1206:true -> e4943:r2043:count->d1794:count; p1207:false -> e4944:r2044:input_len->d1796:input_len }
  my d1798:rest: 'a = e4952:(e4950:(e4948:(e4946:r2045:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e4947:r2046:input->d1777:input) e4949:r2047:end->d1797:end) e4951:r2048:input_len->d1796:input_len)
  d1799:line arg
  d1800:column arg
  d1801:v arg
  d1802:input arg
  d1803:line arg
  d1804:column arg
  d1805:parser arg
  d1806:k arg
  d1807:k arg
  my d1808:item: 'a = e5012:(e5010:(e5008:r2070:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e5009:r2071:input->d1802:input) e5011:0)
  my d1809:rest: 'a = e5019:(e5015:(e5013:r2072:"std::text::str::index_range"->d792:"std.text.str.index_range" e5014:r2073:input->d1802:input) e5018:(e5016:r2074:"std::data::range::from_excluded"->d518:"std.data.range.from_excluded" e5017:0))
  d1810:e arg
  d1811:k arg
  d1812:k arg
  d1813:k arg
  d1814:k arg
  d1815:input arg
  d1816:line arg
  d1817:column arg
  d1818:k arg
  d1819:count arg
  d1820:k arg
  my d1821:input_len = e5124:(e5123:r2123:input->d1802:input.s227.len->d840:"std.text.str.str.len")
  my d1822:end: 'a | 'b | 'c | int = e5134:case e5131:(e5130:r2127:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e5129:(e5128:(e5126:r2125:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e5125:r2124:count->d1819:count) e5127:r2126:input_len->d1821:input_len)) { p1248:true -> e5132:r2128:count->d1819:count; p1249:false -> e5133:r2129:input_len->d1821:input_len }
  my d1823:rest: 'a = e5141:(e5139:(e5137:(e5135:r2130:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5136:r2131:input->d1802:input) e5138:r2132:end->d1822:end) e5140:r2133:input_len->d1821:input_len)
  d1824:line arg
  d1825:column arg
  d1826:v arg
  d1827:source arg
  d1828:parser arg
  d1829:source arg
  d1830:start arg
  d1831:parser arg
  my d1832:rest: 'a = e5206:(e5203:(e5201:(e5199:r2155:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5200:r2156:source->d1829:source) e5202:r2157:start->d1830:start) e5205:(e5204:r2158:source->d1829:source.s229.len->d840:"std.text.str.str.len"))
  d1833:found arg
  my d1834:consumed: 'a = e5229:(e5228:(e5224:r2166:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e5223:(e5222:r2165:rest->d1832:rest.s230.len->d840:"std.text.str.str.len")) e5227:(e5226:(e5225:r2167:found->d1833:found.s231.rest->d744).s232.len->d840:"std.text.str.str.len"))
  d1835:source arg
  d1836:parser arg
  d1837:source arg
  d1838:parser arg
  d1839:replacement arg
  d1840:found arg
  d1841:source arg
  d1842:parser arg
  d1843:replacement arg
  my d1844:loop: int -> std::text::str::str -> std::text::str::str = e5385:(fn p1282:d1845:start -> e5384:(fn p1283:d1846:out -> e5383:case e5346:(e5344:(e5342:(e5340:r2216:find_from->d763:"std.text.parse.find_from" e5341:r2217:source->d1841:source) e5343:r2218:start->d1845:start) e5345:r2219:parser->d1842:parser) { p1285:r2220:just->d506:"std.data.opt.opt.just"(p1284:d1847:found) -> e5370:(e5350:(e5347:r2221:loop->d1844:loop e5349:(e5348:r2222:found->d1847:found.s238.end->d751)) e5369:(e5364:(e5351:r2223:"std::text::str::concat"->d786:"std.text.str.concat" e5363:(e5354:(e5352:r2224:"std::text::str::concat"->d786:"std.text.str.concat" e5353:r2225:out->d1846:out) e5362:(e5359:(e5357:(e5355:r2226:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5356:r2227:source->d1841:source) e5358:r2228:start->d1845:start) e5361:(e5360:r2229:found->d1847:found.s239.start->d749)))) e5368:(e5365:r2230:replacement->d1843:replacement e5367:(e5366:r2231:found->d1847:found.s240.value->d747)))); p1286:r2232:nil->d505:"std.data.opt.opt.nil" -> e5382:(e5373:(e5371:r2233:"std::text::str::concat"->d786:"std.text.str.concat" e5372:r2234:out->d1846:out) e5381:(e5378:(e5376:(e5374:r2235:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5375:r2236:source->d1841:source) e5377:r2237:start->d1845:start) e5380:(e5379:r2238:source->d1841:source.s241.len->d840:"std.text.str.str.len"))) }))
  d1845:start arg
  d1846:out arg
  d1847:found arg
  d1848:source arg
  d1849:parser arg
  d1850:replacement arg
  d1851:found arg
  d1852:source arg
  d1853:parser arg
  d1854:replacement arg
  my d1855:loop: int -> std::text::str::str -> std::text::str::str = e5473:(fn p1297:d1856:start -> e5472:(fn p1298:d1857:out -> e5471:case e5437:(e5435:(e5433:(e5431:r2256:find_from->d763:"std.text.parse.find_from" e5432:r2257:source->d1852:source) e5434:r2258:start->d1856:start) e5436:r2259:parser->d1853:parser) { p1300:r2260:just->d506:"std.data.opt.opt.just"(p1299:d1858:found) -> e5458:(e5441:(e5438:r2261:loop->d1855:loop e5440:(e5439:r2262:found->d1858:found.s245.end->d751)) e5457:(e5455:(e5442:r2263:"std::text::str::concat"->d786:"std.text.str.concat" e5454:(e5445:(e5443:r2264:"std::text::str::concat"->d786:"std.text.str.concat" e5444:r2265:out->d1857:out) e5453:(e5450:(e5448:(e5446:r2266:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5447:r2267:source->d1852:source) e5449:r2268:start->d1856:start) e5452:(e5451:r2269:found->d1858:found.s246.start->d749)))) e5456:r2270:replacement->d1854:replacement)); p1301:r2271:nil->d505:"std.data.opt.opt.nil" -> e5470:(e5461:(e5459:r2272:"std::text::str::concat"->d786:"std.text.str.concat" e5460:r2273:out->d1857:out) e5469:(e5466:(e5464:(e5462:r2274:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e5463:r2275:source->d1852:source) e5465:r2276:start->d1856:start) e5468:(e5467:r2277:source->d1852:source.s247.len->d840:"std.text.str.str.len"))) }))
  d1856:start arg
  d1857:out arg
  d1858:found arg
  d1859:parser arg
  d1860:replacement arg
  d1861:source arg
  d1862:p arg
  d1863:q arg
  my d1864:snap: 'a = e5495:(e5493:r2283:"parse::snapshot"->d716:"std.text.parse.parse.snapshot" e5494:())
  d1865:k arg
  d1866:e arg
  d1867:e1 arg
  d1868:e2 arg
  d1869:p arg
  my d1870:pos: 'a = e5531:(e5529:r2295:"parse::pos"->d714:"std.text.parse.parse.pos" e5530:())
  my d1871:item: 'a = e5546:(e5544:r2302:"parse::item"->d711:"std.text.parse.parse.item" e5545:())
  d1872:expected arg
  d1873:input arg
  d1874:input arg
  d1875:p arg
  d1876:p arg
  d1877:p arg
  d1878:p arg
  d1879:label_text arg
  d1880:e arg
  d1881:input arg
  my d1882:found: 'a = e5707:(e5705:(e5703:r2353:"std::text::str::word_prefix_at"->d881:"std.text.str.word_prefix_at" e5704:r2354:input->d1881:input) e5706:0)
  d1883:p arg
  d1884:b arg
  d1885:p arg
  d1886:ls arg
  d1887:i arg
  my d1888:line_range: 'a = e5771:(e5769:(e5763:r2372:"std::text::str::line_range"->d790:"std.text.str.line_range" e5768:(e5766:(e5765:(e5764:r2373:ls->d1886:ls.s257.source->d802).s258.get->d238) e5767:())) e5770:r2374:i->d1887:i)
  my d1889:loop: 'a [std::control::var::ref_update 'b; 'c] -> [std::control::var::ref_update 'd, 'c] 'a = e5810:(fn p1372:d1890:x -> e5809:catch e5783:r2378:x->d1890:x { std::control::var::ref_update::update p1373:d1891:old, p1374:d1892:k -> e5808:block { let my p1375:d1893:line_range = e5788:(e5786:(e5784:r2379:"std::text::str::line_range"->d790:"std.text.str.line_range" e5785:r2380:old->d1891:old) e5787:r2381:i->d1887:i); e5807:block { let my p1376:d1894:new_item = e5795:(e5789:r2382:"ref_update::update"->d236:"std.control.var.ref_update.update" e5794:(e5792:(e5790:r2383:"std::text::str::index_range"->d792:"std.text.str.index_range" e5791:r2384:old->d1891:old) e5793:r2385:line_range->d1893:line_range)); e5806:(e5796:r2386:loop->d1889:loop e5805:(e5797:r2387:k->d1892:k e5804:(e5802:(e5800:(e5798:r2388:"std::text::str::splice"->d794:"std.text.str.splice" e5799:r2389:old->d1891:old) e5801:r2390:line_range->d1893:line_range) e5803:r2391:new_item->d1894:new_item))) } } })
  d1890:x arg
  d1891:old arg
  d1892:k arg
  my d1893:line_range: 'a = e5788:(e5786:(e5784:r2379:"std::text::str::line_range"->d790:"std.text.str.line_range" e5785:r2380:old->d1891:old) e5787:r2381:i->d1887:i)
  my d1894:new_item: 'a = e5795:(e5789:r2382:"ref_update::update"->d236:"std.control.var.ref_update.update" e5794:(e5792:(e5790:r2383:"std::text::str::index_range"->d792:"std.text.str.index_range" e5791:r2384:old->d1891:old) e5793:r2385:line_range->d1893:line_range))
  d1895:source arg
  d1896:source arg
  d1897:ls arg
  d1898:i arg
  my d1899:line_range: 'a = e5839:(e5837:(e5834:r2398:"std::text::str::line_range"->d790:"std.text.str.line_range" e5836:(e5835:r2399:ls->d1897:ls.s263.source->d798)) e5838:r2400:i->d1898:i)
  d1900:ls arg
  d1901:i arg
  my d1902:line_range: 'a = e5858:(e5856:(e5850:r2405:"std::text::str::line_range"->d790:"std.text.str.line_range" e5855:(e5853:(e5852:(e5851:r2406:ls->d1900:ls.s265.source->d802).s266.get->d238) e5854:())) e5857:r2407:i->d1901:i)
  my d1903:loop: 'a [std::control::var::ref_update 'b; 'c] -> [std::control::var::ref_update 'd, 'c] 'a = e5897:(fn p1388:d1904:x -> e5896:catch e5870:r2411:x->d1904:x { std::control::var::ref_update::update p1389:d1905:old, p1390:d1906:k -> e5895:block { let my p1391:d1907:line_range = e5875:(e5873:(e5871:r2412:"std::text::str::line_range"->d790:"std.text.str.line_range" e5872:r2413:old->d1905:old) e5874:r2414:i->d1901:i); e5894:block { let my p1392:d1908:new_item = e5882:(e5876:r2415:"ref_update::update"->d236:"std.control.var.ref_update.update" e5881:(e5879:(e5877:r2416:"std::text::str::index_range"->d792:"std.text.str.index_range" e5878:r2417:old->d1905:old) e5880:r2418:line_range->d1907:line_range)); e5893:(e5883:r2419:loop->d1903:loop e5892:(e5884:r2420:k->d1906:k e5891:(e5889:(e5887:(e5885:r2421:"std::text::str::splice"->d794:"std.text.str.splice" e5886:r2422:old->d1905:old) e5888:r2423:line_range->d1907:line_range) e5890:r2424:new_item->d1908:new_item))) } } })
  d1904:x arg
  d1905:old arg
  d1906:k arg
  my d1907:line_range: 'a = e5875:(e5873:(e5871:r2412:"std::text::str::line_range"->d790:"std.text.str.line_range" e5872:r2413:old->d1905:old) e5874:r2414:i->d1901:i)
  my d1908:new_item: 'a = e5882:(e5876:r2415:"ref_update::update"->d236:"std.control.var.ref_update.update" e5881:(e5879:(e5877:r2416:"std::text::str::index_range"->d792:"std.text.str.index_range" e5878:r2417:old->d1905:old) e5880:r2418:line_range->d1907:line_range))
  d1909:ls arg
  d1910:i arg
  d1911:end arg
  d1912:acc arg
  d1913:f arg
  d1914:ls arg
  d1915:i arg
  d1916:end arg
  d1917:acc arg
  d1918:f arg
  d1919:ls arg
  d1920:z arg
  d1921:f arg
  d1922:ls arg
  d1923:z arg
  d1924:f arg
  d1925:s arg
  d1926:r arg
  d1927:insert arg
  d1928:s arg
  d1929:needle arg
  d1930:s arg
  d1931:needle arg
  d1932:s arg
  d1933:prefix arg
  d1934:s arg
  d1935:suffix arg
  d1936:s arg
  d1937:separator arg
  d1938:s arg
  d1939:separator arg
  d1940:s arg
  d1941:from arg
  d1942:to arg
  d1943:s arg
  d1944:from arg
  d1945:to arg
  d1946:s arg
  d1947:s arg
  d1948:s arg
  d1949:"&r" arg
  d1950:pattern arg
  d1951:replacement arg
  d1952:s arg
  d1953:"&r" arg
  d1954:pattern arg
  d1955:replacement arg
  d1956:s arg
  d1957:"&r" arg
  d1958:pattern arg
  d1959:replacement arg
  d1960:s arg
  d1961:"&r" arg
  d1962:range arg
  d1963:replacement arg
  d1964:s arg
  d1965:"&r" arg
  d1966:s arg
  d1967:"&r" arg
  d1968:s arg
  d1969:"&r" arg
  d1970:s arg
  d1971:s arg
  d1972:count arg
  d1973:s arg
  d1974:s arg
  d1975:s arg
  d1976:s arg
  d1977:"&s" arg
  d1978:s arg
  d1979:s arg
  d1980:s arg
  d1981:s arg
  d1982:s arg
  d1983:source arg
  d1984:source_len arg
  d1985:needle arg
  d1986:needle_len arg
  d1987:start arg
  my d1988:end: 'a = e6239:(e6237:(e6235:r2558:"std::int::add"->d52:"std.int.add" e6236:r2559:start->d1987:start) e6238:r2560:needle_len->d1986:needle_len)
  d1989:source arg
  d1990:needle arg
  d1991:start arg
  d1992:source arg
  d1993:source_len arg
  d1994:needle arg
  d1995:needle_len arg
  d1996:start arg
  d1997:source arg
  d1998:source_len arg
  d1999:needle arg
  d2000:needle_len arg
  d2001:limit arg
  d2002:i arg
  d2003:source arg
  d2004:needle arg
  d2005:start arg
  d2006:source arg
  d2007:needle arg
  d2008:i arg
  d2009:source arg
  d2010:needle arg
  d2011:source arg
  d2012:prefix arg
  d2013:source arg
  d2014:suffix arg
  my d2015:source_len: 'a = e6431:(e6429:r2644:"std::text::str::len"->d788:"std.text.str.len" e6430:r2645:source->d2013:source)
  my d2016:suffix_len: 'a = e6434:(e6432:r2646:"std::text::str::len"->d788:"std.text.str.len" e6433:r2647:suffix->d2014:suffix)
  d2017:source arg
  d2018:separator arg
  my d2019:source_len: 'a = e6462:(e6460:r2658:"std::text::str::len"->d788:"std.text.str.len" e6461:r2659:source->d2017:source)
  my d2020:separator_len: 'a = e6465:(e6463:r2660:"std::text::str::len"->d788:"std.text.str.len" e6464:r2661:separator->d2018:separator)
  d2021:parts arg
  d2022:source arg
  d2023:source_len arg
  d2024:separator arg
  d2025:separator_len arg
  d2026:source arg
  d2027:source_len arg
  d2028:separator arg
  d2029:separator_len arg
  d2030:start arg
  d2031:out arg
  d2032:i arg
  my d2033:piece: 'a = e6565:(e6563:(e6561:(e6559:r2705:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e6560:r2706:source->d2026:source) e6562:r2707:start->d2030:start) e6564:r2708:i->d2032:i)
  d2034:source arg
  my d2035:data: 'a = e6610:(e6608:r2728:"std::text::str::to_bytes"->d796:"std.text.str.to_bytes" e6609:r2729:source->d2034:source)
  my d2036:end: 'a = e6613:(e6611:r2730:"std::text::bytes::len"->d655:"std.text.bytes.len" e6612:r2731:data->d2035:data)
  my d2037:chunk_count: 'a = e6622:(e6620:(e6614:r2732:"std::int::div"->d55:"std.int.div" e6619:(e6618:(e6616:r2734:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e6615:r2733:end->d2036:end) e6617:1023)) e6621:1024)
  my d2038:scan: 'a = e6647:(e6635:(e6628:(e6627:(e6626:(e6624:r2735:"#op:infix:..<"->d410:"std.core.ops.#op:infix:..<" e6623:0) e6625:r2736:chunk_count->d2037:chunk_count).s283.fold=>d451:"std.data.fold.Fold.fold") e6634:(e6629:0, e6632:(e6630:builtin_op::list_empty e6631:()), e6633:true)) e6646:(fn p1552:d2039:state -> e6645:(fn p1553:d2040:chunk -> e6644:(e6642:(e6640:(e6638:(e6636:r2737:split_newline_bytes_chunk->d863:"std.text.str.split_newline_bytes_chunk" e6637:r2738:data->d2035:data) e6639:r2739:end->d2036:end) e6641:r2740:state->d2039:state) e6643:r2741:chunk->d2040:chunk))))
  d2039:state arg
  d2040:chunk arg
  d2041:start arg
  d2042:out arg
  d2043:data arg
  d2044:end arg
  d2045:state arg
  d2046:chunk arg
  my d2047:i: 'a = e6681:(e6680:(e6678:r2757:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e6677:r2756:chunk->d2046:chunk) e6679:1024)
  my d2048:chunk_end: 'a | 'b | 'c | int = e6699:case e6692:(e6691:r2762:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6690:(e6689:(e6687:r2760:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e6686:(e6685:(e6683:r2759:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e6682:r2758:i->d2047:i) e6684:1024)) e6688:r2761:end->d2044:end)) { p1570:true -> e6697:(e6696:(e6694:r2764:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e6693:r2763:i->d2047:i) e6695:1024); p1571:false -> e6698:r2765:end->d2044:end }
  d2049:state arg
  d2050:j arg
  d2051:data arg
  d2052:state arg
  d2053:i arg
  d2054:start arg
  d2055:out arg
  my d2056:piece: 'a = e6741:(e6731:r2778:"std::text::bytes::to_utf8_lossy"->d668:"std.text.bytes.to_utf8_lossy" e6740:(e6734:(e6732:r2779:"std::text::bytes::index_range"->d659:"std.text.bytes.index_range" e6733:r2780:data->d2051:data) e6739:(e6737:(e6735:r2781:"std::data::range::range"->d513:"std.data.range.range" e6736:r2782:start->d2054:start) e6738:r2783:i->d2053:i)))
  d2057:source arg
  d2058:separator arg
  my d2059:source_len: 'a = e6768:(e6766:r2793:"std::text::str::len"->d788:"std.text.str.len" e6767:r2794:source->d2057:source)
  my d2060:separator_len: 'a = e6771:(e6769:r2795:"std::text::str::len"->d788:"std.text.str.len" e6770:r2796:separator->d2058:separator)
  d2061:i arg
  d2062:parts arg
  d2063:separator arg
  d2064:out arg
  d2065:part arg
  d2066:rest arg
  d2067:parts arg
  d2068:separator arg
  d2069:head arg
  d2070:tail arg
  d2071:source arg
  d2072:i arg
  d2073:source arg
  d2074:end arg
  my d2075:previous: 'a = e6891:(e6889:(e6887:r2855:"std::int::sub"->d53:"std.int.sub" e6888:r2856:end->d2074:end) e6890:1)
  d2076:source arg
  d2077:source arg
  d2078:source arg
  my d2079:start: 'a = e6945:(e6943:(e6941:r2879:trim_start_index->d868:"std.text.str.trim_start_index" e6942:r2880:source->d2078:source) e6944:0)
  my d2080:end: 'a = e6952:(e6948:(e6946:r2881:trim_end_index->d869:"std.text.str.trim_end_index" e6947:r2882:source->d2078:source) e6951:(e6949:r2883:"std::text::str::len"->d788:"std.text.str.len" e6950:r2884:source->d2078:source))
  d2081:source arg
  d2082:count arg
  my d2083:loop: int -> std::text::str::str -> std::text::str::str = e6995:(fn p1631:d2084:i -> e6994:(fn p1632:d2085:out -> e6993:case e6978:(e6977:r2896:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e6976:(e6974:(e6972:r2893:"std::int::lt"->d48:"std.int.lt" e6973:r2894:i->d2084:i) e6975:r2895:count->d2082:count)) { p1633:true -> e6991:(e6985:(e6979:r2897:loop->d2083:loop e6984:(e6982:(e6980:r2898:"std::int::add"->d52:"std.int.add" e6981:r2899:i->d2084:i) e6983:1)) e6990:(e6988:(e6986:r2900:"std::text::str::concat"->d786:"std.text.str.concat" e6987:r2901:out->d2085:out) e6989:r2902:source->d2081:source)); p1634:false -> e6992:r2903:out->d2085:out }))
  d2084:i arg
  d2085:out arg
  d2086:item arg
  d2087:source arg
  d2088:start arg
  d2089:i arg
  d2090:acc arg
  d2091:digit arg
  d2092:source arg
  d2093:value arg
  d2094:source arg
  d2095:from arg
  d2096:to arg
  d2097:i arg
  d2098:source arg
  d2099:from arg
  d2100:to arg
  d2101:source arg
  d2102:from arg
  d2103:to arg
  my d2104:loop: int -> std::text::str::str -> std::text::str::str = e7282:(fn p1684:d2105:start -> e7281:(fn p1685:d2106:out -> e7280:case e7239:(e7237:(e7235:(e7233:r3003:find_at->d853:"std.text.str.find_at" e7234:r3004:source->d2101:source) e7236:r3005:from->d2102:from) e7238:r3006:start->d2105:start) { p1687:r3007:just->d506:"std.data.opt.opt.just"(p1686:d2107:i) -> e7266:block { let my p1688:d2108:prefix = e7246:(e7244:(e7242:(e7240:r3008:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e7241:r3009:source->d2101:source) e7243:r3010:start->d2105:start) e7245:r3011:i->d2107:i); e7265:(e7255:(e7247:r3012:loop->d2104:loop e7254:(e7250:(e7248:r3013:"std::int::add"->d52:"std.int.add" e7249:r3014:i->d2107:i) e7253:(e7251:r3015:"std::text::str::len"->d788:"std.text.str.len" e7252:r3016:from->d2102:from))) e7264:(e7262:(e7256:r3017:"std::text::str::concat"->d786:"std.text.str.concat" e7261:(e7259:(e7257:r3018:"std::text::str::concat"->d786:"std.text.str.concat" e7258:r3019:out->d2106:out) e7260:r3020:prefix->d2108:prefix)) e7263:r3021:to->d2103:to)) }; p1689:r3022:nil->d505:"std.data.opt.opt.nil" -> e7279:(e7269:(e7267:r3023:"std::text::str::concat"->d786:"std.text.str.concat" e7268:r3024:out->d2106:out) e7278:(e7274:(e7272:(e7270:r3025:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e7271:r3026:source->d2101:source) e7273:r3027:start->d2105:start) e7277:(e7275:r3028:"std::text::str::len"->d788:"std.text.str.len" e7276:r3029:source->d2101:source))) }))
  d2105:start arg
  d2106:out arg
  d2107:i arg
  my d2108:prefix: 'a = e7246:(e7244:(e7242:(e7240:r3008:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e7241:r3009:source->d2101:source) e7243:r3010:start->d2105:start) e7245:r3011:i->d2107:i)
  d2109:source arg
  d2110:start arg
  my d2111:source_len: 'a = e7296:(e7294:r3031:"std::text::str::len"->d788:"std.text.str.len" e7295:r3032:source->d2109:source)
  my d2112:remaining: 'a = e7301:(e7300:(e7298:r3034:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e7297:r3033:source_len->d2111:source_len) e7299:r3035:start->d2110:start)
  my d2113:loop: int -> std::text::str::str = e7350:(fn p1697:d2114:i -> e7349:case e7315:(e7314:r3043:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7313:(e7312:(e7310:r3041:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e7309:r3040:i->d2114:i) e7311:r3042:source_len->d2111:source_len)) { p1701:true -> e7341:block { let my p1698:d2115:item = e7320:(e7318:(e7316:r3044:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e7317:r3045:source->d2109:source) e7319:r3046:i->d2114:i); e7340:case e7325:(e7324:r3049:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7323:(e7321:r3047:"std::text::char::is_word"->d677:"std.text.char.is_word" e7322:r3048:item->d2115:item)) { p1699:true -> e7332:(e7326:r3050:loop->d2113:loop e7331:(e7330:(e7328:r3052:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7327:r3051:i->d2114:i) e7329:1)); p1700:false -> e7339:(e7337:(e7335:(e7333:r3053:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e7334:r3054:source->d2109:source) e7336:r3055:start->d2110:start) e7338:r3056:i->d2114:i) } }; p1702:false -> e7348:(e7346:(e7344:(e7342:r3057:"std::text::str::index_range_raw"->d793:"std.text.str.index_range_raw" e7343:r3058:source->d2109:source) e7345:r3059:start->d2110:start) e7347:r3060:i->d2114:i) })
  d2114:i arg
  my d2115:item: 'a = e7320:(e7318:(e7316:r3044:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e7317:r3045:source->d2109:source) e7319:r3046:i->d2114:i)
  my d2116:end: 'a = e7374:case e7361:(e7360:r3065:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7359:(e7358:(e7356:r3064:"#op:infix:=="->d421:"std.core.ops.#op:infix:==" e7355:r3063:start->d2110:start) e7357:0)) { p1704:true -> e7366:(e7364:(e7362:r3066:word_prefix_ascii_or_slow_end->d882:"std.text.str.word_prefix_ascii_or_slow_end" e7363:r3067:source->d2109:source) e7365:r3068:source_len->d2111:source_len); p1705:false -> e7373:(e7371:(e7369:(e7367:r3069:word_prefix_slow_end->d886:"std.text.str.word_prefix_slow_end" e7368:r3070:source->d2109:source) e7370:r3071:source_len->d2111:source_len) e7372:r3072:start->d2110:start) }
  d2117:source arg
  d2118:source_len arg
  my d2119:data: 'a = e7390:(e7388:r3077:"std::text::str::to_bytes"->d796:"std.text.str.to_bytes" e7389:r3078:source->d2117:source)
  my d2120:data_len: 'a = e7393:(e7391:r3079:"std::text::bytes::len"->d655:"std.text.bytes.len" e7392:r3080:data->d2119:data)
  my d2121:chunk_count: 'a = e7402:(e7400:(e7394:r3081:"std::int::div"->d55:"std.int.div" e7399:(e7398:(e7396:r3083:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7395:r3082:data_len->d2120:data_len) e7397:1023)) e7401:1024)
  my d2122:scan: 'a = e7424:(e7412:(e7408:(e7407:(e7406:(e7404:r3084:"#op:infix:..<"->d410:"std.core.ops.#op:infix:..<" e7403:0) e7405:r3085:chunk_count->d2121:chunk_count).s285.fold=>d451:"std.data.fold.Fold.fold") e7411:(e7409:0, e7410:0)) e7423:(fn p1714:d2123:state -> e7422:(fn p1715:d2124:chunk -> e7421:(e7419:(e7417:(e7415:(e7413:r3086:word_prefix_ascii_chunk->d883:"std.text.str.word_prefix_ascii_chunk" e7414:r3087:data->d2119:data) e7416:r3088:data_len->d2120:data_len) e7418:r3089:state->d2123:state) e7420:r3090:chunk->d2124:chunk))))
  d2123:state arg
  d2124:chunk arg
  d2125:end arg
  d2126:end arg
  d2127:data arg
  d2128:data_len arg
  d2129:state arg
  d2130:chunk arg
  my d2131:i: 'a = e7446:(e7445:(e7443:r3099:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e7442:r3098:chunk->d2130:chunk) e7444:1024)
  my d2132:chunk_end: 'a | 'b | 'c | int = e7464:case e7457:(e7456:r3104:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7455:(e7454:(e7452:r3102:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e7451:(e7450:(e7448:r3101:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7447:r3100:i->d2131:i) e7449:1024)) e7453:r3103:data_len->d2128:data_len)) { p1731:true -> e7462:(e7461:(e7459:r3106:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7458:r3105:i->d2131:i) e7460:1024); p1732:false -> e7463:r3107:data_len->d2128:data_len }
  d2133:state arg
  d2134:j arg
  d2135:data arg
  d2136:state arg
  d2137:i arg
  d2138:end arg
  my d2139:byte: 'a = e7496:(e7494:(e7492:r3118:"std::text::bytes::index_raw"->d658:"std.text.bytes.index_raw" e7493:r3119:data->d2135:data) e7495:r3120:i->d2137:i)
  d2140:byte arg
  d2141:source arg
  d2142:source_len arg
  d2143:i arg
  my d2144:count: 'a = e7600:(e7599:(e7597:r3153:"#op:infix:-"->d416:"std.core.ops.#op:infix:-" e7596:r3152:source_len->d2142:source_len) e7598:r3154:i->d2143:i)
  my d2145:chunk_count: 'a = e7609:(e7607:(e7601:r3155:"std::int::div"->d55:"std.int.div" e7606:(e7605:(e7603:r3157:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7602:r3156:count->d2144:count) e7604:1023)) e7608:1024)
  my d2146:scan: 'a = e7633:(e7619:(e7615:(e7614:(e7613:(e7611:r3158:"#op:infix:..<"->d410:"std.core.ops.#op:infix:..<" e7610:0) e7612:r3159:chunk_count->d2145:chunk_count).s287.fold=>d451:"std.data.fold.Fold.fold") e7618:(e7616:r3160:i->d2143:i, e7617:true)) e7632:(fn p1767:d2147:state -> e7631:(fn p1768:d2148:chunk -> e7630:(e7628:(e7626:(e7624:(e7622:(e7620:r3161:word_prefix_slow_chunk->d887:"std.text.str.word_prefix_slow_chunk" e7621:r3162:source->d2141:source) e7623:r3163:source_len->d2142:source_len) e7625:r3164:state->d2147:state) e7627:r3165:i->d2143:i) e7629:r3166:chunk->d2148:chunk))))
  d2147:state arg
  d2148:chunk arg
  d2149:end arg
  d2150:source arg
  d2151:source_len arg
  d2152:state arg
  d2153:start arg
  d2154:chunk arg
  my d2155:i: 'a = e7652:(e7651:(e7645:r3171:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7644:r3170:start->d2153:start) e7650:(e7649:(e7647:r3173:"#op:infix:*"->d417:"std.core.ops.#op:infix:*" e7646:r3172:chunk->d2154:chunk) e7648:1024))
  my d2156:chunk_end: 'a | 'b | 'c | int = e7670:case e7663:(e7662:r3178:"std::control::junction::junction::junction"->d219:"std.control.junction.junction.junction" e7661:(e7660:(e7658:r3176:"#op:infix:<"->d423:"std.core.ops.#op:infix:<" e7657:(e7656:(e7654:r3175:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7653:r3174:i->d2155:i) e7655:1024)) e7659:r3177:source_len->d2151:source_len)) { p1782:true -> e7668:(e7667:(e7665:r3180:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7664:r3179:i->d2155:i) e7666:1024); p1783:false -> e7669:r3181:source_len->d2151:source_len }
  d2157:state arg
  d2158:index arg
  d2159:source arg
  d2160:state arg
  d2161:i arg
  d2162:end arg
  d2163:s arg
  d2164:i arg
  d2165:s arg
  d2166:r arg
  d2167:r arg
  d2168:i arg
  my d2169:loop: 'a [std::control::var::ref_update 'b; 'c] -> [std::control::var::ref_update 'd, 'c] 'a = e7769:(fn p1805:d2170:x -> e7768:catch e7748:r3211:x->d2170:x { std::control::var::ref_update::update p1806:d2171:old, p1807:d2172:k -> e7767:block { let my p1808:d2173:new_item = e7755:(e7749:r3212:"ref_update::update"->d236:"std.control.var.ref_update.update" e7754:(e7752:(e7750:r3213:"std::text::str::index_range"->d792:"std.text.str.index_range" e7751:r3214:old->d2171:old) e7753:r3215:i->d2168:i)); e7766:(e7756:r3216:loop->d2169:loop e7765:(e7757:r3217:k->d2172:k e7764:(e7762:(e7760:(e7758:r3218:"std::text::str::splice"->d794:"std.text.str.splice" e7759:r3219:old->d2171:old) e7761:r3220:i->d2168:i) e7763:r3221:new_item->d2173:new_item))) } })
  d2170:x arg
  d2171:old arg
  d2172:k arg
  my d2173:new_item: 'a = e7755:(e7749:r3212:"ref_update::update"->d236:"std.control.var.ref_update.update" e7754:(e7752:(e7750:r3213:"std::text::str::index_range"->d792:"std.text.str.index_range" e7751:r3214:old->d2171:old) e7753:r3215:i->d2168:i))
  d2174:r arg
  d2175:i arg
  my d2176:loop: 'a [std::control::var::ref_update 'b; 'c] -> [std::control::var::ref_update 'd, 'c] 'a = e7825:(fn p1814:d2177:x -> e7824:catch e7792:r3228:x->d2177:x { std::control::var::ref_update::update p1815:d2178:old, p1816:d2179:k -> e7823:block { let my p1817:d2180:new_item = e7799:(e7793:r3229:"ref_update::update"->d236:"std.control.var.ref_update.update" e7798:(e7796:(e7794:r3230:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e7795:r3231:old->d2178:old) e7797:r3232:i->d2175:i)); e7822:block { let my p1818:d2181:replacement = e7802:(e7800:r3233:"std::text::char::to_string"->d674:"std.text.char.to_string" e7801:r3234:new_item->d2180:new_item); e7821:(e7803:r3235:loop->d2176:loop e7820:(e7804:r3236:k->d2179:k e7819:(e7817:(e7807:(e7805:r3237:"std::text::str::splice"->d794:"std.text.str.splice" e7806:r3238:old->d2178:old) e7816:(e7810:(e7808:r3239:range->d513:"std.data.range.range" e7809:r3240:i->d2175:i) e7815:(e7814:(e7812:r3242:"#op:infix:+"->d415:"std.core.ops.#op:infix:+" e7811:r3241:i->d2175:i) e7813:1))) e7818:r3243:replacement->d2181:replacement))) } } })
  d2177:x arg
  d2178:old arg
  d2179:k arg
  my d2180:new_item: 'a = e7799:(e7793:r3229:"ref_update::update"->d236:"std.control.var.ref_update.update" e7798:(e7796:(e7794:r3230:"std::text::str::index_raw"->d791:"std.text.str.index_raw" e7795:r3231:old->d2178:old) e7797:r3232:i->d2175:i))
  my d2181:replacement: 'a = e7802:(e7800:r3233:"std::text::char::to_string"->d674:"std.text.char.to_string" e7801:r3234:new_item->d2180:new_item)
  d2182:format arg
  d2183:algebra arg
  d2184:head arg
  d2185:tail arg
  d2186:format arg
  d2187:algebra arg
  d2188:value arg
  d2189:format arg
  d2190:algebra arg
  d2191:children arg
  d2192:format arg
  d2193:algebra arg
  d2194:marker arg
  d2195:level arg
  d2196:children arg
  d2197:format arg
  d2198:algebra arg
  d2199:marker arg
  d2200:format arg
  d2201:algebra arg
  d2202:marker arg
  d2203:children arg
  d2204:format arg
  d2205:algebra arg
  d2206:ordered arg
  d2207:items arg
  d2208:format arg
  d2209:algebra arg
  d2210:marker arg
  d2211:children arg
  d2212:format arg
  d2213:algebra arg
  d2214:children arg
  d2215:format arg
  d2216:algebra arg
  d2217:info arg
  d2218:body arg
  d2219:format arg
  d2220:algebra arg
  d2221:children arg
  d2222:format arg
  d2223:algebra arg
  d2224:children arg
  d2225:format arg
  d2226:algebra arg
  d2227:children arg
  d2228:format arg
  d2229:algebra arg
  d2230:node arg
  d2231:format arg
  d2232:document arg
  d2233:document arg
  d2234:document arg
  d2235:head arg
  d2236:tail arg
  d2237:value arg
  d2238:children arg
  d2239:marker arg
  d2240:level arg
  d2241:children arg
  d2242:marker arg
  d2243:marker arg
  d2244:children arg
  d2245:ordered arg
  d2246:items arg
  d2247:marker arg
  d2248:children arg
  d2249:children arg
  d2250:info arg
  d2251:body arg
  my d2252:info_node: 'a = e8211:(e8207:r3389:html_node->d932:"std.text.yumark.html_node" e8210:{tag: e8208:"code-info", body: e8209:r3390:info->d2250:info})
  my d2253:body_node: 'a = e8216:(e8212:r3391:html_node->d932:"std.text.yumark.html_node" e8215:{tag: e8213:"code", body: e8214:r3392:body->d2251:body})
  d2254:children arg
  d2255:children arg
  d2256:children arg
  d2257:head arg
  d2258:tail arg
  d2259:value arg
  d2260:children arg
  d2261:marker arg
  d2262:level arg
  d2263:children arg
  d2264:marker arg
  d2265:marker arg
  d2266:children arg
  d2267:ordered arg
  d2268:items arg
  d2269:marker arg
  d2270:children arg
  d2271:children arg
  d2272:info arg
  d2273:body arg
  d2274:children arg
  d2275:children arg
  d2276:children arg
  d2277:left arg
  d2278:right arg
  d2279:a arg
  d2280:b arg
  d2281:c arg
  d2282:a arg
  d2283:b arg
  d2284:c arg
  d2285:d arg
  d2286:format arg
  d2287:format arg
}
error: catch expression is missing the computation to handle
```

## 118. x25-explicit-direct / --poly-raw

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x25-explicit-direct.yu --poly-raw
```

UTC start: 2026-11-08T12:41:26.229803+00:00; elapsed: 0.0028860669990535825 s; exit: 0

```text
raw roots [d0:ping, d2:plain, d3:handle, d4:higher]
raw root exprs [e19]
raw runtime roots [e19]
defs {
  d0:ping = Mod { vis: our, children: [] }
  d1:"ping.get" = Let { vis: our, body: <missing>, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p3
        types:
          p0 = Con(ping, [])
          p1 = Row([p0])
          p2 = Con(int, [])
          p3 = Fun { arg: n0, arg_eff: n2, ret_eff: p1, ret: p2 }
          n0 = Con(unit, [])
          n1 = Top
          n2 = Row([], tail: n1)
      }
  d2:plain = Let { vis: our, body: e1, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p5
        types:
          p2 = Con(int, [])
          p4 = Bot
          p5 = Fun { arg: n3, arg_eff: n4, ret_eff: p4, ret: p2 }
          n3 = Con(int, [])
          n4 = Bot
      }
  d3:handle = Let { vis: our, body: e8, children: [] }
    scheme:
      scheme {
        quantifiers: ['17]
        stack_quantifiers: []
        predicate: p7
        types:
          p2 = Con(int, [])
          p6 = Var('17)
          p7 = Fun { arg: n3, arg_eff: n8, ret_eff: p6, ret: p2 }
          n3 = Con(int, [])
          n5 = Var('17)
          n6 = Con(ping, [])
          n7 = Row([n6], tail: n5)
          n8 = Intersection(n5, n7)
      }
  d4:higher = Let { vis: our, body: e14, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p8
        types:
          p2 = Con(int, [])
          p4 = Bot
          p8 = Fun { arg: n10, arg_eff: n4, ret_eff: p4, ret: p2 }
          n1 = Top
          n3 = Con(int, [])
          n4 = Bot
          n6 = Con(ping, [])
          n9 = Row([n6], tail: n1)
          n10 = Fun { arg: p2, arg_eff: p4, ret_eff: n9, ret: n3 }
      }
  d5:x = Arg
  d6:action = Arg
  d7:k = Arg
  d8:value = Arg
  d9:f = Arg
}
exprs {
  e0 = Var(r0:x->d5:x)
  e1 = Lambda(p0, e0)
  e2 = Var(r1:action->d6:action)
  e3 = Var(r2:k->d7:k)
  e4 = Lit(Int(7))
  e5 = App(e3, e4)
  e6 = Var(r3:value->d8:value)
  e7 = Catch(e2, [{ op: ping::get, pat: p2, k: p3, guard: none, body: e5 }, { op: value, pat: p4, k: none, guard: none, body: e6 }])
  e8 = Lambda(p1, e7)
  e9 = Var(r4:f->d9:f)
  e10 = Var(r5:"ping::get"->d1:"ping.get")
  e11 = Lit(Unit)
  e12 = App(e10, e11)
  e13 = App(e9, e12)
  e14 = Lambda(p5, e13)
  e15 = Var(r6:handle->d3:handle)
  e16 = Var(r7:higher->d4:higher)
  e17 = Var(r8:plain->d2:plain)
  e18 = App(e16, e17)
  e19 = App(e15, e18)
}
pats {
  p0 = Var(d5:x)
  p1 = Var(d6:action)
  p2 = Wild
  p3 = Var(d7:k)
  p4 = Var(d8:value)
  p5 = Var(d9:f)
}
```

## 119. x25-explicit-direct / --mono

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x25-explicit-direct.yu --mono
```

UTC start: 2026-11-08T12:41:26.232853+00:00; elapsed: 0.002757784001005348 s; exit: 1

```text
conflicting type candidates: [ping] vs []
```

## 120. x25-explicit-direct / --runtime-ir

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x25-explicit-direct.yu --runtime-ir
```

UTC start: 2026-11-08T12:41:26.235749+00:00; elapsed: 0.002453204000630649 s; exit: 1

```text
conflicting type candidates: [ping] vs []
```

## 121. x25-argonly-direct / --poly-raw

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x25-argonly-direct.yu --poly-raw
```

UTC start: 2026-11-08T12:41:26.238345+00:00; elapsed: 0.0017694749985821545 s; exit: 0

```text
raw roots [d0:ping, d2:plain, d3:handle, d4:higher]
raw root exprs [e19]
raw runtime roots [e19]
defs {
  d0:ping = Mod { vis: our, children: [] }
  d1:"ping.get" = Let { vis: our, body: <missing>, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p3
        types:
          p0 = Con(ping, [])
          p1 = Row([p0])
          p2 = Con(int, [])
          p3 = Fun { arg: n0, arg_eff: n2, ret_eff: p1, ret: p2 }
          n0 = Con(unit, [])
          n1 = Top
          n2 = Row([], tail: n1)
      }
  d2:plain = Let { vis: our, body: e1, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p5
        types:
          p2 = Con(int, [])
          p4 = Bot
          p5 = Fun { arg: n3, arg_eff: n4, ret_eff: p4, ret: p2 }
          n3 = Con(int, [])
          n4 = Bot
      }
  d3:handle = Let { vis: our, body: e8, children: [] }
    scheme:
      scheme {
        quantifiers: ['17]
        stack_quantifiers: []
        predicate: p7
        types:
          p2 = Con(int, [])
          p6 = Var('17)
          p7 = Fun { arg: n3, arg_eff: n8, ret_eff: p6, ret: p2 }
          n3 = Con(int, [])
          n5 = Var('17)
          n6 = Con(ping, [])
          n7 = Row([n6], tail: n5)
          n8 = Intersection(n5, n7)
      }
  d4:higher = Let { vis: our, body: e14, children: [] }
    scheme:
      scheme {
        quantifiers: ['50]
        stack_quantifiers: []
        predicate: p9
        types:
          p0 = Con(ping, [])
          p1 = Row([p0])
          p2 = Con(int, [])
          p8 = Var('50)
          p9 = Fun { arg: n11, arg_eff: n4, ret_eff: p8, ret: p2 }
          n3 = Con(int, [])
          n4 = Bot
          n9 = Var('50)
          n10 = Row([], tail: n9)
          n11 = Fun { arg: p2, arg_eff: p1, ret_eff: n10, ret: n3 }
      }
  d5:x = Arg
  d6:action = Arg
  d7:k = Arg
  d8:value = Arg
  d9:f = Arg
}
exprs {
  e0 = Var(r0:x->d5:x)
  e1 = Lambda(p0, e0)
  e2 = Var(r1:action->d6:action)
  e3 = Var(r2:k->d7:k)
  e4 = Lit(Int(7))
  e5 = App(e3, e4)
  e6 = Var(r3:value->d8:value)
  e7 = Catch(e2, [{ op: ping::get, pat: p2, k: p3, guard: none, body: e5 }, { op: value, pat: p4, k: none, guard: none, body: e6 }])
  e8 = Lambda(p1, e7)
  e9 = Var(r4:f->d9:f)
  e10 = Var(r5:"ping::get"->d1:"ping.get")
  e11 = Lit(Unit)
  e12 = App(e10, e11)
  e13 = App(e9, e12)
  e14 = Lambda(p5, e13)
  e15 = Var(r6:handle->d3:handle)
  e16 = Var(r7:higher->d4:higher)
  e17 = Var(r8:plain->d2:plain)
  e18 = App(e16, e17)
  e19 = App(e15, e18)
}
pats {
  p0 = Var(d5:x)
  p1 = Var(d6:action)
  p2 = Wild
  p3 = Var(d7:k)
  p4 = Var(d8:value)
  p5 = Var(d9:f)
}
```

## 122. x25-argonly-direct / --mono

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x25-argonly-direct.yu --mono
```

UTC start: 2026-11-08T12:41:26.240277+00:00; elapsed: 0.0020134619990130886 s; exit: 0

```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((adapter[(thunk[[ping], int] -> int) -> int => (thunk[[ping], int] -> int) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m1) adapter[thunk[[ping], int] -> int => thunk[[ping], int] -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m2))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> (d7 7), d8 -> d8
m1 = d4 : (thunk[[ping], int] -> int) -> int
  adapter[(thunk[[ping], int] -> int) -> int => (thunk[[ping], int] -> int) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](\d9 -> (d9 (<effect-op ping::get> ())))
m2 = d2 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d5 -> d5)
```

## 123. x25-argonly-direct / --runtime-ir

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [ping] int -> int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x25-argonly-direct.yu --runtime-ir
```

UTC start: 2026-11-08T12:41:26.242431+00:00; elapsed: 0.0017633060015214141 s; exit: 0

```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((adapter[(thunk[[ping], int] -> int) -> int => (thunk[[ping], int] -> int) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m1) adapter[thunk[[ping], int] -> int => thunk[[ping], int] -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m2))))]
m0 = d3 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> (d7 7), d8 -> d8
m1 = d4 : (thunk[[ping], int] -> int) -> int
  adapter[(thunk[[ping], int] -> int) -> int => (thunk[[ping], int] -> int) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](\d9 -> (d9 (<effect-op ping::get> ())))
m2 = d2 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d5 -> d5)
```

## 124. x25-wildarg-direct / --poly-raw

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x25-wildarg-direct.yu --poly-raw
```

UTC start: 2026-11-08T12:41:26.244332+00:00; elapsed: 0.0016710470008547418 s; exit: 0

```text
raw roots [d0:ping, d2:plain, d3:handle, d4:higher]
raw root exprs [e19]
raw runtime roots [e19]
defs {
  d0:ping = Mod { vis: our, children: [] }
  d1:"ping.get" = Let { vis: our, body: <missing>, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p3
        types:
          p0 = Con(ping, [])
          p1 = Row([p0])
          p2 = Con(int, [])
          p3 = Fun { arg: n0, arg_eff: n2, ret_eff: p1, ret: p2 }
          n0 = Con(unit, [])
          n1 = Top
          n2 = Row([], tail: n1)
      }
  d2:plain = Let { vis: our, body: e1, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p5
        types:
          p2 = Con(int, [])
          p4 = Bot
          p5 = Fun { arg: n3, arg_eff: n4, ret_eff: p4, ret: p2 }
          n3 = Con(int, [])
          n4 = Bot
      }
  d3:handle = Let { vis: our, body: e8, children: [] }
    scheme:
      scheme {
        quantifiers: ['17]
        stack_quantifiers: []
        predicate: p7
        types:
          p2 = Con(int, [])
          p6 = Var('17)
          p7 = Fun { arg: n3, arg_eff: n8, ret_eff: p6, ret: p2 }
          n3 = Con(int, [])
          n5 = Var('17)
          n6 = Con(ping, [])
          n7 = Row([n6], tail: n5)
          n8 = Intersection(n5, n7)
      }
  d4:higher = Let { vis: our, body: e14, children: [] }
    scheme:
      scheme {
        quantifiers: ['46, '51]
        stack_quantifiers: [#1]
        predicate: p12
        types:
          p0 = Con(ping, [])
          p1 = Row([p0])
          p2 = Con(int, [])
          p8 = Var('51)
          p9 = Var('46)
          p10 = Stack { inner: p9, weight: { #1 -> floor: [], pops: 0, stack: [Set(ping, [])] } }
          p11 = Union(p8, p10)
          p12 = Fun { arg: n13, arg_eff: n4, ret_eff: p11, ret: p2 }
          n3 = Con(int, [])
          n4 = Bot
          n6 = Con(ping, [])
          n9 = Var('51)
          n10 = Var('46)
          n11 = Row([n6], tail: n10)
          n12 = Intersection(n9, n11)
          n13 = Fun { arg: p2, arg_eff: p1, ret_eff: n12, ret: n3 }
      }
  d5:x = Arg
  d6:action = Arg
  d7:k = Arg
  d8:value = Arg
  d9:f = Arg
}
exprs {
  e0 = Var(r0:x->d5:x)
  e1 = Lambda(p0, e0)
  e2 = Var(r1:action->d6:action)
  e3 = Var(r2:k->d7:k)
  e4 = Lit(Int(7))
  e5 = App(e3, e4)
  e6 = Var(r3:value->d8:value)
  e7 = Catch(e2, [{ op: ping::get, pat: p2, k: p3, guard: none, body: e5 }, { op: value, pat: p4, k: none, guard: none, body: e6 }])
  e8 = Lambda(p1, e7)
  e9 = Var(r4:f->d9:f)
  e10 = Var(r5:"ping::get"->d1:"ping.get")
  e11 = Lit(Unit)
  e12 = App(e10, e11)
  e13 = App(e9, e12)
  e14 = Lambda(p5, e13)
  e15 = Var(r6:handle->d3:handle)
  e16 = Var(r7:higher->d4:higher)
  e17 = Var(r8:plain->d2:plain)
  e18 = App(e16, e17)
  e19 = App(e15, e18)
}
pats {
  p0 = Var(d5:x)
  p1 = Var(d6:action)
  p2 = Wild
  p3 = Var(d7:k)
  p4 = Var(d8:value)
  p5 = Var(d9:f)
}
```

## 125. x25-wildarg-direct / --mono

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x25-wildarg-direct.yu --mono
```

UTC start: 2026-11-08T12:41:26.246527+00:00; elapsed: 0.001867332000983879 s; exit: 0

```text
mono roots [(m0 (adapter[(thunk[[ping], int] -> int) -> int => (thunk[[ping], int] -> int) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m1) adapter[thunk[[ping], int] -> int => thunk[[ping], int] -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m2)))]
m0 = d3 : int -> int
  \d6 -> catch d6: ping::get _, d7 -> (d7 7), d8 -> d8
m1 = d4 : (thunk[[ping], int] -> int) -> int
  adapter[(thunk[[ping], int] -> int) -> int => (thunk[[ping], int] -> int) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](\d9 -> (d9 (<effect-op ping::get> ())))
m2 = d2 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d5 -> d5)
```

## 126. x25-wildarg-direct / --runtime-ir

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher plain)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x25-wildarg-direct.yu --runtime-ir
```

UTC start: 2026-11-08T12:41:26.248554+00:00; elapsed: 0.002049557002465008 s; exit: 0

```text
mono roots [(m0 (adapter[(thunk[[ping], int] -> int) -> int => (thunk[[ping], int] -> int) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m1) adapter[thunk[[ping], int] -> int => thunk[[ping], int] -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m2)))]
m0 = d3 : int -> int
  \d6 -> catch d6: ping::get _, d7 -> (d7 7), d8 -> d8
m1 = d4 : (thunk[[ping], int] -> int) -> int
  adapter[(thunk[[ping], int] -> int) -> int => (thunk[[ping], int] -> int) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](\d9 -> (d9 (<effect-op ping::get> ())))
m2 = d2 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d5 -> d5)
```

## 127. x25-wildarg-eta / --poly-raw

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x25-wildarg-eta.yu --poly-raw
```

UTC start: 2026-11-08T12:41:26.250770+00:00; elapsed: 0.0019052390016440768 s; exit: 0

```text
raw roots [d0:ping, d2:plain, d3:handle, d4:higher]
raw root exprs [e22]
raw runtime roots [e22]
defs {
  d0:ping = Mod { vis: our, children: [] }
  d1:"ping.get" = Let { vis: our, body: <missing>, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p3
        types:
          p0 = Con(ping, [])
          p1 = Row([p0])
          p2 = Con(int, [])
          p3 = Fun { arg: n0, arg_eff: n2, ret_eff: p1, ret: p2 }
          n0 = Con(unit, [])
          n1 = Top
          n2 = Row([], tail: n1)
      }
  d2:plain = Let { vis: our, body: e1, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p5
        types:
          p2 = Con(int, [])
          p4 = Bot
          p5 = Fun { arg: n3, arg_eff: n4, ret_eff: p4, ret: p2 }
          n3 = Con(int, [])
          n4 = Bot
      }
  d3:handle = Let { vis: our, body: e8, children: [] }
    scheme:
      scheme {
        quantifiers: ['17]
        stack_quantifiers: []
        predicate: p7
        types:
          p2 = Con(int, [])
          p6 = Var('17)
          p7 = Fun { arg: n3, arg_eff: n8, ret_eff: p6, ret: p2 }
          n3 = Con(int, [])
          n5 = Var('17)
          n6 = Con(ping, [])
          n7 = Row([n6], tail: n5)
          n8 = Intersection(n5, n7)
      }
  d4:higher = Let { vis: our, body: e14, children: [] }
    scheme:
      scheme {
        quantifiers: ['46, '51]
        stack_quantifiers: [#1]
        predicate: p12
        types:
          p0 = Con(ping, [])
          p1 = Row([p0])
          p2 = Con(int, [])
          p8 = Var('51)
          p9 = Var('46)
          p10 = Stack { inner: p9, weight: { #1 -> floor: [], pops: 0, stack: [Set(ping, [])] } }
          p11 = Union(p8, p10)
          p12 = Fun { arg: n13, arg_eff: n4, ret_eff: p11, ret: p2 }
          n3 = Con(int, [])
          n4 = Bot
          n6 = Con(ping, [])
          n9 = Var('51)
          n10 = Var('46)
          n11 = Row([n6], tail: n10)
          n12 = Intersection(n9, n11)
          n13 = Fun { arg: p2, arg_eff: p1, ret_eff: n12, ret: n3 }
      }
  d5:x = Arg
  d6:action = Arg
  d7:k = Arg
  d8:value = Arg
  d9:f = Arg
  d11:x = Arg
}
exprs {
  e0 = Var(r0:x->d5:x)
  e1 = Lambda(p0, e0)
  e2 = Var(r1:action->d6:action)
  e3 = Var(r2:k->d7:k)
  e4 = Lit(Int(7))
  e5 = App(e3, e4)
  e6 = Var(r3:value->d8:value)
  e7 = Catch(e2, [{ op: ping::get, pat: p2, k: p3, guard: none, body: e5 }, { op: value, pat: p4, k: none, guard: none, body: e6 }])
  e8 = Lambda(p1, e7)
  e9 = Var(r4:f->d9:f)
  e10 = Var(r5:"ping::get"->d1:"ping.get")
  e11 = Lit(Unit)
  e12 = App(e10, e11)
  e13 = App(e9, e12)
  e14 = Lambda(p5, e13)
  e15 = Var(r6:handle->d3:handle)
  e16 = Var(r7:higher->d4:higher)
  e17 = Var(r8:plain->d2:plain)
  e18 = Var(r9:x->d11:x)
  e19 = App(e17, e18)
  e20 = Lambda(p6, e19)
  e21 = App(e16, e20)
  e22 = App(e15, e21)
}
pats {
  p0 = Var(d5:x)
  p1 = Var(d6:action)
  p2 = Wild
  p3 = Var(d7:k)
  p4 = Var(d8:value)
  p5 = Var(d9:f)
  p6 = Var(d11:x)
}
```

## 128. x25-wildarg-eta / --mono

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x25-wildarg-eta.yu --mono
```

UTC start: 2026-11-08T12:41:26.252865+00:00; elapsed: 0.0021598029998131096 s; exit: 0

```text
mono roots [force-thunk[thunk[[ping], int] => int ! [ping]]((m0 (adapter[(thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int] => (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]; hygiene[arg[add_id[1, ping, own, resume-own]]]](m1) adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> thunk[[ping], int]; hygiene[arg[add_id[1, ping, own, resume-own]]]](\d11 -> make-thunk[int ! [ping] => thunk[[ping], int]]((m2 force-thunk[thunk[[ping], int] => int ! [ping]](d11)))))))]
m0 = d3 : thunk[[ping], int] -> thunk[[ping], int]
  adapter[thunk[[ping], int] -> int => thunk[[ping], int] -> thunk[[ping], int]; hygiene[]](\d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> (d7 7), d8 -> d8)
m1 = d4 : (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]
  adapter[(thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int] => (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]; hygiene[arg[add_id[1, ping, own, resume-own]]]](\d9 -> (d9 (<effect-op ping::get> ())))
m2 = d2 : int -> int
  \d5 -> d5
```

## 129. x25-wildarg-eta / --runtime-ir

```yulang
act ping:
    our get: () -> int
our plain(x: int): int = x
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: [_] int -> [ping] int) = f(ping::get())
handle(higher (\x -> plain x))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x25-wildarg-eta.yu --runtime-ir
```

UTC start: 2026-11-08T12:41:26.255213+00:00; elapsed: 0.0014889830017636996 s; exit: 0

```text
mono roots [force-thunk[thunk[[ping], int] => int ! [ping]]((m0 (adapter[(thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int] => (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]; hygiene[arg[add_id[1, ping, own, resume-own]]]](m1) adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> thunk[[ping], int]; hygiene[arg[add_id[1, ping, own, resume-own]]]](\d11 -> make-thunk[int ! [ping] => thunk[[ping], int]]((m2 force-thunk[thunk[[ping], int] => int ! [ping]](d11)))))))]
m0 = d3 : thunk[[ping], int] -> thunk[[ping], int]
  adapter[thunk[[ping], int] -> int => thunk[[ping], int] -> thunk[[ping], int]; hygiene[]](\d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> (d7 7), d8 -> d8)
m1 = d4 : (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]
  adapter[(thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int] => (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]; hygiene[arg[add_id[1, ping, own, resume-own]]]](\d9 -> (d9 (<effect-op ping::get> ())))
m2 = d2 : int -> int
  \d5 -> d5
```

## 130. x22-inferred-missing / --poly-raw

```yulang
our read_port(config) = case config:
    {port: p} -> p
    _ -> 80
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x22-inferred-missing.yu --poly-raw
```

UTC start: 2026-11-08T12:41:26.256896+00:00; elapsed: 0.0018462599982740358 s; exit: 0

```text
raw roots [d0:read_port]
raw root exprs [e7]
raw runtime roots [e7]
defs {
  d0:read_port = Let { vis: our, body: e4, children: [] }
    scheme:
      scheme {
        quantifiers: ['8]
        stack_quantifiers: []
        predicate: p4
        types:
          p0 = Bot
          p1 = Var('8)
          p2 = Con(int, [])
          p3 = Union(p1, p2)
          p4 = Fun { arg: n1, arg_eff: n2, ret_eff: p0, ret: p3 }
          n0 = Var('8)
          n1 = Record(port: n0)
          n2 = Bot
      }
  d1:config = Arg
  d2:p = Arg
}
exprs {
  e0 = Var(r0:config->d1:config)
  e1 = Var(r1:p->d2:p)
  e2 = Lit(Int(80))
  e3 = Case(e0, [{ pat: p2, guard: none, body: e1 }, { pat: p3, guard: none, body: e2 }])
  e4 = Lambda(p0, e3)
  e5 = Var(r2:read_port->d0:read_port)
  e6 = Record(; spread: none)
  e7 = App(e5, e6)
}
pats {
  p0 = Var(d1:config)
  p1 = Var(d2:p)
  p2 = Record(port: p1; spread: none)
  p3 = Wild
}
```

## 131. x22-inferred-missing / --mono

```yulang
our read_port(config) = case config:
    {port: p} -> p
    _ -> 80
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x22-inferred-missing.yu --mono
```

UTC start: 2026-11-08T12:41:26.258964+00:00; elapsed: 0.0019393260008655488 s; exit: 1

```text
compile error [yulang.unsatisfied-subtype]: record is missing field `port`
  detail: unsatisfied subtype constraint: {} <: {port: 'open0}
  hint: add `port` to this record or use a value that provides it; actual record has no fields
```

## 132. x22-inferred-missing / --runtime-ir

```yulang
our read_port(config) = case config:
    {port: p} -> p
    _ -> 80
read_port {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-case/x22-inferred-missing.yu --runtime-ir
```

UTC start: 2026-11-08T12:41:26.261223+00:00; elapsed: 0.0014133290023892187 s; exit: 1

```text
compile error [yulang.unsatisfied-subtype]: record is missing field `port`
  detail: unsatisfied subtype constraint: {} <: {port: 'open0}
  hint: add `port` to this record or use a value that provides it; actual record has no fields
```

## 133. default-function / check

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()} = a
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/default-function.yu
```

UTC start: 2026-11-08T12:42:16.138851+00:00; elapsed: 0.009 s; exit: 0

```text
```

## 134. default-function / dump

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()} = a
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/default-function.yu
```

UTC start: 2026-11-08T12:42:16.147738+00:00; elapsed: 0.009 s; exit: 0

```text
roots d0:ping d2:pick d3:handle
d0:ping mod {
}
d2:pick: {a?: 'a} -> 'a | int = e4:(fn p1:{a: p0:d4:a = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:())} -> e3:r1:a->d4:a)
d3:handle: 'a ['b & [ping; 'b]] -> ['b] 'a = e11:(fn p2:d5:action -> e10:catch e5:r2:action->d5:action { ping::get p3:_, p4:d6:k -> e8:(e6:r3:k->d6:k e7:7); p5:d7:value -> e9:r4:value->d7:value })
root exprs e16:(e12:r5:handle->d3:handle e15:(e13:r6:pick->d2:pick e14:{}))
runtime roots e16:(e12:r5:handle->d3:handle e15:(e13:r6:pick->d2:pick e14:{}))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:a arg
  d5:action arg
  d6:k arg
  d7:value arg
}
```

## 135. default-function / run

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()} = a
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/default-function.yu
```

UTC start: 2026-11-08T12:42:16.157507+00:00; elapsed: 0.004 s; exit: 1

```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
    --> line 3, column 15
    3 | our pick {a = ping::get()} = a
      |               ^^^^^^^^^
  hint: handle this computation with a matching effect handler before running it
  note: application occurs here
    --> line 3, column 15
    3 | our pick {a = ping::get()} = a
      |               ^^^^^^^^^^^
```

## 136. default-inline-catch / check

```yulang
act ping:
    our get: () -> int
catch (case {}:
    {a = ping::get()} -> a
):
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/default-inline-catch.yu
```

UTC start: 2026-11-08T12:42:16.161822+00:00; elapsed: 0.006 s; exit: 0

```text
```

## 137. default-inline-catch / dump

```yulang
act ping:
    our get: () -> int
catch (case {}:
    {a = ping::get()} -> a
):
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/default-inline-catch.yu
```

UTC start: 2026-11-08T12:42:16.168263+00:00; elapsed: 0.007 s; exit: 0

```text
roots d0:ping
d0:ping mod {
}
root exprs e10:catch e5:case e0:{} { p1:{a: p0:d3:a = e3:(e1:r0:"ping::get"->d1:"ping.get" e2:())} -> e4:r1:a->d3:a } { ping::get p2:_, p3:d4:k -> e8:(e6:r2:k->d4:k e7:7); p4:d5:value -> e9:r3:value->d5:value }
runtime roots e10:catch e5:case e0:{} { p1:{a: p0:d3:a = e3:(e1:r0:"ping::get"->d1:"ping.get" e2:())} -> e4:r1:a->d3:a } { ping::get p2:_, p3:d4:k -> e8:(e6:r2:k->d4:k e7:7); p4:d5:value -> e9:r3:value->d5:value }
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:a arg
  d4:k arg
  d5:value arg
}
```

## 138. default-inline-catch / run

```yulang
act ping:
    our get: () -> int
catch (case {}:
    {a = ping::get()} -> a
):
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/default-inline-catch.yu
```

UTC start: 2026-11-08T12:42:16.175221+00:00; elapsed: 0.004 s; exit: 0

```text
run roots [<thunk>]
```

## 139. default-function-directcatch / check

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()} = a
catch pick {}:
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/default-function-directcatch.yu
```

UTC start: 2026-11-08T12:42:16.179610+00:00; elapsed: 0.004 s; exit: 1

```text
diagnostics:
  error [yulang.missing-catch-arm-body]: catch arm is missing a body expression
    --> line 4, column 13
    4 | catch pick {}:
      |             ^
    hint: write an expression after `->`
```

## 140. default-function-directcatch / dump

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()} = a
catch pick {}:
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/default-function-directcatch.yu
```

UTC start: 2026-11-08T12:42:16.184344+00:00; elapsed: 0.005 s; exit: 0

```text
roots d0:ping d2:pick
d0:ping mod {
}
d2:pick: {a?: 'a} -> 'a | int = e4:(fn p1:{a: p0:d3:a = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:())} -> e3:r1:a->d3:a)
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:a arg
}
error: catch arm is missing a body expression
```

## 141. default-function-directcatch / run

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()} = a
catch pick {}:
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/default-function-directcatch.yu
```

UTC start: 2026-11-08T12:42:16.189908+00:00; elapsed: 0.007 s; exit: 1

```text
compile error [yulang.lowering]: source has lowering errors
  detail: catch arm is missing a body expression
  hint: run `yulang check` to see source ranges before running
```

## 142. default-body-fallback / check

```yulang
act ping:
    our get: () -> int
our pick x = ping::get()
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/default-body-fallback.yu
```

UTC start: 2026-11-08T12:42:16.196893+00:00; elapsed: 0.008 s; exit: 0

```text
```

## 143. default-body-fallback / dump

```yulang
act ping:
    our get: () -> int
our pick x = ping::get()
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/default-body-fallback.yu
```

UTC start: 2026-11-08T12:42:16.205434+00:00; elapsed: 0.009 s; exit: 0

```text
roots d0:ping d2:pick d3:handle
d0:ping mod {
}
d2:pick: any -> [ping] int = e3:(fn p0:d4:x -> e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()))
d3:handle: 'a ['b & [ping; 'b]] -> ['b] 'a = e10:(fn p1:d5:action -> e9:catch e4:r1:action->d5:action { ping::get p2:_, p3:d6:k -> e7:(e5:r2:k->d6:k e6:7); p4:d7:value -> e8:r3:value->d7:value })
root exprs e15:(e11:r4:handle->d3:handle e14:(e12:r5:pick->d2:pick e13:{}))
runtime roots e15:(e11:r4:handle->d3:handle e14:(e12:r5:pick->d2:pick e13:{}))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:x arg
  d5:action arg
  d6:k arg
  d7:value arg
}
```

## 144. default-body-fallback / run

```yulang
act ping:
    our get: () -> int
our pick x = ping::get()
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/default-body-fallback.yu
```

UTC start: 2026-11-08T12:42:16.214874+00:00; elapsed: 0.004 s; exit: 0

```text
run roots [7]
```

## 145. default-explicit-result / check

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()}: [ping] int = a
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/default-explicit-result.yu
```

UTC start: 2026-11-08T12:42:16.219503+00:00; elapsed: 0.008 s; exit: 0

```text
```

## 146. default-explicit-result / dump

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()}: [ping] int = a
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/default-explicit-result.yu
```

UTC start: 2026-11-08T12:42:16.227448+00:00; elapsed: 0.01 s; exit: 0

```text
roots d0:ping d2:pick d3:handle
d0:ping mod {
}
d2:pick: {a?: int} -> int = e4:(fn p1:{a: p0:d4:a = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:())} -> e3:r1:a->d4:a)
d3:handle: 'a ['b & [ping; 'b]] -> ['b] 'a = e11:(fn p2:d5:action -> e10:catch e5:r2:action->d5:action { ping::get p3:_, p4:d6:k -> e8:(e6:r3:k->d6:k e7:7); p5:d7:value -> e9:r4:value->d7:value })
root exprs e16:(e12:r5:handle->d3:handle e15:(e13:r6:pick->d2:pick e14:{}))
runtime roots e16:(e12:r5:handle->d3:handle e15:(e13:r6:pick->d2:pick e14:{}))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:a arg
  d5:action arg
  d6:k arg
  d7:value arg
}
```

## 147. default-explicit-result / run

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()}: [ping] int = a
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/default-explicit-result.yu
```

UTC start: 2026-11-08T12:42:16.237681+00:00; elapsed: 0.005 s; exit: 1

```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
    --> line 3, column 15
    3 | our pick {a = ping::get()}: [ping] int = a
      |               ^^^^^^^^^
  hint: handle this computation with a matching effect handler before running it
  note: application occurs here
    --> line 3, column 15
    3 | our pick {a = ping::get()}: [ping] int = a
      |               ^^^^^^^^^^^
```

## 148. default-internal-handler / check

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our pick {a = handle(ping::get())} = a
pick {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/default-internal-handler.yu
```

UTC start: 2026-11-08T12:42:16.242637+00:00; elapsed: 0.008 s; exit: 0

```text
```

## 149. default-internal-handler / dump

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our pick {a = handle(ping::get())} = a
pick {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/default-internal-handler.yu
```

UTC start: 2026-11-08T12:42:16.251323+00:00; elapsed: 0.009 s; exit: 0

```text
roots d0:ping d2:handle d3:pick
d0:ping mod {
}
d2:handle: 'a ['b & [ping; 'b]] -> ['b] 'a = e6:(fn p0:d4:action -> e5:catch e0:r0:action->d4:action { ping::get p1:_, p2:d5:k -> e3:(e1:r1:k->d5:k e2:7); p3:d6:value -> e4:r2:value->d6:value })
d3:pick: {a?: 'a} -> 'a | int = e13:(fn p5:{a: p4:d7:a = e11:(e7:r3:handle->d2:handle e10:(e8:r4:"ping::get"->d1:"ping.get" e9:()))} -> e12:r5:a->d7:a)
root exprs e16:(e14:r6:pick->d3:pick e15:{})
runtime roots e16:(e14:r6:pick->d3:pick e15:{})
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:action arg
  d5:k arg
  d6:value arg
  d7:a arg
}
```

## 150. default-internal-handler / run

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our pick {a = handle(ping::get())} = a
pick {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/default-internal-handler.yu
```

UTC start: 2026-11-08T12:42:16.260472+00:00; elapsed: 0.004 s; exit: 0

```text
run roots [7]
```

## 151. default-pure-filter / check

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()}: [] int = a
pick {a: 9}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/default-pure-filter.yu
```

UTC start: 2026-11-08T12:42:16.265138+00:00; elapsed: 0.004 s; exit: 0

```text
```

## 152. default-pure-filter / dump

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()}: [] int = a
pick {a: 9}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/default-pure-filter.yu
```

UTC start: 2026-11-08T12:42:16.269091+00:00; elapsed: 0.004 s; exit: 0

```text
roots d0:ping d2:pick
d0:ping mod {
}
d2:pick: {a?: int} -> int = e4:(fn p1:{a: p0:d3:a = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:())} -> e3:r1:a->d3:a)
root exprs e8:(e5:r2:pick->d2:pick e7:{a: e6:9})
runtime roots e8:(e5:r2:pick->d2:pick e7:{a: e6:9})
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:a arg
}
```

## 153. default-pure-filter / run

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()}: [] int = a
pick {a: 9}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/default-pure-filter.yu
```

UTC start: 2026-11-08T12:42:16.273267+00:00; elapsed: 0.003 s; exit: 0

```text
run roots [9]
```

## 154. default-two-effects / check

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get(), b = ping::get()} = (a,b)
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/default-two-effects.yu
```

UTC start: 2026-11-08T12:42:16.276338+00:00; elapsed: 0.008 s; exit: 0

```text
```

## 155. default-two-effects / dump

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get(), b = ping::get()} = (a,b)
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/default-two-effects.yu
```

UTC start: 2026-11-08T12:42:16.284225+00:00; elapsed: 0.008 s; exit: 0

```text
roots d0:ping d2:pick d3:handle
d0:ping mod {
}
d2:pick: {a?: 'a, b?: 'b} -> ('a | int, 'b | int) = e9:(fn p2:{a: p0:d4:a = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()), b: p1:d5:b = e5:(e3:r1:"ping::get"->d1:"ping.get" e4:())} -> e8:(e6:r2:a->d4:a, e7:r3:b->d5:b))
d3:handle: 'a ['b & [ping; 'b]] -> ['b] 'a = e16:(fn p3:d6:action -> e15:catch e10:r4:action->d6:action { ping::get p4:_, p5:d7:k -> e13:(e11:r5:k->d7:k e12:7); p6:d8:value -> e14:r6:value->d8:value })
root exprs e21:(e17:r7:handle->d3:handle e20:(e18:r8:pick->d2:pick e19:{}))
runtime roots e21:(e17:r7:handle->d3:handle e20:(e18:r8:pick->d2:pick e19:{}))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:a arg
  d5:b arg
  d6:action arg
  d7:k arg
  d8:value arg
}
```

## 156. default-two-effects / run

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get(), b = ping::get()} = (a,b)
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/default-two-effects.yu
```

UTC start: 2026-11-08T12:42:16.292390+00:00; elapsed: 0.005 s; exit: 1

```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
    --> line 3, column 15
    3 | our pick {a = ping::get(), b = ping::get()} = (a,b)
      |               ^^^^^^^^^
  hint: handle this computation with a matching effect handler before running it
  note: application occurs here
    --> line 3, column 15
    3 | our pick {a = ping::get(), b = ping::get()} = (a,b)
      |               ^^^^^^^^^^^
```

## 157. default-case-function / check

```yulang
act ping:
    our get: () -> int
our pick x = case x:
    {a = ping::get()} -> a
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/default-case-function.yu
```

UTC start: 2026-11-08T12:42:16.297738+00:00; elapsed: 0.008 s; exit: 0

```text
```

## 158. default-case-function / dump

```yulang
act ping:
    our get: () -> int
our pick x = case x:
    {a = ping::get()} -> a
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/default-case-function.yu
```

UTC start: 2026-11-08T12:42:16.305957+00:00; elapsed: 0.01 s; exit: 0

```text
roots d0:ping d2:pick d3:handle
d0:ping mod {
}
d2:pick: {a?: 'a} -> 'a | int = e6:(fn p0:d4:x -> e5:case e0:r0:x->d4:x { p2:{a: p1:d5:a = e3:(e1:r1:"ping::get"->d1:"ping.get" e2:())} -> e4:r2:a->d5:a })
d3:handle: 'a ['b & [ping; 'b]] -> ['b] 'a = e13:(fn p3:d6:action -> e12:catch e7:r3:action->d6:action { ping::get p4:_, p5:d7:k -> e10:(e8:r4:k->d7:k e9:7); p6:d8:value -> e11:r5:value->d8:value })
root exprs e18:(e14:r6:handle->d3:handle e17:(e15:r7:pick->d2:pick e16:{}))
runtime roots e18:(e14:r6:handle->d3:handle e17:(e15:r7:pick->d2:pick e16:{}))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:x arg
  d5:a arg
  d6:action arg
  d7:k arg
  d8:value arg
}
```

## 159. default-case-function / run

```yulang
act ping:
    our get: () -> int
our pick x = case x:
    {a = ping::get()} -> a
our handle(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
handle(pick {})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/default-case-function.yu
```

UTC start: 2026-11-08T12:42:16.316166+00:00; elapsed: 0.004 s; exit: 1

```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
    --> line 4, column 10
    4 |     {a = ping::get()} -> a
      |          ^^^^^^^^^
  hint: handle this computation with a matching effect handler before running it
  note: application occurs here
    --> line 4, column 10
    4 |     {a = ping::get()} -> a
      |          ^^^^^^^^^^^
```

## 160. default-function-directcatch-fixed / check

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()} = a
catch (pick {}):
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/default-function-directcatch-fixed.yu
```

UTC start: 2026-11-08T12:43:22.239541+00:00; elapsed: 0.007 s; exit: 0

```text
```

## 161. default-function-directcatch-fixed / dump

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()} = a
catch (pick {}):
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/default-function-directcatch-fixed.yu
```

UTC start: 2026-11-08T12:43:22.246902+00:00; elapsed: 0.007 s; exit: 0

```text
roots d0:ping d2:pick
d0:ping mod {
}
d2:pick: {a?: 'a} -> 'a | int = e4:(fn p1:{a: p0:d3:a = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:())} -> e3:r1:a->d3:a)
root exprs e12:catch e7:(e5:r2:pick->d2:pick e6:{}) { ping::get p2:_, p3:d5:k -> e10:(e8:r3:k->d5:k e9:7); p4:d6:value -> e11:r4:value->d6:value }
runtime roots e12:catch e7:(e5:r2:pick->d2:pick e6:{}) { ping::get p2:_, p3:d5:k -> e10:(e8:r3:k->d5:k e9:7); p4:d6:value -> e11:r4:value->d6:value }
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:a arg
  d5:k arg
  d6:value arg
}
```

## 162. default-function-directcatch-fixed / run

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()} = a
catch (pick {}):
    ping::get(), k -> k 7
    value -> value
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/default-function-directcatch-fixed.yu
```

UTC start: 2026-11-08T12:43:22.254320+00:00; elapsed: 0.004 s; exit: 0

```text
run roots [7]
```

## 163. default-pure-filter-fixed / check

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()}: [] int = a
pick {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/default-pure-filter-fixed.yu
```

UTC start: 2026-11-08T12:43:22.258634+00:00; elapsed: 0.004 s; exit: 0

```text
```

## 164. default-pure-filter-fixed / dump

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()}: [] int = a
pick {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/default-pure-filter-fixed.yu
```

UTC start: 2026-11-08T12:43:22.262676+00:00; elapsed: 0.005 s; exit: 0

```text
roots d0:ping d2:pick
d0:ping mod {
}
d2:pick: {a?: int} -> int = e4:(fn p1:{a: p0:d3:a = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:())} -> e3:r1:a->d3:a)
root exprs e7:(e5:r2:pick->d2:pick e6:{})
runtime roots e7:(e5:r2:pick->d2:pick e6:{})
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:a arg
}
```

## 165. default-pure-filter-fixed / run

```yulang
act ping:
    our get: () -> int
our pick {a = ping::get()}: [] int = a
pick {}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/default-pure-filter-fixed.yu
```

UTC start: 2026-11-08T12:43:22.267515+00:00; elapsed: 0.003 s; exit: 1

```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
    --> line 3, column 15
    3 | our pick {a = ping::get()}: [] int = a
      |               ^^^^^^^^^
  hint: handle this computation with a matching effect handler before running it
  note: application occurs here
    --> line 3, column 15
    3 | our pick {a = ping::get()}: [] int = a
      |               ^^^^^^^^^^^
```

## 166. default-inline-catch-fixed / check

```yulang
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {}:
    {a = ping::get()} -> a
):
    ping::get(), k -> k 7
    value -> value
 )
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-case/default-inline-catch-fixed.yu
```

UTC start: 2026-11-08T12:43:22.270948+00:00; elapsed: 0.008 s; exit: 1

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 9, column 2
    9 |  )
      |  ^
```

## 167. default-inline-catch-fixed / dump

```yulang
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {}:
    {a = ping::get()} -> a
):
    ping::get(), k -> k 7
    value -> value
 )
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit2-case/default-inline-catch-fixed.yu
```

UTC start: 2026-11-08T12:43:22.279065+00:00; elapsed: 0.008 s; exit: 0

```text
roots d0:ping d2:id
d0:ping mod {
}
d2:id: int -> int = e1:(fn p0:d3:x -> e0:r0:x->d3:x)
root exprs e14:(e2:r1:id->d2:id e13:catch e8:case e3:{} { p2:{a: p1:d5:a = e6:(e4:r2:"ping::get"->d1:"ping.get" e5:())} -> e7:r3:a->d5:a } { ping::get p3:_, p4:d6:k -> e11:(e9:r4:k->d6:k e10:7); p5:d7:value -> e12:r5:value->d7:value })
runtime roots e14:(e2:r1:id->d2:id e13:catch e8:case e3:{} { p2:{a: p1:d5:a = e6:(e4:r2:"ping::get"->d1:"ping.get" e5:())} -> e7:r3:a->d5:a } { ping::get p3:_, p4:d6:k -> e11:(e9:r4:k->d6:k e10:7); p5:d7:value -> e12:r5:value->d7:value })
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:x arg
  d5:a arg
  d6:k arg
  d7:value arg
}
```

## 168. default-inline-catch-fixed / run

```yulang
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {}:
    {a = ping::get()} -> a
):
    ping::get(), k -> k 7
    value -> value
 )
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-case/default-inline-catch-fixed.yu
```

UTC start: 2026-11-08T12:43:22.287035+00:00; elapsed: 0.003 s; exit: 1

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 9, column 2
    9 |  )
      |  ^
```
