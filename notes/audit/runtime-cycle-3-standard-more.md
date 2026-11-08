# Cycle 3 raw log: standard-more

新spec基点 `816ed8f1d`、旧実機 `d4c8bc8fc`。出力はそのまま。dump exit 0 は診断なしを意味しない。

## 1. body-direct

```yulang
act ping:
    our arg: () -> int
    our body: () -> int
our abort(action: [ping] int) = catch action:
    ping::arg(), k -> 11
    ping::body(), k -> 22
    value -> value
our actual(x:int):int = ping::body()
abort(actual(ping::arg()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit3/body-direct.yu
```

UTC start: 2026-11-08T13:47:19.717759+00:00; elapsed: 0.210509 s; exit: 0; timeout: False

stdout:
```text
run roots [11]

```

stderr:
```text

```

## 2. body-high

```yulang
act ping:
    our arg: () -> int
    our body: () -> int
our abort(action: [ping] int) = catch action:
    ping::arg(), k -> 11
    ping::body(), k -> 22
    value -> value
our actual(x:int):int = ping::body()
our higher f=f(ping::arg())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit3/body-high.yu
```

UTC start: 2026-11-08T13:47:19.928497+00:00; elapsed: 0.221177 s; exit: 0; timeout: False

stdout:
```text
run roots [22]

```

stderr:
```text

```

## 3. body-high-eta

```yulang
act ping:
    our arg: () -> int
    our body: () -> int
our abort(action: [ping] int) = catch action:
    ping::arg(), k -> 11
    ping::body(), k -> 22
    value -> value
our actual(x:int):int = ping::body()
our higher f=f(ping::arg())
abort(higher(\x -> actual x))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit3/body-high-eta.yu
```

UTC start: 2026-11-08T13:47:20.149891+00:00; elapsed: 0.211792 s; exit: 0; timeout: False

stdout:
```text
run roots [11]

```

stderr:
```text

```

## 4. high-inferred-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit3/high-inferred-ignore.yu
```

UTC start: 2026-11-08T13:47:20.361889+00:00; elapsed: 0.197056 s; exit: 0; timeout: False

stdout:
```text
run roots [42]

```

stderr:
```text

```

## 5. list-prefix-rest

```yulang
our split xs = case xs:
    [first, ..rest] -> (first, rest)
    [] -> (0, [])
(split [1, 2, 3], split [])

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib check /tmp/audit3/pattern-positive-cases/list-prefix-rest.yu
```

UTC start: 2026-11-08T13:47:20.559165+00:00; elapsed: 120.617126 s; exit: -9; timeout: False

stdout:
```text

```

stderr:
```text

```
