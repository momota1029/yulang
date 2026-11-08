# Cycle 4 recovery runtime checks

既存cycle3の3対照を同一旧Y2実機で再実行。新しい意味論判断は行わない。

## body-direct

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/body-direct.yu
```

UTC: 2026-11-08T14:27:11.131261+00:00; elapsed: 0.003866s; exit: 0

stdout:
```text
run roots [11]

```
stderr:
```text

```

## body-high

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/body-high.yu
```

UTC: 2026-11-08T14:27:11.135260+00:00; elapsed: 0.002932s; exit: 0

stdout:
```text
run roots [22]

```
stderr:
```text

```

## body-high-eta

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/body-high-eta.yu
```

UTC: 2026-11-08T14:27:11.138294+00:00; elapsed: 0.003172s; exit: 0

stdout:
```text
run roots [11]

```
stderr:
```text

```
