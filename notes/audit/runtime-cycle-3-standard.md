# Cycle 3 raw log: standard

新spec基点 `816ed8f1d`、旧実機 `d4c8bc8fc`。出力はそのまま。dump exit 0 は診断なしを意味しない。

## 1. pure-explicit

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib check /tmp/audit3/pure-explicit.yu
```

UTC start: 2026-11-08T13:33:40.003171+00:00; elapsed: 154.646679 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 2. pure-explicit

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit3/pure-explicit.yu
```

UTC start: 2026-11-08T13:36:14.650119+00:00; elapsed: 0.206733 s; exit: 0; timeout: False

stdout:
```text
run roots [3]

```

stderr:
```text

```

## 3. effectarg-pure-explicit

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib check /tmp/audit3/effectarg-pure-explicit.yu
```

UTC start: 2026-11-08T13:36:14.857074+00:00; elapsed: 160.717716 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 4. effectarg-pure-explicit

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit3/effectarg-pure-explicit.yu
```

UTC start: 2026-11-08T13:38:55.575015+00:00; elapsed: 165.267348 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```
