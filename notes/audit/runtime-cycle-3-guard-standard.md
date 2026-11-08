# Cycle 3 raw log: guard-standard

新spec基点 `816ed8f1d`、旧実機 `d4c8bc8fc`。出力はそのまま。dump exit 0 は診断なしを意味しない。

## 1. guard-matched-only

```yulang
act ping:
    our get: () -> bool
our abort(action: [ping] int): int = catch action:
    ping::get(), k -> 99
    value -> value
our yes(action: [ping] int): int = catch action:
    ping::get(), k -> k true
    value -> value
our no(action: [ping] int): int = catch action:
    ping::get(), k -> k false
    value -> value
our decide(n:int):int = case n:
    1 if ping::get() -> 10
    _ -> 20
(abort(decide 1),abort(decide 2),yes(decide 1),no(decide 1))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib check /tmp/audit3/guard-matched-only.yu
```

UTC start: 2026-11-08T13:47:47.937282+00:00; elapsed: 146.828114 s; exit: -9; timeout: False

stdout:
```text

```

stderr:
```text

```

## 2. guard-matched-only

```yulang
act ping:
    our get: () -> bool
our abort(action: [ping] int): int = catch action:
    ping::get(), k -> 99
    value -> value
our yes(action: [ping] int): int = catch action:
    ping::get(), k -> k true
    value -> value
our no(action: [ping] int): int = catch action:
    ping::get(), k -> k false
    value -> value
our decide(n:int):int = case n:
    1 if ping::get() -> 10
    _ -> 20
(abort(decide 1),abort(decide 2),yes(decide 1),no(decide 1))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit3/guard-matched-only.yu
```

UTC start: 2026-11-08T13:50:14.765688+00:00; elapsed: 0.235364 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
    --> line 13, column 10
    13 |     1 if ping::get() -> 10
       |          ^^^^^^^^^
  hint: handle this computation with a matching effect handler before running it
  note: application occurs here
    --> line 13, column 10
    13 |     1 if ping::get() -> 10
       |          ^^^^^^^^^^^^

```
