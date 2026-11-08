# Cycle 3 list remainder renamed controls: full raw log

## list-suffix-rest-renamed / check

```yulang
our split xs = case xs:
    [..init, end_item] -> (init, end_item)
    [] -> ([], 0)
(split [1, 2, 3], split [])
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib check /tmp/audit3/pattern-positive-cases/list-suffix-rest-renamed.yu
```

UTC 2026-11-08T13:48:11.802340+00:00; elapsed 30.064110s; exit None; timeout True

stdout:
```text

```

stderr:
```text

```

## list-suffix-rest-renamed / run

```yulang
our split xs = case xs:
    [..init, end_item] -> (init, end_item)
    [] -> ([], 0)
(split [1, 2, 3], split [])
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit3/pattern-positive-cases/list-suffix-rest-renamed.yu
```

UTC 2026-11-08T13:48:41.866981+00:00; elapsed 30.067945s; exit None; timeout True

stdout:
```text

```

stderr:
```text

```

## list-middle-rest-renamed / check

```yulang
our split xs = case xs:
    [first, ..middle, end_item] -> (first, middle, end_item)
    _ -> (0, [], 0)
(split [1, 2, 3, 4], split [1, 4], split [1])
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib check /tmp/audit3/pattern-positive-cases/list-middle-rest-renamed.yu
```

UTC 2026-11-08T13:49:11.935298+00:00; elapsed 30.102678s; exit None; timeout True

stdout:
```text

```

stderr:
```text

```

## list-middle-rest-renamed / run

```yulang
our split xs = case xs:
    [first, ..middle, end_item] -> (first, middle, end_item)
    _ -> (0, [], 0)
(split [1, 2, 3, 4], split [1, 4], split [1])
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit3/pattern-positive-cases/list-middle-rest-renamed.yu
```

UTC 2026-11-08T13:49:42.038318+00:00; elapsed 0.246190s; exit 0; timeout False

stdout:
```text
run roots [((1, [2, 3], 4), (1, [], 4), (0, [], 0))]

```

stderr:
```text

```