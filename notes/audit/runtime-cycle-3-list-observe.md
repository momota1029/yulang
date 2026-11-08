# Cycle3 completeness-side candidates: raw logs

Y2 binary main@d4c8bc8fc; no-prelude. These are concrete candidates, not general completeness proofs.

## list-prefix-rest-observe / run

```yulang
our split xs = case xs:
    [first, ..rest] -> case rest:
        [second, third] -> (first, second, third)
        _ -> (first, 0, 0)
    [] -> (0,0,0)
(split [1,2,3], split [9], split [])
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit3/pattern-positive-cases/list-prefix-rest-observe.yu
```

UTC: 2026-11-08T13:43:28.954357+00:00; elapsed: 8.043137s; exit: None; timeout: True

stdout:
```text

```

stderr:
```text

```

## list-suffix-rest-observe / run

```yulang
our split xs = case xs:
    [..init, last] -> case init:
        [first, second] -> (first, second, last)
        _ -> (0, 0, last)
    [] -> (0,0,0)
(split [1,2,3], split [9], split [])
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit3/pattern-positive-cases/list-suffix-rest-observe.yu
```

UTC: 2026-11-08T13:43:36.997847+00:00; elapsed: 8.050134s; exit: None; timeout: True

stdout:
```text

```

stderr:
```text

```

## list-middle-rest-observe / run

```yulang
our split xs = case xs:
    [first, ..middle, last] -> case middle:
        [a, b] -> (first, a, b, last)
        [] -> (first, 0, 0, last)
        _ -> (0,0,0,0)
    _ -> (0,0,0,0)
(split [1,2,3,4], split [1,4], split [1])
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib run --print-roots /tmp/audit3/pattern-positive-cases/list-middle-rest-observe.yu
```

UTC: 2026-11-08T13:43:45.048305+00:00; elapsed: 0.277420s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
runtime error [yulang.unhandled-effect]: unhandled effect request std::control::flow::loop::last
  hint: handle this computation with a matching effect handler before running it

```
