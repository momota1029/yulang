# Cycle3 completeness-side candidates: raw logs

Y2 binary main@d4c8bc8fc; no-prelude. These are concrete candidates, not general completeness proofs.

## head-rest-y / check

```yulang
our keep {..whole, x} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache check /tmp/audit3/rest-cases/head-rest-y.yu
```

UTC: 2026-11-08T13:39:04.060127+00:00; elapsed: 0.005051s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## head-rest-y / dump

```yulang
our keep {..whole, x} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache dump --poly /tmp/audit3/rest-cases/head-rest-y.yu
```

UTC: 2026-11-08T13:39:04.065342+00:00; elapsed: 0.004051s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: ('a & {x: 'b}) -> 'a | {..never, x: 'b} = e1:(fn p2:{..d1:whole, x: p1:d2:x} -> e0:r0:whole->d1:whole)
root exprs e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
runtime roots e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
detached {
  d1:whole arg
  d2:x arg
}

```

stderr:
```text

```

## head-rest-y / run

```yulang
our keep {..whole, x} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache run --print-roots /tmp/audit3/rest-cases/head-rest-y.yu
```

UTC: 2026-11-08T13:39:04.069527+00:00; elapsed: 0.003994s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {x: 'open2} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```

## only-rest-y / check

```yulang
our keep {..whole} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache check /tmp/audit3/rest-cases/only-rest-y.yu
```

UTC: 2026-11-08T13:39:04.073696+00:00; elapsed: 0.003508s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## only-rest-y / dump

```yulang
our keep {..whole} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache dump --poly /tmp/audit3/rest-cases/only-rest-y.yu
```

UTC: 2026-11-08T13:39:04.077344+00:00; elapsed: 0.003466s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: ('a & {}) -> 'a | {..never} = e1:(fn p1:{..d1:whole} -> e0:r0:whole->d1:whole)
root exprs e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
runtime roots e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
detached {
  d1:whole arg
}

```

stderr:
```text

```

## only-rest-y / run

```yulang
our keep {..whole} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache run --print-roots /tmp/audit3/rest-cases/only-rest-y.yu
```

UTC: 2026-11-08T13:39:04.080957+00:00; elapsed: 0.003668s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```

## both-fields-y / check

```yulang
our keep {x, y, ..whole} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache check /tmp/audit3/rest-cases/both-fields-y.yu
```

UTC: 2026-11-08T13:39:04.084794+00:00; elapsed: 0.003456s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## both-fields-y / dump

```yulang
our keep {x, y, ..whole} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache dump --poly /tmp/audit3/rest-cases/both-fields-y.yu
```

UTC: 2026-11-08T13:39:04.088406+00:00; elapsed: 0.005284s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: ('a & {x: 'b, y: 'c}) -> 'a | {x: 'b, y: 'c, ..never} = e1:(fn p3:{x: p0:d1:x, y: p1:d2:y, ..d3:whole} -> e0:r0:whole->d3:whole)
root exprs e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
runtime roots e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
detached {
  d1:x arg
  d2:y arg
  d3:whole arg
}

```

stderr:
```text

```

## both-fields-y / run

```yulang
our keep {x, y, ..whole} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache run --print-roots /tmp/audit3/rest-cases/both-fields-y.yu
```

UTC: 2026-11-08T13:39:04.093904+00:00; elapsed: 0.006131s; exit: 0; timeout: False

stdout:
```text
run roots ["kept"]

```

stderr:
```text

```

## alias-whole-y / check

```yulang
our keep ({x} as whole) = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache check /tmp/audit3/rest-cases/alias-whole-y.yu
```

UTC: 2026-11-08T13:39:04.100280+00:00; elapsed: 0.013961s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## alias-whole-y / dump

```yulang
our keep ({x} as whole) = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache dump --poly /tmp/audit3/rest-cases/alias-whole-y.yu
```

UTC: 2026-11-08T13:39:04.114485+00:00; elapsed: 0.023774s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: {x: 'a} -> {x: 'a} = e1:(fn p2:(p1:{x: p0:d1:x} as d2:whole) -> e0:r0:whole->d2:whole)
root exprs e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
runtime roots e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
detached {
  d1:x arg
  d2:whole arg
}

```

stderr:
```text

```

## alias-whole-y / run

```yulang
our keep ({x} as whole) = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache run --print-roots /tmp/audit3/rest-cases/alias-whole-y.yu
```

UTC: 2026-11-08T13:39:04.138607+00:00; elapsed: 0.005226s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {x: 'open1} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```

## lambda-direct-y / check

```yulang
((\{x, ..whole} -> whole) {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache check /tmp/audit3/rest-cases/lambda-direct-y.yu
```

UTC: 2026-11-08T13:39:04.144125+00:00; elapsed: 0.004305s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## lambda-direct-y / dump

```yulang
((\{x, ..whole} -> whole) {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache dump --poly /tmp/audit3/rest-cases/lambda-direct-y.yu
```

UTC: 2026-11-08T13:39:04.148690+00:00; elapsed: 0.004195s; exit: 0; timeout: False

stdout:
```text
roots
root exprs e6:(e5:(e1:(fn p2:{x: p0:d1:x, ..d2:whole} -> e0:r0:whole->d2:whole) e4:{x: e2:7, y: e3:"kept"}).s0.y#field)
runtime roots e6:(e5:(e1:(fn p2:{x: p0:d1:x, ..d2:whole} -> e0:r0:whole->d2:whole) e4:{x: e2:7, y: e3:"kept"}).s0.y#field)
detached {
  d1:x arg
  d2:whole arg
}

```

stderr:
```text

```

## lambda-direct-y / run

```yulang
((\{x, ..whole} -> whole) {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache run --print-roots /tmp/audit3/rest-cases/lambda-direct-y.yu
```

UTC: 2026-11-08T13:39:04.153250+00:00; elapsed: 0.004345s; exit: 0; timeout: False

stdout:
```text
run roots ["kept"]

```

stderr:
```text

```

## named-lambda-y / check

```yulang
our keep = \{x, ..whole} -> whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache check /tmp/audit3/rest-cases/named-lambda-y.yu
```

UTC: 2026-11-08T13:39:04.157867+00:00; elapsed: 0.003805s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## named-lambda-y / dump

```yulang
our keep = \{x, ..whole} -> whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache dump --poly /tmp/audit3/rest-cases/named-lambda-y.yu
```

UTC: 2026-11-08T13:39:04.161919+00:00; elapsed: 0.003613s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: ('a & {x: 'b}) -> 'a | {x: 'b, ..never} = e1:(fn p2:{x: p0:d1:x, ..d2:whole} -> e0:r0:whole->d2:whole)
root exprs e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
runtime roots e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
detached {
  d1:x arg
  d2:whole arg
}

```

stderr:
```text

```

## named-lambda-y / run

```yulang
our keep = \{x, ..whole} -> whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache run --print-roots /tmp/audit3/rest-cases/named-lambda-y.yu
```

UTC: 2026-11-08T13:39:04.165803+00:00; elapsed: 0.003876s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {x: 'open2} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```

## computed-binding-y / check

```yulang
my kept = (\{x, ..whole} -> whole) {x: 7, y: "kept"}
kept.y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache check /tmp/audit3/rest-cases/computed-binding-y.yu
```

UTC: 2026-11-08T13:39:04.170114+00:00; elapsed: 0.003513s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## computed-binding-y / dump

```yulang
my kept = (\{x, ..whole} -> whole) {x: 7, y: "kept"}
kept.y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache dump --poly /tmp/audit3/rest-cases/computed-binding-y.yu
```

UTC: 2026-11-08T13:39:04.173895+00:00; elapsed: 0.003370s; exit: 0; timeout: False

stdout:
```text
roots d0:kept
my d0:kept: {x: int, y: std::text::str::str} | {x: int, ..never} = e5:(e1:(fn p2:{x: p0:d1:x, ..d2:whole} -> e0:r0:whole->d2:whole) e4:{x: e2:7, y: e3:"kept"})
root exprs e7:(e6:r1:kept->d0:kept.s0.y#field)
runtime roots d0:kept e7:(e6:r1:kept->d0:kept.s0.y#field)
detached {
  d1:x arg
  d2:whole arg
}

```

stderr:
```text

```

## computed-binding-y / run

```yulang
my kept = (\{x, ..whole} -> whole) {x: 7, y: "kept"}
kept.y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude --no-cache run --print-roots /tmp/audit3/rest-cases/computed-binding-y.yu
```

UTC: 2026-11-08T13:39:04.177606+00:00; elapsed: 0.003621s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {x: int} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```
