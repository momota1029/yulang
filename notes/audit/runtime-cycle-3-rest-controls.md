# Cycle3 completeness-side candidates: raw logs

Y2 binary main@d4c8bc8fc; no-prelude. These are concrete candidates, not general completeness proofs.

## head-rest-y / check

```yulang
our keep {..whole, x} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/rest-cases/head-rest-y.yu
```

UTC: 2026-11-08T13:38:20.341015+00:00; elapsed: 0.006457s; exit: 0; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/rest-cases/head-rest-y.yu
```

UTC: 2026-11-08T13:38:20.347715+00:00; elapsed: 0.007610s; exit: 0; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/rest-cases/head-rest-y.yu
```

UTC: 2026-11-08T13:38:20.355550+00:00; elapsed: 0.006669s; exit: 1; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/rest-cases/only-rest-y.yu
```

UTC: 2026-11-08T13:38:20.362492+00:00; elapsed: 0.004684s; exit: 0; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/rest-cases/only-rest-y.yu
```

UTC: 2026-11-08T13:38:20.367343+00:00; elapsed: 0.005184s; exit: 0; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/rest-cases/only-rest-y.yu
```

UTC: 2026-11-08T13:38:20.372757+00:00; elapsed: 0.007328s; exit: 1; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/rest-cases/both-fields-y.yu
```

UTC: 2026-11-08T13:38:20.380353+00:00; elapsed: 0.004900s; exit: 0; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/rest-cases/both-fields-y.yu
```

UTC: 2026-11-08T13:38:20.385618+00:00; elapsed: 0.005798s; exit: 0; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/rest-cases/both-fields-y.yu
```

UTC: 2026-11-08T13:38:20.391643+00:00; elapsed: 0.003849s; exit: 0; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/rest-cases/alias-whole-y.yu
```

UTC: 2026-11-08T13:38:20.395770+00:00; elapsed: 0.004168s; exit: 0; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/rest-cases/alias-whole-y.yu
```

UTC: 2026-11-08T13:38:20.400143+00:00; elapsed: 0.004504s; exit: 0; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/rest-cases/alias-whole-y.yu
```

UTC: 2026-11-08T13:38:20.404929+00:00; elapsed: 0.005703s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {x: 'open1} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```

## plain-input-case-y / check

```yulang
our keep whole = case whole:
    {x} -> whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/rest-cases/plain-input-case-y.yu
```

UTC: 2026-11-08T13:38:20.410892+00:00; elapsed: 0.005899s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## plain-input-case-y / dump

```yulang
our keep whole = case whole:
    {x} -> whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/rest-cases/plain-input-case-y.yu
```

UTC: 2026-11-08T13:38:20.417112+00:00; elapsed: 0.005145s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: {x: 'a} -> {x: 'a} = e3:(fn p0:d1:whole -> e2:case e0:r0:whole->d1:whole { p2:{x: p1:d2:x} -> e1:r1:whole->d1:whole })
root exprs e9:(e8:(e4:r2:keep->d0:keep e7:{x: e5:7, y: e6:"kept"}).s0.y#field)
runtime roots e9:(e8:(e4:r2:keep->d0:keep e7:{x: e5:7, y: e6:"kept"}).s0.y#field)
detached {
  d1:whole arg
  d2:x arg
}

```

stderr:
```text

```

## plain-input-case-y / run

```yulang
our keep whole = case whole:
    {x} -> whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/rest-cases/plain-input-case-y.yu
```

UTC: 2026-11-08T13:38:20.422516+00:00; elapsed: 0.006419s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {x: 'open1} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```

## case-rest-y / check

```yulang
our keep input = case input:
    {x, ..whole} -> whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/rest-cases/case-rest-y.yu
```

UTC: 2026-11-08T13:38:20.429428+00:00; elapsed: 0.005454s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## case-rest-y / dump

```yulang
our keep input = case input:
    {x, ..whole} -> whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/rest-cases/case-rest-y.yu
```

UTC: 2026-11-08T13:38:20.435151+00:00; elapsed: 0.006538s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: ('a & {x: 'b}) -> 'a | {x: 'b, ..never} = e3:(fn p0:d1:input -> e2:case e0:r0:input->d1:input { p3:{x: p1:d2:x, ..d3:whole} -> e1:r1:whole->d3:whole })
root exprs e9:(e8:(e4:r2:keep->d0:keep e7:{x: e5:7, y: e6:"kept"}).s0.y#field)
runtime roots e9:(e8:(e4:r2:keep->d0:keep e7:{x: e5:7, y: e6:"kept"}).s0.y#field)
detached {
  d1:input arg
  d2:x arg
  d3:whole arg
}

```

stderr:
```text

```

## case-rest-y / run

```yulang
our keep input = case input:
    {x, ..whole} -> whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/rest-cases/case-rest-y.yu
```

UTC: 2026-11-08T13:38:20.442241+00:00; elapsed: 0.005838s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {x: 'open2} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```

## local-rest-y / check

```yulang
my {x, ..whole} = {x: 7, y: "kept"}
whole.y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/rest-cases/local-rest-y.yu
```

UTC: 2026-11-08T13:38:20.448892+00:00; elapsed: 0.002642s; exit: 1; timeout: False

stdout:
```text
diagnostics:
  error [yulang.unresolved-value]: unresolved value name in root expression: whole
    --> line 2, column 1
    2 | whole.y
      | ^^^^^
    hint: define `whole` before this use, or import the module that provides it

```

stderr:
```text

```

## local-rest-y / dump

```yulang
my {x, ..whole} = {x: 7, y: "kept"}
whole.y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/rest-cases/local-rest-y.yu
```

UTC: 2026-11-08T13:38:20.451840+00:00; elapsed: 0.003598s; exit: 0; timeout: False

stdout:
```text
roots

```

stderr:
```text
error: unresolved value name in root expression: whole

```

## local-rest-y / run

```yulang
my {x, ..whole} = {x: 7, y: "kept"}
whole.y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/rest-cases/local-rest-y.yu
```

UTC: 2026-11-08T13:38:20.455795+00:00; elapsed: 0.003288s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name in root expression: whole
  hint: run `yulang check` to see source ranges before running

```

## lambda-direct-y / check

```yulang
((\{x, ..whole} -> whole) {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/rest-cases/lambda-direct-y.yu
```

UTC: 2026-11-08T13:38:20.459461+00:00; elapsed: 0.003423s; exit: 0; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/rest-cases/lambda-direct-y.yu
```

UTC: 2026-11-08T13:38:20.463309+00:00; elapsed: 0.005150s; exit: 0; timeout: False

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/rest-cases/lambda-direct-y.yu
```

UTC: 2026-11-08T13:38:20.468887+00:00; elapsed: 0.004580s; exit: 0; timeout: False

stdout:
```text
run roots ["kept"]

```

stderr:
```text

```

## rest-default-y / check

```yulang
our keep {x = 7, ..whole} = whole
(keep {y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/rest-cases/rest-default-y.yu
```

UTC: 2026-11-08T13:38:20.473934+00:00; elapsed: 0.005032s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## rest-default-y / dump

```yulang
our keep {x = 7, ..whole} = whole
(keep {y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/rest-cases/rest-default-y.yu
```

UTC: 2026-11-08T13:38:20.479430+00:00; elapsed: 0.004422s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: ('a & {x?: 'b}) -> 'a | {x?: 'b, ..never} = e2:(fn p2:{x: p0:d1:x = e0:7, ..d2:whole} -> e1:r0:whole->d2:whole)
root exprs e7:(e6:(e3:r1:keep->d0:keep e5:{y: e4:"kept"}).s0.y#field)
runtime roots e7:(e6:(e3:r1:keep->d0:keep e5:{y: e4:"kept"}).s0.y#field)
detached {
  d1:x arg
  d2:whole arg
}

```

stderr:
```text

```

## rest-default-y / run

```yulang
our keep {x = 7, ..whole} = whole
(keep {y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/rest-cases/rest-default-y.yu
```

UTC: 2026-11-08T13:38:20.484301+00:00; elapsed: 0.007370s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {x?: 'open2} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```

## whole-then-get-y / check

```yulang
our keep {x, ..whole} = whole
our get r = r.y
get (keep {x: 7, y: "kept"})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/rest-cases/whole-then-get-y.yu
```

UTC: 2026-11-08T13:38:20.492179+00:00; elapsed: 0.004616s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## whole-then-get-y / dump

```yulang
our keep {x, ..whole} = whole
our get r = r.y
get (keep {x: 7, y: "kept"})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/rest-cases/whole-then-get-y.yu
```

UTC: 2026-11-08T13:38:20.497324+00:00; elapsed: 0.006911s; exit: 0; timeout: False

stdout:
```text
roots d0:keep d1:get
d0:keep: ('a & {x: 'b}) -> 'a | {x: 'b, ..never} = e1:(fn p2:{x: p0:d2:x, ..d3:whole} -> e0:r0:whole->d3:whole)
d1:get: {y: 'a} -> 'a = e4:(fn p3:d4:r -> e3:(e2:r1:r->d4:r.s0.y#field))
root exprs e11:(e5:r2:get->d1:get e10:(e6:r3:keep->d0:keep e9:{x: e7:7, y: e8:"kept"}))
runtime roots e11:(e5:r2:get->d1:get e10:(e6:r3:keep->d0:keep e9:{x: e7:7, y: e8:"kept"}))
detached {
  d2:x arg
  d3:whole arg
  d4:r arg
}

```

stderr:
```text

```

## whole-then-get-y / run

```yulang
our keep {x, ..whole} = whole
our get r = r.y
get (keep {x: 7, y: "kept"})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/rest-cases/whole-then-get-y.yu
```

UTC: 2026-11-08T13:38:20.504904+00:00; elapsed: 0.007520s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {x: 'open2} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```

## width-only-identity-y / check

```yulang
our keep whole = whole
my {x} = keep {x: 7, y: "kept"}
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/rest-cases/width-only-identity-y.yu
```

UTC: 2026-11-08T13:38:20.513036+00:00; elapsed: 0.004904s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## width-only-identity-y / dump

```yulang
our keep whole = whole
my {x} = keep {x: 7, y: "kept"}
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/rest-cases/width-only-identity-y.yu
```

UTC: 2026-11-08T13:38:20.518389+00:00; elapsed: 0.005300s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: 'a -> 'a = e1:(fn p0:d1:whole -> e0:r0:whole->d1:whole)
root exprs e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
runtime roots e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
detached {
  d1:whole arg
}

```

stderr:
```text

```

## width-only-identity-y / run

```yulang
our keep whole = whole
my {x} = keep {x: 7, y: "kept"}
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/rest-cases/width-only-identity-y.yu
```

UTC: 2026-11-08T13:38:20.524061+00:00; elapsed: 0.003609s; exit: 0; timeout: False

stdout:
```text
run roots ["kept"]

```

stderr:
```text

```

## direct-input-case-alias-y / check

```yulang
our keep whole = case whole:
    {x, ..rest} -> whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/rest-cases/direct-input-case-alias-y.yu
```

UTC: 2026-11-08T13:38:20.528051+00:00; elapsed: 0.006845s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## direct-input-case-alias-y / dump

```yulang
our keep whole = case whole:
    {x, ..rest} -> whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/rest-cases/direct-input-case-alias-y.yu
```

UTC: 2026-11-08T13:38:20.535289+00:00; elapsed: 0.006178s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: ('a & {x: 'b}) -> 'a | {x: 'b, ..never} = e3:(fn p0:d1:whole -> e2:case e0:r0:whole->d1:whole { p3:{x: p1:d2:x, ..d3:rest} -> e1:r1:whole->d1:whole })
root exprs e9:(e8:(e4:r2:keep->d0:keep e7:{x: e5:7, y: e6:"kept"}).s0.y#field)
runtime roots e9:(e8:(e4:r2:keep->d0:keep e7:{x: e5:7, y: e6:"kept"}).s0.y#field)
detached {
  d1:whole arg
  d2:x arg
  d3:rest arg
}

```

stderr:
```text

```

## direct-input-case-alias-y / run

```yulang
our keep whole = case whole:
    {x, ..rest} -> whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/rest-cases/direct-input-case-alias-y.yu
```

UTC: 2026-11-08T13:38:20.541881+00:00; elapsed: 0.006285s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {x: 'open2} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```
