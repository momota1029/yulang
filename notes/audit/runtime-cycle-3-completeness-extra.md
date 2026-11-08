# Cycle3 completeness-side candidates: raw logs

Y2 binary main@d4c8bc8fc; no-prelude. These are concrete candidates, not general completeness proofs.

## phantom-text / check

```yulang
type text
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom int = phantom::next (phantom::next phantom::end)
my b: phantom text = a
b
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/phantom-text.yu
```

UTC: 2026-11-08T13:31:54.368167+00:00; elapsed: 0.014619s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## phantom-text / dump

```yulang
type text
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom int = phantom::next (phantom::next phantom::end)
my b: phantom text = a
b
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/phantom-text.yu
```

UTC: 2026-11-08T13:31:54.383060+00:00; elapsed: 0.008626s; exit: 0; timeout: False

stdout:
```text
roots d0:phantom d3:a d4:b
d0:phantom mod {
  d1:"phantom.end": phantom 'a = <missing>
  d2:"phantom.next": phantom 'a -> phantom 'a = <missing>
}
my d3:a: phantom int = e4:(e0:r0:"phantom::next"->d2:"phantom.next" e3:(e1:r1:"phantom::next"->d2:"phantom.next" e2:r2:"phantom::end"->d1:"phantom.end"))
my d4:b: phantom text = e5:r3:a->d3:a
root exprs e6:r4:b->d4:b
runtime roots d3:a e6:r4:b->d4:b

```

stderr:
```text

```

## phantom-text / run

```yulang
type text
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom int = phantom::next (phantom::next phantom::end)
my b: phantom text = a
b
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/phantom-text.yu
```

UTC: 2026-11-08T13:31:54.391952+00:00; elapsed: 0.010339s; exit: 0; timeout: False

stdout:
```text
run roots [phantom::next(phantom::next(phantom::end))]

```

stderr:
```text

```

## variant-case-join / check

```yulang
our make flag = case flag:
    true -> :some 7
    false -> :none
our consume x = case x:
    :some value -> value
    :none -> 0
(consume (make true), consume (make false))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/variant-case-join.yu
```

UTC: 2026-11-08T13:31:54.405897+00:00; elapsed: 0.011571s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## variant-case-join / dump

```yulang
our make flag = case flag:
    true -> :some 7
    false -> :none
our consume x = case x:
    :some value -> value
    :none -> 0
(consume (make true), consume (make false))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/variant-case-join.yu
```

UTC: 2026-11-08T13:31:54.418050+00:00; elapsed: 0.023437s; exit: 0; timeout: False

stdout:
```text
roots d0:make d1:consume
d0:make: bool -> :{some int, none} = e5:(fn p0:d2:flag -> e4:case e0:r0:flag->d2:flag { p1:true -> e2::some(e1:7); p2:false -> e3::none })
d1:consume: :{some 'a, none} -> 'a | int = e10:(fn p3:d3:x -> e9:case e6:r1:x->d3:x { p5::some(p4:d4:value) -> e7:r2:value->d4:value; p6::none -> e8:0 })
root exprs e21:(e15:(e11:r3:consume->d1:consume e14:(e12:r4:make->d0:make e13:true)), e20:(e16:r5:consume->d1:consume e19:(e17:r6:make->d0:make e18:false)))
runtime roots e21:(e15:(e11:r3:consume->d1:consume e14:(e12:r4:make->d0:make e13:true)), e20:(e16:r5:consume->d1:consume e19:(e17:r6:make->d0:make e18:false)))
detached {
  d2:flag arg
  d3:x arg
  d4:value arg
}

```

stderr:
```text

```

## variant-case-join / run

```yulang
our make flag = case flag:
    true -> :some 7
    false -> :none
our consume x = case x:
    :some value -> value
    :none -> 0
(consume (make true), consume (make false))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/variant-case-join.yu
```

UTC: 2026-11-08T13:31:54.441822+00:00; elapsed: 0.009890s; exit: 0; timeout: False

stdout:
```text
run roots [(7, 0)]

```

stderr:
```text

```

## spread-return-whole / check

```yulang
our keep {x, ..whole} = whole
keep {x: 7, y: "kept"}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/spread-return-whole.yu
```

UTC: 2026-11-08T13:31:54.452029+00:00; elapsed: 0.006214s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## spread-return-whole / dump

```yulang
our keep {x, ..whole} = whole
keep {x: 7, y: "kept"}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/spread-return-whole.yu
```

UTC: 2026-11-08T13:31:54.458733+00:00; elapsed: 0.005553s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: ('a & {x: 'b}) -> 'a | {x: 'b, ..never} = e1:(fn p2:{x: p0:d1:x, ..d2:whole} -> e0:r0:whole->d2:whole)
root exprs e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"})
runtime roots e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"})
detached {
  d1:x arg
  d2:whole arg
}

```

stderr:
```text

```

## spread-return-whole / run

```yulang
our keep {x, ..whole} = whole
keep {x: 7, y: "kept"}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/spread-return-whole.yu
```

UTC: 2026-11-08T13:31:54.464864+00:00; elapsed: 0.004192s; exit: 0; timeout: False

stdout:
```text
run roots [{x: 7, y: "kept"}]

```

stderr:
```text

```

## spread-project-x / check

```yulang
our keep {x, ..whole} = whole
(keep {x: 7, y: "kept"}).x
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/spread-project-x.yu
```

UTC: 2026-11-08T13:31:54.469409+00:00; elapsed: 0.011480s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## spread-project-x / dump

```yulang
our keep {x, ..whole} = whole
(keep {x: 7, y: "kept"}).x
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/spread-project-x.yu
```

UTC: 2026-11-08T13:31:54.481267+00:00; elapsed: 0.015880s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: ('a & {x: 'b}) -> 'a | {x: 'b, ..never} = e1:(fn p2:{x: p0:d1:x, ..d2:whole} -> e0:r0:whole->d2:whole)
root exprs e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.x#field)
runtime roots e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.x#field)
detached {
  d1:x arg
  d2:whole arg
}

```

stderr:
```text

```

## spread-project-x / run

```yulang
our keep {x, ..whole} = whole
(keep {x: 7, y: "kept"}).x
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/spread-project-x.yu
```

UTC: 2026-11-08T13:31:54.497646+00:00; elapsed: 0.004726s; exit: 0; timeout: False

stdout:
```text
run roots [7]

```

stderr:
```text

```

## spread-inside-project-y / check

```yulang
our keep {x, ..whole} = whole.y
keep {x: 7, y: "kept"}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/spread-inside-project-y.yu
```

UTC: 2026-11-08T13:31:54.502720+00:00; elapsed: 0.005923s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## spread-inside-project-y / dump

```yulang
our keep {x, ..whole} = whole.y
keep {x: 7, y: "kept"}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/spread-inside-project-y.yu
```

UTC: 2026-11-08T13:31:54.509194+00:00; elapsed: 0.006889s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: {x: any, y: 'a} -> 'a = e2:(fn p2:{x: p0:d1:x, ..d2:whole} -> e1:(e0:r0:whole->d2:whole.s0.y#field))
root exprs e7:(e3:r1:keep->d0:keep e6:{x: e4:7, y: e5:"kept"})
runtime roots e7:(e3:r1:keep->d0:keep e6:{x: e4:7, y: e5:"kept"})
detached {
  d1:x arg
  d2:whole arg
}

```

stderr:
```text

```

## spread-inside-project-y / run

```yulang
our keep {x, ..whole} = whole.y
keep {x: 7, y: "kept"}
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/spread-inside-project-y.yu
```

UTC: 2026-11-08T13:31:54.516390+00:00; elapsed: 0.004692s; exit: 0; timeout: False

stdout:
```text
run roots ["kept"]

```

stderr:
```text

```

## spread-monomorphic-y / check

```yulang
my kept = (\{x, ..whole} -> whole) {x: 7, y: "kept"}
kept.y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/spread-monomorphic-y.yu
```

UTC: 2026-11-08T13:31:54.522119+00:00; elapsed: 0.006999s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## spread-monomorphic-y / dump

```yulang
my kept = (\{x, ..whole} -> whole) {x: 7, y: "kept"}
kept.y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/spread-monomorphic-y.yu
```

UTC: 2026-11-08T13:31:54.529678+00:00; elapsed: 0.005935s; exit: 0; timeout: False

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

## spread-monomorphic-y / run

```yulang
my kept = (\{x, ..whole} -> whole) {x: 7, y: "kept"}
kept.y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/spread-monomorphic-y.yu
```

UTC: 2026-11-08T13:31:54.535938+00:00; elapsed: 0.005383s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {x: int} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```

## identity-record-y / check

```yulang
our keep whole = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/identity-record-y.yu
```

UTC: 2026-11-08T13:31:54.543256+00:00; elapsed: 0.006529s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## identity-record-y / dump

```yulang
our keep whole = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/identity-record-y.yu
```

UTC: 2026-11-08T13:31:54.550793+00:00; elapsed: 0.007791s; exit: 0; timeout: False

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

## identity-record-y / run

```yulang
our keep whole = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/identity-record-y.yu
```

UTC: 2026-11-08T13:31:54.559046+00:00; elapsed: 0.005409s; exit: 0; timeout: False

stdout:
```text
run roots ["kept"]

```

stderr:
```text

```

## pattern-spread-reconstruct / check

```yulang
our keep {x, ..whole} = {..whole}
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/pattern-spread-reconstruct.yu
```

UTC: 2026-11-08T13:31:54.565159+00:00; elapsed: 0.009938s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## pattern-spread-reconstruct / dump

```yulang
our keep {x, ..whole} = {..whole}
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/pattern-spread-reconstruct.yu
```

UTC: 2026-11-08T13:31:54.575533+00:00; elapsed: 0.006608s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: ('a & {x: 'b}) -> {..'a | {x: 'b, ..never}} = e2:(fn p2:{x: p0:d1:x, ..d2:whole} -> e1:{..e0:r0:whole->d2:whole})
root exprs e8:(e7:(e3:r1:keep->d0:keep e6:{x: e4:7, y: e5:"kept"}).s0.y#field)
runtime roots e8:(e7:(e3:r1:keep->d0:keep e6:{x: e4:7, y: e5:"kept"}).s0.y#field)
detached {
  d1:x arg
  d2:whole arg
}

```

stderr:
```text

```

## pattern-spread-reconstruct / run

```yulang
our keep {x, ..whole} = {..whole}
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/pattern-spread-reconstruct.yu
```

UTC: 2026-11-08T13:31:54.582730+00:00; elapsed: 0.007816s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```

## record-pair-pattern / check

```yulang
our project_pair (left, right) = (left.x, right.y)
project_pair ({x: 7, spare: true}, {y: "kept", spare: 0})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/record-pair-pattern.yu
```

UTC: 2026-11-08T13:31:54.591350+00:00; elapsed: 0.007425s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## record-pair-pattern / dump

```yulang
our project_pair (left, right) = (left.x, right.y)
project_pair ({x: 7, spare: true}, {y: "kept", spare: 0})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/record-pair-pattern.yu
```

UTC: 2026-11-08T13:31:54.599904+00:00; elapsed: 0.011222s; exit: 0; timeout: False

stdout:
```text
roots d0:project_pair
d0:project_pair: ({x: 'a}, {y: 'b}) -> ('a, 'b) = e5:(fn p2:(p0:d1:left, p1:d2:right) -> e4:(e1:(e0:r0:left->d1:left.s0.x#field), e3:(e2:r1:right->d2:right.s1.y#field)))
root exprs e14:(e6:r2:project_pair->d0:project_pair e13:(e9:{x: e7:7, spare: e8:true}, e12:{y: e10:"kept", spare: e11:0}))
runtime roots e14:(e6:r2:project_pair->d0:project_pair e13:(e9:{x: e7:7, spare: e8:true}, e12:{y: e10:"kept", spare: e11:0}))
detached {
  d1:left arg
  d2:right arg
}

```

stderr:
```text

```

## record-pair-pattern / run

```yulang
our project_pair (left, right) = (left.x, right.y)
project_pair ({x: 7, spare: true}, {y: "kept", spare: 0})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/record-pair-pattern.yu
```

UTC: 2026-11-08T13:31:54.611625+00:00; elapsed: 0.003844s; exit: 0; timeout: False

stdout:
```text
run roots [(7, "kept")]

```

stderr:
```text

```
