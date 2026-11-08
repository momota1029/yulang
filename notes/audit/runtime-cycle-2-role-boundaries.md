# 全出力

## single / check
```yu
role R 'a:
  our a.r: int
impl R int:
  our a.r = 1
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/single.yu
exit=0 elapsed=0.005077362060546875
stdout:

stderr:

```

## single / dump
```yu
role R 'a:
  our a.r: int
impl R int:
  our a.r = 1
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/single.yu --poly
exit=0 elapsed=0.005900144577026367
stdout:
roots d0:R d2
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
my d2 mod {
  d3: int -> int = e1:(fn p0:d4:a -> e0:1)
}
root exprs e3:(e2:1.s0.r=>d1:"R.r")
runtime roots e3:(e2:1.s0.r=>d1:"R.r")
detached {
  d4:a arg
}

stderr:

```

## single / run
```yu
role R 'a:
  our a.r: int
impl R int:
  our a.r = 1
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/single.yu
exit=0 elapsed=0.003930330276489258
stdout:
run roots [1]

stderr:

```

## duplicate / check
```yu
role R 'a:
  our a.r: int
impl R int:
  our a.r = 1
impl R int:
  our a.r = 2
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/duplicate.yu
exit=1 elapsed=0.005329132080078125
stdout:
diagnostics:
  error [yulang.ambiguous-method]: r: more than one role implementation satisfies this method call for receiver int
    --> line 7, column 3
    7 | 1.r
      |   ^
    hint: make the receiver type more specific or keep only one matching impl in scope
    note: matching impl method candidate: R.r
    --> line 4, column 9
    4 |   our a.r = 1
      |         ^
    note: matching impl method candidate: R.r
    --> line 6, column 9
    6 |   our a.r = 2
      |         ^

stderr:

```

## duplicate / dump
```yu
role R 'a:
  our a.r: int
impl R int:
  our a.r = 1
impl R int:
  our a.r = 2
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/duplicate.yu --poly
exit=0 elapsed=0.005035400390625
stdout:
roots d0:R d2 d4
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
my d2 mod {
  d3: int -> int = e1:(fn p0:d6:a -> e0:1)
}
my d4 mod {
  d5: int -> int = e3:(fn p1:d7:a -> e2:2)
}
root exprs e5:(e4:1.s0.r=>d1:"R.r")
runtime roots e5:(e4:1.s0.r=>d1:"R.r")
detached {
  d6:a arg
  d7:a arg
}

stderr:

```

## duplicate / run
```yu
role R 'a:
  our a.r: int
impl R int:
  our a.r = 1
impl R int:
  our a.r = 2
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/duplicate.yu
exit=1 elapsed=0.004476785659790039
stdout:

stderr:
compile error [yulang.ambiguous-method]: more than one role implementation satisfies this method call
    --> line 7, column 3
    7 | 1.r
      |   ^
  detail: more than one role implementation satisfies this method call for receiver int
  hint: make the receiver type more specific or keep only one matching impl in scope
  note: matching impl method candidate: R.r
    --> line 4, column 9
    4 |   our a.r = 1
      |         ^
  note: matching impl method candidate: R.r
    --> line 6, column 9
    6 |   our a.r = 2
      |         ^

```

## duplicate-reverse / check
```yu
role R 'a:
  our a.r: int
impl R int:
  our a.r = 2
impl R int:
  our a.r = 1
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/duplicate-reverse.yu
exit=1 elapsed=0.004862308502197266
stdout:
diagnostics:
  error [yulang.ambiguous-method]: r: more than one role implementation satisfies this method call for receiver int
    --> line 7, column 3
    7 | 1.r
      |   ^
    hint: make the receiver type more specific or keep only one matching impl in scope
    note: matching impl method candidate: R.r
    --> line 4, column 9
    4 |   our a.r = 2
      |         ^
    note: matching impl method candidate: R.r
    --> line 6, column 9
    6 |   our a.r = 1
      |         ^

stderr:

```

## duplicate-reverse / dump
```yu
role R 'a:
  our a.r: int
impl R int:
  our a.r = 2
impl R int:
  our a.r = 1
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/duplicate-reverse.yu --poly
exit=0 elapsed=0.004381418228149414
stdout:
roots d0:R d2 d4
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
my d2 mod {
  d3: int -> int = e1:(fn p0:d6:a -> e0:2)
}
my d4 mod {
  d5: int -> int = e3:(fn p1:d7:a -> e2:1)
}
root exprs e5:(e4:1.s0.r=>d1:"R.r")
runtime roots e5:(e4:1.s0.r=>d1:"R.r")
detached {
  d6:a arg
  d7:a arg
}

stderr:

```

## duplicate-reverse / run
```yu
role R 'a:
  our a.r: int
impl R int:
  our a.r = 2
impl R int:
  our a.r = 1
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/duplicate-reverse.yu
exit=1 elapsed=0.00496363639831543
stdout:

stderr:
compile error [yulang.ambiguous-method]: more than one role implementation satisfies this method call
    --> line 7, column 3
    7 | 1.r
      |   ^
  detail: more than one role implementation satisfies this method call for receiver int
  hint: make the receiver type more specific or keep only one matching impl in scope
  note: matching impl method candidate: R.r
    --> line 4, column 9
    4 |   our a.r = 2
      |         ^
  note: matching impl method candidate: R.r
    --> line 6, column 9
    6 |   our a.r = 1
      |         ^

```

## missing / check
```yu
role R 'a:
  our a.r: int
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/missing.yu
exit=1 elapsed=0.0030274391174316406
stdout:
diagnostics:
  error [yulang.unresolved-method]: r: no role implementation satisfies this method call for receiver int
    --> line 3, column 3
    3 | 1.r
      |   ^
    hint: add or import an impl for the receiver type, or call a method supported by that value

stderr:

```

## missing / dump
```yu
role R 'a:
  our a.r: int
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/missing.yu --poly
exit=0 elapsed=0.0037670135498046875
stdout:
roots d0:R
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
root exprs e1:(e0:1.s0.r=>d1:"R.r")
runtime roots e1:(e0:1.s0.r=>d1:"R.r")

stderr:

```

## missing / run
```yu
role R 'a:
  our a.r: int
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/missing.yu
exit=1 elapsed=0.0037963390350341797
stdout:

stderr:
compile error [yulang.unresolved-method]: no role implementation satisfies this method call
    --> line 3, column 3
    3 | 1.r
      |   ^
  detail: no role implementation satisfies this method call for receiver int
  hint: add or import an impl for the receiver type, or call a method supported by that value

```

## generic-concrete / check
```yu
role R 'a:
  our a.r: int
impl R int:
  our a.r = 1
impl R 'a:
  our a.r = 2
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/generic-concrete.yu
exit=1 elapsed=0.004725456237792969
stdout:
diagnostics:
  error [yulang.ambiguous-method]: r: more than one role implementation satisfies this method call for receiver int
    --> line 7, column 3
    7 | 1.r
      |   ^
    hint: make the receiver type more specific or keep only one matching impl in scope
    note: matching impl method candidate: R.r
    --> line 4, column 9
    4 |   our a.r = 1
      |         ^
    note: matching impl method candidate: R.r
    --> line 6, column 9
    6 |   our a.r = 2
      |         ^

stderr:

```

## generic-concrete / dump
```yu
role R 'a:
  our a.r: int
impl R int:
  our a.r = 1
impl R 'a:
  our a.r = 2
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/generic-concrete.yu --poly
exit=0 elapsed=0.004453420639038086
stdout:
roots d0:R d2 d4
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
my d2 mod {
  d3: int -> int = e1:(fn p0:d6:a -> e0:1)
}
my d4 mod {
  d5: 'a -> int = e3:(fn p1:d7:a -> e2:2)
}
root exprs e5:(e4:1.s0.r=>d1:"R.r")
runtime roots e5:(e4:1.s0.r=>d1:"R.r")
detached {
  d6:a arg
  d7:a arg
}

stderr:

```

## generic-concrete / run
```yu
role R 'a:
  our a.r: int
impl R int:
  our a.r = 1
impl R 'a:
  our a.r = 2
1.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/generic-concrete.yu
exit=1 elapsed=0.006241559982299805
stdout:

stderr:
compile error [yulang.ambiguous-method]: more than one role implementation satisfies this method call
    --> line 7, column 3
    7 | 1.r
      |   ^
  detail: more than one role implementation satisfies this method call for receiver int
  hint: make the receiver type more specific or keep only one matching impl in scope
  note: matching impl method candidate: R.r
    --> line 4, column 9
    4 |   our a.r = 1
      |         ^
  note: matching impl method candidate: R.r
    --> line 6, column 9
    6 |   our a.r = 2
      |         ^

```

## conditional-missing / check
```yu
struct box 'a {value: 'a}
role Q 'a:
  our a.q: int
role R 'a:
  our a.r: int
impl R (box 'a):
  where 'a: Q
  our a.r = 1
(box {value: 1}).r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/conditional-missing.yu
exit=0 elapsed=0.005988359451293945
stdout:

stderr:

```

## conditional-missing / dump
```yu
struct box 'a {value: 'a}
role Q 'a:
  our a.q: int
role R 'a:
  our a.r: int
impl R (box 'a):
  where 'a: Q
  our a.r = 1
(box {value: 1}).r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/conditional-missing.yu --poly
exit=0 elapsed=0.006627321243286133
stdout:
roots d0:box d3:Q d5:R d7
d0:box: {value: 'a} -> box 'a = <missing>
d3:Q mod {
  d4:"Q.q": 'a -> int where 'a: Q = <missing>
}
d5:R mod {
  d6:"R.r": 'a -> int where 'a: R = <missing>
}
my d7 mod {
  d8: box 'a -> int = e1:(fn p0:d9:a -> e0:1)
}
root exprs e6:(e5:(e2:r0:box->d0:box e4:{value: e3:1}).s0.r=>d6:"R.r")
runtime roots e6:(e5:(e2:r0:box->d0:box e4:{value: e3:1}).s0.r=>d6:"R.r")
detached {
  d1: box 'a -> 'a = <missing>
  d2: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:a arg
}

stderr:

```

## conditional-missing / run
```yu
struct box 'a {value: 'a}
role Q 'a:
  our a.q: int
role R 'a:
  our a.r: int
impl R (box 'a):
  where 'a: Q
  our a.r = 1
(box {value: 1}).r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/conditional-missing.yu
exit=0 elapsed=0.004463672637939453
stdout:
run roots [1]

stderr:

```

## conditional-used / check
```yu
struct box 'a {value: 'a}
role Q 'a:
  our a.q: int
role R 'a:
  our a.r: int
impl R (box 'a):
  where 'a: Q
  our a.r = a.value.q
(box {value: 1}).r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/conditional-used.yu
exit=1 elapsed=0.00881195068359375
stdout:
diagnostics:
  error [yulang.unresolved-method]: q: no role implementation satisfies this method call for receiver int
    --> line 8, column 21
    8 |   our a.r = a.value.q
      |                     ^
    hint: add or import an impl for the receiver type, or call a method supported by that value

stderr:

```

## conditional-used / dump
```yu
struct box 'a {value: 'a}
role Q 'a:
  our a.q: int
role R 'a:
  our a.r: int
impl R (box 'a):
  where 'a: Q
  our a.r = a.value.q
(box {value: 1}).r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/conditional-used.yu --poly
exit=0 elapsed=0.007837533950805664
stdout:
roots d0:box d3:Q d5:R d7
d0:box: {value: 'a} -> box 'a = <missing>
d3:Q mod {
  d4:"Q.q": 'a -> int where 'a: Q = <missing>
}
d5:R mod {
  d6:"R.r": 'a -> int where 'a: R = <missing>
}
my d7 mod {
  d8: box 'a -> int where 'a: Q = e3:(fn p0:d9:a -> e2:(e1:(e0:r0:a->d9:a.s0.value->d1).s1.q=>d4:"Q.q"))
}
root exprs e8:(e7:(e4:r1:box->d0:box e6:{value: e5:1}).s2.r=>d6:"R.r")
runtime roots e8:(e7:(e4:r1:box->d0:box e6:{value: e5:1}).s2.r=>d6:"R.r")
detached {
  d1: box 'a -> 'a = <missing>
  d2: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:a arg
}

stderr:

```

## conditional-used / run
```yu
struct box 'a {value: 'a}
role Q 'a:
  our a.q: int
role R 'a:
  our a.r: int
impl R (box 'a):
  where 'a: Q
  our a.r = a.value.q
(box {value: 1}).r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/conditional-used.yu
exit=1 elapsed=0.009164810180664062
stdout:

stderr:
compile error [yulang.unresolved-method]: no role implementation satisfies this method call
    --> line 8, column 21
    8 |   our a.r = a.value.q
      |                     ^
  detail: no role implementation satisfies this method call for receiver int
  hint: add or import an impl for the receiver type, or call a method supported by that value

```

## role-name-ambiguity / check
```yu
role R 'a:
  our a.r: int
role S 'a:
  our a.r: int
our f(x) = x.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/role-name-ambiguity.yu
exit=0 elapsed=0.005230426788330078
stdout:

stderr:

```

## role-name-ambiguity / dump
```yu
role R 'a:
  our a.r: int
role S 'a:
  our a.r: int
our f(x) = x.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/role-name-ambiguity.yu --poly
exit=0 elapsed=0.004786252975463867
stdout:
roots d0:R d2:S d4:f
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
d2:S mod {
  d3:"S.r": 'a -> int where 'a: S = <missing>
}
d4:f: {r: 'a} -> 'a = e2:(fn p0:d5:x -> e1:(e0:r0:x->d5:x.s0.r#field))
detached {
  d5:x arg
}

stderr:

```

## role-name-ambiguity / run
```yu
role R 'a:
  our a.r: int
role S 'a:
  our a.r: int
our f(x) = x.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/role-name-ambiguity.yu
exit=0 elapsed=0.0028443336486816406
stdout:
run roots []

stderr:

```

## conditional-used-solved / check
```yu
struct box 'a {value: 'a}
role Q 'a:
  our a.q: int
role R 'a:
  our a.r: int
impl R (box 'a):
  where 'a: Q
  our a.r = a.value.q
impl Q int:
  our a.q = 7
(box {value: 1}).r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/conditional-used-solved.yu
exit=0 elapsed=0.008116960525512695
stdout:

stderr:

```

## conditional-used-solved / dump
```yu
struct box 'a {value: 'a}
role Q 'a:
  our a.q: int
role R 'a:
  our a.r: int
impl R (box 'a):
  where 'a: Q
  our a.r = a.value.q
impl Q int:
  our a.q = 7
(box {value: 1}).r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/conditional-used-solved.yu --poly
exit=0 elapsed=0.007417917251586914
stdout:
roots d0:box d3:Q d5:R d7 d9
d0:box: {value: 'a} -> box 'a = <missing>
d3:Q mod {
  d4:"Q.q": 'a -> int where 'a: Q = <missing>
}
d5:R mod {
  d6:"R.r": 'a -> int where 'a: R = <missing>
}
my d7 mod {
  d8: box 'a -> int where 'a: Q = e3:(fn p0:d11:a -> e2:(e1:(e0:r0:a->d11:a.s0.value->d1).s1.q=>d4:"Q.q"))
}
my d9 mod {
  d10: int -> int = e5:(fn p1:d12:a -> e4:7)
}
root exprs e10:(e9:(e6:r1:box->d0:box e8:{value: e7:1}).s2.r=>d6:"R.r")
runtime roots e10:(e9:(e6:r1:box->d0:box e8:{value: e7:1}).s2.r=>d6:"R.r")
detached {
  d1: box 'a -> 'a = <missing>
  d2: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d11:a arg
  d12:a arg
}

stderr:

```

## conditional-used-solved / run
```yu
struct box 'a {value: 'a}
role Q 'a:
  our a.q: int
role R 'a:
  our a.r: int
impl R (box 'a):
  where 'a: Q
  our a.r = a.value.q
impl Q int:
  our a.q = 7
(box {value: 1}).r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/conditional-used-solved.yu
exit=0 elapsed=0.0037653446197509766
stdout:
run roots [7]

stderr:

```

## conditional-overlap / check
```yu
struct box 'a {value: 'a}
role Q 'a:
  our a.q: int
role R 'a:
  our a.r: int
impl R (box 'a):
  where 'a: Q
  our a.r = 1
impl R (box int):
  our a.r = 2
(box {value: 1}).r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/conditional-overlap.yu
exit=1 elapsed=0.00616455078125
stdout:
diagnostics:
  error [yulang.ambiguous-method]: r: more than one role implementation satisfies this method call for receiver box(int)
    --> line 11, column 18
    11 | (box {value: 1}).r
       |                  ^
    hint: make the receiver type more specific or keep only one matching impl in scope
    note: matching impl method candidate: R.r
    --> line 8, column 9
    8 |   our a.r = 1
      |         ^
    note: matching impl method candidate: R.r
    --> line 10, column 9
    10 |   our a.r = 2
       |         ^

stderr:

```

## conditional-overlap / dump
```yu
struct box 'a {value: 'a}
role Q 'a:
  our a.q: int
role R 'a:
  our a.r: int
impl R (box 'a):
  where 'a: Q
  our a.r = 1
impl R (box int):
  our a.r = 2
(box {value: 1}).r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/conditional-overlap.yu --poly
exit=0 elapsed=0.006727695465087891
stdout:
roots d0:box d3:Q d5:R d7 d9
d0:box: {value: 'a} -> box 'a = <missing>
d3:Q mod {
  d4:"Q.q": 'a -> int where 'a: Q = <missing>
}
d5:R mod {
  d6:"R.r": 'a -> int where 'a: R = <missing>
}
my d7 mod {
  d8: box 'a -> int = e1:(fn p0:d11:a -> e0:1)
}
my d9 mod {
  d10: box int -> int = e3:(fn p1:d12:a -> e2:2)
}
root exprs e8:(e7:(e4:r0:box->d0:box e6:{value: e5:1}).s0.r=>d6:"R.r")
runtime roots e8:(e7:(e4:r0:box->d0:box e6:{value: e5:1}).s0.r=>d6:"R.r")
detached {
  d1: box 'a -> 'a = <missing>
  d2: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d11:a arg
  d12:a arg
}

stderr:

```

## conditional-overlap / run
```yu
struct box 'a {value: 'a}
role Q 'a:
  our a.q: int
role R 'a:
  our a.r: int
impl R (box 'a):
  where 'a: Q
  our a.r = 1
impl R (box int):
  our a.r = 2
(box {value: 1}).r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/conditional-overlap.yu
exit=1 elapsed=0.0080108642578125
stdout:

stderr:
compile error [yulang.ambiguous-method]: more than one role implementation satisfies this method call
    --> line 11, column 18
    11 | (box {value: 1}).r
       |                  ^
  detail: more than one role implementation satisfies this method call for receiver box(int)
  hint: make the receiver type more specific or keep only one matching impl in scope
  note: matching impl method candidate: R.r
    --> line 8, column 9
    8 |   our a.r = 1
      |         ^
  note: matching impl method candidate: R.r
    --> line 10, column 9
    10 |   our a.r = 2
       |         ^

```

## unknown-single / check
```yu
role R 'a:
  our a.r: int
our f(x) = x.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/unknown-single.yu
exit=0 elapsed=0.004562854766845703
stdout:

stderr:

```

## unknown-single / dump
```yu
role R 'a:
  our a.r: int
our f(x) = x.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/unknown-single.yu --poly
exit=0 elapsed=0.004392385482788086
stdout:
roots d0:R d2:f
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
d2:f: 'a -> int where 'a: R = e2:(fn p0:d3:x -> e1:(e0:r0:x->d3:x.s0.r=>d1:"R.r"))
detached {
  d3:x arg
}

stderr:

```

## unknown-single / run
```yu
role R 'a:
  our a.r: int
our f(x) = x.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/unknown-single.yu
exit=0 elapsed=0.0025968551635742188
stdout:
run roots []

stderr:

```

## unknown-double-used / check
```yu
role R 'a:
  our a.r: int
role S 'a:
  our a.r: int
our f(x) = x.r
f {r: 9}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/unknown-double-used.yu
exit=0 elapsed=0.004146099090576172
stdout:

stderr:

```

## unknown-double-used / dump
```yu
role R 'a:
  our a.r: int
role S 'a:
  our a.r: int
our f(x) = x.r
f {r: 9}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/unknown-double-used.yu --poly
exit=0 elapsed=0.004851818084716797
stdout:
roots d0:R d2:S d4:f
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
d2:S mod {
  d3:"S.r": 'a -> int where 'a: S = <missing>
}
d4:f: {r: 'a} -> 'a = e2:(fn p0:d5:x -> e1:(e0:r0:x->d5:x.s0.r#field))
root exprs e6:(e3:r1:f->d4:f e5:{r: e4:9})
runtime roots e6:(e3:r1:f->d4:f e5:{r: e4:9})
detached {
  d5:x arg
}

stderr:

```

## unknown-double-used / run
```yu
role R 'a:
  our a.r: int
role S 'a:
  our a.r: int
our f(x) = x.r
f {r: 9}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/unknown-double-used.yu
exit=0 elapsed=0.003539562225341797
stdout:
run roots [9]

stderr:

```

## known-field-double / check
```yu
role R 'a:
  our a.r: int
role S 'a:
  our a.r: int
{r: 9}.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-role-more/known-field-double.yu
exit=0 elapsed=0.0032536983489990234
stdout:

stderr:

```

## known-field-double / dump
```yu
role R 'a:
  our a.r: int
role S 'a:
  our a.r: int
{r: 9}.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-role-more/known-field-double.yu --poly
exit=0 elapsed=0.003142118453979492
stdout:
roots d0:R d2:S
d0:R mod {
  d1:"R.r": 'a -> int where 'a: R = <missing>
}
d2:S mod {
  d3:"S.r": 'a -> int where 'a: S = <missing>
}
root exprs e2:(e1:{r: e0:9}.s0.r#field)
runtime roots e2:(e1:{r: e0:9}.s0.r#field)

stderr:

```

## known-field-double / run
```yu
role R 'a:
  our a.r: int
role S 'a:
  our a.r: int
{r: 9}.r
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-role-more/known-field-double.yu
exit=0 elapsed=0.0024747848510742188
stdout:
run roots [9]

stderr:

```

## 既存unit
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/debug/deps/infer-dfea53230aacf9c4 lowering::tests::case_07::generic_role_impl_conformance_stage4_p0a_captures_impl_where_with_u_binder --exact --nocapture
exit=0 elapsed=0.025918006896972656

running 1 test
test lowering::tests::case_07::generic_role_impl_conformance_stage4_p0a_captures_impl_where_with_u_binder ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1392 filtered out; finished in 0.02s


stderr:

```
