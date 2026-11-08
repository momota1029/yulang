# Cycle 3 raw log: parent-fixed

新spec基点 `816ed8f1d`、旧実機 `d4c8bc8fc`。出力はそのまま。dump exit 0 は診断なしを意味しない。

## 1. parent-left-right

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
(box {value: (seed {value: 3}).produce}).parent

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/parent-left-right.yu
```

UTC start: 2026-11-08T13:33:28.480260+00:00; elapsed: 0.012218 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 2. parent-left-right

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
(box {value: (seed {value: 3}).produce}).parent

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/parent-left-right.yu
```

UTC start: 2026-11-08T13:33:28.492728+00:00; elapsed: 0.002572 s; exit: 0; timeout: False

stdout:
```text
roots d0:seed d3:box d6:Produce d8 d10:Left d12:Right d14 d16 d18:Parent d20
d0:seed: {value: int} -> seed = <missing>
d3:box: {value: 'a} -> box 'a = <missing>
d6:Produce mod {
  d7:"Produce.produce": 'a -> 'b where 'a: Produce(value = 'b) = <missing>
}
my d8 mod {
  d9: seed -> int = e2:(fn p0:d22:r -> e1:(e0:r0:r->d22:r.s0.value->d1))
}
d10:Left mod {
  d11:"Left.left": 'a -> int where 'a: Left = <missing>
}
d12:Right mod {
  d13:"Right.right": 'a -> int where 'a: Right = <missing>
}
my d14 mod {
  d15: int -> int = e4:(fn p1:d23:a -> e3:11)
}
my d16 mod {
  d17: int -> int = e6:(fn p2:d24:a -> e5:22)
}
d18:Parent mod {
  d19:"Parent.parent": 'a -> (int, int) where 'a: Parent = <missing>
}
my d20 mod {
  d21: box 'a -> (int, int) where 'a: Left, 'a: Right = e14:(fn p3:d25:b -> e13:(e9:(e8:(e7:r1:b->d25:b.s1.value->d4).s2.left=>d11:"Left.left"), e12:(e11:(e10:r2:b->d25:b.s3.value->d4).s4.right=>d13:"Right.right")))
}
root exprs e23:(e22:(e15:r3:box->d3:box e21:{value: e20:(e19:(e16:r4:seed->d0:seed e18:{value: e17:3}).s5.produce=>d7:"Produce.produce")}).s6.parent=>d19:"Parent.parent")
runtime roots e23:(e22:(e15:r3:box->d3:box e21:{value: e20:(e19:(e16:r4:seed->d0:seed e18:{value: e17:3}).s5.produce=>d7:"Produce.produce")}).s6.parent=>d19:"Parent.parent")
detached {
  d1: seed -> int = <missing>
  d2: std::control::var::ref 'a seed -> std::control::var::ref 'a int = <missing>
  d4: box 'a -> 'a = <missing>
  d5: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d22:r arg
  d23:a arg
  d24:a arg
  d25:b arg
}

```

stderr:
```text

```

## 3. parent-left-right

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
(box {value: (seed {value: 3}).produce}).parent

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/parent-left-right.yu
```

UTC start: 2026-11-08T13:33:28.495626+00:00; elapsed: 0.002190 s; exit: 0; timeout: False

stdout:
```text
mono roots [(<ctor d3 / 1> {value: (<ctor d0 / 1> {value: 3}).produce <method>}).parent <method>]
m0 = d9 : seed -> int
  \d22 -> d22.value
m1 = d21 : box(int) -> (int, int)
  \d25 -> (d25.value.left <method>, d25.value.right <method>)
m2 = d15 : int -> int
  \d23 -> 11
m3 = d17 : int -> int
  \d24 -> 22

```

stderr:
```text

```

## 4. parent-left-right

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
(box {value: (seed {value: 3}).produce}).parent

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/parent-left-right.yu
```

UTC start: 2026-11-08T13:33:28.497997+00:00; elapsed: 0.003679 s; exit: 0; timeout: False

stdout:
```text
run roots [(11, 22)]

```

stderr:
```text

```

## 5. parent-right-left

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Right
    where 'a: Left
    our b.parent = (b.value.left, b.value.right)
(box {value: (seed {value: 3}).produce}).parent

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/parent-right-left.yu
```

UTC start: 2026-11-08T13:33:28.502619+00:00; elapsed: 0.012085 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 6. parent-right-left

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Right
    where 'a: Left
    our b.parent = (b.value.left, b.value.right)
(box {value: (seed {value: 3}).produce}).parent

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/parent-right-left.yu
```

UTC start: 2026-11-08T13:33:28.514963+00:00; elapsed: 0.002549 s; exit: 0; timeout: False

stdout:
```text
roots d0:seed d3:box d6:Produce d8 d10:Left d12:Right d14 d16 d18:Parent d20
d0:seed: {value: int} -> seed = <missing>
d3:box: {value: 'a} -> box 'a = <missing>
d6:Produce mod {
  d7:"Produce.produce": 'a -> 'b where 'a: Produce(value = 'b) = <missing>
}
my d8 mod {
  d9: seed -> int = e2:(fn p0:d22:r -> e1:(e0:r0:r->d22:r.s0.value->d1))
}
d10:Left mod {
  d11:"Left.left": 'a -> int where 'a: Left = <missing>
}
d12:Right mod {
  d13:"Right.right": 'a -> int where 'a: Right = <missing>
}
my d14 mod {
  d15: int -> int = e4:(fn p1:d23:a -> e3:11)
}
my d16 mod {
  d17: int -> int = e6:(fn p2:d24:a -> e5:22)
}
d18:Parent mod {
  d19:"Parent.parent": 'a -> (int, int) where 'a: Parent = <missing>
}
my d20 mod {
  d21: box 'a -> (int, int) where 'a: Left, 'a: Right = e14:(fn p3:d25:b -> e13:(e9:(e8:(e7:r1:b->d25:b.s1.value->d4).s2.left=>d11:"Left.left"), e12:(e11:(e10:r2:b->d25:b.s3.value->d4).s4.right=>d13:"Right.right")))
}
root exprs e23:(e22:(e15:r3:box->d3:box e21:{value: e20:(e19:(e16:r4:seed->d0:seed e18:{value: e17:3}).s5.produce=>d7:"Produce.produce")}).s6.parent=>d19:"Parent.parent")
runtime roots e23:(e22:(e15:r3:box->d3:box e21:{value: e20:(e19:(e16:r4:seed->d0:seed e18:{value: e17:3}).s5.produce=>d7:"Produce.produce")}).s6.parent=>d19:"Parent.parent")
detached {
  d1: seed -> int = <missing>
  d2: std::control::var::ref 'a seed -> std::control::var::ref 'a int = <missing>
  d4: box 'a -> 'a = <missing>
  d5: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d22:r arg
  d23:a arg
  d24:a arg
  d25:b arg
}

```

stderr:
```text

```

## 7. parent-right-left

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Right
    where 'a: Left
    our b.parent = (b.value.left, b.value.right)
(box {value: (seed {value: 3}).produce}).parent

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/parent-right-left.yu
```

UTC start: 2026-11-08T13:33:28.517773+00:00; elapsed: 0.002128 s; exit: 0; timeout: False

stdout:
```text
mono roots [(<ctor d3 / 1> {value: (<ctor d0 / 1> {value: 3}).produce <method>}).parent <method>]
m0 = d9 : seed -> int
  \d22 -> d22.value
m1 = d21 : box(int) -> (int, int)
  \d25 -> (d25.value.left <method>, d25.value.right <method>)
m2 = d15 : int -> int
  \d23 -> 11
m3 = d17 : int -> int
  \d24 -> 22

```

stderr:
```text

```

## 8. parent-right-left

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Right
    where 'a: Left
    our b.parent = (b.value.left, b.value.right)
(box {value: (seed {value: 3}).produce}).parent

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/parent-right-left.yu
```

UTC start: 2026-11-08T13:33:28.520236+00:00; elapsed: 0.003677 s; exit: 0; timeout: False

stdout:
```text
run roots [(11, 22)]

```

stderr:
```text

```

## 9. parent-generic-function

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
our consume(r) = (box {value: r.produce}).parent
consume (seed {value: 3})

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/parent-generic-function.yu
```

UTC start: 2026-11-08T13:33:28.524162+00:00; elapsed: 0.016094 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 10. parent-generic-function

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
our consume(r) = (box {value: r.produce}).parent
consume (seed {value: 3})

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/parent-generic-function.yu
```

UTC start: 2026-11-08T13:33:28.540956+00:00; elapsed: 0.015874 s; exit: 0; timeout: False

stdout:
```text
roots d0:seed d3:box d6:Produce d8 d10:Left d12:Right d14 d16 d18:Parent d20 d22:consume
d0:seed: {value: int} -> seed = <missing>
d3:box: {value: 'a} -> box 'a = <missing>
d6:Produce mod {
  d7:"Produce.produce": 'a -> 'b where 'a: Produce(value = 'b) = <missing>
}
my d8 mod {
  d9: seed -> int = e2:(fn p0:d23:r -> e1:(e0:r0:r->d23:r.s0.value->d1))
}
d10:Left mod {
  d11:"Left.left": 'a -> int where 'a: Left = <missing>
}
d12:Right mod {
  d13:"Right.right": 'a -> int where 'a: Right = <missing>
}
my d14 mod {
  d15: int -> int = e4:(fn p1:d24:a -> e3:11)
}
my d16 mod {
  d17: int -> int = e6:(fn p2:d25:a -> e5:22)
}
d18:Parent mod {
  d19:"Parent.parent": 'a -> (int, int) where 'a: Parent = <missing>
}
my d20 mod {
  d21: box 'a -> (int, int) where 'a: Left, 'a: Right = e14:(fn p3:d26:b -> e13:(e9:(e8:(e7:r1:b->d26:b.s1.value->d4).s2.left=>d11:"Left.left"), e12:(e11:(e10:r2:b->d26:b.s3.value->d4).s4.right=>d13:"Right.right")))
}
d22:consume: 'a -> (int, int) where 'a: Produce(value = 'b), Left('b | 'c), Right('b | 'c) = e21:(fn p4:d27:r -> e20:(e19:(e15:r3:box->d3:box e18:{value: e17:(e16:r4:r->d27:r.s5.produce=>d7:"Produce.produce")}).s6.parent=>d19:"Parent.parent"))
root exprs e27:(e22:r5:consume->d22:consume e26:(e23:r6:seed->d0:seed e25:{value: e24:3}))
runtime roots e27:(e22:r5:consume->d22:consume e26:(e23:r6:seed->d0:seed e25:{value: e24:3}))
detached {
  d1: seed -> int = <missing>
  d2: std::control::var::ref 'a seed -> std::control::var::ref 'a int = <missing>
  d4: box 'a -> 'a = <missing>
  d5: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d23:r arg
  d24:a arg
  d25:a arg
  d26:b arg
  d27:r arg
}

```

stderr:
```text

```

## 11. parent-generic-function

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
our consume(r) = (box {value: r.produce}).parent
consume (seed {value: 3})

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/parent-generic-function.yu
```

UTC start: 2026-11-08T13:33:28.557411+00:00; elapsed: 0.003373 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 (<ctor d0 / 1> {value: 3}))]
m0 = d22 : seed -> (int, int)
  \d27 -> (<ctor d3 / 1> {value: d27.produce <method>}).parent <method>
m1 = d9 : seed -> int
  \d23 -> d23.value
m2 = d21 : box(int) -> (int, int)
  \d26 -> (d26.value.left <method>, d26.value.right <method>)
m3 = d15 : int -> int
  \d24 -> 11
m4 = d17 : int -> int
  \d25 -> 22

```

stderr:
```text

```

## 12. parent-generic-function

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
our consume(r) = (box {value: r.produce}).parent
consume (seed {value: 3})

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/parent-generic-function.yu
```

UTC start: 2026-11-08T13:33:28.561192+00:00; elapsed: 0.004546 s; exit: 0; timeout: False

stdout:
```text
run roots [(11, 22)]

```

stderr:
```text

```

## 13. parent-result-first

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
our consume(r): (int, int) = (box {value: r.produce}).parent
consume (seed {value: 3})

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/parent-result-first.yu
```

UTC start: 2026-11-08T13:33:28.566282+00:00; elapsed: 0.012313 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 14. parent-result-first

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
our consume(r): (int, int) = (box {value: r.produce}).parent
consume (seed {value: 3})

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/parent-result-first.yu
```

UTC start: 2026-11-08T13:33:28.578899+00:00; elapsed: 0.014017 s; exit: 0; timeout: False

stdout:
```text
roots d0:seed d3:box d6:Produce d8 d10:Left d12:Right d14 d16 d18:Parent d20 d22:consume
d0:seed: {value: int} -> seed = <missing>
d3:box: {value: 'a} -> box 'a = <missing>
d6:Produce mod {
  d7:"Produce.produce": 'a -> 'b where 'a: Produce(value = 'b) = <missing>
}
my d8 mod {
  d9: seed -> int = e2:(fn p0:d23:r -> e1:(e0:r0:r->d23:r.s0.value->d1))
}
d10:Left mod {
  d11:"Left.left": 'a -> int where 'a: Left = <missing>
}
d12:Right mod {
  d13:"Right.right": 'a -> int where 'a: Right = <missing>
}
my d14 mod {
  d15: int -> int = e4:(fn p1:d24:a -> e3:11)
}
my d16 mod {
  d17: int -> int = e6:(fn p2:d25:a -> e5:22)
}
d18:Parent mod {
  d19:"Parent.parent": 'a -> (int, int) where 'a: Parent = <missing>
}
my d20 mod {
  d21: box 'a -> (int, int) where 'a: Left, 'a: Right = e14:(fn p3:d26:b -> e13:(e9:(e8:(e7:r1:b->d26:b.s1.value->d4).s2.left=>d11:"Left.left"), e12:(e11:(e10:r2:b->d26:b.s3.value->d4).s4.right=>d13:"Right.right")))
}
d22:consume: 'a -> (int, int) where 'a: Produce(value = 'b), Left('b | 'c), Right('b | 'c) = e21:(fn p4:d27:r -> e20:(e19:(e15:r3:box->d3:box e18:{value: e17:(e16:r4:r->d27:r.s5.produce=>d7:"Produce.produce")}).s6.parent=>d19:"Parent.parent"))
root exprs e27:(e22:r5:consume->d22:consume e26:(e23:r6:seed->d0:seed e25:{value: e24:3}))
runtime roots e27:(e22:r5:consume->d22:consume e26:(e23:r6:seed->d0:seed e25:{value: e24:3}))
detached {
  d1: seed -> int = <missing>
  d2: std::control::var::ref 'a seed -> std::control::var::ref 'a int = <missing>
  d4: box 'a -> 'a = <missing>
  d5: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d23:r arg
  d24:a arg
  d25:a arg
  d26:b arg
  d27:r arg
}

```

stderr:
```text

```

## 15. parent-result-first

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
our consume(r): (int, int) = (box {value: r.produce}).parent
consume (seed {value: 3})

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/parent-result-first.yu
```

UTC start: 2026-11-08T13:33:28.593439+00:00; elapsed: 0.002912 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 (<ctor d0 / 1> {value: 3}))]
m0 = d22 : seed -> (int, int)
  \d27 -> (<ctor d3 / 1> {value: d27.produce <method>}).parent <method>
m1 = d9 : seed -> int
  \d23 -> d23.value
m2 = d21 : box(int) -> (int, int)
  \d26 -> (d26.value.left <method>, d26.value.right <method>)
m3 = d15 : int -> int
  \d24 -> 11
m4 = d17 : int -> int
  \d25 -> 22

```

stderr:
```text

```

## 16. parent-result-first

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
our consume(r): (int, int) = (box {value: r.produce}).parent
consume (seed {value: 3})

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/parent-result-first.yu
```

UTC start: 2026-11-08T13:33:28.596768+00:00; elapsed: 0.004217 s; exit: 0; timeout: False

stdout:
```text
run roots [(11, 22)]

```

stderr:
```text

```

## 17. parent-missing-child

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
(box {value: seed {value: 3}}).parent

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/parent-missing-child.yu
```

UTC start: 2026-11-08T13:33:28.601397+00:00; elapsed: 0.010543 s; exit: 1; timeout: False

stdout:
```text
diagnostics:
  error [yulang.unresolved-method]: left: no role implementation satisfies this method call for receiver seed
    --> line 22, column 29
    22 |     our b.parent = (b.value.left, b.value.right)
       |                             ^^^^
    hint: add or import an impl for the receiver type, or call a method supported by that value
  error [yulang.unresolved-method]: right: no role implementation satisfies this method call for receiver seed
    --> line 22, column 43
    22 |     our b.parent = (b.value.left, b.value.right)
       |                                           ^^^^^
    hint: add or import an impl for the receiver type, or call a method supported by that value

```

stderr:
```text

```

## 18. parent-missing-child

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
(box {value: seed {value: 3}}).parent

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/parent-missing-child.yu
```

UTC start: 2026-11-08T13:33:28.612513+00:00; elapsed: 0.002526 s; exit: 0; timeout: False

stdout:
```text
roots d0:seed d3:box d6:Produce d8 d10:Left d12:Right d14 d16 d18:Parent d20
d0:seed: {value: int} -> seed = <missing>
d3:box: {value: 'a} -> box 'a = <missing>
d6:Produce mod {
  d7:"Produce.produce": 'a -> 'b where 'a: Produce(value = 'b) = <missing>
}
my d8 mod {
  d9: seed -> int = e2:(fn p0:d22:r -> e1:(e0:r0:r->d22:r.s0.value->d1))
}
d10:Left mod {
  d11:"Left.left": 'a -> int where 'a: Left = <missing>
}
d12:Right mod {
  d13:"Right.right": 'a -> int where 'a: Right = <missing>
}
my d14 mod {
  d15: int -> int = e4:(fn p1:d23:a -> e3:11)
}
my d16 mod {
  d17: int -> int = e6:(fn p2:d24:a -> e5:22)
}
d18:Parent mod {
  d19:"Parent.parent": 'a -> (int, int) where 'a: Parent = <missing>
}
my d20 mod {
  d21: box 'a -> (int, int) where 'a: Left, 'a: Right = e14:(fn p3:d25:b -> e13:(e9:(e8:(e7:r1:b->d25:b.s1.value->d4).s2.left=>d11:"Left.left"), e12:(e11:(e10:r2:b->d25:b.s3.value->d4).s4.right=>d13:"Right.right")))
}
root exprs e22:(e21:(e15:r3:box->d3:box e20:{value: e19:(e16:r4:seed->d0:seed e18:{value: e17:3})}).s5.parent=>d19:"Parent.parent")
runtime roots e22:(e21:(e15:r3:box->d3:box e20:{value: e19:(e16:r4:seed->d0:seed e18:{value: e17:3})}).s5.parent=>d19:"Parent.parent")
detached {
  d1: seed -> int = <missing>
  d2: std::control::var::ref 'a seed -> std::control::var::ref 'a int = <missing>
  d4: box 'a -> 'a = <missing>
  d5: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d22:r arg
  d23:a arg
  d24:a arg
  d25:b arg
}

```

stderr:
```text

```

## 19. parent-missing-child

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
(box {value: seed {value: 3}}).parent

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/parent-missing-child.yu
```

UTC start: 2026-11-08T13:33:28.615453+00:00; elapsed: 0.002375 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unresolved-method]: no role implementation satisfies this method call
    --> line 22, column 29
    22 |     our b.parent = (b.value.left, b.value.right)
       |                             ^^^^
  detail: no role implementation satisfies this method call for receiver seed
  hint: add or import an impl for the receiver type, or call a method supported by that value

```

## 20. parent-missing-child

```yulang
struct seed { value: int }
struct box 'a { value: 'a }
role Produce 'r:
    type value
    our r.produce: value
impl Produce seed:
    type value = int
    our r.produce = r.value
role Left 'a:
    our a.left: int
role Right 'a:
    our a.right: int
impl Left int:
    our a.left = 11
impl Right int:
    our a.right = 22
role Parent 'a:
    our a.parent: (int, int)
impl Parent (box 'a):
    where 'a: Left
    where 'a: Right
    our b.parent = (b.value.left, b.value.right)
(box {value: seed {value: 3}}).parent

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/parent-missing-child.yu
```

UTC start: 2026-11-08T13:33:28.618217+00:00; elapsed: 0.013833 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.unresolved-method]: no role implementation satisfies this method call
    --> line 22, column 29
    22 |     our b.parent = (b.value.left, b.value.right)
       |                             ^^^^
  detail: no role implementation satisfies this method call for receiver seed
  hint: add or import an impl for the receiver type, or call a method supported by that value

```
