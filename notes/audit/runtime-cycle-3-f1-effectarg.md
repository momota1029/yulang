# Cycle 3 raw log: f1-effectarg

新spec基点 `816ed8f1d`、旧実機 `d4c8bc8fc`。出力はそのまま。dump exit 0 は診断なしを意味しない。

## 1. pure-explicit

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/effectarg-pure-explicit.yu
```

UTC start: 2026-11-08T13:31:26.991340+00:00; elapsed: 0.010638 s; exit: 0; timeout: False

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
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/effectarg-pure-explicit.yu
```

UTC start: 2026-11-08T13:31:27.002166+00:00; elapsed: 0.009365 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> int = e8:(fn p4:d8:x -> e7:r3:x->d8:x)
d4:higher: (int -> [ping] int) -> int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e19:(e15:r6:handle->d2:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d3:plain))
runtime roots e19:(e15:r6:handle->d2:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d3:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:x arg
  d9:f arg
}

```

stderr:
```text

```

## 3. pure-explicit

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/effectarg-pure-explicit.yu
```

UTC start: 2026-11-08T13:31:27.011731+00:00; elapsed: 0.002810 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 4. pure-explicit

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
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/effectarg-pure-explicit.yu
```

UTC start: 2026-11-08T13:31:27.014810+00:00; elapsed: 0.014319 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 5. pure-literal-lambda

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher (\x -> x))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/effectarg-pure-literal-lambda.yu
```

UTC start: 2026-11-08T13:31:27.029423+00:00; elapsed: 0.009069 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 6. pure-literal-lambda

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher (\x -> x))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/effectarg-pure-literal-lambda.yu
```

UTC start: 2026-11-08T13:31:27.038719+00:00; elapsed: 0.008978 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d4:action -> e5:catch e0:r0:action->d4:action { ping::get p1:_, p2:d5:k -> e3:(e1:r1:k->d5:k e2:7); p3:d6:value -> e4:r2:value->d6:value })
d3:higher: (int -> [ping] int) -> int = e12:(fn p4:d7:f -> e11:(e7:r3:f->d7:f e10:(e8:r4:"ping::get"->d1:"ping.get" e9:())))
root exprs e18:(e13:r5:handle->d2:handle e17:(e14:r6:higher->d3:higher e16:(fn p5:d9:x -> e15:r7:x->d9:x)))
runtime roots e18:(e13:r5:handle->d2:handle e17:(e14:r6:higher->d3:higher e16:(fn p5:d9:x -> e15:r7:x->d9:x)))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:action arg
  d5:k arg
  d6:value arg
  d7:f arg
  d9:x arg
}

```

stderr:
```text

```

## 7. pure-literal-lambda

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher (\x -> x))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/effectarg-pure-literal-lambda.yu
```

UTC start: 2026-11-08T13:31:27.047911+00:00; elapsed: 0.002795 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 8. pure-literal-lambda

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher (\x -> x))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/effectarg-pure-literal-lambda.yu
```

UTC start: 2026-11-08T13:31:27.050908+00:00; elapsed: 0.009608 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 9. effectful-actual

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): [ping] int = ping::get()
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/effectarg-effectful-actual.yu
```

UTC start: 2026-11-08T13:31:27.060791+00:00; elapsed: 0.008530 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 10. effectful-actual

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): [ping] int = ping::get()
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/effectarg-effectful-actual.yu
```

UTC start: 2026-11-08T13:31:27.069609+00:00; elapsed: 0.010557 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> [ping] int = e10:(fn p4:d8:x -> e9:(e7:r3:"ping::get"->d1:"ping.get" e8:()))
d4:higher: (int -> [ping] int) -> int = e16:(fn p5:d9:f -> e15:(e11:r4:f->d9:f e14:(e12:r5:"ping::get"->d1:"ping.get" e13:())))
root exprs e21:(e17:r6:handle->d2:handle e20:(e18:r7:higher->d4:higher e19:r8:plain->d3:plain))
runtime roots e21:(e17:r6:handle->d2:handle e20:(e18:r7:higher->d4:higher e19:r8:plain->d3:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:x arg
  d9:f arg
}

```

stderr:
```text

```

## 11. effectful-actual

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): [ping] int = ping::get()
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/effectarg-effectful-actual.yu
```

UTC start: 2026-11-08T13:31:27.080494+00:00; elapsed: 0.002303 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 12. effectful-actual

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): [ping] int = ping::get()
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/effectarg-effectful-actual.yu
```

UTC start: 2026-11-08T13:31:27.083004+00:00; elapsed: 0.015365 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 13. effectful-unreachable

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int) = case x:
    _ -> x
    _ -> ping::get()
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/effectarg-effectful-unreachable.yu
```

UTC start: 2026-11-08T13:31:27.098683+00:00; elapsed: 0.010328 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 14. effectful-unreachable

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int) = case x:
    _ -> x
    _ -> ping::get()
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/effectarg-effectful-unreachable.yu
```

UTC start: 2026-11-08T13:31:27.109298+00:00; elapsed: 0.018551 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> [ping] int = e13:(fn p4:d8:x -> e12:case e7:r3:x->d8:x { p5:_ -> e8:r4:x->d8:x; p6:_ -> e11:(e9:r5:"ping::get"->d1:"ping.get" e10:()) })
d4:higher: (int -> [ping] int) -> int = e19:(fn p7:d9:f -> e18:(e14:r6:f->d9:f e17:(e15:r7:"ping::get"->d1:"ping.get" e16:())))
root exprs e24:(e20:r8:handle->d2:handle e23:(e21:r9:higher->d4:higher e22:r10:plain->d3:plain))
runtime roots e24:(e20:r8:handle->d2:handle e23:(e21:r9:higher->d4:higher e22:r10:plain->d3:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:x arg
  d9:f arg
}

```

stderr:
```text

```

## 15. effectful-unreachable

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int) = case x:
    _ -> x
    _ -> ping::get()
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/effectarg-effectful-unreachable.yu
```

UTC start: 2026-11-08T13:31:27.128263+00:00; elapsed: 0.003011 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 16. effectful-unreachable

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int) = case x:
    _ -> x
    _ -> ping::get()
our higher(f: int -> [ping] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/effectarg-effectful-unreachable.yu
```

UTC start: 2026-11-08T13:31:27.131592+00:00; elapsed: 0.014324 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 17. pure-ascribed-function

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
my f: int -> [ping] int = plain
handle(f(ping::get()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/effectarg-pure-ascribed-function.yu
```

UTC start: 2026-11-08T13:31:27.146296+00:00; elapsed: 0.009611 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 18. pure-ascribed-function

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
my f: int -> [ping] int = plain
handle(f(ping::get()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/effectarg-pure-ascribed-function.yu
```

UTC start: 2026-11-08T13:31:27.156237+00:00; elapsed: 0.011177 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:f
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> int = e8:(fn p4:d8:x -> e7:r3:x->d8:x)
my d4:f: int -> int = e9:r4:plain->d3:plain
root exprs e16:(e10:r5:handle->d2:handle e15:(e11:r6:f->d4:f e14:(e12:r7:"ping::get"->d1:"ping.get" e13:())))
runtime roots e16:(e10:r5:handle->d2:handle e15:(e11:r6:f->d4:f e14:(e12:r7:"ping::get"->d1:"ping.get" e13:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:x arg
}

```

stderr:
```text

```

## 19. pure-ascribed-function

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
my f: int -> [ping] int = plain
handle(f(ping::get()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/effectarg-pure-ascribed-function.yu
```

UTC start: 2026-11-08T13:31:27.167745+00:00; elapsed: 0.002462 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())))))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> (d6 7), d7 -> d7
m1 = d4 : int -> int
  m2
m2 = d3 : int -> int
  \d8 -> d8

```

stderr:
```text

```

## 20. pure-ascribed-function

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
my f: int -> [ping] int = plain
handle(f(ping::get()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/effectarg-pure-ascribed-function.yu
```

UTC start: 2026-11-08T13:31:27.170481+00:00; elapsed: 0.005001 s; exit: 0; timeout: False

stdout:
```text
run roots [7]

```

stderr:
```text

```

## 21. effectful-inferred

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int) = ping::get()
our higher(f) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/effectarg-effectful-inferred.yu
```

UTC start: 2026-11-08T13:31:27.175856+00:00; elapsed: 0.010913 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 22. effectful-inferred

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int) = ping::get()
our higher(f) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/effectarg-effectful-inferred.yu
```

UTC start: 2026-11-08T13:31:27.187075+00:00; elapsed: 0.008984 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> [ping] int = e10:(fn p4:d8:x -> e9:(e7:r3:"ping::get"->d1:"ping.get" e8:()))
d4:higher: (int [ping] -> ['a] 'b) -> ['a] 'b = e16:(fn p5:d9:f -> e15:(e11:r4:f->d9:f e14:(e12:r5:"ping::get"->d1:"ping.get" e13:())))
root exprs e21:(e17:r6:handle->d2:handle e20:(e18:r7:higher->d4:higher e19:r8:plain->d3:plain))
runtime roots e21:(e17:r6:handle->d2:handle e20:(e18:r7:higher->d4:higher e19:r8:plain->d3:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:x arg
  d9:f arg
}

```

stderr:
```text

```

## 23. effectful-inferred

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int) = ping::get()
our higher(f) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/effectarg-effectful-inferred.yu
```

UTC start: 2026-11-08T13:31:27.196401+00:00; elapsed: 0.002822 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 (m1 m2))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> (d6 7), d7 -> d7
m1 = d4 : (thunk[[ping], int] -> thunk[[ping], int]) -> thunk[[ping], int]
  \d9 -> (d9 (<effect-op ping::get> ()))
m2 = d3 : thunk[[ping], int] -> thunk[[ping], int]
  \d8 -> (<effect-op ping::get> ())

```

stderr:
```text

```

## 24. effectful-inferred

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int) = ping::get()
our higher(f) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/effectarg-effectful-inferred.yu
```

UTC start: 2026-11-08T13:31:27.199530+00:00; elapsed: 0.003873 s; exit: 0; timeout: False

stdout:
```text
run roots [7]

```

stderr:
```text

```

## 25. polymorphic-effect-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> ['e] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/effectarg-polymorphic-effect-ret.yu
```

UTC start: 2026-11-08T13:31:27.203773+00:00; elapsed: 0.011865 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 26. polymorphic-effect-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> ['e] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/effectarg-polymorphic-effect-ret.yu
```

UTC start: 2026-11-08T13:31:27.216015+00:00; elapsed: 0.010578 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> int = e8:(fn p4:d8:x -> e7:r3:x->d8:x)
d4:higher: (int [ping] -> ['a] int) -> ['a] int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e19:(e15:r6:handle->d2:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d3:plain))
runtime roots e19:(e15:r6:handle->d2:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d3:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:x arg
  d9:f arg
}

```

stderr:
```text

```

## 27. polymorphic-effect-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> ['e] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/effectarg-polymorphic-effect-ret.yu
```

UTC start: 2026-11-08T13:31:27.226959+00:00; elapsed: 0.002657 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> (d6 7), d7 -> d7
m1 = d4 : (thunk[[ping], int] -> int) -> int
  \d9 -> (d9 (<effect-op ping::get> ()))
m2 = d3 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d8 -> d8)

```

stderr:
```text

```

## 28. polymorphic-effect-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> ['e] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/effectarg-polymorphic-effect-ret.yu
```

UTC start: 2026-11-08T13:31:27.229953+00:00; elapsed: 0.004421 s; exit: 0; timeout: False

stdout:
```text
run roots [7]

```

stderr:
```text

```

## 29. explicit-empty-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/effectarg-explicit-empty-ret.yu
```

UTC start: 2026-11-08T13:31:27.234815+00:00; elapsed: 0.010028 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 30. explicit-empty-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/effectarg-explicit-empty-ret.yu
```

UTC start: 2026-11-08T13:31:27.245227+00:00; elapsed: 0.009832 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> int = e8:(fn p4:d8:x -> e7:r3:x->d8:x)
d4:higher: (int [ping] -> ['a] int) -> ['a] int = e14:(fn p5:d9:f -> e13:(e9:r4:f->d9:f e12:(e10:r5:"ping::get"->d1:"ping.get" e11:())))
root exprs e19:(e15:r6:handle->d2:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d3:plain))
runtime roots e19:(e15:r6:handle->d2:handle e18:(e16:r7:higher->d4:higher e17:r8:plain->d3:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:x arg
  d9:f arg
}

```

stderr:
```text

```

## 31. explicit-empty-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/effectarg-explicit-empty-ret.yu
```

UTC start: 2026-11-08T13:31:27.255689+00:00; elapsed: 0.002751 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> (d6 7), d7 -> d7
m1 = d4 : (thunk[[ping], int] -> int) -> int
  \d9 -> (d9 (<effect-op ping::get> ()))
m2 = d3 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d8 -> d8)

```

stderr:
```text

```

## 32. explicit-empty-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [] int) = f(ping::get())
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/effectarg-explicit-empty-ret.yu
```

UTC start: 2026-11-08T13:31:27.258835+00:00; elapsed: 0.004611 s; exit: 0; timeout: False

stdout:
```text
run roots [7]

```

stderr:
```text

```
