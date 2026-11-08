# Cycle 3 raw log: timing

新spec基点 `816ed8f1d`、旧実機 `d4c8bc8fc`。出力はそのまま。dump exit 0 は診断なしを意味しない。

## 1. ignored-argument

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore(x: int): int = 42
(abort(ignore(ping::get())), resume(ignore(ping::get())))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/ignored-argument.yu
```

UTC start: 2026-11-08T13:34:25.514785+00:00; elapsed: 0.016318 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 2. ignored-argument

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore(x: int): int = 42
(abort(ignore(ping::get())), resume(ignore(ping::get())))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/ignored-argument.yu
```

UTC start: 2026-11-08T13:34:25.531339+00:00; elapsed: 0.019315 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:abort d3:resume d4:ignore
d0:ping mod {
}
d2:abort: int [ping; 'a] -> ['a] int = e4:(fn p0:d5:action -> e3:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e1:99; p3:d7:value -> e2:r1:value->d7:value })
d3:resume: int ['a & [ping; 'a]] -> ['a] int = e11:(fn p4:d8:action -> e10:catch e5:r2:action->d8:action { ping::get p5:_, p6:d9:k -> e8:(e6:r3:k->d9:k e7:7); p7:d10:value -> e9:r4:value->d10:value })
d4:ignore: int -> int = e13:(fn p8:d11:x -> e12:42)
root exprs e28:(e20:(e14:r5:abort->d2:abort e19:(e15:r6:ignore->d4:ignore e18:(e16:r7:"ping::get"->d1:"ping.get" e17:()))), e27:(e21:r8:resume->d3:resume e26:(e22:r9:ignore->d4:ignore e25:(e23:r10:"ping::get"->d1:"ping.get" e24:()))))
runtime roots e28:(e20:(e14:r5:abort->d2:abort e19:(e15:r6:ignore->d4:ignore e18:(e16:r7:"ping::get"->d1:"ping.get" e17:()))), e27:(e21:r8:resume->d3:resume e26:(e22:r9:ignore->d4:ignore e25:(e23:r10:"ping::get"->d1:"ping.get" e24:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:action arg
  d9:k arg
  d10:value arg
  d11:x arg
}

```

stderr:
```text

```

## 3. ignored-argument

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore(x: int): int = 42
(abort(ignore(ping::get())), resume(ignore(ping::get())))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/ignored-argument.yu
```

UTC start: 2026-11-08T13:34:25.550909+00:00; elapsed: 0.003686 s; exit: 0; timeout: False

stdout:
```text
mono roots [((m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ()))))), (m2 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ()))))))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> 99, d7 -> d7
m1 = d4 : int -> int
  \d11 -> 42
m2 = d3 : thunk[[ping], int] -> int
  \d8 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d8)): ping::get _, d9 -> (d9 7), d10 -> d10

```

stderr:
```text

```

## 4. ignored-argument

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore(x: int): int = 42
(abort(ignore(ping::get())), resume(ignore(ping::get())))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/ignored-argument.yu
```

UTC start: 2026-11-08T13:34:25.554793+00:00; elapsed: 0.005429 s; exit: 0; timeout: False

stdout:
```text
run roots [(99, 42)]

```

stderr:
```text

```

## 5. used-argument

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ident(x: int): int = x
(abort(ident(ping::get())), resume(ident(ping::get())))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/used-argument.yu
```

UTC start: 2026-11-08T13:34:25.561012+00:00; elapsed: 0.017161 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 6. used-argument

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ident(x: int): int = x
(abort(ident(ping::get())), resume(ident(ping::get())))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/used-argument.yu
```

UTC start: 2026-11-08T13:34:25.578459+00:00; elapsed: 0.014851 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:abort d3:resume d4:ident
d0:ping mod {
}
d2:abort: int [ping; 'a] -> ['a] int = e4:(fn p0:d5:action -> e3:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e1:99; p3:d7:value -> e2:r1:value->d7:value })
d3:resume: int ['a & [ping; 'a]] -> ['a] int = e11:(fn p4:d8:action -> e10:catch e5:r2:action->d8:action { ping::get p5:_, p6:d9:k -> e8:(e6:r3:k->d9:k e7:7); p7:d10:value -> e9:r4:value->d10:value })
d4:ident: int -> int = e13:(fn p8:d11:x -> e12:r5:x->d11:x)
root exprs e28:(e20:(e14:r6:abort->d2:abort e19:(e15:r7:ident->d4:ident e18:(e16:r8:"ping::get"->d1:"ping.get" e17:()))), e27:(e21:r9:resume->d3:resume e26:(e22:r10:ident->d4:ident e25:(e23:r11:"ping::get"->d1:"ping.get" e24:()))))
runtime roots e28:(e20:(e14:r6:abort->d2:abort e19:(e15:r7:ident->d4:ident e18:(e16:r8:"ping::get"->d1:"ping.get" e17:()))), e27:(e21:r9:resume->d3:resume e26:(e22:r10:ident->d4:ident e25:(e23:r11:"ping::get"->d1:"ping.get" e24:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:action arg
  d9:k arg
  d10:value arg
  d11:x arg
}

```

stderr:
```text

```

## 7. used-argument

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ident(x: int): int = x
(abort(ident(ping::get())), resume(ident(ping::get())))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/used-argument.yu
```

UTC start: 2026-11-08T13:34:25.593709+00:00; elapsed: 0.004266 s; exit: 0; timeout: False

stdout:
```text
mono roots [((m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ()))))), (m2 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ()))))))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> 99, d7 -> d7
m1 = d4 : int -> int
  \d11 -> d11
m2 = d3 : thunk[[ping], int] -> int
  \d8 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d8)): ping::get _, d9 -> (d9 7), d10 -> d10

```

stderr:
```text

```

## 8. used-argument

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ident(x: int): int = x
(abort(ident(ping::get())), resume(ident(ping::get())))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/used-argument.yu
```

UTC start: 2026-11-08T13:34:25.598388+00:00; elapsed: 0.005335 s; exit: 0; timeout: False

stdout:
```text
run roots [(99, 7)]

```

stderr:
```text

```

## 9. argument-twice

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our twice(x: int): (int,int) = (x,x)
catch twice(ping::get()):
    ping::get(), k -> k 7
    value -> value

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/argument-twice.yu
```

UTC start: 2026-11-08T13:34:25.603989+00:00; elapsed: 0.012974 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 10. argument-twice

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our twice(x: int): (int,int) = (x,x)
catch twice(ping::get()):
    ping::get(), k -> k 7
    value -> value

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/argument-twice.yu
```

UTC start: 2026-11-08T13:34:25.617238+00:00; elapsed: 0.012773 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:abort d3:resume d4:twice
d0:ping mod {
}
d2:abort: int [ping; 'a] -> ['a] int = e4:(fn p0:d5:action -> e3:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e1:99; p3:d7:value -> e2:r1:value->d7:value })
d3:resume: int ['a & [ping; 'a]] -> ['a] int = e11:(fn p4:d8:action -> e10:catch e5:r2:action->d8:action { ping::get p5:_, p6:d9:k -> e8:(e6:r3:k->d9:k e7:7); p7:d10:value -> e9:r4:value->d10:value })
d4:twice: int -> (int, int) = e15:(fn p8:d11:x -> e14:(e12:r5:x->d11:x, e13:r6:x->d11:x))
root exprs e25:catch e20:(e16:r7:twice->d4:twice e19:(e17:r8:"ping::get"->d1:"ping.get" e18:())) { ping::get p9:_, p10:d13:k -> e23:(e21:r9:k->d13:k e22:7); p11:d14:value -> e24:r10:value->d14:value }
runtime roots e25:catch e20:(e16:r7:twice->d4:twice e19:(e17:r8:"ping::get"->d1:"ping.get" e18:())) { ping::get p9:_, p10:d13:k -> e23:(e21:r9:k->d13:k e22:7); p11:d14:value -> e24:r10:value->d14:value }
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:action arg
  d9:k arg
  d10:value arg
  d11:x arg
  d13:k arg
  d14:value arg
}

```

stderr:
```text

```

## 11. argument-twice

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our twice(x: int): (int,int) = (x,x)
catch twice(ping::get()):
    ping::get(), k -> k 7
    value -> value

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/argument-twice.yu
```

UTC start: 2026-11-08T13:34:25.630708+00:00; elapsed: 0.003306 s; exit: 0; timeout: False

stdout:
```text
mono roots [catch (m0 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ()))): ping::get _, d13 -> (d13 7), d14 -> d14]
m0 = d4 : int -> (int, int)
  \d11 -> (d11, d11)

```

stderr:
```text

```

## 12. argument-twice

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our twice(x: int): (int,int) = (x,x)
catch twice(ping::get()):
    ping::get(), k -> k 7
    value -> value

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/argument-twice.yu
```

UTC start: 2026-11-08T13:34:25.634290+00:00; elapsed: 0.004146 s; exit: 0; timeout: False

stdout:
```text
run roots [(7, 7)]

```

stderr:
```text

```

## 13. pure-let-unused

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our f(): int =
    my x = ping::get()
    42
(abort(f()), resume(f()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/pure-let-unused.yu
```

UTC start: 2026-11-08T13:34:25.638918+00:00; elapsed: 0.013825 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 14. pure-let-unused

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our f(): int =
    my x = ping::get()
    42
(abort(f()), resume(f()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/pure-let-unused.yu
```

UTC start: 2026-11-08T13:34:25.653148+00:00; elapsed: 0.012690 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:abort d3:resume d4:f
d0:ping mod {
}
d2:abort: int [ping; 'a] -> ['a] int = e4:(fn p0:d5:action -> e3:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e1:99; p3:d7:value -> e2:r1:value->d7:value })
d3:resume: int ['a & [ping; 'a]] -> ['a] int = e11:(fn p4:d8:action -> e10:catch e5:r2:action->d8:action { ping::get p5:_, p6:d9:k -> e8:(e6:r3:k->d9:k e7:7); p7:d10:value -> e9:r4:value->d10:value })
d4:f: () -> [ping] int = e17:(fn p8:() -> e16:block { let my p9:d11:x = e14:(e12:r5:"ping::get"->d1:"ping.get" e13:()); e15:42 })
root exprs e28:(e22:(e18:r6:abort->d2:abort e21:(e19:r7:f->d4:f e20:())), e27:(e23:r8:resume->d3:resume e26:(e24:r9:f->d4:f e25:())))
runtime roots e28:(e22:(e18:r6:abort->d2:abort e21:(e19:r7:f->d4:f e20:())), e27:(e23:r8:resume->d3:resume e26:(e24:r9:f->d4:f e25:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:action arg
  d9:k arg
  d10:value arg
  my d11:x: 'a | int = e14:(e12:r5:"ping::get"->d1:"ping.get" e13:())
}

```

stderr:
```text

```

## 15. pure-let-unused

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our f(): int =
    my x = ping::get()
    42
(abort(f()), resume(f()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/pure-let-unused.yu
```

UTC start: 2026-11-08T13:34:25.666283+00:00; elapsed: 0.003995 s; exit: 0; timeout: False

stdout:
```text
mono roots [((m0 (m1 ())), (m2 (m1 ())))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> 99, d7 -> d7
m1 = d4 : unit -> thunk[[ping], int]
  \() -> make-thunk[int ! [ping] => thunk[[ping], int]]({ my d11 = force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())); 42 })
m2 = d3 : thunk[[ping], int] -> int
  \d8 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d8)): ping::get _, d9 -> (d9 7), d10 -> d10

```

stderr:
```text

```

## 16. pure-let-unused

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our f(): int =
    my x = ping::get()
    42
(abort(f()), resume(f()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/pure-let-unused.yu
```

UTC start: 2026-11-08T13:34:25.670853+00:00; elapsed: 0.005018 s; exit: 0; timeout: False

stdout:
```text
run roots [(99, 42)]

```

stderr:
```text

```

## 17. bare-discard

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our f(): int =
    ping::get()
    42
(abort(f()), resume(f()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/bare-discard.yu
```

UTC start: 2026-11-08T13:34:25.676227+00:00; elapsed: 0.012752 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 18. bare-discard

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our f(): int =
    ping::get()
    42
(abort(f()), resume(f()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/bare-discard.yu
```

UTC start: 2026-11-08T13:34:25.689348+00:00; elapsed: 0.013211 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:abort d3:resume d4:f
d0:ping mod {
}
d2:abort: int [ping; 'a] -> ['a] int = e4:(fn p0:d5:action -> e3:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e1:99; p3:d7:value -> e2:r1:value->d7:value })
d3:resume: int ['a & [ping; 'a]] -> ['a] int = e11:(fn p4:d8:action -> e10:catch e5:r2:action->d8:action { ping::get p5:_, p6:d9:k -> e8:(e6:r3:k->d9:k e7:7); p7:d10:value -> e9:r4:value->d10:value })
d4:f: () -> [ping] int = e17:(fn p8:() -> e16:block { e14:(e12:r5:"ping::get"->d1:"ping.get" e13:()); e15:42 })
root exprs e28:(e22:(e18:r6:abort->d2:abort e21:(e19:r7:f->d4:f e20:())), e27:(e23:r8:resume->d3:resume e26:(e24:r9:f->d4:f e25:())))
runtime roots e28:(e22:(e18:r6:abort->d2:abort e21:(e19:r7:f->d4:f e20:())), e27:(e23:r8:resume->d3:resume e26:(e24:r9:f->d4:f e25:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:action arg
  d9:k arg
  d10:value arg
}

```

stderr:
```text

```

## 19. bare-discard

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our f(): int =
    ping::get()
    42
(abort(f()), resume(f()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/bare-discard.yu
```

UTC start: 2026-11-08T13:34:25.703116+00:00; elapsed: 0.003667 s; exit: 0; timeout: False

stdout:
```text
mono roots [((m0 (m1 ())), (m2 (m1 ())))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> 99, d7 -> d7
m1 = d4 : unit -> thunk[[ping], int]
  \() -> make-thunk[int ! [ping] => thunk[[ping], int]]({ force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())); 42 })
m2 = d3 : thunk[[ping], int] -> int
  \d8 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d8)): ping::get _, d9 -> (d9 7), d10 -> d10

```

stderr:
```text

```

## 20. bare-discard

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our f(): int =
    ping::get()
    42
(abort(f()), resume(f()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/bare-discard.yu
```

UTC start: 2026-11-08T13:34:25.707117+00:00; elapsed: 0.004282 s; exit: 0; timeout: False

stdout:
```text
run roots [(99, 42)]

```

stderr:
```text

```

## 21. partial-unused-first

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our second(x: int)(y: int): int = y
abort((second(ping::get())) 42)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/partial-unused-first.yu
```

UTC start: 2026-11-08T13:34:25.711918+00:00; elapsed: 0.011813 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 22. partial-unused-first

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our second(x: int)(y: int): int = y
abort((second(ping::get())) 42)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/partial-unused-first.yu
```

UTC start: 2026-11-08T13:34:25.724233+00:00; elapsed: 0.012131 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:abort d3:resume d4:second
d0:ping mod {
}
d2:abort: int [ping; 'a] -> ['a] int = e4:(fn p0:d5:action -> e3:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e1:99; p3:d7:value -> e2:r1:value->d7:value })
d3:resume: int ['a & [ping; 'a]] -> ['a] int = e11:(fn p4:d8:action -> e10:catch e5:r2:action->d8:action { ping::get p5:_, p6:d9:k -> e8:(e6:r3:k->d9:k e7:7); p7:d10:value -> e9:r4:value->d10:value })
d4:second: int -> int -> int = e14:(fn p8:d11:x -> e13:(fn p9:d12:y -> e12:r5:y->d12:y))
root exprs e23:(e15:r6:abort->d2:abort e22:(e20:(e16:r7:second->d4:second e19:(e17:r8:"ping::get"->d1:"ping.get" e18:())) e21:42))
runtime roots e23:(e15:r6:abort->d2:abort e22:(e20:(e16:r7:second->d4:second e19:(e17:r8:"ping::get"->d1:"ping.get" e18:())) e21:42))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:action arg
  d9:k arg
  d10:value arg
  d11:x arg
  d12:y arg
}

```

stderr:
```text

```

## 23. partial-unused-first

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our second(x: int)(y: int): int = y
abort((second(ping::get())) 42)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/partial-unused-first.yu
```

UTC start: 2026-11-08T13:34:25.736933+00:00; elapsed: 0.003446 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]](((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ()))) 42)))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> 99, d7 -> d7
m1 = d4 : int -> int -> int
  \d11 -> \d12 -> d12

```

stderr:
```text

```

## 24. partial-unused-first

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our second(x: int)(y: int): int = y
abort((second(ping::get())) 42)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/partial-unused-first.yu
```

UTC start: 2026-11-08T13:34:25.740924+00:00; elapsed: 0.004499 s; exit: 0; timeout: False

stdout:
```text
run roots [99]

```

stderr:
```text

```

## 25. partial-return-ignored

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our second(x: int)(y: int): int = y
our ignore_fun f = 42
abort(ignore_fun(second(ping::get())))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/partial-return-ignored.yu
```

UTC start: 2026-11-08T13:34:25.745920+00:00; elapsed: 0.010916 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 26. partial-return-ignored

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our second(x: int)(y: int): int = y
our ignore_fun f = 42
abort(ignore_fun(second(ping::get())))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/partial-return-ignored.yu
```

UTC start: 2026-11-08T13:34:25.757245+00:00; elapsed: 0.012505 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:abort d3:resume d4:second d5:ignore_fun
d0:ping mod {
}
d2:abort: int [ping; 'a] -> ['a] int = e4:(fn p0:d6:action -> e3:catch e0:r0:action->d6:action { ping::get p1:_, p2:d7:k -> e1:99; p3:d8:value -> e2:r1:value->d8:value })
d3:resume: int ['a & [ping; 'a]] -> ['a] int = e11:(fn p4:d9:action -> e10:catch e5:r2:action->d9:action { ping::get p5:_, p6:d10:k -> e8:(e6:r3:k->d10:k e7:7); p7:d11:value -> e9:r4:value->d11:value })
d4:second: int -> int -> int = e14:(fn p8:d12:x -> e13:(fn p9:d13:y -> e12:r5:y->d13:y))
d5:ignore_fun: any -> int = e16:(fn p10:d14:f -> e15:42)
root exprs e25:(e17:r6:abort->d2:abort e24:(e18:r7:ignore_fun->d5:ignore_fun e23:(e19:r8:second->d4:second e22:(e20:r9:"ping::get"->d1:"ping.get" e21:()))))
runtime roots e25:(e17:r6:abort->d2:abort e24:(e18:r7:ignore_fun->d5:ignore_fun e23:(e19:r8:second->d4:second e22:(e20:r9:"ping::get"->d1:"ping.get" e21:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d6:action arg
  d7:k arg
  d8:value arg
  d9:action arg
  d10:k arg
  d11:value arg
  d12:x arg
  d13:y arg
  d14:f arg
}

```

stderr:
```text

```

## 27. partial-return-ignored

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our second(x: int)(y: int): int = y
our ignore_fun f = 42
abort(ignore_fun(second(ping::get())))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/partial-return-ignored.yu
```

UTC start: 2026-11-08T13:34:25.770277+00:00; elapsed: 0.003592 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 (m2 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ()))))))]
m0 = d2 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> 99, d8 -> d8
m1 = d5 : (int -> int) -> int
  \d14 -> 42
m2 = d4 : int -> int -> int
  \d12 -> \d13 -> d13

```

stderr:
```text

```

## 28. partial-return-ignored

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our second(x: int)(y: int): int = y
our ignore_fun f = 42
abort(ignore_fun(second(ping::get())))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/partial-return-ignored.yu
```

UTC start: 2026-11-08T13:34:25.774301+00:00; elapsed: 0.004913 s; exit: 0; timeout: False

stdout:
```text
run roots [99]

```

stderr:
```text

```

## 29. lambda-delay

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore_fun f = 42
abort(ignore_fun(\x -> ping::get()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/lambda-delay.yu
```

UTC start: 2026-11-08T13:34:25.779715+00:00; elapsed: 0.010644 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 30. lambda-delay

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore_fun f = 42
abort(ignore_fun(\x -> ping::get()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/lambda-delay.yu
```

UTC start: 2026-11-08T13:34:25.791036+00:00; elapsed: 0.011630 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:abort d3:resume d4:ignore_fun
d0:ping mod {
}
d2:abort: int [ping; 'a] -> ['a] int = e4:(fn p0:d5:action -> e3:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e1:99; p3:d7:value -> e2:r1:value->d7:value })
d3:resume: int ['a & [ping; 'a]] -> ['a] int = e11:(fn p4:d8:action -> e10:catch e5:r2:action->d8:action { ping::get p5:_, p6:d9:k -> e8:(e6:r3:k->d9:k e7:7); p7:d10:value -> e9:r4:value->d10:value })
d4:ignore_fun: any -> int = e13:(fn p8:d11:f -> e12:42)
root exprs e21:(e14:r5:abort->d2:abort e20:(e15:r6:ignore_fun->d4:ignore_fun e19:(fn p9:d13:x -> e18:(e16:r7:"ping::get"->d1:"ping.get" e17:()))))
runtime roots e21:(e14:r5:abort->d2:abort e20:(e15:r6:ignore_fun->d4:ignore_fun e19:(fn p9:d13:x -> e18:(e16:r7:"ping::get"->d1:"ping.get" e17:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:action arg
  d9:k arg
  d10:value arg
  d11:f arg
  d13:x arg
}

```

stderr:
```text

```

## 31. lambda-delay

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore_fun f = 42
abort(ignore_fun(\x -> ping::get()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/lambda-delay.yu
```

UTC start: 2026-11-08T13:34:25.803472+00:00; elapsed: 0.003449 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 \d13 -> (<effect-op ping::get> ()))))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> 99, d7 -> d7
m1 = d4 : (unit -> thunk[[ping], int]) -> int
  \d11 -> 42

```

stderr:
```text

```

## 32. lambda-delay

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore_fun f = 42
abort(ignore_fun(\x -> ping::get()))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/lambda-delay.yu
```

UTC start: 2026-11-08T13:34:25.807396+00:00; elapsed: 0.004509 s; exit: 0; timeout: False

stdout:
```text
run roots [42]

```

stderr:
```text

```

## 33. pipe-ignored

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore(x: int): int = 42
abort(ping::get() | ignore)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/pipe-ignored.yu
```

UTC start: 2026-11-08T13:34:25.812592+00:00; elapsed: 0.010777 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 34. pipe-ignored

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore(x: int): int = 42
abort(ping::get() | ignore)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/pipe-ignored.yu
```

UTC start: 2026-11-08T13:34:25.824047+00:00; elapsed: 0.010470 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:abort d3:resume d4:ignore
d0:ping mod {
}
d2:abort: int [ping; 'a] -> ['a] int = e4:(fn p0:d5:action -> e3:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e1:99; p3:d7:value -> e2:r1:value->d7:value })
d3:resume: int ['a & [ping; 'a]] -> ['a] int = e11:(fn p4:d8:action -> e10:catch e5:r2:action->d8:action { ping::get p5:_, p6:d9:k -> e8:(e6:r3:k->d9:k e7:7); p7:d10:value -> e9:r4:value->d10:value })
d4:ignore: int -> int = e13:(fn p8:d11:x -> e12:42)
root exprs e20:(e14:r5:abort->d2:abort e19:(e18:r7:ignore->d4:ignore e17:(e15:r6:"ping::get"->d1:"ping.get" e16:())))
runtime roots e20:(e14:r5:abort->d2:abort e19:(e18:r7:ignore->d4:ignore e17:(e15:r6:"ping::get"->d1:"ping.get" e16:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:action arg
  d9:k arg
  d10:value arg
  d11:x arg
}

```

stderr:
```text

```

## 35. pipe-ignored

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore(x: int): int = 42
abort(ping::get() | ignore)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/pipe-ignored.yu
```

UTC start: 2026-11-08T13:34:25.835084+00:00; elapsed: 0.003158 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [ping] => thunk[[ping], int]]((m1 force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())))))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> 99, d7 -> d7
m1 = d4 : int -> int
  \d11 -> 42

```

stderr:
```text

```

## 36. pipe-ignored

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore(x: int): int = 42
abort(ping::get() | ignore)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/pipe-ignored.yu
```

UTC start: 2026-11-08T13:34:25.839040+00:00; elapsed: 0.004410 s; exit: 0; timeout: False

stdout:
```text
run roots [99]

```

stderr:
```text

```

## 37. higher-ignored

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore(x: int): int = 42
our higher f = f(ping::get())
abort(higher ignore)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/higher-ignored.yu
```

UTC start: 2026-11-08T13:34:25.844153+00:00; elapsed: 0.010687 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 38. higher-ignored

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore(x: int): int = 42
our higher f = f(ping::get())
abort(higher ignore)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/higher-ignored.yu
```

UTC start: 2026-11-08T13:34:25.855665+00:00; elapsed: 0.012047 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:abort d3:resume d4:ignore d5:higher
d0:ping mod {
}
d2:abort: int [ping; 'a] -> ['a] int = e4:(fn p0:d6:action -> e3:catch e0:r0:action->d6:action { ping::get p1:_, p2:d7:k -> e1:99; p3:d8:value -> e2:r1:value->d8:value })
d3:resume: int ['a & [ping; 'a]] -> ['a] int = e11:(fn p4:d9:action -> e10:catch e5:r2:action->d9:action { ping::get p5:_, p6:d10:k -> e8:(e6:r3:k->d10:k e7:7); p7:d11:value -> e9:r4:value->d11:value })
d4:ignore: int -> int = e13:(fn p8:d12:x -> e12:42)
d5:higher: (int [ping] -> ['a] 'b) -> ['a] 'b = e19:(fn p9:d13:f -> e18:(e14:r5:f->d13:f e17:(e15:r6:"ping::get"->d1:"ping.get" e16:())))
root exprs e24:(e20:r7:abort->d2:abort e23:(e21:r8:higher->d5:higher e22:r9:ignore->d4:ignore))
runtime roots e24:(e20:r7:abort->d2:abort e23:(e21:r8:higher->d5:higher e22:r9:ignore->d4:ignore))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d6:action arg
  d7:k arg
  d8:value arg
  d9:action arg
  d10:k arg
  d11:value arg
  d12:x arg
  d13:f arg
}

```

stderr:
```text

```

## 39. higher-ignored

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore(x: int): int = 42
our higher f = f(ping::get())
abort(higher ignore)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/higher-ignored.yu
```

UTC start: 2026-11-08T13:34:25.868340+00:00; elapsed: 0.003003 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d2 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> 99, d8 -> d8
m1 = d5 : (thunk[[ping], int] -> int) -> int
  \d13 -> (d13 (<effect-op ping::get> ()))
m2 = d4 : thunk[[ping], int] -> int
  \d12 -> 42

```

stderr:
```text

```

## 40. higher-ignored

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our ignore(x: int): int = 42
our higher f = f(ping::get())
abort(higher ignore)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/higher-ignored.yu
```

UTC start: 2026-11-08T13:34:25.872350+00:00; elapsed: 0.004057 s; exit: 0; timeout: False

stdout:
```text
run roots [42]

```

stderr:
```text

```
