# Cycle 3 raw log: f1

新spec基点 `816ed8f1d`、旧実機 `d4c8bc8fc`。出力はそのまま。dump exit 0 は診断なしを意味しない。

## 1. pure-explicit

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/pure-explicit.yu
```

UTC start: 2026-11-08T13:31:16.844033+00:00; elapsed: 0.011315 s; exit: 0; timeout: False

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
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/pure-explicit.yu
```

UTC start: 2026-11-08T13:31:16.855798+00:00; elapsed: 0.022894 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> int = e8:(fn p4:d8:x -> e7:r3:x->d8:x)
d4:higher: (int -> [ping] int) -> int = e12:(fn p5:d9:f -> e11:(e9:r4:f->d9:f e10:3))
root exprs e17:(e13:r5:handle->d2:handle e16:(e14:r6:higher->d4:higher e15:r7:plain->d3:plain))
runtime roots e17:(e13:r5:handle->d2:handle e16:(e14:r6:higher->d4:higher e15:r7:plain->d3:plain))
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
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## 3. pure-explicit

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/pure-explicit.yu
```

UTC start: 2026-11-08T13:31:16.878986+00:00; elapsed: 0.012136 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((adapter[(int -> thunk[[ping], int]) -> int => (int -> thunk[[ping], int]) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m1) adapter[int -> thunk[[ping], int] => int -> thunk[[ping], int]; hygiene[arg[add_id[1, ping, own, resume-own]]]](m2))))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> (d6 7), d7 -> d7
m1 = d4 : (int -> thunk[[ping], int]) -> int
  adapter[(int -> thunk[[ping], int]) -> thunk[[ping], int] => (int -> thunk[[ping], int]) -> int; hygiene[body[add_id[0, ping, own]], arg[add_id[1, ping, own, resume-own]]]](\d9 -> (d9 3))
m2 = d3 : int -> thunk[[ping], int]
  adapter[int -> int => int -> thunk[[ping], int]; hygiene[]](\d8 -> d8)

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)

```

## 4. pure-explicit

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/pure-explicit.yu
```

UTC start: 2026-11-08T13:31:16.891914+00:00; elapsed: 0.011871 s; exit: 0; timeout: False

stdout:
```text
run roots [3]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

```

## 5. pure-literal-lambda

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f 3
handle(higher (\x -> x))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/pure-literal-lambda.yu
```

UTC start: 2026-11-08T13:31:16.904274+00:00; elapsed: 0.012228 s; exit: 0; timeout: False

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
our higher(f: int -> [ping] int) = f 3
handle(higher (\x -> x))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/pure-literal-lambda.yu
```

UTC start: 2026-11-08T13:31:16.917019+00:00; elapsed: 0.009361 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d4:action -> e5:catch e0:r0:action->d4:action { ping::get p1:_, p2:d5:k -> e3:(e1:r1:k->d5:k e2:7); p3:d6:value -> e4:r2:value->d6:value })
d3:higher: (int -> [ping] int) -> int = e10:(fn p4:d7:f -> e9:(e7:r3:f->d7:f e8:3))
root exprs e16:(e11:r4:handle->d2:handle e15:(e12:r5:higher->d3:higher e14:(fn p5:d9:x -> e13:r6:x->d9:x)))
runtime roots e16:(e11:r4:handle->d2:handle e15:(e12:r5:higher->d3:higher e14:(fn p5:d9:x -> e13:r6:x->d9:x)))
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
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## 7. pure-literal-lambda

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f 3
handle(higher (\x -> x))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/pure-literal-lambda.yu
```

UTC start: 2026-11-08T13:31:16.926691+00:00; elapsed: 0.011265 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((adapter[(int -> thunk[[ping], int]) -> int => (int -> thunk[[ping], int]) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m1) adapter[int -> int => int -> thunk[[ping], int]; hygiene[arg[add_id[1, ping, own, resume-own]]]](\d9 -> d9))))]
m0 = d2 : thunk[[ping], int] -> int
  \d4 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d4)): ping::get _, d5 -> (d5 7), d6 -> d6
m1 = d3 : (int -> thunk[[ping], int]) -> int
  adapter[(int -> thunk[[ping], int]) -> thunk[[ping], int] => (int -> thunk[[ping], int]) -> int; hygiene[body[add_id[0, ping, own]], arg[add_id[1, ping, own, resume-own]]]](\d7 -> (d7 3))

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)

```

## 8. pure-literal-lambda

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our higher(f: int -> [ping] int) = f 3
handle(higher (\x -> x))

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/pure-literal-lambda.yu
```

UTC start: 2026-11-08T13:31:16.940743+00:00; elapsed: 0.010846 s; exit: 0; timeout: False

stdout:
```text
run roots [3]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

```

## 9. effectful-actual

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): [ping] int = ping::get()
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/effectful-actual.yu
```

UTC start: 2026-11-08T13:31:16.951890+00:00; elapsed: 0.010921 s; exit: 0; timeout: False

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
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/effectful-actual.yu
```

UTC start: 2026-11-08T13:31:16.963203+00:00; elapsed: 0.010926 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> [ping] int = e10:(fn p4:d8:x -> e9:(e7:r3:"ping::get"->d1:"ping.get" e8:()))
d4:higher: (int -> [ping] int) -> int = e14:(fn p5:d9:f -> e13:(e11:r4:f->d9:f e12:3))
root exprs e19:(e15:r5:handle->d2:handle e18:(e16:r6:higher->d4:higher e17:r7:plain->d3:plain))
runtime roots e19:(e15:r5:handle->d2:handle e18:(e16:r6:higher->d4:higher e17:r7:plain->d3:plain))
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
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## 11. effectful-actual

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): [ping] int = ping::get()
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/effectful-actual.yu
```

UTC start: 2026-11-08T13:31:16.974944+00:00; elapsed: 0.011910 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((adapter[(int -> thunk[[ping], int]) -> int => (int -> thunk[[ping], int]) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m1) adapter[int -> thunk[[ping], int] => int -> thunk[[ping], int]; hygiene[arg[add_id[1, ping, own, resume-own]]]](m2))))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> (d6 7), d7 -> d7
m1 = d4 : (int -> thunk[[ping], int]) -> int
  adapter[(int -> thunk[[ping], int]) -> thunk[[ping], int] => (int -> thunk[[ping], int]) -> int; hygiene[body[add_id[0, ping, own]], arg[add_id[1, ping, own, resume-own]]]](\d9 -> (d9 3))
m2 = d3 : int -> thunk[[ping], int]
  \d8 -> (<effect-op ping::get> ())

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)

```

## 12. effectful-actual

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): [ping] int = ping::get()
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/effectful-actual.yu
```

UTC start: 2026-11-08T13:31:16.987230+00:00; elapsed: 0.012121 s; exit: 0; timeout: False

stdout:
```text
run roots [7]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

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
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/effectful-unreachable.yu
```

UTC start: 2026-11-08T13:31:16.999779+00:00; elapsed: 0.010890 s; exit: 0; timeout: False

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
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/effectful-unreachable.yu
```

UTC start: 2026-11-08T13:31:17.011222+00:00; elapsed: 0.013186 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> [ping] int = e13:(fn p4:d8:x -> e12:case e7:r3:x->d8:x { p5:_ -> e8:r4:x->d8:x; p6:_ -> e11:(e9:r5:"ping::get"->d1:"ping.get" e10:()) })
d4:higher: (int -> [ping] int) -> int = e17:(fn p7:d9:f -> e16:(e14:r6:f->d9:f e15:3))
root exprs e22:(e18:r7:handle->d2:handle e21:(e19:r8:higher->d4:higher e20:r9:plain->d3:plain))
runtime roots e22:(e18:r7:handle->d2:handle e21:(e19:r8:higher->d4:higher e20:r9:plain->d3:plain))
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
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

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
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/effectful-unreachable.yu
```

UTC start: 2026-11-08T13:31:17.024760+00:00; elapsed: 0.014680 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((adapter[(int -> thunk[[ping], int]) -> int => (int -> thunk[[ping], int]) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m1) adapter[int -> thunk[[ping], int] => int -> thunk[[ping], int]; hygiene[arg[add_id[1, ping, own, resume-own]]]](m2))))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> (d6 7), d7 -> d7
m1 = d4 : (int -> thunk[[ping], int]) -> int
  adapter[(int -> thunk[[ping], int]) -> thunk[[ping], int] => (int -> thunk[[ping], int]) -> int; hygiene[body[add_id[0, ping, own]], arg[add_id[1, ping, own, resume-own]]]](\d9 -> (d9 3))
m2 = d3 : int -> thunk[[ping], int]
  \d8 -> make-thunk[int ! [ping] => thunk[[ping], int]](case d8: _ -> d8, _ -> force-thunk[thunk[[ping], int] => int ! [ping]]((<effect-op ping::get> ())))

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)

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
our higher(f: int -> [ping] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/effectful-unreachable.yu
```

UTC start: 2026-11-08T13:31:17.039789+00:00; elapsed: 0.013397 s; exit: 0; timeout: False

stdout:
```text
run roots [3]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

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
handle(f 3)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/pure-ascribed-function.yu
```

UTC start: 2026-11-08T13:31:17.053876+00:00; elapsed: 0.008641 s; exit: 0; timeout: False

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
handle(f 3)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/pure-ascribed-function.yu
```

UTC start: 2026-11-08T13:31:17.062847+00:00; elapsed: 0.009183 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:f
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> int = e8:(fn p4:d8:x -> e7:r3:x->d8:x)
my d4:f: int -> int = e9:r4:plain->d3:plain
root exprs e14:(e10:r5:handle->d2:handle e13:(e11:r6:f->d4:f e12:3))
runtime roots e14:(e10:r5:handle->d2:handle e13:(e11:r6:f->d4:f e12:3))
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
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

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
handle(f 3)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/pure-ascribed-function.yu
```

UTC start: 2026-11-08T13:31:17.072577+00:00; elapsed: 0.039785 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 3)))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> (d6 7), d7 -> d7
m1 = d4 : int -> int
  m2
m2 = d3 : int -> int
  \d8 -> d8

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)

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
handle(f 3)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/pure-ascribed-function.yu
```

UTC start: 2026-11-08T13:31:17.112843+00:00; elapsed: 0.010521 s; exit: 0; timeout: False

stdout:
```text
run roots [3]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

```

## 21. effectful-inferred

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int) = ping::get()
our higher(f) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/effectful-inferred.yu
```

UTC start: 2026-11-08T13:31:17.123781+00:00; elapsed: 0.010209 s; exit: 0; timeout: False

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
our higher(f) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/effectful-inferred.yu
```

UTC start: 2026-11-08T13:31:17.134547+00:00; elapsed: 0.010145 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> [ping] int = e10:(fn p4:d8:x -> e9:(e7:r3:"ping::get"->d1:"ping.get" e8:()))
d4:higher: (int -> ['a] 'b) -> ['a] 'b = e14:(fn p5:d9:f -> e13:(e11:r4:f->d9:f e12:3))
root exprs e19:(e15:r5:handle->d2:handle e18:(e16:r6:higher->d4:higher e17:r7:plain->d3:plain))
runtime roots e19:(e15:r5:handle->d2:handle e18:(e16:r6:higher->d4:higher e17:r7:plain->d3:plain))
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
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## 23. effectful-inferred

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int) = ping::get()
our higher(f) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/effectful-inferred.yu
```

UTC start: 2026-11-08T13:31:17.145076+00:00; elapsed: 0.008212 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 (m1 m2))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> (d6 7), d7 -> d7
m1 = d4 : (int -> thunk[[ping], int]) -> thunk[[ping], int]
  \d9 -> (d9 3)
m2 = d3 : int -> thunk[[ping], int]
  \d8 -> (<effect-op ping::get> ())

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)

```

## 24. effectful-inferred

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int) = ping::get()
our higher(f) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/effectful-inferred.yu
```

UTC start: 2026-11-08T13:31:17.153905+00:00; elapsed: 0.010464 s; exit: 0; timeout: False

stdout:
```text
run roots [7]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

```

## 25. polymorphic-effect-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> ['e] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/polymorphic-effect-ret.yu
```

UTC start: 2026-11-08T13:31:17.164904+00:00; elapsed: 0.009433 s; exit: 0; timeout: False

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
our higher(f: int -> ['e] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/polymorphic-effect-ret.yu
```

UTC start: 2026-11-08T13:31:17.174762+00:00; elapsed: 0.008448 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> int = e8:(fn p4:d8:x -> e7:r3:x->d8:x)
d4:higher: (int -> ['a] int) -> ['a] int = e12:(fn p5:d9:f -> e11:(e9:r4:f->d9:f e10:3))
root exprs e17:(e13:r5:handle->d2:handle e16:(e14:r6:higher->d4:higher e15:r7:plain->d3:plain))
runtime roots e17:(e13:r5:handle->d2:handle e16:(e14:r6:higher->d4:higher e15:r7:plain->d3:plain))
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
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## 27. polymorphic-effect-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> ['e] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/polymorphic-effect-ret.yu
```

UTC start: 2026-11-08T13:31:17.183623+00:00; elapsed: 0.010253 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> (d6 7), d7 -> d7
m1 = d4 : (int -> int) -> int
  \d9 -> (d9 3)
m2 = d3 : int -> int
  \d8 -> d8

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)

```

## 28. polymorphic-effect-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> ['e] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/polymorphic-effect-ret.yu
```

UTC start: 2026-11-08T13:31:17.194392+00:00; elapsed: 0.011045 s; exit: 0; timeout: False

stdout:
```text
run roots [3]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

```

## 29. explicit-empty-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/explicit-empty-ret.yu
```

UTC start: 2026-11-08T13:31:17.206032+00:00; elapsed: 0.008508 s; exit: 0; timeout: False

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
our higher(f: int -> [] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/explicit-empty-ret.yu
```

UTC start: 2026-11-08T13:31:17.214982+00:00; elapsed: 0.009096 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping d2:handle d3:plain d4:higher
d0:ping mod {
}
d2:handle: int ['a & [ping; 'a]] -> ['a] int = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:7); p3:d7:value -> e4:r2:value->d7:value })
d3:plain: int -> int = e8:(fn p4:d8:x -> e7:r3:x->d8:x)
d4:higher: (int -> ['a] int) -> ['a] int = e12:(fn p5:d9:f -> e11:(e9:r4:f->d9:f e10:3))
root exprs e17:(e13:r5:handle->d2:handle e16:(e14:r6:higher->d4:higher e15:r7:plain->d3:plain))
runtime roots e17:(e13:r5:handle->d2:handle e16:(e14:r6:higher->d4:higher e15:r7:plain->d3:plain))
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
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## 31. explicit-empty-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/explicit-empty-ret.yu
```

UTC start: 2026-11-08T13:31:17.224655+00:00; elapsed: 0.009235 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d2 : thunk[[ping], int] -> int
  \d5 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d5)): ping::get _, d6 -> (d6 7), d7 -> d7
m1 = d4 : (int -> int) -> int
  \d9 -> (d9 3)
m2 = d3 : int -> int
  \d8 -> d8

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)

```

## 32. explicit-empty-ret

```yulang
act ping:
    our get: () -> int
our handle(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our plain(x: int): int = x
our higher(f: int -> [] int) = f 3
handle(higher plain)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/explicit-empty-ret.yu
```

UTC start: 2026-11-08T13:31:17.234363+00:00; elapsed: 0.009181 s; exit: 0; timeout: False

stdout:
```text
run roots [3]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

```
