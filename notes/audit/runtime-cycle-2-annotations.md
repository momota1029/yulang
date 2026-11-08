# §5.5b runtime raw log

61 CLI calls, 30 named inputs; 12 runner timeouts. All raw output follows. Timeout 124 is assigned by runner, not program exit.

## scc-forward
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(x): [ping] int = g x
my g(x): int = case x:
    true -> pong::get()
    false -> f true
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-forward.yu
```
exit=124; elapsed=40.05253358200207 seconds
```text
Command '['/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang', '--std-root', '/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib', '--no-prelude', 'check', '/tmp/audit2-annotations/scc-forward.yu']' timed out after 40 seconds
```

## quick-late-unknown
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g): [ping] int = g()
my later() = apply (\() -> pong::get())
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/quick-late-unknown.yu
```
exit=0; elapsed=0.008374515997275012 seconds
```text

```

## quick-late-unknown
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g): [ping] int = g()
my later() = apply (\() -> pong::get())
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/quick-late-unknown.yu --poly
```
exit=0; elapsed=0.007186976999946637 seconds
```text
roots d0:ping d2:pong d4:apply d5:later
d0:ping mod {
}
d2:pong mod {
}
my d4:apply: (() -> ['a] int) -> ['a] int = e3:(fn p0:d6:g -> e2:(e0:r0:g->d6:g e1:()))
my d5:later: () -> [pong] int = e10:(fn p1:() -> e9:(e4:r1:apply->d4:apply e8:(fn p2:() -> e7:(e5:r2:"pong::get"->d3:"pong.get" e6:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  d6:g arg
}

```

## quick-known-callback
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g: () -> [pong] int): [ping] int = g()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/quick-known-callback.yu
```
exit=1; elapsed=0.005153742000402417 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## quick-known-callback
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g: () -> [pong] int): [ping] int = g()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/quick-known-callback.yu --poly
```
exit=0; elapsed=0.005297633000736823 seconds
```text
roots d0:ping d2:pong d4:apply
d0:ping mod {
}
d2:pong mod {
}
my d4:apply: (() -> [pong] int) -> int = e3:(fn p0:d5:g -> e2:(e0:r0:g->d5:g e1:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  d5:g arg
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## quick-direct-body
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = pong::get()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/quick-direct-body.yu
```
exit=1; elapsed=0.0037102809983480256 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## quick-direct-body
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = pong::get()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/quick-direct-body.yu --poly
```
exit=0; elapsed=0.0052343290008138865 seconds
```text
roots d0:ping d2:pong d4:f
d0:ping mod {
}
d2:pong mod {
}
my d4:f: () -> [pong] int = e3:(fn p0:() -> e2:(e0:r0:"pong::get"->d3:"pong.get" e1:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## quick-late-glob
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g: () -> [_] int): [ping] int = g()
my later() = apply (\() -> pong::get())
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/quick-late-glob.yu
```
exit=0; elapsed=0.007023698002740275 seconds
```text

```

## quick-late-glob
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g: () -> [_] int): [ping] int = g()
my later() = apply (\() -> pong::get())
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/quick-late-glob.yu --poly
```
exit=0; elapsed=0.009147275999566773 seconds
```text
roots d0:ping d2:pong d4:apply d5:later
d0:ping mod {
}
d2:pong mod {
}
my d4:apply: (() -> ['a] int) -> ['a] int = e3:(fn p0:d6:g -> e2:(e0:r0:g->d6:g e1:()))
my d5:later: () -> [pong] int = e10:(fn p1:() -> e9:(e4:r1:apply->d4:apply e8:(fn p2:() -> e7:(e5:r2:"pong::get"->d3:"pong.get" e6:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  d6:g arg
}

```

## quick-nested-late
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my outer(g) = { my inner(): [ping] int = g(); inner() }
my later() = outer (\() -> pong::get())
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/quick-nested-late.yu
```
exit=0; elapsed=0.010117675999936182 seconds
```text

```

## quick-nested-late
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my outer(g) = { my inner(): [ping] int = g(); inner() }
my later() = outer (\() -> pong::get())
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/quick-nested-late.yu --poly
```
exit=0; elapsed=0.011342140998749528 seconds
```text
roots d0:ping d2:pong d4:outer d5:later
d0:ping mod {
}
d2:pong mod {
}
my d4:outer: (() -> ['a] int) -> ['a] int = e8:(fn p0:d6:g -> e7:block { let my p1:d7:inner = e3:(fn p2:() -> e2:(e0:r0:g->d6:g e1:())); e6:(e4:r1:inner->d7:inner e5:()) })
my d5:later: () -> [pong] int = e15:(fn p3:() -> e14:(e9:r2:outer->d4:outer e13:(fn p4:() -> e12:(e10:r3:"pong::get"->d3:"pong.get" e11:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  d6:g arg
  my d7:inner: () -> ['a, 'b, 'c, 'd, 'e] 'f | 'g | int = e3:(fn p2:() -> e2:(e0:r0:g->d6:g e1:()))
}

```

## quick-nested-known
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my outer() = { my inner(): [ping] int = pong::get(); inner() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/quick-nested-known.yu
```
exit=1; elapsed=0.004933631000312744 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## quick-nested-known
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my outer() = { my inner(): [ping] int = pong::get(); inner() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/quick-nested-known.yu --poly
```
exit=0; elapsed=0.005771641001047101 seconds
```text
roots d0:ping d2:pong d4:outer
d0:ping mod {
}
d2:pong mod {
}
my d4:outer: () -> [pong] int = e8:(fn p0:() -> e7:block { let my p1:d5:inner = e3:(fn p2:() -> e2:(e0:r0:"pong::get"->d3:"pong.get" e1:())); e6:(e4:r1:inner->d5:inner e5:()) })
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  my d5:inner: () -> [pong] int = e3:(fn p2:() -> e2:(e0:r0:"pong::get"->d3:"pong.get" e1:()))
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## scc-forward
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(x): [ping] int = g x
my g(x): int = case x:
    true -> pong::get()
    false -> f true
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-forward.yu --poly
```
exit=124; elapsed=40.058389261997945 seconds
```text
Command '['/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang', '--std-root', '/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib', '--no-prelude', 'dump', '/tmp/audit2-annotations/scc-forward.yu', '--poly']' timed out after 40 seconds
```

## scc-short-forward
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = g()
my g(): int = { pong::get(); f() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-short-forward.yu
```
exit=124; elapsed=5.014661935998447 seconds
```text
Command '['/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang', '--std-root', '/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib', '--no-prelude', 'check', '/tmp/audit2-annotations/scc-short-forward.yu']' timed out after 5 seconds
```

## scc-short-forward
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = g()
my g(): int = { pong::get(); f() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-short-forward.yu --poly
```
exit=124; elapsed=5.016691478002031 seconds
```text
Command '['/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang', '--std-root', '/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib', '--no-prelude', 'dump', '/tmp/audit2-annotations/scc-short-forward.yu', '--poly']' timed out after 5 seconds
```

## scc-short-reverse
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my g(): int = { pong::get(); f() }
my f(): [ping] int = g()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-short-reverse.yu
```
exit=124; elapsed=5.01781879400005 seconds
```text
Command '['/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang', '--std-root', '/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib', '--no-prelude', 'check', '/tmp/audit2-annotations/scc-short-reverse.yu']' timed out after 5 seconds
```

## scc-short-reverse
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my g(): int = { pong::get(); f() }
my f(): [ping] int = g()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-short-reverse.yu --poly
```
exit=124; elapsed=5.017775510998035 seconds
```text
Command '['/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang', '--std-root', '/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib', '--no-prelude', 'dump', '/tmp/audit2-annotations/scc-short-reverse.yu', '--poly']' timed out after 5 seconds
```

## scc-pure
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f() = g()
my g() = f()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-pure.yu
```
exit=0; elapsed=0.015726559999166057 seconds
```text

```

## scc-pure
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f() = g()
my g() = f()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-pure.yu --poly
```
exit=0; elapsed=0.014250281998101855 seconds
```text
roots d0:ping d2:pong d4:f d5:g
d0:ping mod {
}
d2:pong mod {
}
my d4:f: () -> never = e3:(fn p0:() -> e2:(e0:r0:g->d5:g e1:()))
my d5:g: () -> never = e7:(fn p1:() -> e6:(e4:r1:f->d4:f e5:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
}

```

## nested-later-known
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my outer(g) = { my inner(): [ping] int = g(); g as (() -> [pong] int); inner() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/nested-later-known.yu
```
exit=1; elapsed=0.010187318999669515 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## nested-later-known
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my outer(g) = { my inner(): [ping] int = g(); g as (() -> [pong] int); inner() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/nested-later-known.yu --poly
```
exit=0; elapsed=0.012235853999300161 seconds
```text
roots d0:ping d2:pong d4:outer
d0:ping mod {
}
d2:pong mod {
}
my d4:outer: (() -> ['a & [pong; 'b]] int) -> ['a, 'b] int = e10:(fn p0:d5:g -> e9:block { let my p1:d6:inner = e3:(fn p2:() -> e2:(e0:r0:g->d5:g e1:())); e8:block { e4:r1:g->d5:g; e7:(e5:r2:inner->d6:inner e6:()) } })
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  d5:g arg
  my d6:inner: () -> ['a, 'b, 'c, 'd, 'e] 'f | 'g | int = e3:(fn p2:() -> e2:(e0:r0:g->d5:g e1:()))
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## nested-known-before
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my outer(g: () -> [pong] int) = { my inner(): [ping] int = g(); inner() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/nested-known-before.yu
```
exit=1; elapsed=0.00851681499989354 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## nested-known-before
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my outer(g: () -> [pong] int) = { my inner(): [ping] int = g(); inner() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/nested-known-before.yu --poly
```
exit=0; elapsed=0.01000002900036634 seconds
```text
roots d0:ping d2:pong d4:outer
d0:ping mod {
}
d2:pong mod {
}
my d4:outer: (() -> [pong] int) -> int = e8:(fn p0:d5:g -> e7:block { let my p1:d6:inner = e3:(fn p2:() -> e2:(e0:r0:g->d5:g e1:())); e6:(e4:r1:inner->d6:inner e5:()) })
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  d5:g arg
  my d6:inner: () -> ['a, 'b, 'c, 'd, 'e, 'f] 'g | 'h | int = e3:(fn p2:() -> e2:(e0:r0:g->d5:g e1:()))
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## late-use-runtime
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g): [ping] int = g()
my handle(action: [pong] int) = catch action:
    pong::get(), k -> k 7
    v -> v
handle(apply (\() -> pong::get()))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/late-use-runtime.yu
```
exit=0; elapsed=0.01188197099691024 seconds
```text

```

## late-use-runtime
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g): [ping] int = g()
my handle(action: [pong] int) = catch action:
    pong::get(), k -> k 7
    v -> v
handle(apply (\() -> pong::get()))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/late-use-runtime.yu --poly
```
exit=0; elapsed=0.00974672599841142 seconds
```text
roots d0:ping d2:pong d4:apply d5:handle
d0:ping mod {
}
d2:pong mod {
}
my d4:apply: (() -> ['a] int) -> ['a] int = e3:(fn p0:d6:g -> e2:(e0:r0:g->d6:g e1:()))
my d5:handle: int ['a & [pong; 'a]] -> ['a] int = e10:(fn p1:d7:action -> e9:catch e4:r1:action->d7:action { pong::get p2:_, p3:d8:k -> e7:(e5:r2:k->d8:k e6:7); p4:d9:v -> e8:r3:v->d9:v })
root exprs e18:(e11:r4:handle->d5:handle e17:(e12:r5:apply->d4:apply e16:(fn p5:() -> e15:(e13:r6:"pong::get"->d3:"pong.get" e14:()))))
runtime roots e18:(e11:r4:handle->d5:handle e17:(e12:r5:apply->d4:apply e16:(fn p5:() -> e15:(e13:r6:"pong::get"->d3:"pong.get" e14:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  d6:g arg
  d7:action arg
  d8:k arg
  d9:v arg
}

```

## late-use-runtime
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g): [ping] int = g()
my handle(action: [pong] int) = catch action:
    pong::get(), k -> k 7
    v -> v
handle(apply (\() -> pong::get()))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-annotations/late-use-runtime.yu
```
exit=0; elapsed=0.004509831000177655 seconds
```text
run roots [7]

```

## scc-reverse
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my g(x): int = case x:
    true -> pong::get()
    false -> f true
my f(x): [ping] int = g x
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-reverse.yu
```
exit=124; elapsed=40.05139936100022 seconds
```text
Command '['/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang', '--std-root', '/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib', '--no-prelude', 'check', '/tmp/audit2-annotations/scc-reverse.yu']' timed out after 40 seconds
```

## scc-fetch-forward
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = { g; pong::get() }
my g() = f()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-fetch-forward.yu
```
exit=1; elapsed=0.008791280000878032 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## scc-fetch-forward
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = { g; pong::get() }
my g() = f()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-fetch-forward.yu --poly
```
exit=0; elapsed=0.007854625000618398 seconds
```text
roots d0:ping d2:pong d4:f d5:g
d0:ping mod {
}
d2:pong mod {
}
my d4:f: () -> [pong] int = e5:(fn p0:() -> e4:block { e0:r0:g->d5:g; e3:(e1:r1:"pong::get"->d3:"pong.get" e2:()) })
my d5:g: () -> [pong] int = e9:(fn p1:() -> e8:(e6:r2:f->d4:f e7:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## scc-fetch-reverse
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my g() = f()
my f(): [ping] int = { g; pong::get() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-fetch-reverse.yu
```
exit=1; elapsed=0.007392634001007536 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## scc-fetch-reverse
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my g() = f()
my f(): [ping] int = { g; pong::get() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-fetch-reverse.yu --poly
```
exit=0; elapsed=0.008360486001038225 seconds
```text
roots d0:ping d2:pong d4:g d5:f
d0:ping mod {
}
d2:pong mod {
}
my d4:g: () -> [pong] int = e3:(fn p0:() -> e2:(e0:r0:f->d5:f e1:()))
my d5:f: () -> [pong] int = e9:(fn p1:() -> e8:block { e4:r1:g->d4:g; e7:(e5:r2:"pong::get"->d3:"pong.get" e6:()) })
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## scc-fetch-allowed
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = { g; ping::get() }
my g() = f()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-fetch-allowed.yu
```
exit=0; elapsed=0.007917479997558985 seconds
```text

```

## scc-fetch-allowed
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = { g; ping::get() }
my g() = f()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-fetch-allowed.yu --poly
```
exit=0; elapsed=0.008010554000065895 seconds
```text
roots d0:ping d2:pong d4:f d5:g
d0:ping mod {
}
d2:pong mod {
}
my d4:f: () -> [ping] int = e5:(fn p0:() -> e4:block { e0:r0:g->d5:g; e3:(e1:r1:"ping::get"->d1:"ping.get" e2:()) })
my d5:g: () -> [ping] int = e9:(fn p1:() -> e8:(e6:r2:f->d4:f e7:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
}

```

## scc-oneway
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = g()
my g() = pong::get()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-oneway.yu
```
exit=1; elapsed=0.005457858998852316 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## scc-oneway
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = g()
my g() = pong::get()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-oneway.yu --poly
```
exit=0; elapsed=0.005529327001568163 seconds
```text
roots d0:ping d2:pong d4:f d5:g
d0:ping mod {
}
d2:pong mod {
}
my d4:f: () -> [pong] int = e3:(fn p0:() -> e2:(e0:r0:g->d5:g e1:()))
my d5:g: () -> [pong] int = e7:(fn p1:() -> e6:(e4:r1:"pong::get"->d3:"pong.get" e5:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## scc-peer-forward
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = g()
my g() = { f; pong::get() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-peer-forward.yu
```
exit=1; elapsed=0.008599430999311153 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## scc-peer-forward
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = g()
my g() = { f; pong::get() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-peer-forward.yu --poly
```
exit=0; elapsed=0.008763016998273088 seconds
```text
roots d0:ping d2:pong d4:f d5:g
d0:ping mod {
}
d2:pong mod {
}
my d4:f: () -> [pong] int = e3:(fn p0:() -> e2:(e0:r0:g->d5:g e1:()))
my d5:g: () -> [pong] int = e9:(fn p1:() -> e8:block { e4:r1:f->d4:f; e7:(e5:r2:"pong::get"->d3:"pong.get" e6:()) })
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## scc-peer-reverse
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my g() = { f; pong::get() }
my f(): [ping] int = g()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-peer-reverse.yu
```
exit=1; elapsed=0.008232784999563592 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## scc-peer-reverse
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my g() = { f; pong::get() }
my f(): [ping] int = g()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-peer-reverse.yu --poly
```
exit=0; elapsed=0.009337232000689255 seconds
```text
roots d0:ping d2:pong d4:g d5:f
d0:ping mod {
}
d2:pong mod {
}
my d4:g: () -> [pong] int = e5:(fn p0:() -> e4:block { e0:r0:f->d5:f; e3:(e1:r1:"pong::get"->d3:"pong.get" e2:()) })
my d5:f: () -> [pong] int = e9:(fn p1:() -> e8:(e6:r2:g->d4:g e7:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## scc-peer-allowed-forward
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = g()
my g() = { f; ping::get() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-peer-allowed-forward.yu
```
exit=0; elapsed=0.007641847998456797 seconds
```text

```

## scc-peer-allowed-forward
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = g()
my g() = { f; ping::get() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-peer-allowed-forward.yu --poly
```
exit=0; elapsed=0.007417249998979969 seconds
```text
roots d0:ping d2:pong d4:f d5:g
d0:ping mod {
}
d2:pong mod {
}
my d4:f: () -> [ping] int = e3:(fn p0:() -> e2:(e0:r0:g->d5:g e1:()))
my d5:g: () -> [ping] int = e9:(fn p1:() -> e8:block { e4:r1:f->d4:f; e7:(e5:r2:"ping::get"->d1:"ping.get" e6:()) })
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
}

```

## scc-peer-allowed-reverse
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my g() = { f; ping::get() }
my f(): [ping] int = g()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-peer-allowed-reverse.yu
```
exit=0; elapsed=0.007110153997928137 seconds
```text

```

## scc-peer-allowed-reverse
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my g() = { f; ping::get() }
my f(): [ping] int = g()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-peer-allowed-reverse.yu --poly
```
exit=0; elapsed=0.0078112940027494915 seconds
```text
roots d0:ping d2:pong d4:g d5:f
d0:ping mod {
}
d2:pong mod {
}
my d4:g: () -> [ping] int = e5:(fn p0:() -> e4:block { e0:r0:f->d5:f; e3:(e1:r1:"ping::get"->d1:"ping.get" e2:()) })
my d5:f: () -> [ping] int = e9:(fn p1:() -> e8:(e6:r2:g->d4:g e7:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
}

```

## scc-reverse
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my g(x): int = case x:
    true -> pong::get()
    false -> f true
my f(x): [ping] int = g x
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-reverse.yu --poly
```
exit=124; elapsed=40.081935900001554 seconds
```text
Command '['/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang', '--std-root', '/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib', '--no-prelude', 'dump', '/tmp/audit2-annotations/scc-reverse.yu', '--poly']' timed out after 40 seconds
```

## scc-allowed-forward
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(x): [ping] int = g x
my g(x): int = case x:
    true -> ping::get()
    false -> f true
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-allowed-forward.yu
```
exit=124; elapsed=40.02988759100117 seconds
```text
Command '['/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang', '--std-root', '/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib', '--no-prelude', 'check', '/tmp/audit2-annotations/scc-allowed-forward.yu']' timed out after 40 seconds
```

## scc-allowed-forward
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(x): [ping] int = g x
my g(x): int = case x:
    true -> ping::get()
    false -> f true
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-allowed-forward.yu --poly
```
exit=124; elapsed=40.06503626900303 seconds
```text
Command '['/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang', '--std-root', '/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib', '--no-prelude', 'dump', '/tmp/audit2-annotations/scc-allowed-forward.yu', '--poly']' timed out after 40 seconds
```

## scc-allowed-reverse
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my g(x): int = case x:
    true -> ping::get()
    false -> f true
my f(x): [ping] int = g x
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/scc-allowed-reverse.yu
```
exit=124; elapsed=40.07196776899946 seconds
```text
Command '['/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang', '--std-root', '/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib', '--no-prelude', 'check', '/tmp/audit2-annotations/scc-allowed-reverse.yu']' timed out after 40 seconds
```

## scc-allowed-reverse
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my g(x): int = case x:
    true -> ping::get()
    false -> f true
my f(x): [ping] int = g x
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/scc-allowed-reverse.yu --poly
```
exit=124; elapsed=40.04714540100031 seconds
```text
Command '['/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang', '--std-root', '/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib', '--no-prelude', 'dump', '/tmp/audit2-annotations/scc-allowed-reverse.yu', '--poly']' timed out after 40 seconds
```

## late-unknown
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g): [ping] int = g()
my later() = apply (\() -> pong::get())
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/late-unknown.yu
```
exit=0; elapsed=0.005589137999777449 seconds
```text

```

## late-unknown
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g): [ping] int = g()
my later() = apply (\() -> pong::get())
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/late-unknown.yu --poly
```
exit=0; elapsed=0.006406528002116829 seconds
```text
roots d0:ping d2:pong d4:apply d5:later
d0:ping mod {
}
d2:pong mod {
}
my d4:apply: (() -> ['a] int) -> ['a] int = e3:(fn p0:d6:g -> e2:(e0:r0:g->d6:g e1:()))
my d5:later: () -> [pong] int = e10:(fn p1:() -> e9:(e4:r1:apply->d4:apply e8:(fn p2:() -> e7:(e5:r2:"pong::get"->d3:"pong.get" e6:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  d6:g arg
}

```

## known-callback
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g: () -> [pong] int): [ping] int = g()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/known-callback.yu
```
exit=1; elapsed=0.005823722000059206 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## known-callback
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g: () -> [pong] int): [ping] int = g()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/known-callback.yu --poly
```
exit=0; elapsed=0.004174857996986248 seconds
```text
roots d0:ping d2:pong d4:apply
d0:ping mod {
}
d2:pong mod {
}
my d4:apply: (() -> [pong] int) -> int = e3:(fn p0:d5:g -> e2:(e0:r0:g->d5:g e1:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  d5:g arg
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## direct-body
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = pong::get()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/direct-body.yu
```
exit=1; elapsed=0.00301465699885739 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## direct-body
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my f(): [ping] int = pong::get()
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/direct-body.yu --poly
```
exit=0; elapsed=0.003209203001460992 seconds
```text
roots d0:ping d2:pong d4:f
d0:ping mod {
}
d2:pong mod {
}
my d4:f: () -> [pong] int = e3:(fn p0:() -> e2:(e0:r0:"pong::get"->d3:"pong.get" e1:()))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## late-unknown-glob
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g: () -> [_] int): [ping] int = g()
my later() = apply (\() -> pong::get())
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/late-unknown-glob.yu
```
exit=0; elapsed=0.004403932998684468 seconds
```text

```

## late-unknown-glob
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my apply(g: () -> [_] int): [ping] int = g()
my later() = apply (\() -> pong::get())
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/late-unknown-glob.yu --poly
```
exit=0; elapsed=0.007674307998968288 seconds
```text
roots d0:ping d2:pong d4:apply d5:later
d0:ping mod {
}
d2:pong mod {
}
my d4:apply: (() -> ['a] int) -> ['a] int = e3:(fn p0:d6:g -> e2:(e0:r0:g->d6:g e1:()))
my d5:later: () -> [pong] int = e10:(fn p1:() -> e9:(e4:r1:apply->d4:apply e8:(fn p2:() -> e7:(e5:r2:"pong::get"->d3:"pong.get" e6:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  d6:g arg
}

```

## nested-late
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my outer(g) = { my inner(): [ping] int = g(); inner() }
my later() = outer (\() -> pong::get())
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/nested-late.yu
```
exit=0; elapsed=0.009775022001122124 seconds
```text

```

## nested-late
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my outer(g) = { my inner(): [ping] int = g(); inner() }
my later() = outer (\() -> pong::get())
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/nested-late.yu --poly
```
exit=0; elapsed=0.008489580999594182 seconds
```text
roots d0:ping d2:pong d4:outer d5:later
d0:ping mod {
}
d2:pong mod {
}
my d4:outer: (() -> ['a] int) -> ['a] int = e8:(fn p0:d6:g -> e7:block { let my p1:d7:inner = e3:(fn p2:() -> e2:(e0:r0:g->d6:g e1:())); e6:(e4:r1:inner->d7:inner e5:()) })
my d5:later: () -> [pong] int = e15:(fn p3:() -> e14:(e9:r2:outer->d4:outer e13:(fn p4:() -> e12:(e10:r3:"pong::get"->d3:"pong.get" e11:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  d6:g arg
  my d7:inner: () -> ['a, 'b, 'c, 'd, 'e] 'f | 'g | int = e3:(fn p2:() -> e2:(e0:r0:g->d6:g e1:()))
}

```

## nested-known
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my outer() = { my inner(): [ping] int = pong::get(); inner() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-annotations/nested-known.yu
```
exit=1; elapsed=0.0037650099984603003 seconds
```text
diagnostics:
  error [yulang.analysis]: effect filter mismatch: pong is not allowed by [ping]

```

## nested-known
```yulang
act ping:
    our get: () -> int
act pong:
    our get: () -> int
my outer() = { my inner(): [ping] int = pong::get(); inner() }
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-annotations/nested-known.yu --poly
```
exit=0; elapsed=0.006772725999326212 seconds
```text
roots d0:ping d2:pong d4:outer
d0:ping mod {
}
d2:pong mod {
}
my d4:outer: () -> [pong] int = e8:(fn p0:() -> e7:block { let my p1:d5:inner = e3:(fn p2:() -> e2:(e0:r0:"pong::get"->d3:"pong.get" e1:())); e6:(e4:r1:inner->d5:inner e5:()) })
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:"pong.get": () -> [pong] int = <missing>
  my d5:inner: () -> [pong] int = e3:(fn p2:() -> e2:(e0:r0:"pong::get"->d3:"pong.get" e1:()))
}
error: effect filter mismatch: pong is not allowed by [ping]

```

## Existing unit tests
```text
$ cargo test -p infer --lib neg_stack_filter_is_checked_but_not_stored_as_right_weight -- --nocapture --test-threads=1
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.11s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 1 test
test constraints::tests::case_02::neg_stack_filter_is_checked_but_not_stored_as_right_weight ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1392 filtered out; finished in 0.00s

exit=0
$ cargo test -p infer --lib finalize_drops_filter_only_stack_weights_on_negative_vars -- --nocapture --test-threads=1
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.03s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 1 test
test compact::tests::case_02::finalize_drops_filter_only_stack_weights_on_negative_vars ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1392 filtered out; finished in 0.00s

exit=0

```
## Generalized scheme raw
```text
raw roots [d0:ping, d2:pong, d4:apply, d5:later]
defs {
  d0:ping = Mod { vis: our, children: [] }
  d1:"ping.get" = Let { vis: our, body: <missing>, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p3
        types:
          p0 = Con(ping, [])
          p1 = Row([p0])
          p2 = Con(int, [])
          p3 = Fun { arg: n0, arg_eff: n2, ret_eff: p1, ret: p2 }
          n0 = Con(unit, [])
          n1 = Top
          n2 = Row([], tail: n1)
      }
  d2:pong = Mod { vis: our, children: [] }
  d3:"pong.get" = Let { vis: our, body: <missing>, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p6
        types:
          p2 = Con(int, [])
          p4 = Con(pong, [])
          p5 = Row([p4])
          p6 = Fun { arg: n0, arg_eff: n2, ret_eff: p5, ret: p2 }
          n0 = Con(unit, [])
          n1 = Top
          n2 = Row([], tail: n1)
      }
  d4:apply = Let { vis: my, body: e3, children: [] }
    scheme:
      scheme {
        quantifiers: ['16]
        stack_quantifiers: []
        predicate: p10
        types:
          p2 = Con(int, [])
          p7 = Con(unit, [])
          p8 = Bot
          p9 = Var('16)
          p10 = Fun { arg: n5, arg_eff: n6, ret_eff: p9, ret: p2 }
          n3 = Var('16)
          n4 = Con(int, [])
          n5 = Fun { arg: p7, arg_eff: p8, ret_eff: n3, ret: n4 }
          n6 = Bot
      }
  d5:later = Let { vis: my, body: e10, children: [] }
    scheme:
      scheme {
        quantifiers: []
        stack_quantifiers: []
        predicate: p11
        types:
          p2 = Con(int, [])
          p4 = Con(pong, [])
          p5 = Row([p4])
          p11 = Fun { arg: n0, arg_eff: n6, ret_eff: p5, ret: p2 }
          n0 = Con(unit, [])
          n6 = Bot
      }
  d6:g = Arg
}
exprs {
  e0 = Var(r0:g->d6:g)
  e1 = Lit(Unit)
  e2 = App(e0, e1)
  e3 = Lambda(p0, e2)
  e4 = Var(r1:apply->d4:apply)
  e5 = Var(r2:"pong::get"->d3:"pong.get")
  e6 = Lit(Unit)
  e7 = App(e5, e6)
  e8 = Lambda(p2, e7)
  e9 = App(e4, e8)
  e10 = Lambda(p1, e9)
}
pats {
  p0 = Var(d6:g)
  p1 = Lit(Unit)
  p2 = Lit(Unit)
}

```
