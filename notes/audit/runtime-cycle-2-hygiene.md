# Hygiene runtime raw log

38 calls, 10 inputs; exit counts {0: 33, 1: 5}; total command seconds 0.3109566279927094.

## nested-same-family
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
seven(one(ping::get()))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-hygiene/nested-same-family.yu
```
exit=0; seconds=0.01223301500067464
```text

```

## nested-same-family
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
seven(one(ping::get()))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-hygiene/nested-same-family.yu --poly
```
exit=0; seconds=0.014143958000204293
```text
roots d0:ping d2:one d3:seven
d0:ping mod {
}
d2:one: 'a ['b & [ping; 'b]] -> ['b] 'a = e6:(fn p0:d4:action -> e5:catch e0:r0:action->d4:action { ping::get p1:_, p2:d5:k -> e3:(e1:r1:k->d5:k e2:1); p3:d6:value -> e4:r2:value->d6:value })
d3:seven: 'a ['b & [ping; 'b]] -> ['b] 'a = e13:(fn p4:d7:action -> e12:catch e7:r3:action->d7:action { ping::get p5:_, p6:d8:k -> e10:(e8:r4:k->d8:k e9:7); p7:d9:value -> e11:r5:value->d9:value })
root exprs e20:(e14:r6:seven->d3:seven e19:(e15:r7:one->d2:one e18:(e16:r8:"ping::get"->d1:"ping.get" e17:())))
runtime roots e20:(e14:r6:seven->d3:seven e19:(e15:r7:one->d2:one e18:(e16:r8:"ping::get"->d1:"ping.get" e17:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:action arg
  d5:k arg
  d6:value arg
  d7:action arg
  d8:k arg
  d9:value arg
}

```

## nested-same-family
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
seven(one(ping::get()))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-hygiene/nested-same-family.yu
```
exit=0; seconds=0.004294557998946402
```text
run roots [7]

```

## shallow-two-requests
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our sequence() = { my a = ping::get(); my b = ping::get(); (a,b) }
seven(one(sequence()))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-hygiene/shallow-two-requests.yu
```
exit=0; seconds=0.016622060000372585
```text

```

## shallow-two-requests
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our sequence() = { my a = ping::get(); my b = ping::get(); (a,b) }
seven(one(sequence()))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-hygiene/shallow-two-requests.yu --poly
```
exit=0; seconds=0.014992696000263095
```text
roots d0:ping d2:one d3:seven d4:sequence
d0:ping mod {
}
d2:one: 'a ['b & [ping; 'b]] -> ['b] 'a = e6:(fn p0:d5:action -> e5:catch e0:r0:action->d5:action { ping::get p1:_, p2:d6:k -> e3:(e1:r1:k->d6:k e2:1); p3:d7:value -> e4:r2:value->d7:value })
d3:seven: 'a ['b & [ping; 'b]] -> ['b] 'a = e13:(fn p4:d8:action -> e12:catch e7:r3:action->d8:action { ping::get p5:_, p6:d9:k -> e10:(e8:r4:k->d9:k e9:7); p7:d10:value -> e11:r5:value->d10:value })
d4:sequence: () -> [ping] (int, int) = e25:(fn p8:() -> e24:block { let my p9:d11:a = e16:(e14:r6:"ping::get"->d1:"ping.get" e15:()); e23:block { let my p10:d12:b = e19:(e17:r7:"ping::get"->d1:"ping.get" e18:()); e22:(e20:r8:a->d11:a, e21:r9:b->d12:b) } })
root exprs e32:(e26:r10:seven->d3:seven e31:(e27:r11:one->d2:one e30:(e28:r12:sequence->d4:sequence e29:())))
runtime roots e32:(e26:r10:seven->d3:seven e31:(e27:r11:one->d2:one e30:(e28:r12:sequence->d4:sequence e29:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:action arg
  d6:k arg
  d7:value arg
  d8:action arg
  d9:k arg
  d10:value arg
  my d11:a: 'a | int = e16:(e14:r6:"ping::get"->d1:"ping.get" e15:())
  my d12:b: 'a | int = e19:(e17:r7:"ping::get"->d1:"ping.get" e18:())
}

```

## shallow-two-requests
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our sequence() = { my a = ping::get(); my b = ping::get(); (a,b) }
seven(one(sequence()))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-hygiene/shallow-two-requests.yu
```
exit=1; seconds=0.0056938009984150995
```text
runtime error [yulang.unhandled-effect]: unhandled effect request ping::get
    --> line 9, column 47
    9 | our sequence() = { my a = ping::get(); my b = ping::get(); (a,b) }
      |                                               ^^^^^^^^^
  hint: handle this computation with a matching effect handler before running it
  note: application occurs here
    --> line 9, column 47
    9 | our sequence() = { my a = ping::get(); my b = ping::get(); (a,b) }
      |                                               ^^^^^^^^^^^

```

## double-callback-hidden
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our inner(f) = catch f():
    ping::get(), k -> k 2
    value -> value
our middle(f) = catch f():
    ping::get(), k -> k 3
    value -> value
seven(middle(\() -> inner(\() -> ping::get())))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-hygiene/double-callback-hidden.yu
```
exit=0; seconds=0.02063028399788891
```text

```

## double-callback-hidden
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our inner(f) = catch f():
    ping::get(), k -> k 2
    value -> value
our middle(f) = catch f():
    ping::get(), k -> k 3
    value -> value
seven(middle(\() -> inner(\() -> ping::get())))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-hygiene/double-callback-hidden.yu --poly
```
exit=0; seconds=0.022840731999167474
```text
roots d0:ping d2:one d3:seven d4:inner d5:middle
d0:ping mod {
}
d2:one: 'a ['b & [ping; 'b]] -> ['b] 'a = e6:(fn p0:d6:action -> e5:catch e0:r0:action->d6:action { ping::get p1:_, p2:d7:k -> e3:(e1:r1:k->d7:k e2:1); p3:d8:value -> e4:r2:value->d8:value })
d3:seven: 'a ['b & [ping; 'b]] -> ['b] 'a = e13:(fn p4:d9:action -> e12:catch e7:r3:action->d9:action { ping::get p5:_, p6:d10:k -> e10:(e8:r4:k->d10:k e9:7); p7:d11:value -> e11:r5:value->d11:value })
d4:inner: (() -> ['a] 'b) -> ['a] 'b = e22:(fn p8:d12:f -> e21:catch e16:(e14:r6:f->d12:f e15:()) { ping::get p9:_, p10:d13:k -> e19:(e17:r7:k->d13:k e18:2); p11:d14:value -> e20:r8:value->d14:value })
d5:middle: (() -> ['a] 'b) -> ['a] 'b = e31:(fn p12:d15:f -> e30:catch e25:(e23:r9:f->d15:f e24:()) { ping::get p13:_, p14:d16:k -> e28:(e26:r10:k->d16:k e27:3); p15:d17:value -> e29:r11:value->d17:value })
root exprs e42:(e32:r12:seven->d3:seven e41:(e33:r13:middle->d5:middle e40:(fn p16:() -> e39:(e34:r14:inner->d4:inner e38:(fn p17:() -> e37:(e35:r15:"ping::get"->d1:"ping.get" e36:()))))))
runtime roots e42:(e32:r12:seven->d3:seven e41:(e33:r13:middle->d5:middle e40:(fn p16:() -> e39:(e34:r14:inner->d4:inner e38:(fn p17:() -> e37:(e35:r15:"ping::get"->d1:"ping.get" e36:()))))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d6:action arg
  d7:k arg
  d8:value arg
  d9:action arg
  d10:k arg
  d11:value arg
  d12:f arg
  d13:k arg
  d14:value arg
  d15:f arg
  d16:k arg
  d17:value arg
}

```

## double-callback-hidden
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our inner(f) = catch f():
    ping::get(), k -> k 2
    value -> value
our middle(f) = catch f():
    ping::get(), k -> k 3
    value -> value
seven(middle(\() -> inner(\() -> ping::get())))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-hygiene/double-callback-hidden.yu
```
exit=0; seconds=0.0054936529995757155
```text
run roots [3]

```

## double-callback-explicit
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our inner(f: () -> [ping] int) = catch f():
    ping::get(), k -> k 2
    value -> value
our middle(f: () -> [ping] int) = catch f():
    ping::get(), k -> k 3
    value -> value
seven(middle(\() -> inner(\() -> ping::get())))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-hygiene/double-callback-explicit.yu
```
exit=0; seconds=0.0188399560029211
```text

```

## double-callback-explicit
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our inner(f: () -> [ping] int) = catch f():
    ping::get(), k -> k 2
    value -> value
our middle(f: () -> [ping] int) = catch f():
    ping::get(), k -> k 3
    value -> value
seven(middle(\() -> inner(\() -> ping::get())))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-hygiene/double-callback-explicit.yu --poly
```
exit=0; seconds=0.023094037002010737
```text
roots d0:ping d2:one d3:seven d4:inner d5:middle
d0:ping mod {
}
d2:one: 'a ['b & [ping; 'b]] -> ['b] 'a = e6:(fn p0:d6:action -> e5:catch e0:r0:action->d6:action { ping::get p1:_, p2:d7:k -> e3:(e1:r1:k->d7:k e2:1); p3:d8:value -> e4:r2:value->d8:value })
d3:seven: 'a ['b & [ping; 'b]] -> ['b] 'a = e13:(fn p4:d9:action -> e12:catch e7:r3:action->d9:action { ping::get p5:_, p6:d10:k -> e10:(e8:r4:k->d10:k e9:7); p7:d11:value -> e11:r5:value->d11:value })
d4:inner: (() -> [ping] int) -> int = e22:(fn p8:d12:f -> e21:catch e16:(e14:r6:f->d12:f e15:()) { ping::get p9:_, p10:d13:k -> e19:(e17:r7:k->d13:k e18:2); p11:d14:value -> e20:r8:value->d14:value })
d5:middle: (() -> [ping] int) -> int = e31:(fn p12:d15:f -> e30:catch e25:(e23:r9:f->d15:f e24:()) { ping::get p13:_, p14:d16:k -> e28:(e26:r10:k->d16:k e27:3); p15:d17:value -> e29:r11:value->d17:value })
root exprs e42:(e32:r12:seven->d3:seven e41:(e33:r13:middle->d5:middle e40:(fn p16:() -> e39:(e34:r14:inner->d4:inner e38:(fn p17:() -> e37:(e35:r15:"ping::get"->d1:"ping.get" e36:()))))))
runtime roots e42:(e32:r12:seven->d3:seven e41:(e33:r13:middle->d5:middle e40:(fn p16:() -> e39:(e34:r14:inner->d4:inner e38:(fn p17:() -> e37:(e35:r15:"ping::get"->d1:"ping.get" e36:()))))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d6:action arg
  d7:k arg
  d8:value arg
  d9:action arg
  d10:k arg
  d11:value arg
  d12:f arg
  d13:k arg
  d14:value arg
  d15:f arg
  d16:k arg
  d17:value arg
}

```

## double-callback-explicit
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our inner(f: () -> [ping] int) = catch f():
    ping::get(), k -> k 2
    value -> value
our middle(f: () -> [ping] int) = catch f():
    ping::get(), k -> k 3
    value -> value
seven(middle(\() -> inner(\() -> ping::get())))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-hygiene/double-callback-explicit.yu
```
exit=0; seconds=0.005289056000037817
```text
run roots [3]

```

## direct-nested
```yulang
act ping:
    our get: () -> int
catch (catch ping::get():
    ping::get(), k -> k 1
    value -> value):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-hygiene/direct-nested.yu
```
exit=1; seconds=0.0103795139984868
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 19
    5 |     value -> value):
      |                   ^

```

## direct-nested
```yulang
act ping:
    our get: () -> int
catch (catch ping::get():
    ping::get(), k -> k 1
    value -> value):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-hygiene/direct-nested.yu --poly
```
exit=0; seconds=0.009796163998544216
```text
roots d0:ping
d0:ping mod {
}
root exprs e12:catch e7:catch e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()) { ping::get p0:_, p1:d3:k -> e5:(e3:r1:k->d3:k e4:1); p2:d4:value -> e6:r2:value->d4:value } { ping::get p3:_, p4:d5:k -> e10:(e8:r3:k->d5:k e9:7); p5:d6:value -> e11:r4:value->d6:value }
runtime roots e12:catch e7:catch e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()) { ping::get p0:_, p1:d3:k -> e5:(e3:r1:k->d3:k e4:1); p2:d4:value -> e6:r2:value->d4:value } { ping::get p3:_, p4:d5:k -> e10:(e8:r3:k->d5:k e9:7); p5:d6:value -> e11:r4:value->d6:value }
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:k arg
  d4:value arg
  d5:k arg
  d6:value arg
}

```

## direct-nested
```yulang
act ping:
    our get: () -> int
catch (catch ping::get():
    ping::get(), k -> k 1
    value -> value):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-hygiene/direct-nested.yu
```
exit=1; seconds=0.0026910729975497816
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 19
    5 |     value -> value):
      |                   ^

```

## direct-shallow
```yulang
act ping:
    our get: () -> int
catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
    ping::get(), k -> k 1
    value -> value):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-hygiene/direct-shallow.yu
```
exit=1; seconds=0.002981831999932183
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 19
    3 | catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
      |                   ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 31
    3 | catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
      |                               ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 36
    3 | catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
      |                                    ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 48
    3 | catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
      |                                                ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 54
    3 | catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
      |                                                      ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 11
    5 |     value -> value):
      |           ^^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 19
    5 |     value -> value):
      |                   ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 7, column 11
    7 |     value -> value
      |           ^^
  error [yulang.syntax]: syntax error: unexpected end of input
    --> line 7, column 19
    7 |     value -> value
      |                   ^
  error [yulang.missing-catch-scrutinee]: catch expression is missing the computation to handle
    --> line 3, column 8
    3 | catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
      |        ^^^^^
    hint: write `catch <expr>:` before the handler arms

```

## direct-shallow
```yulang
act ping:
    our get: () -> int
catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
    ping::get(), k -> k 1
    value -> value):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-hygiene/direct-shallow.yu --poly
```
exit=0; seconds=0.003932573999918532
```text
roots d0:ping
d0:ping mod {
}
detached {
  d1:"ping.get": () -> [ping] int = <missing>
}
error: catch expression is missing the computation to handle

```

## direct-shallow
```yulang
act ping:
    our get: () -> int
catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
    ping::get(), k -> k 1
    value -> value):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-hygiene/direct-shallow.yu
```
exit=1; seconds=0.0027338580002833623
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 19
    3 | catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
      |                   ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 31
    3 | catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
      |                               ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 36
    3 | catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
      |                                    ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 48
    3 | catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
      |                                                ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 3, column 54
    3 | catch (catch {my a=ping::get();my b=ping::get();(a,b)}:
      |                                                      ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 11
    5 |     value -> value):
      |           ^^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 19
    5 |     value -> value):
      |                   ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 7, column 11
    7 |     value -> value
      |           ^^
  error [yulang.syntax]: syntax error: unexpected end of input
    --> line 7, column 19
    7 |     value -> value
      |                   ^

```

## direct-callback-hidden
```yulang
act ping:
    our get: () -> int
our inner(f) = catch f():
    ping::get(), k -> k 2
    value -> value
catch inner(\() -> ping::get()):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-hygiene/direct-callback-hidden.yu
```
exit=0; seconds=0.009299699999246513
```text

```

## direct-callback-hidden
```yulang
act ping:
    our get: () -> int
our inner(f) = catch f():
    ping::get(), k -> k 2
    value -> value
catch inner(\() -> ping::get()):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-hygiene/direct-callback-hidden.yu --poly
```
exit=0; seconds=0.010121712999534793
```text
roots d0:ping d2:inner
d0:ping mod {
}
d2:inner: (() -> ['a] 'b) -> ['a] 'b = e8:(fn p0:d3:f -> e7:catch e2:(e0:r0:f->d3:f e1:()) { ping::get p1:_, p2:d4:k -> e5:(e3:r1:k->d4:k e4:2); p3:d5:value -> e6:r2:value->d5:value })
root exprs e19:catch e14:(e9:r3:inner->d2:inner e13:(fn p4:() -> e12:(e10:r4:"ping::get"->d1:"ping.get" e11:()))) { ping::get p5:_, p6:d7:k -> e17:(e15:r5:k->d7:k e16:7); p7:d8:value -> e18:r6:value->d8:value }
runtime roots e19:catch e14:(e9:r3:inner->d2:inner e13:(fn p4:() -> e12:(e10:r4:"ping::get"->d1:"ping.get" e11:()))) { ping::get p5:_, p6:d7:k -> e17:(e15:r5:k->d7:k e16:7); p7:d8:value -> e18:r6:value->d8:value }
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:f arg
  d4:k arg
  d5:value arg
  d7:k arg
  d8:value arg
}

```

## direct-callback-hidden
```yulang
act ping:
    our get: () -> int
our inner(f) = catch f():
    ping::get(), k -> k 2
    value -> value
catch inner(\() -> ping::get()):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-hygiene/direct-callback-hidden.yu
```
exit=0; seconds=0.004557274001854239
```text
run roots [2]

```

## direct-callback-explicit
```yulang
act ping:
    our get: () -> int
our inner(f: () -> [ping] int) = catch f():
    ping::get(), k -> k 2
    value -> value
catch inner(\() -> ping::get()):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-hygiene/direct-callback-explicit.yu
```
exit=0; seconds=0.009189981999952579
```text

```

## direct-callback-explicit
```yulang
act ping:
    our get: () -> int
our inner(f: () -> [ping] int) = catch f():
    ping::get(), k -> k 2
    value -> value
catch inner(\() -> ping::get()):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-hygiene/direct-callback-explicit.yu --poly
```
exit=0; seconds=0.01278385600016918
```text
roots d0:ping d2:inner
d0:ping mod {
}
d2:inner: (() -> [ping] int) -> int = e8:(fn p0:d3:f -> e7:catch e2:(e0:r0:f->d3:f e1:()) { ping::get p1:_, p2:d4:k -> e5:(e3:r1:k->d4:k e4:2); p3:d5:value -> e6:r2:value->d5:value })
root exprs e19:catch e14:(e9:r3:inner->d2:inner e13:(fn p4:() -> e12:(e10:r4:"ping::get"->d1:"ping.get" e11:()))) { ping::get p5:_, p6:d7:k -> e17:(e15:r5:k->d7:k e16:7); p7:d8:value -> e18:r6:value->d8:value }
runtime roots e19:catch e14:(e9:r3:inner->d2:inner e13:(fn p4:() -> e12:(e10:r4:"ping::get"->d1:"ping.get" e11:()))) { ping::get p5:_, p6:d7:k -> e17:(e15:r5:k->d7:k e16:7); p7:d8:value -> e18:r6:value->d8:value }
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:f arg
  d4:k arg
  d5:value arg
  d7:k arg
  d8:value arg
}

```

## direct-callback-explicit
```yulang
act ping:
    our get: () -> int
our inner(f: () -> [ping] int) = catch f():
    ping::get(), k -> k 2
    value -> value
catch inner(\() -> ping::get()):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-hygiene/direct-callback-explicit.yu
```
exit=0; seconds=0.004478935999941314
```text
run roots [2]

```

## direct-nested-fixed
```yulang
act ping:
    our get: () -> int
catch (catch ping::get():
    ping::get(), k -> k 1
    value -> value
):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-hygiene/direct-nested-fixed.yu
```
exit=0; seconds=0.007729582001047675
```text

```

## direct-nested-fixed
```yulang
act ping:
    our get: () -> int
catch (catch ping::get():
    ping::get(), k -> k 1
    value -> value
):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-hygiene/direct-nested-fixed.yu --poly
```
exit=0; seconds=0.0074088789988309145
```text
roots d0:ping
d0:ping mod {
}
root exprs e12:catch e7:catch e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()) { ping::get p0:_, p1:d3:k -> e5:(e3:r1:k->d3:k e4:1); p2:d4:value -> e6:r2:value->d4:value } { ping::get p3:_, p4:d5:k -> e10:(e8:r3:k->d5:k e9:7); p5:d6:value -> e11:r4:value->d6:value }
runtime roots e12:catch e7:catch e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()) { ping::get p0:_, p1:d3:k -> e5:(e3:r1:k->d3:k e4:1); p2:d4:value -> e6:r2:value->d4:value } { ping::get p3:_, p4:d5:k -> e10:(e8:r3:k->d5:k e9:7); p5:d6:value -> e11:r4:value->d6:value }
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:k arg
  d4:value arg
  d5:k arg
  d6:value arg
}

```

## direct-nested-fixed
```yulang
act ping:
    our get: () -> int
catch (catch ping::get():
    ping::get(), k -> k 1
    value -> value
):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-hygiene/direct-nested-fixed.yu
```
exit=0; seconds=0.004422130001330515
```text
run roots [1]

```

## direct-shallow-fixed
```yulang
act ping:
    our get: () -> int
our sequence() = { my a = ping::get(); my b = ping::get(); (a,b) }
catch (catch sequence():
    ping::get(), k -> k 1
    value -> value
):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-hygiene/direct-shallow-fixed.yu
```
exit=0; seconds=0.009921993998432299
```text

```

## direct-shallow-fixed
```yulang
act ping:
    our get: () -> int
our sequence() = { my a = ping::get(); my b = ping::get(); (a,b) }
catch (catch sequence():
    ping::get(), k -> k 1
    value -> value
):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-hygiene/direct-shallow-fixed.yu --poly
```
exit=0; seconds=0.010655793998012086
```text
roots d0:ping d2:sequence
d0:ping mod {
}
d2:sequence: () -> [ping] (int, int) = e11:(fn p0:() -> e10:block { let my p1:d3:a = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:()); e9:block { let my p2:d4:b = e5:(e3:r1:"ping::get"->d1:"ping.get" e4:()); e8:(e6:r2:a->d3:a, e7:r3:b->d4:b) } })
root exprs e24:catch e19:catch e14:(e12:r4:sequence->d2:sequence e13:()) { ping::get p3:_, p4:d6:k -> e17:(e15:r5:k->d6:k e16:1); p5:d7:value -> e18:r6:value->d7:value } { ping::get p6:_, p7:d8:k -> e22:(e20:r7:k->d8:k e21:7); p8:d9:value -> e23:r8:value->d9:value }
runtime roots e24:catch e19:catch e14:(e12:r4:sequence->d2:sequence e13:()) { ping::get p3:_, p4:d6:k -> e17:(e15:r5:k->d6:k e16:1); p5:d7:value -> e18:r6:value->d7:value } { ping::get p6:_, p7:d8:k -> e22:(e20:r7:k->d8:k e21:7); p8:d9:value -> e23:r8:value->d9:value }
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  my d3:a: 'a | int = e2:(e0:r0:"ping::get"->d1:"ping.get" e1:())
  my d4:b: 'a | int = e5:(e3:r1:"ping::get"->d1:"ping.get" e4:())
  d6:k arg
  d7:value arg
  d8:k arg
  d9:value arg
}

```

## direct-shallow-fixed
```yulang
act ping:
    our get: () -> int
our sequence() = { my a = ping::get(); my b = ping::get(); (a,b) }
catch (catch sequence():
    ping::get(), k -> k 1
    value -> value
):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-hygiene/direct-shallow-fixed.yu
```
exit=0; seconds=0.004362976000265917
```text
run roots [(1, 7)]

```

## direct-nested-fixed
```yulang
act ping:
    our get: () -> int
catch (catch ping::get():
    ping::get(), k -> k 1
    value -> value
):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit2-hygiene/direct-nested-fixed.yu
```
exit=0; seconds=0.002922772000601981
```text
run roots [1]

```

## direct-nested-fixed
```yulang
act ping:
    our get: () -> int
catch (catch ping::get():
    ping::get(), k -> k 1
    value -> value
):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --evidence-vm --print-roots /tmp/audit2-hygiene/direct-nested-fixed.yu
```
exit=0; seconds=0.0023228390018630307
```text
run roots [1]

```

## direct-shallow-fixed
```yulang
act ping:
    our get: () -> int
our sequence() = { my a = ping::get(); my b = ping::get(); (a,b) }
catch (catch sequence():
    ping::get(), k -> k 1
    value -> value
):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit2-hygiene/direct-shallow-fixed.yu
```
exit=0; seconds=0.0022568889980902895
```text
run roots [(1, 7)]

```

## direct-shallow-fixed
```yulang
act ping:
    our get: () -> int
our sequence() = { my a = ping::get(); my b = ping::get(); (a,b) }
catch (catch sequence():
    ping::get(), k -> k 1
    value -> value
):
    ping::get(), k -> k 7
    value -> value
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --evidence-vm --print-roots /tmp/audit2-hygiene/direct-shallow-fixed.yu
```
exit=0; seconds=0.0024019379998208024
```text
run roots [(1, 7)]

```

## nested-same-family
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
seven(one(ping::get()))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit2-hygiene/nested-same-family.yu
```
exit=0; seconds=0.0018215439995401539
```text
run roots [7]

```

## nested-same-family
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
seven(one(ping::get()))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --evidence-vm --print-roots /tmp/audit2-hygiene/nested-same-family.yu
```
exit=0; seconds=0.0021967880020383745
```text
run roots [7]

```

## double-callback-hidden
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our inner(f) = catch f():
    ping::get(), k -> k 2
    value -> value
our middle(f) = catch f():
    ping::get(), k -> k 3
    value -> value
seven(middle(\() -> inner(\() -> ping::get())))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit2-hygiene/double-callback-hidden.yu
```
exit=0; seconds=0.002496700999472523
```text
run roots [3]

```

## double-callback-hidden
```yulang
act ping:
    our get: () -> int
our one(action: [ping] _) = catch action:
    ping::get(), k -> k 1
    value -> value
our seven(action: [ping] _) = catch action:
    ping::get(), k -> k 7
    value -> value
our inner(f) = catch f():
    ping::get(), k -> k 2
    value -> value
our middle(f) = catch f():
    ping::get(), k -> k 3
    value -> value
seven(middle(\() -> inner(\() -> ping::get())))
```
```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --evidence-vm --print-roots /tmp/audit2-hygiene/double-callback-hidden.yu
```
exit=0; seconds=0.002921519997471478
```text
run roots [3]

```

## Existing Rust unit output
```text
$ cargo test -p infer --lib constraints::directed_weight::tests::same_id_ -- --nocapture --test-threads=1
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
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.18s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 2 tests
test constraints::directed_weight::tests::same_id_pop_then_take_survives ... ok
test constraints::directed_weight::tests::same_id_take_then_pop_cancels ... ok

test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 1391 filtered out; finished in 0.01s

exit=0

```
