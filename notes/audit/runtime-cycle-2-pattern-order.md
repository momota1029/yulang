# 原ログ

## early-miss / check
```yu
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {x: 0}:
    {x: 1, y = ping::get()} -> 10
    _ -> 20
):
    ping::get(), k -> 99
    value -> value
 )
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-pattern-order/early-miss.yu
exit=1 elapsed=0.010093927383422852
stdout:
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 10, column 2
    10 |  )
       |  ^

stderr:

```

## early-miss / dump
```yu
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {x: 0}:
    {x: 1, y = ping::get()} -> 10
    _ -> 20
):
    ping::get(), k -> 99
    value -> value
 )
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-pattern-order/early-miss.yu --poly
exit=0 elapsed=0.00826716423034668
stdout:
roots d0:ping d2:id
d0:ping mod {
}
d2:id: int -> int = e1:(fn p0:d3:x -> e0:r0:x->d3:x)
root exprs e14:(e2:r1:id->d2:id e13:catch e10:case e4:{x: e3:0} { p3:{x: p1:1, y: p2:d5:y = e7:(e5:r2:"ping::get"->d1:"ping.get" e6:())} -> e8:10; p4:_ -> e9:20 } { ping::get p5:_, p6:d6:k -> e11:99; p7:d7:value -> e12:r3:value->d7:value })
runtime roots e14:(e2:r1:id->d2:id e13:catch e10:case e4:{x: e3:0} { p3:{x: p1:1, y: p2:d5:y = e7:(e5:r2:"ping::get"->d1:"ping.get" e6:())} -> e8:10; p4:_ -> e9:20 } { ping::get p5:_, p6:d6:k -> e11:99; p7:d7:value -> e12:r3:value->d7:value })
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:x arg
  d5:y arg
  d6:k arg
  d7:value arg
}

stderr:

```

## early-miss / run
```yu
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {x: 0}:
    {x: 1, y = ping::get()} -> 10
    _ -> 20
):
    ping::get(), k -> 99
    value -> value
 )
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-pattern-order/early-miss.yu
exit=1 elapsed=0.0022754669189453125
stdout:
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 10, column 2
    10 |  )
       |  ^

stderr:

```

## early-match / check
```yu
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {x: 1}:
    {x: 1, y = ping::get()} -> 10
    _ -> 20
):
    ping::get(), k -> 99
    value -> value
 )
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-pattern-order/early-match.yu
exit=1 elapsed=0.005198955535888672
stdout:
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 10, column 2
    10 |  )
       |  ^

stderr:

```

## early-match / dump
```yu
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {x: 1}:
    {x: 1, y = ping::get()} -> 10
    _ -> 20
):
    ping::get(), k -> 99
    value -> value
 )
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-pattern-order/early-match.yu --poly
exit=0 elapsed=0.005334138870239258
stdout:
roots d0:ping d2:id
d0:ping mod {
}
d2:id: int -> int = e1:(fn p0:d3:x -> e0:r0:x->d3:x)
root exprs e14:(e2:r1:id->d2:id e13:catch e10:case e4:{x: e3:1} { p3:{x: p1:1, y: p2:d5:y = e7:(e5:r2:"ping::get"->d1:"ping.get" e6:())} -> e8:10; p4:_ -> e9:20 } { ping::get p5:_, p6:d6:k -> e11:99; p7:d7:value -> e12:r3:value->d7:value })
runtime roots e14:(e2:r1:id->d2:id e13:catch e10:case e4:{x: e3:1} { p3:{x: p1:1, y: p2:d5:y = e7:(e5:r2:"ping::get"->d1:"ping.get" e6:())} -> e8:10; p4:_ -> e9:20 } { ping::get p5:_, p6:d6:k -> e11:99; p7:d7:value -> e12:r3:value->d7:value })
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:x arg
  d5:y arg
  d6:k arg
  d7:value arg
}

stderr:

```

## early-match / run
```yu
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {x: 1}:
    {x: 1, y = ping::get()} -> 10
    _ -> 20
):
    ping::get(), k -> 99
    value -> value
 )
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-pattern-order/early-match.yu
exit=1 elapsed=0.002613544464111328
stdout:
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 10, column 2
    10 |  )
       |  ^

stderr:

```

## default-first-miss / check
```yu
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {x: 0}:
    {y = ping::get(), x: 1} -> 10
    _ -> 20
):
    ping::get(), k -> 99
    value -> value
 )
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-pattern-order/default-first-miss.yu
exit=1 elapsed=0.005358457565307617
stdout:
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 10, column 2
    10 |  )
       |  ^

stderr:

```

## default-first-miss / dump
```yu
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {x: 0}:
    {y = ping::get(), x: 1} -> 10
    _ -> 20
):
    ping::get(), k -> 99
    value -> value
 )
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-pattern-order/default-first-miss.yu --poly
exit=0 elapsed=0.004832267761230469
stdout:
roots d0:ping d2:id
d0:ping mod {
}
d2:id: int -> int = e1:(fn p0:d3:x -> e0:r0:x->d3:x)
root exprs e14:(e2:r1:id->d2:id e13:catch e10:case e4:{x: e3:0} { p3:{y: p1:d5:y = e7:(e5:r2:"ping::get"->d1:"ping.get" e6:()), x: p2:1} -> e8:10; p4:_ -> e9:20 } { ping::get p5:_, p6:d6:k -> e11:99; p7:d7:value -> e12:r3:value->d7:value })
runtime roots e14:(e2:r1:id->d2:id e13:catch e10:case e4:{x: e3:0} { p3:{y: p1:d5:y = e7:(e5:r2:"ping::get"->d1:"ping.get" e6:()), x: p2:1} -> e8:10; p4:_ -> e9:20 } { ping::get p5:_, p6:d6:k -> e11:99; p7:d7:value -> e12:r3:value->d7:value })
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:x arg
  d5:y arg
  d6:k arg
  d7:value arg
}

stderr:

```

## default-first-miss / run
```yu
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {x: 0}:
    {y = ping::get(), x: 1} -> 10
    _ -> 20
):
    ping::get(), k -> 99
    value -> value
 )
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-pattern-order/default-first-miss.yu
exit=1 elapsed=0.002643585205078125
stdout:
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 10, column 2
    10 |  )
       |  ^

stderr:

```

## pure-control / check
```yu
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {x: 1}:
    {x: 1, y = 7} -> 10
    _ -> 20
):
    ping::get(), k -> 99
    value -> value
 )
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-pattern-order/pure-control.yu
exit=1 elapsed=0.004687070846557617
stdout:
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 10, column 2
    10 |  )
       |  ^

stderr:

```

## pure-control / dump
```yu
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {x: 1}:
    {x: 1, y = 7} -> 10
    _ -> 20
):
    ping::get(), k -> 99
    value -> value
 )
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-pattern-order/pure-control.yu --poly
exit=0 elapsed=0.007152557373046875
stdout:
roots d0:ping d2:id
d0:ping mod {
}
d2:id: int -> int = e1:(fn p0:d3:x -> e0:r0:x->d3:x)
root exprs e12:(e2:r1:id->d2:id e11:catch e8:case e4:{x: e3:1} { p3:{x: p1:1, y: p2:d5:y = e5:7} -> e6:10; p4:_ -> e7:20 } { ping::get p5:_, p6:d6:k -> e9:99; p7:d7:value -> e10:r2:value->d7:value })
runtime roots e12:(e2:r1:id->d2:id e11:catch e8:case e4:{x: e3:1} { p3:{x: p1:1, y: p2:d5:y = e5:7} -> e6:10; p4:_ -> e7:20 } { ping::get p5:_, p6:d6:k -> e9:99; p7:d7:value -> e10:r2:value->d7:value })
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:x arg
  d5:y arg
  d6:k arg
  d7:value arg
}

stderr:

```

## pure-control / run
```yu
act ping:
    our get: () -> int
our id(x:int):int=x
id(catch (case {x: 1}:
    {x: 1, y = 7} -> 10
    _ -> 20
):
    ping::get(), k -> 99
    value -> value
 )
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-pattern-order/pure-control.yu
exit=1 elapsed=0.0021555423736572266
stdout:
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 10, column 2
    10 |  )
       |  ^

stderr:

```

# 許可された修正追加2入力

## early-miss-fixed / check
```yu
act ping:
    our get: () -> int
our run() = case {x: 0}:
    {x: 1, y = ping::get()} -> 10
    _ -> 20
catch (run()):
    ping::get(), k -> 99
    value -> value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-pattern-order/early-miss-fixed.yu
exit=0 elapsed=0.006372690200805664
stdout:

stderr:

```

## early-miss-fixed / dump
```yu
act ping:
    our get: () -> int
our run() = case {x: 0}:
    {x: 1, y = ping::get()} -> 10
    _ -> 20
catch (run()):
    ping::get(), k -> 99
    value -> value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-pattern-order/early-miss-fixed.yu --poly
exit=0 elapsed=0.0049474239349365234
stdout:
roots d0:ping d2:run
d0:ping mod {
}
d2:run: () -> int = e8:(fn p0:() -> e7:case e1:{x: e0:0} { p3:{x: p1:1, y: p2:d3:y = e4:(e2:r0:"ping::get"->d1:"ping.get" e3:())} -> e5:10; p4:_ -> e6:20 })
root exprs e14:catch e11:(e9:r1:run->d2:run e10:()) { ping::get p5:_, p6:d5:k -> e12:99; p7:d6:value -> e13:r2:value->d6:value }
runtime roots e14:catch e11:(e9:r1:run->d2:run e10:()) { ping::get p5:_, p6:d5:k -> e12:99; p7:d6:value -> e13:r2:value->d6:value }
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:y arg
  d5:k arg
  d6:value arg
}

stderr:

```

## early-miss-fixed / run
```yu
act ping:
    our get: () -> int
our run() = case {x: 0}:
    {x: 1, y = ping::get()} -> 10
    _ -> 20
catch (run()):
    ping::get(), k -> 99
    value -> value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-pattern-order/early-miss-fixed.yu
exit=0 elapsed=0.004118919372558594
stdout:
run roots [20]

stderr:

```

## early-match-fixed / check
```yu
act ping:
    our get: () -> int
our run() = case {x: 1}:
    {x: 1, y = ping::get()} -> 10
    _ -> 20
catch (run()):
    ping::get(), k -> 99
    value -> value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-pattern-order/early-match-fixed.yu
exit=0 elapsed=0.005032539367675781
stdout:

stderr:

```

## early-match-fixed / dump
```yu
act ping:
    our get: () -> int
our run() = case {x: 1}:
    {x: 1, y = ping::get()} -> 10
    _ -> 20
catch (run()):
    ping::get(), k -> 99
    value -> value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-pattern-order/early-match-fixed.yu --poly
exit=0 elapsed=0.004670143127441406
stdout:
roots d0:ping d2:run
d0:ping mod {
}
d2:run: () -> int = e8:(fn p0:() -> e7:case e1:{x: e0:1} { p3:{x: p1:1, y: p2:d3:y = e4:(e2:r0:"ping::get"->d1:"ping.get" e3:())} -> e5:10; p4:_ -> e6:20 })
root exprs e14:catch e11:(e9:r1:run->d2:run e10:()) { ping::get p5:_, p6:d5:k -> e12:99; p7:d6:value -> e13:r2:value->d6:value }
runtime roots e14:catch e11:(e9:r1:run->d2:run e10:()) { ping::get p5:_, p6:d5:k -> e12:99; p7:d6:value -> e13:r2:value->d6:value }
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3:y arg
  d5:k arg
  d6:value arg
}

stderr:

```

## early-match-fixed / run
```yu
act ping:
    our get: () -> int
our run() = case {x: 1}:
    {x: 1, y = ping::get()} -> 10
    _ -> 20
catch (run()):
    ping::get(), k -> 99
    value -> value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-pattern-order/early-match-fixed.yu
exit=1 elapsed=0.002938985824584961
stdout:

stderr:
runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: direct abortive continuation binding
  hint: try the interpreter oracle or reduce this source to a smaller report

```
