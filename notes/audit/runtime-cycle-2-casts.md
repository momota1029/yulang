# cast追加 全実行原ログ

## raw.json / arith-control / check
```yu
my add: int -> int -> int = builtin_op::int_add
add 7 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/arith-control.yu
exit=0 elapsed=0.00578618049621582
stdout:

stderr:

```

## raw.json / arith-control / dump
```yu
my add: int -> int -> int = builtin_op::int_add
add 7 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/arith-control.yu --poly
exit=0 elapsed=0.00417017936706543
stdout:
roots d0:add
my d0:add: int -> int -> int = e0:builtin_op::int_add
root exprs e5:(e3:(e1:r0:add->d0:add e2:7) e4:1)
runtime roots e5:(e3:(e1:r0:add->d0:add e2:7) e4:1)

stderr:

```

## raw.json / arith-control / run
```yu
my add: int -> int -> int = builtin_op::int_add
add 7 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/arith-control.yu
exit=0 elapsed=0.005525827407836914
stdout:
run roots [8]

stderr:

```

## raw.json / direct-return / check
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my back(x: user_id): int = x
back (user_id 7)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/direct-return.yu
exit=1 elapsed=0.005595684051513672
stdout:
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `user_id` is not compatible with required shape `function`
    --> line 2, column 26
    2 | cast(x: user_id): int = x.0
      |                          ^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `function` comes from this requirement
    --> line 2, column 25
    2 | cast(x: user_id): int = x.0
      |                         ^

stderr:

```

## raw.json / direct-return / dump
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my back(x: user_id): int = x
back (user_id 7)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/direct-return.yu --poly
exit=0 elapsed=0.0069658756256103516
stdout:
roots d0:user_id d2:box d5:back
d0:user_id: int -> user_id = <missing>
d2:box: {value: 'a} -> box 'a = <missing>
my d5:back: (int & user_id) -> int | user_id = e5:(fn p1:d7:x -> e4:r1:x->d7:x)
root exprs e10:(e6:r2:back->d5:back e9:(e7:r3:user_id->d0:user_id e8:7))
runtime roots e10:(e6:r2:back->d5:back e9:(e7:r3:user_id->d0:user_id e8:7))
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d6:x -> e2:(e0:r0:x->d6:x e1:0.0))
  d3: box 'a -> 'a = <missing>
  d4: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d6:x arg
  d7:x arg
}

stderr:
error: type shape `user_id` is not compatible with required shape `function`

```

## raw.json / direct-return / run
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my back(x: user_id): int = x
back (user_id 7)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/direct-return.yu
exit=1 elapsed=0.008718490600585938
stdout:

stderr:
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## raw.json / direct-arg / check
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my consume(x: int) = x
consume (user_id 7)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/direct-arg.yu
exit=1 elapsed=0.00661778450012207
stdout:
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `user_id` is not compatible with required shape `function`
    --> line 2, column 26
    2 | cast(x: user_id): int = x.0
      |                          ^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `function` comes from this requirement
    --> line 2, column 25
    2 | cast(x: user_id): int = x.0
      |                         ^

stderr:

```

## raw.json / direct-arg / dump
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my consume(x: int) = x
consume (user_id 7)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/direct-arg.yu --poly
exit=0 elapsed=0.006717205047607422
stdout:
roots d0:user_id d2:box d5:consume
d0:user_id: int -> user_id = <missing>
d2:box: {value: 'a} -> box 'a = <missing>
my d5:consume: int -> int = e5:(fn p1:d7:x -> e4:r1:x->d7:x)
root exprs e10:(e6:r2:consume->d5:consume e9:(e7:r3:user_id->d0:user_id e8:7))
runtime roots e10:(e6:r2:consume->d5:consume e9:(e7:r3:user_id->d0:user_id e8:7))
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d6:x -> e2:(e0:r0:x->d6:x e1:0.0))
  d3: box 'a -> 'a = <missing>
  d4: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d6:x arg
  d7:x arg
}

stderr:
error: type shape `user_id` is not compatible with required shape `function`

```

## raw.json / direct-arg / run
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my consume(x: int) = x
consume (user_id 7)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/direct-arg.yu
exit=1 elapsed=0.01210641860961914
stdout:

stderr:
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## raw.json / direct-add / check
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
add (user_id 7) 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/direct-add.yu
exit=1 elapsed=0.005844593048095703
stdout:
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `user_id` is not compatible with required shape `function`
    --> line 2, column 26
    2 | cast(x: user_id): int = x.0
      |                          ^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `function` comes from this requirement
    --> line 2, column 25
    2 | cast(x: user_id): int = x.0
      |                         ^

stderr:

```

## raw.json / direct-add / dump
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
add (user_id 7) 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/direct-add.yu --poly
exit=0 elapsed=0.012781620025634766
stdout:
roots d0:user_id d2:box d5:add
d0:user_id: int -> user_id = <missing>
d2:box: {value: 'a} -> box 'a = <missing>
my d5:add: int -> int -> int = e4:builtin_op::int_add
root exprs e11:(e9:(e5:r1:add->d5:add e8:(e6:r2:user_id->d0:user_id e7:7)) e10:1)
runtime roots e11:(e9:(e5:r1:add->d5:add e8:(e6:r2:user_id->d0:user_id e7:7)) e10:1)
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d6:x -> e2:(e0:r0:x->d6:x e1:0.0))
  d3: box 'a -> 'a = <missing>
  d4: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d6:x arg
}

stderr:
error: type shape `user_id` is not compatible with required shape `function`

```

## raw.json / direct-add / run
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
add (user_id 7) 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/direct-add.yu
exit=1 elapsed=0.008798599243164062
stdout:

stderr:
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## raw.json / box-return / check
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
widen (box {value: user_id 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-return.yu
exit=1 elapsed=0.008412361145019531
stdout:
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `user_id` is not compatible with required shape `function`
    --> line 2, column 26
    2 | cast(x: user_id): int = x.0
      |                          ^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `function` comes from this requirement
    --> line 2, column 25
    2 | cast(x: user_id): int = x.0
      |                         ^

stderr:

```

## raw.json / box-return / dump
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
widen (box {value: user_id 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-return.yu --poly
exit=0 elapsed=0.007613658905029297
stdout:
roots d0:user_id d2:box d5:widen
d0:user_id: int -> user_id = <missing>
d2:box: {value: 'a} -> box 'a = <missing>
my d5:widen: box(int | user_id <: int & user_id) -> box(int | user_id <: int & user_id) = e5:(fn p1:d7:x -> e4:r1:x->d7:x)
root exprs e13:(e6:r2:widen->d5:widen e12:(e7:r3:box->d2:box e11:{value: e10:(e8:r4:user_id->d0:user_id e9:7)}))
runtime roots e13:(e6:r2:widen->d5:widen e12:(e7:r3:box->d2:box e11:{value: e10:(e8:r4:user_id->d0:user_id e9:7)}))
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d6:x -> e2:(e0:r0:x->d6:x e1:0.0))
  d3: box 'a -> 'a = <missing>
  d4: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d6:x arg
  d7:x arg
}

stderr:
error: type shape `user_id` is not compatible with required shape `function`

```

## raw.json / box-return / run
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
widen (box {value: user_id 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-return.yu
exit=1 elapsed=0.009723663330078125
stdout:

stderr:
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## raw.json / box-projection / check
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
(widen (box {value: user_id 7})).value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-projection.yu
exit=1 elapsed=0.009612798690795898
stdout:
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `user_id` is not compatible with required shape `function`
    --> line 2, column 26
    2 | cast(x: user_id): int = x.0
      |                          ^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `function` comes from this requirement
    --> line 2, column 25
    2 | cast(x: user_id): int = x.0
      |                         ^

stderr:

```

## raw.json / box-projection / dump
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
(widen (box {value: user_id 7})).value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-projection.yu --poly
exit=0 elapsed=0.012420892715454102
stdout:
roots d0:user_id d2:box d5:widen
d0:user_id: int -> user_id = <missing>
d2:box: {value: 'a} -> box 'a = <missing>
my d5:widen: box(int | user_id <: int & user_id) -> box(int | user_id <: int & user_id) = e5:(fn p1:d7:x -> e4:r1:x->d7:x)
root exprs e14:(e13:(e6:r2:widen->d5:widen e12:(e7:r3:box->d2:box e11:{value: e10:(e8:r4:user_id->d0:user_id e9:7)})).s0.value->d3)
runtime roots e14:(e13:(e6:r2:widen->d5:widen e12:(e7:r3:box->d2:box e11:{value: e10:(e8:r4:user_id->d0:user_id e9:7)})).s0.value->d3)
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d6:x -> e2:(e0:r0:x->d6:x e1:0.0))
  d3: box 'a -> 'a = <missing>
  d4: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d6:x arg
  d7:x arg
}

stderr:
error: type shape `user_id` is not compatible with required shape `function`

```

## raw.json / box-projection / run
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
(widen (box {value: user_id 7})).value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-projection.yu
exit=1 elapsed=0.021578073501586914
stdout:

stderr:
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## raw.json / box-add / check
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = x
add (widen (box {value: user_id 7})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-add.yu
exit=1 elapsed=0.014008045196533203
stdout:
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `user_id` is not compatible with required shape `function`
    --> line 2, column 26
    2 | cast(x: user_id): int = x.0
      |                          ^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `function` comes from this requirement
    --> line 2, column 25
    2 | cast(x: user_id): int = x.0
      |                         ^

stderr:

```

## raw.json / box-add / dump
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = x
add (widen (box {value: user_id 7})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-add.yu --poly
exit=0 elapsed=0.014298439025878906
stdout:
roots d0:user_id d2:box d5:add d6:widen
d0:user_id: int -> user_id = <missing>
d2:box: {value: 'a} -> box 'a = <missing>
my d5:add: int -> int -> int = e4:builtin_op::int_add
my d6:widen: box(int | user_id <: int & user_id) -> box(int | user_id <: int & user_id) = e6:(fn p1:d8:x -> e5:r1:x->d8:x)
root exprs e19:(e17:(e7:r2:add->d5:add e16:(e15:(e8:r3:widen->d6:widen e14:(e9:r4:box->d2:box e13:{value: e12:(e10:r5:user_id->d0:user_id e11:7)})).s0.value->d3)) e18:1)
runtime roots e19:(e17:(e7:r2:add->d5:add e16:(e15:(e8:r3:widen->d6:widen e14:(e9:r4:box->d2:box e13:{value: e12:(e10:r5:user_id->d0:user_id e11:7)})).s0.value->d3)) e18:1)
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d7:x -> e2:(e0:r0:x->d7:x e1:0.0))
  d3: box 'a -> 'a = <missing>
  d4: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d7:x arg
  d8:x arg
}

stderr:
error: type shape `user_id` is not compatible with required shape `function`

```

## raw.json / box-add / run
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = x
add (widen (box {value: user_id 7})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-add.yu
exit=1 elapsed=0.016544580459594727
stdout:

stderr:
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## raw.json / box-consumer-add / check
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: user_id 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-consumer-add.yu
exit=1 elapsed=0.012491941452026367
stdout:
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `user_id` is not compatible with required shape `function`
    --> line 2, column 26
    2 | cast(x: user_id): int = x.0
      |                          ^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `function` comes from this requirement
    --> line 2, column 25
    2 | cast(x: user_id): int = x.0
      |                         ^

stderr:

```

## raw.json / box-consumer-add / dump
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: user_id 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-consumer-add.yu --poly
exit=0 elapsed=0.012118816375732422
stdout:
roots d0:user_id d2:box d5:add d6:consume
d0:user_id: int -> user_id = <missing>
d2:box: {value: 'a} -> box 'a = <missing>
my d5:add: int -> int -> int = e4:builtin_op::int_add
my d6:consume: box int -> int = e11:(fn p1:d8:x -> e10:(e8:(e5:r1:add->d5:add e7:(e6:r2:x->d8:x.s0.value->d3)) e9:1))
root exprs e19:(e12:r3:consume->d6:consume e18:(e13:r4:box->d2:box e17:{value: e16:(e14:r5:user_id->d0:user_id e15:7)}))
runtime roots e19:(e12:r3:consume->d6:consume e18:(e13:r4:box->d2:box e17:{value: e16:(e14:r5:user_id->d0:user_id e15:7)}))
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d7:x -> e2:(e0:r0:x->d7:x e1:0.0))
  d3: box 'a -> 'a = <missing>
  d4: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d7:x arg
  d8:x arg
}

stderr:
error: type shape `user_id` is not compatible with required shape `function`

```

## raw.json / box-consumer-add / run
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: user_id 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-consumer-add.yu
exit=1 elapsed=0.011458873748779297
stdout:

stderr:
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## raw.json / box-explicit-rebuild / check
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = box {value: x.value}
add (widen (box {value: user_id 7})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-explicit-rebuild.yu
exit=1 elapsed=0.018279075622558594
stdout:
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `user_id` is not compatible with required shape `function`
    --> line 2, column 26
    2 | cast(x: user_id): int = x.0
      |                          ^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `function` comes from this requirement
    --> line 2, column 25
    2 | cast(x: user_id): int = x.0
      |                         ^

stderr:

```

## raw.json / box-explicit-rebuild / dump
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = box {value: x.value}
add (widen (box {value: user_id 7})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-explicit-rebuild.yu --poly
exit=0 elapsed=0.018082380294799805
stdout:
roots d0:user_id d2:box d5:add d6:widen
d0:user_id: int -> user_id = <missing>
d2:box: {value: 'a} -> box 'a = <missing>
my d5:add: int -> int -> int = e4:builtin_op::int_add
my d6:widen: box(user_id <: int & user_id) -> box(int | user_id <: int) = e10:(fn p1:d8:x -> e9:(e5:r1:box->d2:box e8:{value: e7:(e6:r2:x->d8:x.s0.value->d3)}))
root exprs e23:(e21:(e11:r3:add->d5:add e20:(e19:(e12:r4:widen->d6:widen e18:(e13:r5:box->d2:box e17:{value: e16:(e14:r6:user_id->d0:user_id e15:7)})).s1.value->d3)) e22:1)
runtime roots e23:(e21:(e11:r3:add->d5:add e20:(e19:(e12:r4:widen->d6:widen e18:(e13:r5:box->d2:box e17:{value: e16:(e14:r6:user_id->d0:user_id e15:7)})).s1.value->d3)) e22:1)
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d7:x -> e2:(e0:r0:x->d7:x e1:0.0))
  d3: box 'a -> 'a = <missing>
  d4: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d7:x arg
  d8:x arg
}

stderr:
error: type shape `user_id` is not compatible with required shape `function`

```

## raw.json / box-explicit-rebuild / run
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = box {value: x.value}
add (widen (box {value: user_id 7})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-explicit-rebuild.yu
exit=1 elapsed=0.02002096176147461
stdout:

stderr:
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## raw.json / record-return / check
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: {value: user_id}): {value: int} = x
widen {value: user_id 7}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/record-return.yu
exit=1 elapsed=0.005645275115966797
stdout:
diagnostics:
  error [yulang.unsupported-type-syntax]: widen: unsupported type annotation syntax: record type annotation
    --> line 4, column 13
    4 | my widen(x: {value: user_id}): {value: int} = x
      |             ^^^^^^^^^^^^^^^^
    hint: use a supported type annotation form and keep effect rows in effect position
  error [yulang.unsatisfied-subtype]: type shape `user_id` is not compatible with required shape `function`
    --> line 2, column 26
    2 | cast(x: user_id): int = x.0
      |                          ^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `function` comes from this requirement
    --> line 2, column 25
    2 | cast(x: user_id): int = x.0
      |                         ^

stderr:

```

## raw.json / record-return / dump
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: {value: user_id}): {value: int} = x
widen {value: user_id 7}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/record-return.yu --poly
exit=0 elapsed=0.005903959274291992
stdout:
roots d0:user_id d2:box d5:widen
d0:user_id: int -> user_id = <missing>
d2:box: {value: 'a} -> box 'a = <missing>
my d5:widen: never = <missing>
root exprs e9:(e4:r1:widen->d5:widen e8:{value: e7:(e5:r2:user_id->d0:user_id e6:7)})
runtime roots e9:(e4:r1:widen->d5:widen e8:{value: e7:(e5:r2:user_id->d0:user_id e6:7)})
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d6:x -> e2:(e0:r0:x->d6:x e1:0.0))
  d3: box 'a -> 'a = <missing>
  d4: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d6:x arg
}

stderr:
error: unsupported type annotation syntax: record type annotation
error: type shape `user_id` is not compatible with required shape `function`

```

## raw.json / record-return / run
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: {value: user_id}): {value: int} = x
widen {value: user_id 7}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/record-return.yu
exit=1 elapsed=0.006623744964599609
stdout:

stderr:
compile error [yulang.lowering]: source has lowering errors
  detail: unsupported type annotation syntax: record type annotation
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## raw.json / tuple-return / check
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: (user_id, int)): (int, int) = x
widen (user_id 7, 1)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/tuple-return.yu
exit=1 elapsed=0.005945920944213867
stdout:
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `user_id` is not compatible with required shape `function`
    --> line 2, column 26
    2 | cast(x: user_id): int = x.0
      |                          ^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `function` comes from this requirement
    --> line 2, column 25
    2 | cast(x: user_id): int = x.0
      |                         ^

stderr:

```

## raw.json / tuple-return / dump
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: (user_id, int)): (int, int) = x
widen (user_id 7, 1)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/tuple-return.yu --poly
exit=0 elapsed=0.00829005241394043
stdout:
roots d0:user_id d2:box d5:widen
d0:user_id: int -> user_id = <missing>
d2:box: {value: 'a} -> box 'a = <missing>
my d5:widen: (int & user_id, int) -> (int | user_id, int) = e5:(fn p1:d7:x -> e4:r1:x->d7:x)
root exprs e12:(e6:r2:widen->d5:widen e11:(e9:(e7:r3:user_id->d0:user_id e8:7), e10:1))
runtime roots e12:(e6:r2:widen->d5:widen e11:(e9:(e7:r3:user_id->d0:user_id e8:7), e10:1))
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d6:x -> e2:(e0:r0:x->d6:x e1:0.0))
  d3: box 'a -> 'a = <missing>
  d4: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d6:x arg
  d7:x arg
}

stderr:
error: type shape `user_id` is not compatible with required shape `function`

```

## raw.json / tuple-return / run
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: (user_id, int)): (int, int) = x
widen (user_id 7, 1)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/tuple-return.yu
exit=1 elapsed=0.00633692741394043
stdout:

stderr:
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## raw.json / nominal-target / check
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
struct target {value: int}
cast(x: user_id): target = target {value: x.0}
my consume(x: target) = x
consume (user_id 7)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/nominal-target.yu
exit=1 elapsed=0.0102691650390625
stdout:
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `user_id` is not compatible with required shape `function`
    --> line 2, column 26
    2 | cast(x: user_id): int = x.0
      |                          ^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `function` comes from this requirement
    --> line 2, column 25
    2 | cast(x: user_id): int = x.0
      |                         ^
  error [yulang.unsatisfied-subtype]: type shape `user_id` is not compatible with required shape `function`
    --> line 5, column 44
    5 | cast(x: user_id): target = target {value: x.0}
      |                                            ^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `function` comes from this requirement
    --> line 5, column 43
    5 | cast(x: user_id): target = target {value: x.0}
      |                                           ^

stderr:

```

## raw.json / nominal-target / dump
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
struct target {value: int}
cast(x: user_id): target = target {value: x.0}
my consume(x: target) = x
consume (user_id 7)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/nominal-target.yu --poly
exit=0 elapsed=0.011789560317993164
stdout:
roots d0:user_id d2:box d5:target d9:consume
d0:user_id: int -> user_id = <missing>
d2:box: {value: 'a} -> box 'a = <missing>
d5:target: {value: int} -> target = <missing>
my d9:consume: target -> target = e12:(fn p2:d12:x -> e11:r3:x->d12:x)
root exprs e17:(e13:r4:consume->d9:consume e16:(e14:r5:user_id->d0:user_id e15:7))
runtime roots e17:(e13:r4:consume->d9:consume e16:(e14:r5:user_id->d0:user_id e15:7))
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d10:x -> e2:(e0:r0:x->d10:x e1:0.0))
  d3: box 'a -> 'a = <missing>
  d4: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d6: target -> int = <missing>
  d7: std::control::var::ref 'a target -> std::control::var::ref 'a int = <missing>
  my d8:"#cast": (user_id & (float -> ['a] int)) -> ['a] target = e10:(fn p1:d11:x -> e9:(e4:r1:target->d5:target e8:{value: e7:(e5:r2:x->d11:x e6:0.0)}))
  d10:x arg
  d11:x arg
  d12:x arg
}

stderr:
error: type shape `user_id` is not compatible with required shape `function`
error: type shape `user_id` is not compatible with required shape `function`

```

## raw.json / nominal-target / run
```yu
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
struct target {value: int}
cast(x: user_id): target = target {value: x.0}
my consume(x: target) = x
consume (user_id 7)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/nominal-target.yu
exit=1 elapsed=0.009402990341186523
stdout:

stderr:
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## record-nominal-raw.json / arith-control / check
```yu
my add: int -> int -> int = builtin_op::int_add
add 7 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/arith-control.yu
exit=0 elapsed=0.005021333694458008
stdout:

stderr:

```

## record-nominal-raw.json / arith-control / dump
```yu
my add: int -> int -> int = builtin_op::int_add
add 7 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/arith-control.yu --poly
exit=0 elapsed=0.0022754669189453125
stdout:
roots d0:add
my d0:add: int -> int -> int = e0:builtin_op::int_add
root exprs e5:(e3:(e1:r0:add->d0:add e2:7) e4:1)
runtime roots e5:(e3:(e1:r0:add->d0:add e2:7) e4:1)

stderr:

```

## record-nominal-raw.json / arith-control / run
```yu
my add: int -> int -> int = builtin_op::int_add
add 7 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/arith-control.yu
exit=0 elapsed=0.0024366378784179688
stdout:
run roots [8]

stderr:

```

## record-nominal-raw.json / direct-return / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my back(x: user_id): int = x
back (user_id {raw: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/direct-return.yu
exit=0 elapsed=0.005815029144287109
stdout:

stderr:

```

## record-nominal-raw.json / direct-return / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my back(x: user_id): int = x
back (user_id {raw: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/direct-return.yu --poly
exit=0 elapsed=0.007799625396728516
stdout:
roots d0:user_id d4:box d7:back
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:back: (int & user_id) -> int | user_id = e4:(fn p1:d9:x -> e3:r1:x->d9:x)
root exprs e10:(e5:r2:back->d7:back e9:(e6:r3:user_id->d0:user_id e8:{raw: e7:7}))
runtime roots e10:(e5:r2:back->d7:back e9:(e6:r3:user_id->d0:user_id e8:{raw: e7:7}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8:x arg
  d9:x arg
}

stderr:

```

## record-nominal-raw.json / direct-return / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my back(x: user_id): int = x
back (user_id {raw: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/direct-return.yu
exit=0 elapsed=0.004076242446899414
stdout:
run roots [7]

stderr:

```

## record-nominal-raw.json / direct-arg / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my consume(x: int) = x
consume (user_id {raw: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/direct-arg.yu
exit=0 elapsed=0.0068323612213134766
stdout:

stderr:

```

## record-nominal-raw.json / direct-arg / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my consume(x: int) = x
consume (user_id {raw: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/direct-arg.yu --poly
exit=0 elapsed=0.00816965103149414
stdout:
roots d0:user_id d4:box d7:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:consume: int -> int = e4:(fn p1:d9:x -> e3:r1:x->d9:x)
root exprs e10:(e5:r2:consume->d7:consume e9:(e6:r3:user_id->d0:user_id e8:{raw: e7:7}))
runtime roots e10:(e5:r2:consume->d7:consume e9:(e6:r3:user_id->d0:user_id e8:{raw: e7:7}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8:x arg
  d9:x arg
}

stderr:

```

## record-nominal-raw.json / direct-arg / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my consume(x: int) = x
consume (user_id {raw: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/direct-arg.yu
exit=0 elapsed=0.004189252853393555
stdout:
run roots [7]

stderr:

```

## record-nominal-raw.json / direct-add / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
add (user_id {raw: 7}) 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/direct-add.yu
exit=0 elapsed=0.007263660430908203
stdout:

stderr:

```

## record-nominal-raw.json / direct-add / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
add (user_id {raw: 7}) 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/direct-add.yu --poly
exit=0 elapsed=0.007527351379394531
stdout:
roots d0:user_id d4:box d7:add
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
root exprs e11:(e9:(e4:r1:add->d7:add e8:(e5:r2:user_id->d0:user_id e7:{raw: e6:7})) e10:1)
runtime roots e11:(e9:(e4:r1:add->d7:add e8:(e5:r2:user_id->d0:user_id e7:{raw: e6:7})) e10:1)
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8:x arg
}

stderr:

```

## record-nominal-raw.json / direct-add / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
add (user_id {raw: 7}) 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/direct-add.yu
exit=0 elapsed=0.0032973289489746094
stdout:
run roots [8]

stderr:

```

## record-nominal-raw.json / box-return / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
widen (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-return.yu
exit=0 elapsed=0.008216381072998047
stdout:

stderr:

```

## record-nominal-raw.json / box-return / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
widen (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-return.yu --poly
exit=0 elapsed=0.010453939437866211
stdout:
roots d0:user_id d4:box d7:widen
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:widen: box(int | user_id <: int & user_id) -> box(int | user_id <: int & user_id) = e4:(fn p1:d9:x -> e3:r1:x->d9:x)
root exprs e13:(e5:r2:widen->d7:widen e12:(e6:r3:box->d4:box e11:{value: e10:(e7:r4:user_id->d0:user_id e9:{raw: e8:7})}))
runtime roots e13:(e5:r2:widen->d7:widen e12:(e6:r3:box->d4:box e11:{value: e10:(e7:r4:user_id->d0:user_id e9:{raw: e8:7})}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8:x arg
  d9:x arg
}

stderr:

```

## record-nominal-raw.json / box-return / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
widen (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-return.yu
exit=0 elapsed=0.00491642951965332
stdout:
run roots [box({value: user_id({raw: 7})})]

stderr:

```

## record-nominal-raw.json / box-projection / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
(widen (box {value: user_id {raw: 7}})).value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-projection.yu
exit=0 elapsed=0.014323711395263672
stdout:

stderr:

```

## record-nominal-raw.json / box-projection / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
(widen (box {value: user_id {raw: 7}})).value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-projection.yu --poly
exit=0 elapsed=0.013833761215209961
stdout:
roots d0:user_id d4:box d7:widen
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:widen: box(int | user_id <: int & user_id) -> box(int | user_id <: int & user_id) = e4:(fn p1:d9:x -> e3:r1:x->d9:x)
root exprs e14:(e13:(e5:r2:widen->d7:widen e12:(e6:r3:box->d4:box e11:{value: e10:(e7:r4:user_id->d0:user_id e9:{raw: e8:7})})).s1.value->d5)
runtime roots e14:(e13:(e5:r2:widen->d7:widen e12:(e6:r3:box->d4:box e11:{value: e10:(e7:r4:user_id->d0:user_id e9:{raw: e8:7})})).s1.value->d5)
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8:x arg
  d9:x arg
}

stderr:

```

## record-nominal-raw.json / box-projection / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
(widen (box {value: user_id {raw: 7}})).value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-projection.yu
exit=0 elapsed=0.00532841682434082
stdout:
run roots [user_id({raw: 7})]

stderr:

```

## record-nominal-raw.json / box-add / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = x
add (widen (box {value: user_id {raw: 7}})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-add.yu
exit=0 elapsed=0.015897750854492188
stdout:

stderr:

```

## record-nominal-raw.json / box-add / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = x
add (widen (box {value: user_id {raw: 7}})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-add.yu --poly
exit=0 elapsed=0.023257732391357422
stdout:
roots d0:user_id d4:box d7:add d8:widen
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
my d8:widen: box(int | user_id <: int & user_id) -> box(int | user_id <: int & user_id) = e5:(fn p1:d10:x -> e4:r1:x->d10:x)
root exprs e19:(e17:(e6:r2:add->d7:add e16:(e15:(e7:r3:widen->d8:widen e14:(e8:r4:box->d4:box e13:{value: e12:(e9:r5:user_id->d0:user_id e11:{raw: e10:7})})).s1.value->d5)) e18:1)
runtime roots e19:(e17:(e6:r2:add->d7:add e16:(e15:(e7:r3:widen->d8:widen e14:(e8:r4:box->d4:box e13:{value: e12:(e9:r5:user_id->d0:user_id e11:{raw: e10:7})})).s1.value->d5)) e18:1)
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d9:x -> e1:(e0:r0:x->d9:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:x arg
  d10:x arg
}

stderr:

```

## record-nominal-raw.json / box-add / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = x
add (widen (box {value: user_id {raw: 7}})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-add.yu
exit=0 elapsed=0.007044792175292969
stdout:
run roots [8]

stderr:

```

## record-nominal-raw.json / box-consumer-add / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-consumer-add.yu
exit=0 elapsed=0.011379241943359375
stdout:

stderr:

```

## record-nominal-raw.json / box-consumer-add / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-consumer-add.yu --poly
exit=0 elapsed=0.01087188720703125
stdout:
roots d0:user_id d4:box d7:add d8:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
my d8:consume: box int -> int = e10:(fn p1:d10:x -> e9:(e7:(e4:r1:add->d7:add e6:(e5:r2:x->d10:x.s1.value->d5)) e8:1))
root exprs e19:(e11:r3:consume->d8:consume e18:(e12:r4:box->d4:box e17:{value: e16:(e13:r5:user_id->d0:user_id e15:{raw: e14:7})}))
runtime roots e19:(e11:r3:consume->d8:consume e18:(e12:r4:box->d4:box e17:{value: e16:(e13:r5:user_id->d0:user_id e15:{raw: e14:7})}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d9:x -> e1:(e0:r0:x->d9:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:x arg
  d10:x arg
}

stderr:

```

## record-nominal-raw.json / box-consumer-add / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-consumer-add.yu
exit=1 elapsed=0.004494667053222656
stdout:

stderr:
runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: non-int primitive argument
  hint: try the interpreter oracle or reduce this source to a smaller report

```

## record-nominal-raw.json / box-explicit-rebuild / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = box {value: x.value}
add (widen (box {value: user_id {raw: 7}})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-explicit-rebuild.yu
exit=0 elapsed=0.018467187881469727
stdout:

stderr:

```

## record-nominal-raw.json / box-explicit-rebuild / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = box {value: x.value}
add (widen (box {value: user_id {raw: 7}})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-explicit-rebuild.yu --poly
exit=0 elapsed=0.021828413009643555
stdout:
roots d0:user_id d4:box d7:add d8:widen
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
my d8:widen: box(user_id <: int & user_id) -> box(int | user_id <: int) = e9:(fn p1:d10:x -> e8:(e4:r1:box->d4:box e7:{value: e6:(e5:r2:x->d10:x.s1.value->d5)}))
root exprs e23:(e21:(e10:r3:add->d7:add e20:(e19:(e11:r4:widen->d8:widen e18:(e12:r5:box->d4:box e17:{value: e16:(e13:r6:user_id->d0:user_id e15:{raw: e14:7})})).s2.value->d5)) e22:1)
runtime roots e23:(e21:(e10:r3:add->d7:add e20:(e19:(e11:r4:widen->d8:widen e18:(e12:r5:box->d4:box e17:{value: e16:(e13:r6:user_id->d0:user_id e15:{raw: e14:7})})).s2.value->d5)) e22:1)
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d9:x -> e1:(e0:r0:x->d9:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:x arg
  d10:x arg
}

stderr:

```

## record-nominal-raw.json / box-explicit-rebuild / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = box {value: x.value}
add (widen (box {value: user_id {raw: 7}})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-explicit-rebuild.yu
exit=1 elapsed=0.0053882598876953125
stdout:

stderr:
runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: non-int primitive argument
  hint: try the interpreter oracle or reduce this source to a smaller report

```

## record-nominal-raw.json / record-return / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my widen(x: {value: user_id}): {value: int} = x
widen {value: user_id {raw: 7}}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/record-return.yu
exit=1 elapsed=0.006628990173339844
stdout:
diagnostics:
  error [yulang.unsupported-type-syntax]: widen: unsupported type annotation syntax: record type annotation
    --> line 4, column 13
    4 | my widen(x: {value: user_id}): {value: int} = x
      |             ^^^^^^^^^^^^^^^^
    hint: use a supported type annotation form and keep effect rows in effect position

stderr:

```

## record-nominal-raw.json / record-return / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my widen(x: {value: user_id}): {value: int} = x
widen {value: user_id {raw: 7}}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/record-return.yu --poly
exit=0 elapsed=0.0060918331146240234
stdout:
roots d0:user_id d4:box d7:widen
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:widen: never = <missing>
root exprs e9:(e3:r1:widen->d7:widen e8:{value: e7:(e4:r2:user_id->d0:user_id e6:{raw: e5:7})})
runtime roots e9:(e3:r1:widen->d7:widen e8:{value: e7:(e4:r2:user_id->d0:user_id e6:{raw: e5:7})})
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8:x arg
}

stderr:
error: unsupported type annotation syntax: record type annotation

```

## record-nominal-raw.json / record-return / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my widen(x: {value: user_id}): {value: int} = x
widen {value: user_id {raw: 7}}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/record-return.yu
exit=1 elapsed=0.00615692138671875
stdout:

stderr:
compile error [yulang.lowering]: source has lowering errors
  detail: unsupported type annotation syntax: record type annotation
  hint: run `yulang check` to see source ranges before running

```

## record-nominal-raw.json / tuple-return / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my widen(x: (user_id, int)): (int, int) = x
widen (user_id {raw: 7}, 1)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/tuple-return.yu
exit=0 elapsed=0.006855487823486328
stdout:

stderr:

```

## record-nominal-raw.json / tuple-return / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my widen(x: (user_id, int)): (int, int) = x
widen (user_id {raw: 7}, 1)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/tuple-return.yu --poly
exit=0 elapsed=0.007750511169433594
stdout:
roots d0:user_id d4:box d7:widen
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:widen: (int & user_id, int) -> (int | user_id, int) = e4:(fn p1:d9:x -> e3:r1:x->d9:x)
root exprs e12:(e5:r2:widen->d7:widen e11:(e9:(e6:r3:user_id->d0:user_id e8:{raw: e7:7}), e10:1))
runtime roots e12:(e5:r2:widen->d7:widen e11:(e9:(e6:r3:user_id->d0:user_id e8:{raw: e7:7}), e10:1))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8:x arg
  d9:x arg
}

stderr:

```

## record-nominal-raw.json / tuple-return / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my widen(x: (user_id, int)): (int, int) = x
widen (user_id {raw: 7}, 1)
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/tuple-return.yu
exit=1 elapsed=0.009232521057128906
stdout:

stderr:
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: (user_id, int) -> (user_id, int) <: (user_id, int) -> (int, int)
  hint: check that the value provides the fields or shape required by this use

```

## record-nominal-raw.json / nominal-target / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
struct target {value: int}
cast(x: user_id): target = target {value: x.raw}
my consume(x: target) = x
consume (user_id {raw: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/nominal-target.yu
exit=0 elapsed=0.007445573806762695
stdout:

stderr:

```

## record-nominal-raw.json / nominal-target / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
struct target {value: int}
cast(x: user_id): target = target {value: x.raw}
my consume(x: target) = x
consume (user_id {raw: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/nominal-target.yu --poly
exit=0 elapsed=0.00949859619140625
stdout:
roots d0:user_id d4:box d7:target d11:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
d7:target: {value: int} -> target = <missing>
my d11:consume: target -> target = e10:(fn p2:d14:x -> e9:r3:x->d14:x)
root exprs e16:(e11:r4:consume->d11:consume e15:(e12:r5:user_id->d0:user_id e14:{raw: e13:7}))
runtime roots e16:(e11:r4:consume->d11:consume e15:(e12:r5:user_id->d0:user_id e14:{raw: e13:7}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d12:x -> e1:(e0:r0:x->d12:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8: target -> int = <missing>
  d9: std::control::var::ref 'a target -> std::control::var::ref 'a int = <missing>
  my d10:"#cast": user_id -> target = e8:(fn p1:d13:x -> e7:(e3:r1:target->d7:target e6:{value: e5:(e4:r2:x->d13:x.s1.raw->d1)}))
  d12:x arg
  d13:x arg
  d14:x arg
}

stderr:

```

## record-nominal-raw.json / nominal-target / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
struct target {value: int}
cast(x: user_id): target = target {value: x.raw}
my consume(x: target) = x
consume (user_id {raw: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/nominal-target.yu
exit=0 elapsed=0.004374980926513672
stdout:
run roots [target({value: 7})]

stderr:

```

## boundary-raw.json / box-consumer-control / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-consumer-control.yu
exit=0 elapsed=0.009721517562866211
stdout:

stderr:

```

## boundary-raw.json / box-consumer-control / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-consumer-control.yu --poly
exit=0 elapsed=0.008424520492553711
stdout:
roots d0:user_id d4:box d7:add d8:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
my d8:consume: box int -> int = e10:(fn p1:d10:x -> e9:(e7:(e4:r1:add->d7:add e6:(e5:r2:x->d10:x.s1.value->d5)) e8:1))
root exprs e16:(e11:r3:consume->d8:consume e15:(e12:r4:box->d4:box e14:{value: e13:7}))
runtime roots e16:(e11:r3:consume->d8:consume e15:(e12:r4:box->d4:box e14:{value: e13:7}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d9:x -> e1:(e0:r0:x->d9:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:x arg
  d10:x arg
}

stderr:

```

## boundary-raw.json / box-consumer-control / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-consumer-control.yu
exit=0 elapsed=0.003547191619873047
stdout:
run roots [8]

stderr:

```

## boundary-raw.json / box-fixed-producer / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my make(): box user_id = box {value: user_id {raw: 7}}
my consume(x: box int) = add x.value 1
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-fixed-producer.yu
exit=0 elapsed=0.009438753128051758
stdout:

stderr:

```

## boundary-raw.json / box-fixed-producer / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my make(): box user_id = box {value: user_id {raw: 7}}
my consume(x: box int) = add x.value 1
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-fixed-producer.yu --poly
exit=0 elapsed=0.010329961776733398
stdout:
roots d0:user_id d4:box d7:add d8:make d9:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
my d8:make: () -> box user_id = e11:(fn p1:() -> e10:(e4:r1:box->d4:box e9:{value: e8:(e5:r2:user_id->d0:user_id e7:{raw: e6:7})}))
my d9:consume: box int -> int = e18:(fn p2:d11:x -> e17:(e15:(e12:r3:add->d7:add e14:(e13:r4:x->d11:x.s1.value->d5)) e16:1))
root exprs e23:(e19:r5:consume->d9:consume e22:(e20:r6:make->d8:make e21:()))
runtime roots e23:(e19:r5:consume->d9:consume e22:(e20:r6:make->d8:make e21:()))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d10:x -> e1:(e0:r0:x->d10:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d10:x arg
  d11:x arg
}

stderr:

```

## boundary-raw.json / box-fixed-producer / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my make(): box user_id = box {value: user_id {raw: 7}}
my consume(x: box int) = add x.value 1
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-fixed-producer.yu
exit=1 elapsed=0.011325836181640625
stdout:

stderr:
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: box(user_id) <: box(int)
  hint: check that the value provides the fields or shape required by this use

```

## boundary-raw.json / row-inferred-consumer / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x) = add x.value 1
consume {value: user_id {raw: 7}}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/row-inferred-consumer.yu
exit=0 elapsed=0.007228374481201172
stdout:

stderr:

```

## boundary-raw.json / row-inferred-consumer / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x) = add x.value 1
consume {value: user_id {raw: 7}}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/row-inferred-consumer.yu --poly
exit=0 elapsed=0.0073397159576416016
stdout:
roots d0:user_id d4:box d7:add d8:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
my d8:consume: {value: int} -> int = e10:(fn p1:d10:x -> e9:(e7:(e4:r1:add->d7:add e6:(e5:r2:x->d10:x.s1.value#field)) e8:1))
root exprs e17:(e11:r3:consume->d8:consume e16:{value: e15:(e12:r4:user_id->d0:user_id e14:{raw: e13:7})})
runtime roots e17:(e11:r3:consume->d8:consume e16:{value: e15:(e12:r4:user_id->d0:user_id e14:{raw: e13:7})})
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d9:x -> e1:(e0:r0:x->d9:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:x arg
  d10:x arg
}

stderr:

```

## boundary-raw.json / row-inferred-consumer / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x) = add x.value 1
consume {value: user_id {raw: 7}}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/row-inferred-consumer.yu
exit=0 elapsed=0.0030608177185058594
stdout:
run roots [8]

stderr:

```

## boundary-raw.json / row-inferred-control / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x) = add x.value 1
consume {value: 7}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/row-inferred-control.yu
exit=0 elapsed=0.0067479610443115234
stdout:

stderr:

```

## boundary-raw.json / row-inferred-control / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x) = add x.value 1
consume {value: 7}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/row-inferred-control.yu --poly
exit=0 elapsed=0.007358551025390625
stdout:
roots d0:user_id d4:box d7:add d8:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
my d8:consume: {value: int} -> int = e10:(fn p1:d10:x -> e9:(e7:(e4:r1:add->d7:add e6:(e5:r2:x->d10:x.s1.value#field)) e8:1))
root exprs e14:(e11:r3:consume->d8:consume e13:{value: e12:7})
runtime roots e14:(e11:r3:consume->d8:consume e13:{value: e12:7})
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d9:x -> e1:(e0:r0:x->d9:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:x arg
  d10:x arg
}

stderr:

```

## boundary-raw.json / row-inferred-control / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x) = add x.value 1
consume {value: 7}
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/row-inferred-control.yu
exit=0 elapsed=0.002786397933959961
stdout:
run roots [8]

stderr:

```

## boundary-raw.json / box-explicit-back / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my back(x: user_id): int = x
my convert(x: box user_id): box int = box {value: back x.value}
my consume(x: box int) = add x.value 1
consume (convert (box {value: user_id {raw: 7}}))
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-explicit-back.yu
exit=0 elapsed=0.017339468002319336
stdout:

stderr:

```

## boundary-raw.json / box-explicit-back / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my back(x: user_id): int = x
my convert(x: box user_id): box int = box {value: back x.value}
my consume(x: box int) = add x.value 1
consume (convert (box {value: user_id {raw: 7}}))
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-explicit-back.yu --poly
exit=0 elapsed=0.01782083511352539
stdout:
roots d0:user_id d4:box d7:add d8:back d9:convert d10:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
my d8:back: (int & user_id) -> int | user_id = e5:(fn p1:d12:x -> e4:r1:x->d12:x)
my d9:convert: box(user_id <: int & user_id) -> box(int | user_id <: int) = e13:(fn p2:d13:x -> e12:(e6:r2:box->d4:box e11:{value: e10:(e7:r3:back->d8:back e9:(e8:r4:x->d13:x.s1.value->d5))}))
my d10:consume: box int -> int = e20:(fn p3:d14:x -> e19:(e17:(e14:r5:add->d7:add e16:(e15:r6:x->d14:x.s2.value->d5)) e18:1))
root exprs e31:(e21:r7:consume->d10:consume e30:(e22:r8:convert->d9:convert e29:(e23:r9:box->d4:box e28:{value: e27:(e24:r10:user_id->d0:user_id e26:{raw: e25:7})})))
runtime roots e31:(e21:r7:consume->d10:consume e30:(e22:r8:convert->d9:convert e29:(e23:r9:box->d4:box e28:{value: e27:(e24:r10:user_id->d0:user_id e26:{raw: e25:7})})))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d11:x -> e1:(e0:r0:x->d11:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d11:x arg
  d12:x arg
  d13:x arg
  d14:x arg
}

stderr:

```

## boundary-raw.json / box-explicit-back / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my back(x: user_id): int = x
my convert(x: box user_id): box int = box {value: back x.value}
my consume(x: box int) = add x.value 1
consume (convert (box {value: user_id {raw: 7}}))
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-explicit-back.yu
exit=0 elapsed=0.004165172576904297
stdout:
run roots [8]

stderr:

```

## boundary-raw.json / box-explicit-cast / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
cast(x: box user_id): box int = box {value: x.value.raw}
my consume(x: box int) = add x.value 1
consume (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-explicit-cast.yu
exit=0 elapsed=0.012840509414672852
stdout:

stderr:

```

## boundary-raw.json / box-explicit-cast / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
cast(x: box user_id): box int = box {value: x.value.raw}
my consume(x: box int) = add x.value 1
consume (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-explicit-cast.yu --poly
exit=0 elapsed=0.01374197006225586
stdout:
roots d0:user_id d4:box d7:add d9:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
my d9:consume: box int -> int = e17:(fn p2:d12:x -> e16:(e14:(e11:r3:add->d7:add e13:(e12:r4:x->d12:x.s3.value->d5)) e15:1))
root exprs e26:(e18:r5:consume->d9:consume e25:(e19:r6:box->d4:box e24:{value: e23:(e20:r7:user_id->d0:user_id e22:{raw: e21:7})}))
runtime roots e26:(e18:r5:consume->d9:consume e25:(e19:r6:box->d4:box e24:{value: e23:(e20:r7:user_id->d0:user_id e22:{raw: e21:7})}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d10:x -> e1:(e0:r0:x->d10:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  my d8:"#cast": box user_id -> box int = e10:(fn p1:d11:x -> e9:(e4:r1:box->d4:box e8:{value: e7:(e6:(e5:r2:x->d11:x.s1.value->d5).s2.raw->d1)}))
  d10:x arg
  d11:x arg
  d12:x arg
}

stderr:

```

## boundary-raw.json / box-explicit-cast / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
cast(x: box user_id): box int = box {value: x.value.raw}
my consume(x: box int) = add x.value 1
consume (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-explicit-cast.yu
exit=1 elapsed=0.0038330554962158203
stdout:

stderr:
runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: non-int primitive argument
  hint: try the interpreter oracle or reduce this source to a smaller report

```

## boundary-raw.json / box-direct-projection-consumer / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: int) = add x 1
consume (box {value: user_id {raw: 7}}).value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-direct-projection-consumer.yu
exit=0 elapsed=0.012064218521118164
stdout:

stderr:

```

## boundary-raw.json / box-direct-projection-consumer / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: int) = add x 1
consume (box {value: user_id {raw: 7}}).value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-direct-projection-consumer.yu --poly
exit=0 elapsed=0.011344432830810547
stdout:
roots d0:user_id d4:box d7:add d8:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
my d8:consume: int -> int = e9:(fn p1:d10:x -> e8:(e6:(e4:r1:add->d7:add e5:r2:x->d10:x) e7:1))
root exprs e19:(e10:r3:consume->d8:consume e18:(e17:(e11:r4:box->d4:box e16:{value: e15:(e12:r5:user_id->d0:user_id e14:{raw: e13:7})}).s1.value->d5))
runtime roots e19:(e10:r3:consume->d8:consume e18:(e17:(e11:r4:box->d4:box e16:{value: e15:(e12:r5:user_id->d0:user_id e14:{raw: e13:7})}).s1.value->d5))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d9:x -> e1:(e0:r0:x->d9:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:x arg
  d10:x arg
}

stderr:

```

## boundary-raw.json / box-direct-projection-consumer / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: int) = add x 1
consume (box {value: user_id {raw: 7}}).value
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-direct-projection-consumer.yu
exit=1 elapsed=0.0036039352416992188
stdout:

stderr:
runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: non-int primitive argument
  hint: try the interpreter oracle or reduce this source to a smaller report

```

## boundary-raw.json / box-consumer-no-cast / check
```yu
struct user_id {raw: int}
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-consumer-no-cast.yu
exit=0 elapsed=0.00861048698425293
stdout:

stderr:

```

## boundary-raw.json / box-consumer-no-cast / dump
```yu
struct user_id {raw: int}
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-consumer-no-cast.yu --poly
exit=0 elapsed=0.0094757080078125
stdout:
roots d0:user_id d3:box d6:add d7:consume
d0:user_id: {raw: int} -> user_id = <missing>
d3:box: {value: 'a} -> box 'a = <missing>
my d6:add: int -> int -> int = e0:builtin_op::int_add
my d7:consume: box int -> int = e7:(fn p0:d8:x -> e6:(e4:(e1:r0:add->d6:add e3:(e2:r1:x->d8:x.s0.value->d4)) e5:1))
root exprs e16:(e8:r2:consume->d7:consume e15:(e9:r3:box->d3:box e14:{value: e13:(e10:r4:user_id->d0:user_id e12:{raw: e11:7})}))
runtime roots e16:(e8:r2:consume->d7:consume e15:(e9:r3:box->d3:box e14:{value: e13:(e10:r4:user_id->d0:user_id e12:{raw: e11:7})}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  d4: box 'a -> 'a = <missing>
  d5: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8:x arg
}

stderr:

```

## boundary-raw.json / box-consumer-no-cast / run
```yu
struct user_id {raw: int}
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-consumer-no-cast.yu
exit=1 elapsed=0.009432077407836914
stdout:

stderr:
conflicting type candidates: user_id vs int

```

## boundary-raw.json / direct-return-marker / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = 42
struct box 'a { value: 'a }
my back(x: user_id): int = x
back (user_id {raw: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/direct-return-marker.yu
exit=0 elapsed=0.006282806396484375
stdout:

stderr:

```

## boundary-raw.json / direct-return-marker / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = 42
struct box 'a { value: 'a }
my back(x: user_id): int = x
back (user_id {raw: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/direct-return-marker.yu --poly
exit=0 elapsed=0.00823664665222168
stdout:
roots d0:user_id d4:box d7:back
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:back: (int & user_id) -> int | user_id = e3:(fn p1:d9:x -> e2:r0:x->d9:x)
root exprs e9:(e4:r1:back->d7:back e8:(e5:r2:user_id->d0:user_id e7:{raw: e6:7}))
runtime roots e9:(e4:r1:back->d7:back e8:(e5:r2:user_id->d0:user_id e7:{raw: e6:7}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e1:(fn p0:d8:x -> e0:42)
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8:x arg
  d9:x arg
}

stderr:

```

## boundary-raw.json / direct-return-marker / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = 42
struct box 'a { value: 'a }
my back(x: user_id): int = x
back (user_id {raw: 7})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/direct-return-marker.yu
exit=0 elapsed=0.003421306610107422
stdout:
run roots [42]

stderr:

```

## boundary-raw.json / box-projection-marker / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = 42
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = x
add (widen (box {value: user_id {raw: 7}})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-projection-marker.yu
exit=0 elapsed=0.017165422439575195
stdout:

stderr:

```

## boundary-raw.json / box-projection-marker / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = 42
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = x
add (widen (box {value: user_id {raw: 7}})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-projection-marker.yu --poly
exit=0 elapsed=0.017313241958618164
stdout:
roots d0:user_id d4:box d7:add d8:widen
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e2:builtin_op::int_add
my d8:widen: box(int | user_id <: int & user_id) -> box(int | user_id <: int & user_id) = e4:(fn p1:d10:x -> e3:r0:x->d10:x)
root exprs e18:(e16:(e5:r1:add->d7:add e15:(e14:(e6:r2:widen->d8:widen e13:(e7:r3:box->d4:box e12:{value: e11:(e8:r4:user_id->d0:user_id e10:{raw: e9:7})})).s0.value->d5)) e17:1)
runtime roots e18:(e16:(e5:r1:add->d7:add e15:(e14:(e6:r2:widen->d8:widen e13:(e7:r3:box->d4:box e12:{value: e11:(e8:r4:user_id->d0:user_id e10:{raw: e9:7})})).s0.value->d5)) e17:1)
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e1:(fn p0:d9:x -> e0:42)
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:x arg
  d10:x arg
}

stderr:

```

## boundary-raw.json / box-projection-marker / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = 42
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my widen(x: box user_id): box int = x
add (widen (box {value: user_id {raw: 7}})).value 1
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-projection-marker.yu
exit=0 elapsed=0.004167318344116211
stdout:
run roots [43]

stderr:

```

## boundary-raw.json / box-consumer-marker / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = 42
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-consumer-marker.yu
exit=0 elapsed=0.009521484375
stdout:

stderr:

```

## boundary-raw.json / box-consumer-marker / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = 42
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-consumer-marker.yu --poly
exit=0 elapsed=0.010293006896972656
stdout:
roots d0:user_id d4:box d7:add d8:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e2:builtin_op::int_add
my d8:consume: box int -> int = e9:(fn p1:d10:x -> e8:(e6:(e3:r0:add->d7:add e5:(e4:r1:x->d10:x.s0.value->d5)) e7:1))
root exprs e18:(e10:r2:consume->d8:consume e17:(e11:r3:box->d4:box e16:{value: e15:(e12:r4:user_id->d0:user_id e14:{raw: e13:7})}))
runtime roots e18:(e10:r2:consume->d8:consume e17:(e11:r3:box->d4:box e16:{value: e15:(e12:r4:user_id->d0:user_id e14:{raw: e13:7})}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e1:(fn p0:d9:x -> e0:42)
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:x arg
  d10:x arg
}

stderr:

```

## boundary-raw.json / box-consumer-marker / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = 42
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my consume(x: box int) = add x.value 1
consume (box {value: user_id {raw: 7}})
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-consumer-marker.yu
exit=1 elapsed=0.003346681594848633
stdout:

stderr:
runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: non-int primitive argument
  hint: try the interpreter oracle or reduce this source to a smaller report

```

## fixed-raw.json / row-fixed-producer / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my make() = {value: user_id {raw: 7}}
my consume(x) = add x.value 1
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/row-fixed-producer.yu
exit=0 elapsed=0.008728504180908203
stdout:

stderr:

```

## fixed-raw.json / row-fixed-producer / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my make() = {value: user_id {raw: 7}}
my consume(x) = add x.value 1
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/row-fixed-producer.yu --poly
exit=0 elapsed=0.007689952850341797
stdout:
roots d0:user_id d4:box d7:add d8:make d9:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
my d8:make: () -> {value: user_id} = e9:(fn p1:() -> e8:{value: e7:(e4:r1:user_id->d0:user_id e6:{raw: e5:7})})
my d9:consume: {value: int} -> int = e16:(fn p2:d11:x -> e15:(e13:(e10:r2:add->d7:add e12:(e11:r3:x->d11:x.s1.value#field)) e14:1))
root exprs e21:(e17:r4:consume->d9:consume e20:(e18:r5:make->d8:make e19:()))
runtime roots e21:(e17:r4:consume->d9:consume e20:(e18:r5:make->d8:make e19:()))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d10:x -> e1:(e0:r0:x->d10:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d10:x arg
  d11:x arg
}

stderr:

```

## fixed-raw.json / row-fixed-producer / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my make() = {value: user_id {raw: 7}}
my consume(x) = add x.value 1
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/row-fixed-producer.yu
exit=1 elapsed=0.0031604766845703125
stdout:

stderr:
runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: non-int primitive argument
  hint: try the interpreter oracle or reduce this source to a smaller report

```

## fixed-raw.json / row-fixed-marker / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = 42
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my make() = {value: user_id {raw: 7}}
my consume(x) = add x.value 1
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/row-fixed-marker.yu
exit=0 elapsed=0.006461143493652344
stdout:

stderr:

```

## fixed-raw.json / row-fixed-marker / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = 42
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my make() = {value: user_id {raw: 7}}
my consume(x) = add x.value 1
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/row-fixed-marker.yu --poly
exit=0 elapsed=0.00684809684753418
stdout:
roots d0:user_id d4:box d7:add d8:make d9:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e2:builtin_op::int_add
my d8:make: () -> {value: user_id} = e8:(fn p1:() -> e7:{value: e6:(e3:r0:user_id->d0:user_id e5:{raw: e4:7})})
my d9:consume: {value: int} -> int = e15:(fn p2:d11:x -> e14:(e12:(e9:r1:add->d7:add e11:(e10:r2:x->d11:x.s0.value#field)) e13:1))
root exprs e20:(e16:r3:consume->d9:consume e19:(e17:r4:make->d8:make e18:()))
runtime roots e20:(e16:r3:consume->d9:consume e19:(e17:r4:make->d8:make e18:()))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e1:(fn p0:d10:x -> e0:42)
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d10:x arg
  d11:x arg
}

stderr:

```

## fixed-raw.json / row-fixed-marker / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = 42
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
my make() = {value: user_id {raw: 7}}
my consume(x) = add x.value 1
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/row-fixed-marker.yu
exit=1 elapsed=0.003865480422973633
stdout:

stderr:
runtime error [yulang.unsupported-runtime-feature]: unsupported expression in runtime: non-int primitive argument
  hint: try the interpreter oracle or reduce this source to a smaller report

```

## fixed-raw.json / box-producer-bare / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my make(): box user_id = box {value: user_id {raw: 7}}
make()
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-producer-bare.yu
exit=0 elapsed=0.00910496711730957
stdout:

stderr:

```

## fixed-raw.json / box-producer-bare / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my make(): box user_id = box {value: user_id {raw: 7}}
make()
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-producer-bare.yu --poly
exit=0 elapsed=0.008026361465454102
stdout:
roots d0:user_id d4:box d7:make
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:make: () -> box user_id = e10:(fn p1:() -> e9:(e3:r1:box->d4:box e8:{value: e7:(e4:r2:user_id->d0:user_id e6:{raw: e5:7})}))
root exprs e13:(e11:r3:make->d7:make e12:())
runtime roots e13:(e11:r3:make->d7:make e12:())
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8:x arg
}

stderr:

```

## fixed-raw.json / box-producer-bare / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my make(): box user_id = box {value: user_id {raw: 7}}
make()
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-producer-bare.yu
exit=0 elapsed=0.004347562789916992
stdout:
run roots [box({value: user_id({raw: 7})})]

stderr:

```

## fixed-raw.json / box-fixed-consumer-identity / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my make(): box user_id = box {value: user_id {raw: 7}}
my consume(x: box int) = x
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-fixed-consumer-identity.yu
exit=0 elapsed=0.011517763137817383
stdout:

stderr:

```

## fixed-raw.json / box-fixed-consumer-identity / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my make(): box user_id = box {value: user_id {raw: 7}}
my consume(x: box int) = x
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-fixed-consumer-identity.yu --poly
exit=0 elapsed=0.00881505012512207
stdout:
roots d0:user_id d4:box d7:make d8:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:make: () -> box user_id = e10:(fn p1:() -> e9:(e3:r1:box->d4:box e8:{value: e7:(e4:r2:user_id->d0:user_id e6:{raw: e5:7})}))
my d8:consume: box int -> box int = e12:(fn p2:d10:x -> e11:r3:x->d10:x)
root exprs e17:(e13:r4:consume->d8:consume e16:(e14:r5:make->d7:make e15:()))
runtime roots e17:(e13:r4:consume->d8:consume e16:(e14:r5:make->d7:make e15:()))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d9:x -> e1:(e0:r0:x->d9:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:x arg
  d10:x arg
}

stderr:

```

## fixed-raw.json / box-fixed-consumer-identity / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my make(): box user_id = box {value: user_id {raw: 7}}
my consume(x: box int) = x
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-fixed-consumer-identity.yu
exit=1 elapsed=0.008765459060668945
stdout:

stderr:
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: box(user_id) <: box(int)
  hint: check that the value provides the fields or shape required by this use

```

## fixed-raw.json / box-fixed-outer-rule / check
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
cast(x: box user_id): box int = box {value: x.value.raw}
my make(): box user_id = box {value: user_id {raw: 7}}
my consume(x: box int) = add x.value 1
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-cast-more/box-fixed-outer-rule.yu
exit=0 elapsed=0.014573097229003906
stdout:

stderr:

```

## fixed-raw.json / box-fixed-outer-rule / dump
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
cast(x: box user_id): box int = box {value: x.value.raw}
my make(): box user_id = box {value: user_id {raw: 7}}
my consume(x: box int) = add x.value 1
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-cast-more/box-fixed-outer-rule.yu --poly
exit=0 elapsed=0.01581573486328125
stdout:
roots d0:user_id d4:box d7:add d9:make d10:consume
d0:user_id: {raw: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:add: int -> int -> int = e3:builtin_op::int_add
my d9:make: () -> box user_id = e18:(fn p2:() -> e17:(e11:r3:box->d4:box e16:{value: e15:(e12:r4:user_id->d0:user_id e14:{raw: e13:7})}))
my d10:consume: box int -> int = e25:(fn p3:d13:x -> e24:(e22:(e19:r5:add->d7:add e21:(e20:r6:x->d13:x.s3.value->d5)) e23:1))
root exprs e30:(e26:r7:consume->d10:consume e29:(e27:r8:make->d9:make e28:()))
runtime roots e30:(e26:r7:consume->d10:consume e29:(e27:r8:make->d9:make e28:()))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d11:x -> e1:(e0:r0:x->d11:x.s0.raw->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  my d8:"#cast": box user_id -> box int = e10:(fn p1:d12:x -> e9:(e4:r1:box->d4:box e8:{value: e7:(e6:(e5:r2:x->d12:x.s1.value->d5).s2.raw->d1)}))
  d11:x arg
  d12:x arg
  d13:x arg
}

stderr:

```

## fixed-raw.json / box-fixed-outer-rule / run
```yu
struct user_id {raw: int}
cast(x: user_id): int = x.raw
struct box 'a { value: 'a }
my add: int -> int -> int = builtin_op::int_add
cast(x: box user_id): box int = box {value: x.value.raw}
my make(): box user_id = box {value: user_id {raw: 7}}
my consume(x: box int) = add x.value 1
consume (make())
```
```text
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-cast-more/box-fixed-outer-rule.yu
exit=1 elapsed=0.018255949020385742
stdout:

stderr:
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: box(user_id) <: box(int)
  hint: check that the value provides the fields or shape required by this use

```

## Existing ordinary cast characterization suite (bounded)

Command: target/debug/deps/infer-dfea53230aacf9c4 ordinary_cast_characterization --nocapture --test-threads=1

Start: 2026-11-08T13:02:26.591179+00:00; elapsed: 240.20651626299878 s; exit: none (external timeout240s)

```text

running 25 tests
test analysis::tests::ordinary_cast_characterization::cached_prefix_seed_preserves_cast_table_and_poly_rule_cardinality ... ok
test analysis::tests::ordinary_cast_characterization::cached_prefix_seed_retains_defs_without_changing_schemes ... ok
test analysis::tests::ordinary_cast_characterization::compact_cast_discovery_treats_one_and_two_candidates_as_the_same_present_pair ... ok
test analysis::tests::ordinary_cast_characterization::direct_and_compact_shadow_observations_match_the_ocast_a_oracle ... ok
test analysis::tests::ordinary_cast_characterization::direct_nominal_cast_event_applies_zero_one_or_every_visible_candidate ... ok
test analysis::tests::ordinary_cast_characterization::disjoint_looking_same_pair_schemes_are_both_applied_today ... ok
test analysis::tests::ordinary_cast_characterization::duplicated_imported_registry_entry_is_currently_counted_twice ... ok
test analysis::tests::ordinary_cast_characterization::infer_adapter_preserves_raw_cardinality_for_ocast_a_ambiguous_edge_fixtures ... ok
test analysis::tests::ordinary_cast_characterization::prefix_seeded_infer_and_poly_classification_match_the_ocast_a_oracle ... ok
test analysis::tests::ordinary_cast_characterization::repeated_identical_nominal_subtype_constraint_emits_only_one_current_cast_event ... ok
test lowering::tests::ordinary_cast_characterization::cprov_i_source_paths_require_complete_origins_and_coherent_ownership ... ok
test lowering::tests::ordinary_cast_characterization::live_application_cast_diagnostics_follow_zero_one_two_cardinality ... ok
test lowering::tests::ordinary_cast_characterization::missing_boundary_shadow_observation_matches_the_ocast_a_oracle ... ok
test lowering::tests::ordinary_cast_characterization::missing_cast_explanation_reaches_unannotated_parameter_boolean_condition ... ok
test lowering::tests::ordinary_cast_characterization::missing_ordinary_cast_function_result_and_struct_field_reject ... ok
test lowering::tests::ordinary_cast_characterization::repository_std_infer_and_poly_classification_are_unique ... 
[runner timeout240s; no test executable exit code]

```
