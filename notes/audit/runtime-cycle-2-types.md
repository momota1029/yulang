# X13–X21 原出力

## 1. x18-box

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
widen (box {value: user_id 7})
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x18-box.yu`

Exit: 1; seconds: 0.007244

```text
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

```

## 2. x18-box

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
widen (box {value: user_id 7})
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x18-box.yu --poly`

Exit: 0; seconds: 0.007310

```text
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
error: type shape `user_id` is not compatible with required shape `function`

```

## 3. x18-box

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
widen (box {value: user_id 7})
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x18-box.yu`

Exit: 1; seconds: 0.007062

```text
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## 4. x18-box2

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
struct box2 'a { value: box (box 'a) }
my widen(x: box2 user_id): box2 int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x18-box2.yu`

Exit: 1; seconds: 0.004500

```text
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

```

## 5. x18-box2

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
struct box2 'a { value: box (box 'a) }
my widen(x: box2 user_id): box2 int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x18-box2.yu --poly`

Exit: 0; seconds: 0.005159

```text
roots d0:user_id d2:box d5:box2 d8:widen
d0:user_id: int -> user_id = <missing>
d2:box: {value: 'a} -> box 'a = <missing>
d5:box2: {value: box(box 'a)} -> box2 'a = <missing>
my d8:widen: box2(int | user_id <: int & user_id) -> box2(int | user_id <: int & user_id) = e5:(fn p1:d10:x -> e4:r1:x->d10:x)
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d9:x -> e2:(e0:r0:x->d9:x e1:0.0))
  d3: box 'a -> 'a = <missing>
  d4: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d6: box2 'a -> box(box 'a) = <missing>
  d7: std::control::var::ref('a, box2 'b) -> std::control::var::ref 'a box(box 'b) = <missing>
  d9:x arg
  d10:x arg
}
error: type shape `user_id` is not compatible with required shape `function`

```

## 6. x18-box2

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
struct box 'a { value: 'a }
struct box2 'a { value: box (box 'a) }
my widen(x: box2 user_id): box2 int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x18-box2.yu`

Exit: 1; seconds: 0.005912

```text
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## 7. x18-reset

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
enum reset 'a:
    value 'a
    next (reset int)
my widen(x: reset user_id): reset int = x
widen (reset::value (user_id 7))
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x18-reset.yu`

Exit: 1; seconds: 0.005511

```text
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

```

## 8. x18-reset

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
enum reset 'a:
    value 'a
    next (reset int)
my widen(x: reset user_id): reset int = x
widen (reset::value (user_id 7))
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x18-reset.yu --poly`

Exit: 0; seconds: 0.005708

```text
roots d0:user_id d2:reset d5:widen
d0:user_id: int -> user_id = <missing>
d2:reset mod {
  d3:"reset.value": 'a -> reset 'a = <missing>
  d4:"reset.next": reset int -> reset 'a = <missing>
}
my d5:widen: reset(int | user_id <: int & user_id) -> reset(int | user_id <: int & user_id) = e5:(fn p1:d7:x -> e4:r1:x->d7:x)
root exprs e12:(e6:r2:widen->d5:widen e11:(e7:r3:"reset::value"->d3:"reset.value" e10:(e8:r4:user_id->d0:user_id e9:7)))
runtime roots e12:(e6:r2:widen->d5:widen e11:(e7:r3:"reset::value"->d3:"reset.value" e10:(e8:r4:user_id->d0:user_id e9:7)))
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d6:x -> e2:(e0:r0:x->d6:x e1:0.0))
  d6:x arg
  d7:x arg
}
error: type shape `user_id` is not compatible with required shape `function`

```

## 9. x18-reset

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
enum reset 'a:
    value 'a
    next (reset int)
my widen(x: reset user_id): reset int = x
widen (reset::value (user_id 7))
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x18-reset.yu`

Exit: 1; seconds: 0.006161

```text
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## 10. x18-stream

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
struct stream 'a { next: () -> ('a, stream 'a) }
my widen(x: stream user_id): stream int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x18-stream.yu`

Exit: 1; seconds: 0.004184

```text
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

```

## 11. x18-stream

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
struct stream 'a { next: () -> ('a, stream 'a) }
my widen(x: stream user_id): stream int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x18-stream.yu --poly`

Exit: 0; seconds: 0.005284

```text
roots d0:user_id d2:stream d5:widen
d0:user_id: int -> user_id = <missing>
d2:stream: {next: () -> ('a, stream 'a)} -> stream 'a = <missing>
my d5:widen: stream(int | user_id <: int & user_id) -> stream(int | user_id <: int & user_id) = e5:(fn p1:d7:x -> e4:r1:x->d7:x)
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d6:x -> e2:(e0:r0:x->d6:x e1:0.0))
  d3: stream 'a -> () -> ('a, stream 'a) = <missing>
  d4: std::control::var::ref('a, stream 'b) -> std::control::var::ref('a, () ['[]] -> ['[]] ('b, stream 'b)) = <missing>
  d6:x arg
  d7:x arg
}
error: type shape `user_id` is not compatible with required shape `function`

```

## 12. x18-stream

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
struct stream 'a { next: () -> ('a, stream 'a) }
my widen(x: stream user_id): stream int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x18-stream.yu`

Exit: 1; seconds: 0.006557

```text
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## 13. x19-chain

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
enum chain 'a:
    end
    link 'a (chain 'a)
my widen(x: chain user_id): chain int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x19-chain.yu`

Exit: 1; seconds: 0.005387

```text
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

```

## 14. x19-chain

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
enum chain 'a:
    end
    link 'a (chain 'a)
my widen(x: chain user_id): chain int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x19-chain.yu --poly`

Exit: 0; seconds: 0.004936

```text
roots d0:user_id d2:chain d5:widen
d0:user_id: int -> user_id = <missing>
d2:chain mod {
  d3:"chain.end": chain 'a = <missing>
  d4:"chain.link": 'a -> chain 'a -> chain 'a = <missing>
}
my d5:widen: chain(int | user_id <: int & user_id) -> chain(int | user_id <: int & user_id) = e5:(fn p1:d7:x -> e4:r1:x->d7:x)
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d6:x -> e2:(e0:r0:x->d6:x e1:0.0))
  d6:x arg
  d7:x arg
}
error: type shape `user_id` is not compatible with required shape `function`

```

## 15. x19-chain

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
enum chain 'a:
    end
    link 'a (chain 'a)
my widen(x: chain user_id): chain int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x19-chain.yu`

Exit: 1; seconds: 0.005090

```text
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## 16. x19-mutual

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
enum left 'a:
    value 'a
    next (right 'a)
enum right 'a:
    next (left 'a)
my widen(x: left user_id): left int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x19-mutual.yu`

Exit: 1; seconds: 0.004397

```text
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

```

## 17. x19-mutual

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
enum left 'a:
    value 'a
    next (right 'a)
enum right 'a:
    next (left 'a)
my widen(x: left user_id): left int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x19-mutual.yu --poly`

Exit: 0; seconds: 0.004618

```text
roots d0:user_id d2:left d5:right d7:widen
d0:user_id: int -> user_id = <missing>
d2:left mod {
  d3:"left.value": 'a -> left 'a = <missing>
  d4:"left.next": right 'a -> left 'a = <missing>
}
d5:right mod {
  d6:"right.next": left 'a -> right 'a = <missing>
}
my d7:widen: left(int | user_id <: int & user_id) -> left(int | user_id <: int & user_id) = e5:(fn p1:d9:x -> e4:r1:x->d9:x)
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d8:x -> e2:(e0:r0:x->d8:x e1:0.0))
  d8:x arg
  d9:x arg
}
error: type shape `user_id` is not compatible with required shape `function`

```

## 18. x19-mutual

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
enum left 'a:
    value 'a
    next (right 'a)
enum right 'a:
    next (left 'a)
my widen(x: left user_id): left int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x19-mutual.yu`

Exit: 1; seconds: 0.006026

```text
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## 19. x20-phantom

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
enum phantom 'a:
    end
    next (phantom 'a)
my retag(x: phantom user_id): phantom int = x
retag phantom::end
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x20-phantom.yu`

Exit: 1; seconds: 0.005036

```text
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

```

## 20. x20-phantom

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
enum phantom 'a:
    end
    next (phantom 'a)
my retag(x: phantom user_id): phantom int = x
retag phantom::end
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x20-phantom.yu --poly`

Exit: 0; seconds: 0.007656

```text
roots d0:user_id d2:phantom d5:retag
d0:user_id: int -> user_id = <missing>
d2:phantom mod {
  d3:"phantom.end": phantom 'a = <missing>
  d4:"phantom.next": phantom 'a -> phantom 'a = <missing>
}
my d5:retag: phantom(int | user_id <: int & user_id) -> phantom(int | user_id <: int & user_id) = e5:(fn p1:d7:x -> e4:r1:x->d7:x)
root exprs e8:(e6:r2:retag->d5:retag e7:r3:"phantom::end"->d3:"phantom.end")
runtime roots e8:(e6:r2:retag->d5:retag e7:r3:"phantom::end"->d3:"phantom.end")
detached {
  my d1:"#cast": (user_id & (float -> ['a] int)) -> ['a] int = e3:(fn p0:d6:x -> e2:(e0:r0:x->d6:x e1:0.0))
  d6:x arg
  d7:x arg
}
error: type shape `user_id` is not compatible with required shape `function`

```

## 21. x20-phantom

```yulang
struct user_id(int)
cast(x: user_id): int = x.0
enum phantom 'a:
    end
    next (phantom 'a)
my retag(x: phantom user_id): phantom int = x
retag phantom::end
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x20-phantom.yu`

Exit: 1; seconds: 0.006162

```text
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `user_id` is not compatible with required shape `function`
  hint: run `yulang check` to see source ranges before running

```

## 22. x18-box-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
widen (box {value: user_id { value: 7 }})
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x18-box-record.yu`

Exit: 0; seconds: 0.008227

```text

```

## 23. x18-box-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
widen (box {value: user_id { value: 7 }})
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x18-box-record.yu --poly`

Exit: 0; seconds: 0.007563

```text
roots d0:user_id d4:box d7:widen
d0:user_id: {value: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:widen: box(int | user_id <: int & user_id) -> box(int | user_id <: int & user_id) = e4:(fn p1:d9:x -> e3:r1:x->d9:x)
root exprs e13:(e5:r2:widen->d7:widen e12:(e6:r3:box->d4:box e11:{value: e10:(e7:r4:user_id->d0:user_id e9:{value: e8:7})}))
runtime roots e13:(e5:r2:widen->d7:widen e12:(e6:r3:box->d4:box e11:{value: e10:(e7:r4:user_id->d0:user_id e9:{value: e8:7})}))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.value->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8:x arg
  d9:x arg
}

```

## 24. x18-box-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
struct box 'a { value: 'a }
my widen(x: box user_id): box int = x
widen (box {value: user_id { value: 7 }})
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x18-box-record.yu`

Exit: 0; seconds: 0.003688

```text

```

## 25. x18-box2-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
struct box 'a { value: 'a }
struct box2 'a { value: box (box 'a) }
my widen(x: box2 user_id): box2 int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x18-box2-record.yu`

Exit: 0; seconds: 0.005017

```text

```

## 26. x18-box2-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
struct box 'a { value: 'a }
struct box2 'a { value: box (box 'a) }
my widen(x: box2 user_id): box2 int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x18-box2-record.yu --poly`

Exit: 0; seconds: 0.005889

```text
roots d0:user_id d4:box d7:box2 d10:widen
d0:user_id: {value: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
d7:box2: {value: box(box 'a)} -> box2 'a = <missing>
my d10:widen: box2(int | user_id <: int & user_id) -> box2(int | user_id <: int & user_id) = e4:(fn p1:d12:x -> e3:r1:x->d12:x)
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d11:x -> e1:(e0:r0:x->d11:x.s0.value->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d8: box2 'a -> box(box 'a) = <missing>
  d9: std::control::var::ref('a, box2 'b) -> std::control::var::ref 'a box(box 'b) = <missing>
  d11:x arg
  d12:x arg
}

```

## 27. x18-box2-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
struct box 'a { value: 'a }
struct box2 'a { value: box (box 'a) }
my widen(x: box2 user_id): box2 int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x18-box2-record.yu`

Exit: 0; seconds: 0.002631

```text

```

## 28. x18-reset-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum reset 'a:
    value 'a
    next (reset int)
my widen(x: reset user_id): reset int = x
widen (reset::value (user_id { value: 7 }))
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x18-reset-record.yu`

Exit: 0; seconds: 0.006189

```text

```

## 29. x18-reset-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum reset 'a:
    value 'a
    next (reset int)
my widen(x: reset user_id): reset int = x
widen (reset::value (user_id { value: 7 }))
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x18-reset-record.yu --poly`

Exit: 0; seconds: 0.006400

```text
roots d0:user_id d4:reset d7:widen
d0:user_id: {value: int} -> user_id = <missing>
d4:reset mod {
  d5:"reset.value": 'a -> reset 'a = <missing>
  d6:"reset.next": reset int -> reset 'a = <missing>
}
my d7:widen: reset(int | user_id <: int & user_id) -> reset(int | user_id <: int & user_id) = e4:(fn p1:d9:x -> e3:r1:x->d9:x)
root exprs e12:(e5:r2:widen->d7:widen e11:(e6:r3:"reset::value"->d5:"reset.value" e10:(e7:r4:user_id->d0:user_id e9:{value: e8:7})))
runtime roots e12:(e5:r2:widen->d7:widen e11:(e6:r3:"reset::value"->d5:"reset.value" e10:(e7:r4:user_id->d0:user_id e9:{value: e8:7})))
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.value->d1))
  d8:x arg
  d9:x arg
}

```

## 30. x18-reset-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum reset 'a:
    value 'a
    next (reset int)
my widen(x: reset user_id): reset int = x
widen (reset::value (user_id { value: 7 }))
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x18-reset-record.yu`

Exit: 0; seconds: 0.004048

```text

```

## 31. x18-stream-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
struct stream 'a { next: () -> ('a, stream 'a) }
my widen(x: stream user_id): stream int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x18-stream-record.yu`

Exit: 0; seconds: 0.005959

```text

```

## 32. x18-stream-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
struct stream 'a { next: () -> ('a, stream 'a) }
my widen(x: stream user_id): stream int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x18-stream-record.yu --poly`

Exit: 0; seconds: 0.008189

```text
roots d0:user_id d4:stream d7:widen
d0:user_id: {value: int} -> user_id = <missing>
d4:stream: {next: () -> ('a, stream 'a)} -> stream 'a = <missing>
my d7:widen: stream(int | user_id <: int & user_id) -> stream(int | user_id <: int & user_id) = e4:(fn p1:d9:x -> e3:r1:x->d9:x)
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.value->d1))
  d5: stream 'a -> () -> ('a, stream 'a) = <missing>
  d6: std::control::var::ref('a, stream 'b) -> std::control::var::ref('a, () ['[]] -> ['[]] ('b, stream 'b)) = <missing>
  d8:x arg
  d9:x arg
}

```

## 33. x18-stream-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
struct stream 'a { next: () -> ('a, stream 'a) }
my widen(x: stream user_id): stream int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x18-stream-record.yu`

Exit: 0; seconds: 0.003310

```text

```

## 34. x19-chain-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum chain 'a:
    end
    link 'a (chain 'a)
my widen(x: chain user_id): chain int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x19-chain-record.yu`

Exit: 0; seconds: 0.005524

```text

```

## 35. x19-chain-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum chain 'a:
    end
    link 'a (chain 'a)
my widen(x: chain user_id): chain int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x19-chain-record.yu --poly`

Exit: 0; seconds: 0.006278

```text
roots d0:user_id d4:chain d7:widen
d0:user_id: {value: int} -> user_id = <missing>
d4:chain mod {
  d5:"chain.end": chain 'a = <missing>
  d6:"chain.link": 'a -> chain 'a -> chain 'a = <missing>
}
my d7:widen: chain(int | user_id <: int & user_id) -> chain(int | user_id <: int & user_id) = e4:(fn p1:d9:x -> e3:r1:x->d9:x)
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.value->d1))
  d8:x arg
  d9:x arg
}

```

## 36. x19-chain-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum chain 'a:
    end
    link 'a (chain 'a)
my widen(x: chain user_id): chain int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x19-chain-record.yu`

Exit: 0; seconds: 0.002748

```text

```

## 37. x19-mutual-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum left 'a:
    value 'a
    next (right 'a)
enum right 'a:
    next (left 'a)
my widen(x: left user_id): left int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x19-mutual-record.yu`

Exit: 0; seconds: 0.005672

```text

```

## 38. x19-mutual-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum left 'a:
    value 'a
    next (right 'a)
enum right 'a:
    next (left 'a)
my widen(x: left user_id): left int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x19-mutual-record.yu --poly`

Exit: 0; seconds: 0.005304

```text
roots d0:user_id d4:left d7:right d9:widen
d0:user_id: {value: int} -> user_id = <missing>
d4:left mod {
  d5:"left.value": 'a -> left 'a = <missing>
  d6:"left.next": right 'a -> left 'a = <missing>
}
d7:right mod {
  d8:"right.next": left 'a -> right 'a = <missing>
}
my d9:widen: left(int | user_id <: int & user_id) -> left(int | user_id <: int & user_id) = e4:(fn p1:d11:x -> e3:r1:x->d11:x)
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d10:x -> e1:(e0:r0:x->d10:x.s0.value->d1))
  d10:x arg
  d11:x arg
}

```

## 39. x19-mutual-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum left 'a:
    value 'a
    next (right 'a)
enum right 'a:
    next (left 'a)
my widen(x: left user_id): left int = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x19-mutual-record.yu`

Exit: 0; seconds: 0.003109

```text

```

## 40. x20-phantom-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum phantom 'a:
    end
    next (phantom 'a)
my retag(x: phantom user_id): phantom int = x
retag phantom::end
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x20-phantom-record.yu`

Exit: 0; seconds: 0.005390

```text

```

## 41. x20-phantom-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum phantom 'a:
    end
    next (phantom 'a)
my retag(x: phantom user_id): phantom int = x
retag phantom::end
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x20-phantom-record.yu --poly`

Exit: 0; seconds: 0.006063

```text
roots d0:user_id d4:phantom d7:retag
d0:user_id: {value: int} -> user_id = <missing>
d4:phantom mod {
  d5:"phantom.end": phantom 'a = <missing>
  d6:"phantom.next": phantom 'a -> phantom 'a = <missing>
}
my d7:retag: phantom(int | user_id <: int & user_id) -> phantom(int | user_id <: int & user_id) = e4:(fn p1:d9:x -> e3:r1:x->d9:x)
root exprs e7:(e5:r2:retag->d7:retag e6:r3:"phantom::end"->d5:"phantom.end")
runtime roots e7:(e5:r2:retag->d7:retag e6:r3:"phantom::end"->d5:"phantom.end")
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d8:x -> e1:(e0:r0:x->d8:x.s0.value->d1))
  d8:x arg
  d9:x arg
}

```

## 42. x20-phantom-record

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum phantom 'a:
    end
    next (phantom 'a)
my retag(x: phantom user_id): phantom int = x
retag phantom::end
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run /tmp/audit2-types/x20-phantom-record.yu`

Exit: 0; seconds: 0.002871

```text

```

## 43. x18-box-frozen

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
struct box 'a { value: 'a }
my a: box user_id = box {value: user_id {value: 7}}
my b: box int = a
b.value
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x18-box-frozen.yu`

Exit: 0; seconds: 0.007913

```text

```

## 44. x18-box-frozen

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
struct box 'a { value: 'a }
my a: box user_id = box {value: user_id {value: 7}}
my b: box int = a
b.value
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x18-box-frozen.yu --poly`

Exit: 0; seconds: 0.006390

```text
roots d0:user_id d4:box d7:a d8:b
d0:user_id: {value: int} -> user_id = <missing>
d4:box: {value: 'a} -> box 'a = <missing>
my d7:a: box user_id = e9:(e3:r1:box->d4:box e8:{value: e7:(e4:r2:user_id->d0:user_id e6:{value: e5:7})})
my d8:b: box int = e10:r3:a->d7:a
root exprs e12:(e11:r4:b->d8:b.s1.value->d5)
runtime roots d7:a e12:(e11:r4:b->d8:b.s1.value->d5)
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d9:x -> e1:(e0:r0:x->d9:x.s0.value->d1))
  d5: box 'a -> 'a = <missing>
  d6: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d9:x arg
}

```

## 45. x18-box-frozen

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
struct box 'a { value: 'a }
my a: box user_id = box {value: user_id {value: 7}}
my b: box int = a
b.value
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x18-box-frozen.yu`

Exit: 0; seconds: 0.003382

```text
run roots [user_id({value: 7})]

```

## 46. x19-chain-frozen

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum chain 'a:
    end
    link 'a (chain 'a)
my a: chain user_id = chain::link (user_id {value: 7}) chain::end
my b: chain int = a
b
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x19-chain-frozen.yu`

Exit: 0; seconds: 0.005657

```text

```

## 47. x19-chain-frozen

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum chain 'a:
    end
    link 'a (chain 'a)
my a: chain user_id = chain::link (user_id {value: 7}) chain::end
my b: chain int = a
b
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x19-chain-frozen.yu --poly`

Exit: 0; seconds: 0.006128

```text
roots d0:user_id d4:chain d7:a d8:b
d0:user_id: {value: int} -> user_id = <missing>
d4:chain mod {
  d5:"chain.end": chain 'a = <missing>
  d6:"chain.link": 'a -> chain 'a -> chain 'a = <missing>
}
my d7:a: chain user_id = e10:(e8:(e3:r1:"chain::link"->d6:"chain.link" e7:(e4:r2:user_id->d0:user_id e6:{value: e5:7})) e9:r3:"chain::end"->d5:"chain.end")
my d8:b: chain int = e11:r4:a->d7:a
root exprs e12:r5:b->d8:b
runtime roots d7:a e12:r5:b->d8:b
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d9:x -> e1:(e0:r0:x->d9:x.s0.value->d1))
  d9:x arg
}

```

## 48. x19-chain-frozen

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum chain 'a:
    end
    link 'a (chain 'a)
my a: chain user_id = chain::link (user_id {value: 7}) chain::end
my b: chain int = a
b
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x19-chain-frozen.yu`

Exit: 0; seconds: 0.003295

```text
run roots [chain::link(7, chain::end)]

```

## 49. x20-phantom-frozen

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom user_id = phantom::end
my b: phantom int = a
b
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x20-phantom-frozen.yu`

Exit: 0; seconds: 0.004425

```text

```

## 50. x20-phantom-frozen

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom user_id = phantom::end
my b: phantom int = a
b
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x20-phantom-frozen.yu --poly`

Exit: 0; seconds: 0.005192

```text
roots d0:user_id d4:phantom d7:a d8:b
d0:user_id: {value: int} -> user_id = <missing>
d4:phantom mod {
  d5:"phantom.end": phantom 'a = <missing>
  d6:"phantom.next": phantom 'a -> phantom 'a = <missing>
}
my d7:a: phantom user_id = e3:r1:"phantom::end"->d5:"phantom.end"
my d8:b: phantom int = e4:r2:a->d7:a
root exprs e5:r3:b->d8:b
runtime roots e5:r3:b->d8:b
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d9:x -> e1:(e0:r0:x->d9:x.s0.value->d1))
  d9:x arg
}

```

## 51. x20-phantom-frozen

```yulang
struct user_id { value: int }
cast(x: user_id): int = x.value
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom user_id = phantom::end
my b: phantom int = a
b
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x20-phantom-frozen.yu`

Exit: 0; seconds: 0.002797

```text
run roots [phantom::end]

```

## 52. x21-polyfield

```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> x}
(h.run 1, h.run "x")
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x21-polyfield.yu`

Exit: 0; seconds: 0.004495

```text

```

## 53. x21-polyfield

```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> x}
(h.run 1, h.run "x")
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x21-polyfield.yu --poly`

Exit: 0; seconds: 0.007217

```text
roots d0:holder d3:h
d0:holder: {run: 'a -> 'a} -> holder = <missing>
my d3:h: holder = e4:(e0:r0:holder->d0:holder e3:{run: e2:(fn p0:d4:x -> e1:r1:x->d4:x)})
root exprs e13:(e8:(e6:(e5:r2:h->d3:h.s0.run->d1) e7:1), e12:(e10:(e9:r3:h->d3:h.s1.run->d1) e11:"x"))
runtime roots d3:h e13:(e8:(e6:(e5:r2:h->d3:h.s0.run->d1) e7:1), e12:(e10:(e9:r3:h->d3:h.s1.run->d1) e11:"x"))
detached {
  d1: holder -> 'a -> 'a = <missing>
  d2: std::control::var::ref 'a holder -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  d4:x arg
}

```

## 54. x21-polyfield

```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> x}
(h.run 1, h.run "x")
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x21-polyfield.yu`

Exit: 0; seconds: 0.003552

```text
run roots [(1, "x")]

```

## 55. x21-rigidbad

```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> 1}
h.run "x"
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x21-rigidbad.yu`

Exit: 0; seconds: 0.004718

```text

```

## 56. x21-rigidbad

```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> 1}
h.run "x"
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x21-rigidbad.yu --poly`

Exit: 0; seconds: 0.005583

```text
roots d0:holder d3:h
d0:holder: {run: 'a -> 'a} -> holder = <missing>
my d3:h: holder = e4:(e0:r0:holder->d0:holder e3:{run: e2:(fn p0:d4:x -> e1:1)})
root exprs e8:(e6:(e5:r1:h->d3:h.s0.run->d1) e7:"x")
runtime roots d3:h e8:(e6:(e5:r1:h->d3:h.s0.run->d1) e7:"x")
detached {
  d1: holder -> 'a -> 'a = <missing>
  d2: std::control::var::ref 'a holder -> std::control::var::ref('a, 'b ['[]] -> ['[]] 'b) = <missing>
  d4:x arg
}

```

## 57. x21-rigidbad

```yulang
struct holder { run: 'a -> 'a }
my h = holder {run: \x -> 1}
h.run "x"
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x21-rigidbad.yu`

Exit: 0; seconds: 0.003103

```text
run roots [1]

```

## 58. x21-ref-exact

```yulang
type ref 'e 'a with:
    struct self:
        run: ('a -> ['f] 'a) -> ['e, 'f] ()
my get(r: ref 'e 'a) = sub: r.run \a -> { return a; ... }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x21-ref-exact.yu`

Exit: 1; seconds: 0.006186

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 55
    4 | my get(r: ref 'e 'a) = sub: r.run \a -> { return a; ... }
      |                                                       ^
  error [yulang.unresolved-value]: get: unresolved value name: std::control::flow::sub::sub
    --> line 4, column 4
    4 | my get(r: ref 'e 'a) = sub: r.run \a -> { return a; ... }
      |    ^^^
    hint: define `std::control::flow::sub::sub` before this use, or import the module that provides it

```

## 59. x21-ref-exact

```yulang
type ref 'e 'a with:
    struct self:
        run: ('a -> ['f] 'a) -> ['e, 'f] ()
my get(r: ref 'e 'a) = sub: r.run \a -> { return a; ... }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x21-ref-exact.yu --poly`

Exit: 0; seconds: 0.006060

```text
roots d0:ref d3:ref d4:get
d0:ref: {run: ('a -> ['b] 'a) -> ['c & 'b] ()} -> ref 'c 'a = <missing>
d3:ref mod {
}
my d4:get: never = <missing>
detached {
  d1: ref 'a 'b -> ('b -> ['c] 'b) -> ['a, 'c] () = <missing>
  d2: std::control::var::ref('a, ref 'b 'c) -> std::control::var::ref('a, ('c ['[]] -> ['d] 'c) ['[]] -> ['b | 'd <: 'b & 'd] ()) = <missing>
  d5:r arg
}
error: unresolved value name: std::control::flow::sub::sub

```

## 60. x21-ref-exact

```yulang
type ref 'e 'a with:
    struct self:
        run: ('a -> ['f] 'a) -> ['e, 'f] ()
my get(r: ref 'e 'a) = sub: r.run \a -> { return a; ... }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x21-ref-exact.yu`

Exit: 1; seconds: 0.003312

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 55
    4 | my get(r: ref 'e 'a) = sub: r.run \a -> { return a; ... }
      |                                                       ^

```

## 61. x17-literal-type

```yulang
my id(x: list (int | 'a & float -> int)) = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x17-literal-type.yu`

Exit: 1; seconds: 0.003384

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 1, column 20
    1 | my id(x: list (int | 'a & float -> int)) = x
      |                    ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 1, column 25
    1 | my id(x: list (int | 'a & float -> int)) = x
      |                         ^
  error [yulang.unresolved-type]: id: unresolved type name: list
    --> line 1, column 10
    1 | my id(x: list (int | 'a & float -> int)) = x
      |          ^^^^
    hint: define type `list` before this annotation, or import it

```

## 62. x17-literal-type

```yulang
my id(x: list (int | 'a & float -> int)) = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x17-literal-type.yu --poly`

Exit: 0; seconds: 0.002397

```text
roots d0:id
my d0:id: never = <missing>
error: unresolved type name: list

```

## 63. x17-literal-type

```yulang
my id(x: list (int | 'a & float -> int)) = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x17-literal-type.yu`

Exit: 1; seconds: 0.001556

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 1, column 20
    1 | my id(x: list (int | 'a & float -> int)) = x
      |                    ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 1, column 25
    1 | my id(x: list (int | 'a & float -> int)) = x
      |                         ^

```

## 64. x13-shared-box

```yulang
struct box 'a { value: 'a }
my both(x, f: box 'b -> (), g: box 'c -> ()) = { f x; g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x13-shared-box.yu`

Exit: 0; seconds: 0.004622

```text

```

## 65. x13-shared-box

```yulang
struct box 'a { value: 'a }
my both(x, f: box 'b -> (), g: box 'c -> ()) = { f x; g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x13-shared-box.yu --poly`

Exit: 0; seconds: 0.005501

```text
roots d0:box d3:both
d0:box: {value: 'a} -> box 'a = <missing>
my d3:both: ('a & box 'b) -> (('a | box 'b) -> ['c] ()) -> (('a | box 'b) -> ['c] ()) -> ['c] 'a = e11:(fn p0:d4:x -> e10:(fn p1:d5:f -> e9:(fn p2:d6:g -> e8:block { e2:(e0:r0:f->d5:f e1:r1:x->d4:x); e7:block { e5:(e3:r2:g->d6:g e4:r3:x->d4:x); e6:r4:x->d4:x } })))
detached {
  d1: box 'a -> 'a = <missing>
  d2: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d4:x arg
  d5:f arg
  d6:g arg
}

```

## 66. x13-shared-box

```yulang
struct box 'a { value: 'a }
my both(x, f: box 'b -> (), g: box 'c -> ()) = { f x; g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x13-shared-box.yu`

Exit: 0; seconds: 0.002414

```text
run roots []

```

## 67. x14-nested-lists

```yulang
my use_int(x: list (list int)) = ()
my use_float(x: list (list float)) = ()
my both(x) = { use_int x; use_float x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x14-nested-lists.yu`

Exit: 1; seconds: 0.003113

```text
diagnostics:
  error [yulang.unresolved-type]: use_int: unresolved type name: list
    --> line 1, column 15
    1 | my use_int(x: list (list int)) = ()
      |               ^^^^
    hint: define type `list` before this annotation, or import it
  error [yulang.unresolved-type]: use_float: unresolved type name: list
    --> line 2, column 17
    2 | my use_float(x: list (list float)) = ()
      |                 ^^^^
    hint: define type `list` before this annotation, or import it

```

## 68. x14-nested-lists

```yulang
my use_int(x: list (list int)) = ()
my use_float(x: list (list float)) = ()
my both(x) = { use_int x; use_float x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x14-nested-lists.yu --poly`

Exit: 0; seconds: 0.003657

```text
roots d0:use_int d1:use_float d2:both
my d0:use_int: never = <missing>
my d1:use_float: never = <missing>
my d2:both: 'a -> 'a = e9:(fn p0:d3:x -> e8:block { e2:(e0:r0:use_int->d0:use_int e1:r1:x->d3:x); e7:block { e5:(e3:r2:use_float->d1:use_float e4:r3:x->d3:x); e6:r4:x->d3:x } })
detached {
  d3:x arg
}
error: unresolved type name: list
error: unresolved type name: list

```

## 69. x14-nested-lists

```yulang
my use_int(x: list (list int)) = ()
my use_float(x: list (list float)) = ()
my both(x) = { use_int x; use_float x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x14-nested-lists.yu`

Exit: 1; seconds: 0.004185

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved type name: list
  detail: unresolved type name: list
  hint: run `yulang check` to see source ranges before running

```

## 70. x15-same-head-bounds

```yulang
struct box 'a { value: 'a }
my f(x: list (box 'a), g: list (box 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x15-same-head-bounds.yu`

Exit: 1; seconds: 0.002613

```text
diagnostics:
  error [yulang.unresolved-type]: f: unresolved type name: list
    --> line 2, column 9
    2 | my f(x: list (box 'a), g: list (box 'b) -> ()) = { g x; x }
      |         ^^^^
    hint: define type `list` before this annotation, or import it

```

## 71. x15-same-head-bounds

```yulang
struct box 'a { value: 'a }
my f(x: list (box 'a), g: list (box 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x15-same-head-bounds.yu --poly`

Exit: 0; seconds: 0.003775

```text
roots d0:box d3:f
d0:box: {value: 'a} -> box 'a = <missing>
my d3:f: never = <missing>
detached {
  d1: box 'a -> 'a = <missing>
  d2: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
}
error: unresolved type name: list

```

## 72. x15-same-head-bounds

```yulang
struct box 'a { value: 'a }
my f(x: list (box 'a), g: list (box 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x15-same-head-bounds.yu`

Exit: 1; seconds: 0.003925

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved type name: list
  hint: run `yulang check` to see source ranges before running

```

## 73. x16-distinct-head-bounds

```yulang
struct box 'a { value: 'a }
my f(x: list (box 'a), g: list (list 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x16-distinct-head-bounds.yu`

Exit: 1; seconds: 0.002793

```text
diagnostics:
  error [yulang.unresolved-type]: f: unresolved type name: list
    --> line 2, column 9
    2 | my f(x: list (box 'a), g: list (list 'b) -> ()) = { g x; x }
      |         ^^^^
    hint: define type `list` before this annotation, or import it

```

## 74. x16-distinct-head-bounds

```yulang
struct box 'a { value: 'a }
my f(x: list (box 'a), g: list (list 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x16-distinct-head-bounds.yu --poly`

Exit: 0; seconds: 0.003508

```text
roots d0:box d3:f
d0:box: {value: 'a} -> box 'a = <missing>
my d3:f: never = <missing>
detached {
  d1: box 'a -> 'a = <missing>
  d2: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
}
error: unresolved type name: list

```

## 75. x16-distinct-head-bounds

```yulang
struct box 'a { value: 'a }
my f(x: list (box 'a), g: list (list 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x16-distinct-head-bounds.yu`

Exit: 1; seconds: 0.003883

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved type name: list
  hint: run `yulang check` to see source ranges before running

```

## 76. x14-nested-lists-self-contained

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
my use_int(x: list (list int)) = ()
my use_float(x: list (list float)) = ()
my both(x) = { use_int x; use_float x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x14-nested-lists-self-contained.yu`

Exit: 0; seconds: 0.006827

```text

```

## 77. x14-nested-lists-self-contained

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
my use_int(x: list (list int)) = ()
my use_float(x: list (list float)) = ()
my both(x) = { use_int x; use_float x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x14-nested-lists-self-contained.yu --poly`

Exit: 0; seconds: 0.006127

```text
roots d0:list d3:use_int d4:use_float d5:both
d0:list mod {
  d1:"list.nil": list 'a = <missing>
  d2:"list.cons": 'a -> list 'a -> list 'a = <missing>
}
my d3:use_int: list(list int) -> () = e1:(fn p0:d6:x -> e0:())
my d4:use_float: list(list float) -> () = e3:(fn p1:d7:x -> e2:())
my d5:both: ('a & list(list int)) -> 'a = e13:(fn p2:d8:x -> e12:block { e6:(e4:r0:use_int->d3:use_int e5:r1:x->d8:x); e11:block { e9:(e7:r2:use_float->d4:use_float e8:r3:x->d8:x); e10:r4:x->d8:x } })
detached {
  d6:x arg
  d7:x arg
  d8:x arg
}

```

## 78. x14-nested-lists-self-contained

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
my use_int(x: list (list int)) = ()
my use_float(x: list (list float)) = ()
my both(x) = { use_int x; use_float x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x14-nested-lists-self-contained.yu`

Exit: 0; seconds: 0.003681

```text
run roots []

```

## 79. x15-same-head-bounds-self-contained

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
struct box 'a { value: 'a }
my f(x: list (box 'a), g: list (box 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x15-same-head-bounds-self-contained.yu`

Exit: 0; seconds: 0.004973

```text

```

## 80. x15-same-head-bounds-self-contained

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
struct box 'a { value: 'a }
my f(x: list (box 'a), g: list (box 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x15-same-head-bounds-self-contained.yu --poly`

Exit: 0; seconds: 0.006060

```text
roots d0:list d3:box d6:f
d0:list mod {
  d1:"list.nil": list 'a = <missing>
  d2:"list.cons": 'a -> list 'a -> list 'a = <missing>
}
d3:box: {value: 'a} -> box 'a = <missing>
my d6:f: list(box 'a) -> (list(box 'a) -> ['b] ()) -> ['b] list(box 'a) = e6:(fn p0:d7:x -> e5:(fn p1:d8:g -> e4:block { e2:(e0:r0:g->d8:g e1:r1:x->d7:x); e3:r2:x->d7:x }))
detached {
  d4: box 'a -> 'a = <missing>
  d5: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d7:x arg
  d8:g arg
}

```

## 81. x15-same-head-bounds-self-contained

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
struct box 'a { value: 'a }
my f(x: list (box 'a), g: list (box 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x15-same-head-bounds-self-contained.yu`

Exit: 0; seconds: 0.002712

```text
run roots []

```

## 82. x16-distinct-head-bounds-self-contained

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
struct box 'a { value: 'a }
my f(x: list (box 'a), g: list (list 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x16-distinct-head-bounds-self-contained.yu`

Exit: 0; seconds: 0.004567

```text

```

## 83. x16-distinct-head-bounds-self-contained

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
struct box 'a { value: 'a }
my f(x: list (box 'a), g: list (list 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x16-distinct-head-bounds-self-contained.yu --poly`

Exit: 0; seconds: 0.006914

```text
roots d0:list d3:box d6:f
d0:list mod {
  d1:"list.nil": list 'a = <missing>
  d2:"list.cons": 'a -> list 'a -> list 'a = <missing>
}
d3:box: {value: 'a} -> box 'a = <missing>
my d6:f: list(box 'a | list 'b <: box 'a & list 'b) -> (list(box 'a | list 'b <: box 'a & list 'b) -> ['c] ()) -> ['c] list(box 'a) = e6:(fn p0:d7:x -> e5:(fn p1:d8:g -> e4:block { e2:(e0:r0:g->d8:g e1:r1:x->d7:x); e3:r2:x->d7:x }))
detached {
  d4: box 'a -> 'a = <missing>
  d5: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
  d7:x arg
  d8:g arg
}

```

## 84. x16-distinct-head-bounds-self-contained

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
struct box 'a { value: 'a }
my f(x: list (box 'a), g: list (list 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x16-distinct-head-bounds-self-contained.yu`

Exit: 0; seconds: 0.002760

```text
run roots []

```

## 85. x17-literal-type-self-contained

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
my id(x: list (int | 'a & float -> int)) = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x17-literal-type-self-contained.yu`

Exit: 1; seconds: 0.003222

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 20
    4 | my id(x: list (int | 'a & float -> int)) = x
      |                    ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 25
    4 | my id(x: list (int | 'a & float -> int)) = x
      |                         ^

```

## 86. x17-literal-type-self-contained

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
my id(x: list (int | 'a & float -> int)) = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x17-literal-type-self-contained.yu --poly`

Exit: 0; seconds: 0.003457

```text
roots d0:list d3:id
d0:list mod {
  d1:"list.nil": list 'a = <missing>
  d2:"list.cons": 'a -> list 'a -> list 'a = <missing>
}
my d3:id: list (int, 'a, float ['[]] -> ['[]] int) -> list (int, 'a, float ['[]] -> ['[]] int) = e1:(fn p0:d4:x -> e0:r0:x->d4:x)
detached {
  d4:x arg
}

```

## 87. x17-literal-type-self-contained

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
my id(x: list (int | 'a & float -> int)) = x
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x17-literal-type-self-contained.yu`

Exit: 1; seconds: 0.001947

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 20
    4 | my id(x: list (int | 'a & float -> int)) = x
      |                    ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 25
    4 | my id(x: list (int | 'a & float -> int)) = x
      |                         ^

```

## 88. x21-ref-declaration

```yulang
type ref 'e 'a with:
    struct self:
        run: ('a -> ['f] 'a) -> ['e, 'f] ()
my use(r: ref 'e int) = r.run (\x -> x)
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x21-ref-declaration.yu`

Exit: 1; seconds: 0.003852

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 9
    4 | my use(r: ref 'e int) = r.run (\x -> x)
      |         ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 11
    4 | my use(r: ref 'e int) = r.run (\x -> x)
      |           ^^^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 21
    4 | my use(r: ref 'e int) = r.run (\x -> x)
      |                     ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 23
    4 | my use(r: ref 'e int) = r.run (\x -> x)
      |                       ^
  error [yulang.unresolved-value]: unresolved value name in root expression: 'e
    --> line 4, column 15
    4 | my use(r: ref 'e int) = r.run (\x -> x)
      |               ^^
    hint: define `'e` before this use, or import the module that provides it
  error [yulang.unresolved-value]: unresolved value name in root expression: r
    --> line 4, column 25
    4 | my use(r: ref 'e int) = r.run (\x -> x)
      |                         ^
    hint: define `r` before this use, or import the module that provides it

```

## 89. x21-ref-declaration

```yulang
type ref 'e 'a with:
    struct self:
        run: ('a -> ['f] 'a) -> ['e, 'f] ()
my use(r: ref 'e int) = r.run (\x -> x)
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x21-ref-declaration.yu --poly`

Exit: 0; seconds: 0.004885

```text
roots d0:ref d3:ref
d0:ref: {run: ('a -> ['b] 'a) -> ['c & 'b] ()} -> ref 'c 'a = <missing>
d3:ref mod {
}
detached {
  d1: ref 'a 'b -> ('b -> ['c] 'b) -> ['a, 'c] () = <missing>
  d2: std::control::var::ref('a, ref 'b 'c) -> std::control::var::ref('a, ('c ['[]] -> ['d] 'c) ['[]] -> ['b | 'd <: 'b & 'd] ()) = <missing>
}
error: unresolved value name in root expression: 'e
error: unresolved value name in root expression: r

```

## 90. x21-ref-declaration

```yulang
type ref 'e 'a with:
    struct self:
        run: ('a -> ['f] 'a) -> ['e, 'f] ()
my use(r: ref 'e int) = r.run (\x -> x)
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x21-ref-declaration.yu`

Exit: 1; seconds: 0.003089

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 9
    4 | my use(r: ref 'e int) = r.run (\x -> x)
      |         ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 11
    4 | my use(r: ref 'e int) = r.run (\x -> x)
      |           ^^^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 21
    4 | my use(r: ref 'e int) = r.run (\x -> x)
      |                     ^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 4, column 23
    4 | my use(r: ref 'e int) = r.run (\x -> x)
      |                       ^

```

## 91. x21-ref-nested-handler

```yulang
act ping:
    ping: () -> int
struct ref 'e 'a {run: ('a -> ['f] 'a) -> ['e, 'f] ()}
my r = ref {run: \f -> { f 1; () }}
my answer = handle r.run (\x -> ping ()):
    ping () => resume 7
answer
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x21-ref-nested-handler.yu`

Exit: 1; seconds: 0.004856

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 2, column 14
    2 |     ping: () -> int
      |              ^^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 6, column 14
    6 |     ping () => resume 7
      |              ^
  error [yulang.unresolved-value]: answer: unresolved value name: handle
    --> line 5, column 13
    5 | my answer = handle r.run (\x -> ping ()):
      |             ^^^^^^
    hint: define `handle` before this use, or import the module that provides it

```

## 92. x21-ref-nested-handler

```yulang
act ping:
    ping: () -> int
struct ref 'e 'a {run: ('a -> ['f] 'a) -> ['e, 'f] ()}
my r = ref {run: \f -> { f 1; () }}
my answer = handle r.run (\x -> ping ()):
    ping () => resume 7
answer
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x21-ref-nested-handler.yu --poly`

Exit: 0; seconds: 0.005441

```text
roots d0:ping d1:ref d4:r d5:answer
d0:ping mod {
}
d1:ref: {run: ('a -> ['b] 'a) -> ['c & 'b] ()} -> ref 'c 'a = <missing>
my d4:r: ref('a, 'b | int) = e8:(e0:r0:ref->d1:ref e7:{run: e6:(fn p0:d6:f -> e5:block { e3:(e1:r1:f->d6:f e2:1); e4:() })})
my d5:answer: never = <missing>
root exprs e9:r2:answer->d5:answer
runtime roots d4:r e9:r2:answer->d5:answer
detached {
  d2: ref 'a 'b -> ('b -> ['c] 'b) -> ['a, 'c] () = <missing>
  d3: std::control::var::ref('a, ref 'b 'c) -> std::control::var::ref('a, ('c ['[]] -> ['d] 'c) ['[]] -> ['b | 'd <: 'b & 'd] ()) = <missing>
  d6:f arg
}
error: unresolved value name: handle

```

## 93. x21-ref-nested-handler

```yulang
act ping:
    ping: () -> int
struct ref 'e 'a {run: ('a -> ['f] 'a) -> ['e, 'f] ()}
my r = ref {run: \f -> { f 1; () }}
my answer = handle r.run (\x -> ping ()):
    ping () => resume 7
answer
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x21-ref-nested-handler.yu`

Exit: 1; seconds: 0.001962

```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 2, column 14
    2 |     ping: () -> int
      |              ^^
  error [yulang.syntax]: syntax error: unexpected token
    --> line 6, column 14
    6 |     ping () => resume 7
      |              ^

```

## 94. x21-ref-declaration-fixed

```yulang
type ref 'e 'a with:
    struct self:
        run: ('a -> ['f] 'a) -> ['e, 'f] ()
my apply_ref(r: ref 'e int) = r.run (\x -> x)
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x21-ref-declaration-fixed.yu`

Exit: 0; seconds: 0.010493

```text

```

## 95. x21-ref-declaration-fixed

```yulang
type ref 'e 'a with:
    struct self:
        run: ('a -> ['f] 'a) -> ['e, 'f] ()
my apply_ref(r: ref 'e int) = r.run (\x -> x)
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x21-ref-declaration-fixed.yu --poly`

Exit: 0; seconds: 0.007652

```text
roots d0:ref d3:ref d4:apply_ref
d0:ref: {run: ('a -> ['b] 'a) -> ['c & 'b] ()} -> ref 'c 'a = <missing>
d3:ref mod {
}
my d4:apply_ref: ref 'a int -> ['a] () = e5:(fn p0:d5:r -> e4:(e1:(e0:r0:r->d5:r.s0.run->d1) e3:(fn p1:d6:x -> e2:r1:x->d6:x)))
detached {
  d1: ref 'a 'b -> ('b -> ['c] 'b) -> ['a, 'c] () = <missing>
  d2: std::control::var::ref('a, ref 'b 'c) -> std::control::var::ref('a, ('c ['[]] -> ['d] 'c) ['[]] -> ['b | 'd <: 'b & 'd] ()) = <missing>
  d5:r arg
  d6:x arg
}

```

## 96. x21-ref-declaration-fixed

```yulang
type ref 'e 'a with:
    struct self:
        run: ('a -> ['f] 'a) -> ['e, 'f] ()
my apply_ref(r: ref 'e int) = r.run (\x -> x)
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x21-ref-declaration-fixed.yu`

Exit: 0; seconds: 0.003551

```text
run roots []

```

## 97. x21-ref-effect

```yulang
act ping:
    our get: () -> int
struct ref 'e 'a {run: ('a -> ['f] 'a) -> ['e, 'f] ()}
my r = ref {run: \f -> { f 1; () }}
my handle(action: [ping] ()) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(r.run (\x -> ping::get()))
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x21-ref-effect.yu`

Exit: 0; seconds: 0.013091

```text

```

## 98. x21-ref-effect

```yulang
act ping:
    our get: () -> int
struct ref 'e 'a {run: ('a -> ['f] 'a) -> ['e, 'f] ()}
my r = ref {run: \f -> { f 1; () }}
my handle(action: [ping] ()) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(r.run (\x -> ping::get()))
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x21-ref-effect.yu --poly`

Exit: 0; seconds: 0.012233

```text
roots d0:ping d2:ref d5:r d6:handle
d0:ping mod {
}
d2:ref: {run: ('a -> ['b] 'a) -> ['c & 'b] ()} -> ref 'c 'a = <missing>
my d5:r: ref('a, 'b | int) = e8:(e0:r0:ref->d2:ref e7:{run: e6:(fn p0:d7:f -> e5:block { e3:(e1:r1:f->d7:f e2:1); e4:() })})
my d6:handle: () ['a & [ping; 'a]] -> ['a] () = e15:(fn p1:d8:action -> e14:catch e9:r2:action->d8:action { ping::get p2:_, p3:d9:k -> e12:(e10:r3:k->d9:k e11:7); p4:d10:v -> e13:r4:v->d10:v })
root exprs e24:(e16:r5:handle->d6:handle e23:(e18:(e17:r6:r->d5:r.s0.run->d3) e22:(fn p5:d12:x -> e21:(e19:r7:"ping::get"->d1:"ping.get" e20:()))))
runtime roots d5:r e24:(e16:r5:handle->d6:handle e23:(e18:(e17:r6:r->d5:r.s0.run->d3) e22:(fn p5:d12:x -> e21:(e19:r7:"ping::get"->d1:"ping.get" e20:()))))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d3: ref 'a 'b -> ('b -> ['c] 'b) -> ['a, 'c] () = <missing>
  d4: std::control::var::ref('a, ref 'b 'c) -> std::control::var::ref('a, ('c ['[]] -> ['d] 'c) ['[]] -> ['b | 'd <: 'b & 'd] ()) = <missing>
  d7:f arg
  d8:action arg
  d9:k arg
  d10:v arg
  d12:x arg
}

```

## 99. x21-ref-effect

```yulang
act ping:
    our get: () -> int
struct ref 'e 'a {run: ('a -> ['f] 'a) -> ['e, 'f] ()}
my r = ref {run: \f -> { f 1; () }}
my handle(action: [ping] ()) = catch action:
    ping::get(), k -> k 7
    v -> v
handle(r.run (\x -> ping::get()))
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x21-ref-effect.yu`

Exit: 1; seconds: 0.014587

```text
conflicting type candidates: unit vs int

```

## 100. x17-generated-function-interval

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
my f(x: list ('a -> int), g: list (int -> 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x17-generated-function-interval.yu`

Exit: 0; seconds: 0.005440

```text

```

## 101. x17-generated-function-interval

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
my f(x: list ('a -> int), g: list (int -> 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x17-generated-function-interval.yu --poly`

Exit: 0; seconds: 0.005499

```text
roots d0:list d3:f
d0:list mod {
  d1:"list.nil": list 'a = <missing>
  d2:"list.cons": 'a -> list 'a -> list 'a = <missing>
}
my d3:f: list(int ['[]] -> ['[]] int) -> (list(int ['[]] -> ['[]] int) -> ['a] ()) -> ['a] list(int ['[]] -> ['[]] int) = e6:(fn p0:d4:x -> e5:(fn p1:d5:g -> e4:block { e2:(e0:r0:g->d5:g e1:r1:x->d4:x); e3:r2:x->d4:x }))
detached {
  d4:x arg
  d5:g arg
}

```

## 102. x17-generated-function-interval

```yulang
enum list 'a:
    nil
    cons 'a (list 'a)
my f(x: list ('a -> int), g: list (int -> 'b) -> ()) = { g x; x }
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x17-generated-function-interval.yu`

Exit: 0; seconds: 0.002774

```text
run roots []

```

## 103. x20-phantom-nocast

```yulang
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom int = phantom::next phantom::end
my b: phantom str = a
b
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x20-phantom-nocast.yu`

Exit: 1; seconds: 0.005686

```text
diagnostics:
  error [yulang.unresolved-type]: b: unresolved type name: str
    --> line 5, column 15
    5 | my b: phantom str = a
      |               ^^^
    hint: define type `str` before this annotation, or import it

```

## 104. x20-phantom-nocast

```yulang
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom int = phantom::next phantom::end
my b: phantom str = a
b
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x20-phantom-nocast.yu --poly`

Exit: 0; seconds: 0.004426

```text
roots d0:phantom d3:a d4:b
d0:phantom mod {
  d1:"phantom.end": phantom 'a = <missing>
  d2:"phantom.next": phantom 'a -> phantom 'a = <missing>
}
my d3:a: phantom int = e2:(e0:r0:"phantom::next"->d2:"phantom.next" e1:r1:"phantom::end"->d1:"phantom.end")
my d4:b: never = <missing>
root exprs e4:r3:b->d4:b
runtime roots d3:a e4:r3:b->d4:b
error: unresolved type name: str

```

## 105. x20-phantom-nocast

```yulang
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom int = phantom::next phantom::end
my b: phantom str = a
b
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x20-phantom-nocast.yu`

Exit: 1; seconds: 0.004196

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved type name: str
  hint: run `yulang check` to see source ranges before running

```

## 106. x18-box-nocast

```yulang
struct box 'a {value:'a}
my a: box int = box {value:7}
my b: box str = a
b.value
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x18-box-nocast.yu`

Exit: 1; seconds: 0.003818

```text
diagnostics:
  error [yulang.unresolved-type]: b: unresolved type name: str
    --> line 3, column 11
    3 | my b: box str = a
      |           ^^^
    hint: define type `str` before this annotation, or import it

```

## 107. x18-box-nocast

```yulang
struct box 'a {value:'a}
my a: box int = box {value:7}
my b: box str = a
b.value
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x18-box-nocast.yu --poly`

Exit: 0; seconds: 0.003774

```text
roots d0:box d3:a d4:b
d0:box: {value: 'a} -> box 'a = <missing>
my d3:a: box int = e3:(e0:r0:box->d0:box e2:{value: e1:7})
my d4:b: never = <missing>
root exprs e6:(e5:r2:b->d4:b.s0.value#field)
runtime roots d3:a e6:(e5:r2:b->d4:b.s0.value#field)
detached {
  d1: box 'a -> 'a = <missing>
  d2: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
}
error: unresolved type name: str

```

## 108. x18-box-nocast

```yulang
struct box 'a {value:'a}
my a: box int = box {value:7}
my b: box str = a
b.value
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x18-box-nocast.yu`

Exit: 1; seconds: 0.004318

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved type name: str
  hint: run `yulang check` to see source ranges before running

```

## 109. x19-chain-force

```yulang
struct user_id {value:int}
cast(x:user_id): int=x.value
enum chain 'a:
    end
    link 'a (chain 'a)
my convert(x:chain user_id):chain int=x
my a:chain user_id=chain::link (user_id {value:7}) chain::end
convert a
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x19-chain-force.yu`

Exit: 0; seconds: 0.006622

```text

```

## 110. x19-chain-force

```yulang
struct user_id {value:int}
cast(x:user_id): int=x.value
enum chain 'a:
    end
    link 'a (chain 'a)
my convert(x:chain user_id):chain int=x
my a:chain user_id=chain::link (user_id {value:7}) chain::end
convert a
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x19-chain-force.yu --poly`

Exit: 0; seconds: 0.006746

```text
roots d0:user_id d4:chain d7:convert d8:a
d0:user_id: {value: int} -> user_id = <missing>
d4:chain mod {
  d5:"chain.end": chain 'a = <missing>
  d6:"chain.link": 'a -> chain 'a -> chain 'a = <missing>
}
my d7:convert: chain(int | user_id <: int & user_id) -> chain(int | user_id <: int & user_id) = e4:(fn p1:d10:x -> e3:r1:x->d10:x)
my d8:a: chain user_id = e12:(e10:(e5:r2:"chain::link"->d6:"chain.link" e9:(e6:r3:user_id->d0:user_id e8:{value: e7:7})) e11:r4:"chain::end"->d5:"chain.end")
root exprs e15:(e13:r5:convert->d7:convert e14:r6:a->d8:a)
runtime roots d8:a e15:(e13:r5:convert->d7:convert e14:r6:a->d8:a)
detached {
  d1: user_id -> int = <missing>
  d2: std::control::var::ref 'a user_id -> std::control::var::ref 'a int = <missing>
  my d3:"#cast": user_id -> int = e2:(fn p0:d9:x -> e1:(e0:r0:x->d9:x.s0.value->d1))
  d9:x arg
  d10:x arg
}

```

## 111. x19-chain-force

```yulang
struct user_id {value:int}
cast(x:user_id): int=x.value
enum chain 'a:
    end
    link 'a (chain 'a)
my convert(x:chain user_id):chain int=x
my a:chain user_id=chain::link (user_id {value:7}) chain::end
convert a
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x19-chain-force.yu`

Exit: 0; seconds: 0.003410

```text
run roots [chain::link(user_id({value: 7}), chain::end)]

```

## 112. x20-phantom-nocast-fixed

```yulang
type text
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom int = phantom::next phantom::end
my b: phantom text = a
b
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x20-phantom-nocast-fixed.yu`

Exit: 0; seconds: 0.005880

```text

```

## 113. x20-phantom-nocast-fixed

```yulang
type text
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom int = phantom::next phantom::end
my b: phantom text = a
b
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x20-phantom-nocast-fixed.yu --poly`

Exit: 0; seconds: 0.005452

```text
roots d0:phantom d3:a d4:b
d0:phantom mod {
  d1:"phantom.end": phantom 'a = <missing>
  d2:"phantom.next": phantom 'a -> phantom 'a = <missing>
}
my d3:a: phantom int = e2:(e0:r0:"phantom::next"->d2:"phantom.next" e1:r1:"phantom::end"->d1:"phantom.end")
my d4:b: phantom text = e3:r2:a->d3:a
root exprs e4:r3:b->d4:b
runtime roots d3:a e4:r3:b->d4:b

```

## 114. x20-phantom-nocast-fixed

```yulang
type text
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom int = phantom::next phantom::end
my b: phantom text = a
b
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x20-phantom-nocast-fixed.yu`

Exit: 0; seconds: 0.002916

```text
run roots [phantom::next(phantom::end)]

```

## 115. x18-box-nocast-fixed

```yulang
type text
struct box 'a {value:'a}
my a: box int = box {value:7}
my b: box text = a
b.value
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit2-types/x18-box-nocast-fixed.yu`

Exit: 0; seconds: 0.004094

```text

```

## 116. x18-box-nocast-fixed

```yulang
type text
struct box 'a {value:'a}
my a: box int = box {value:7}
my b: box text = a
b.value
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump /tmp/audit2-types/x18-box-nocast-fixed.yu --poly`

Exit: 0; seconds: 0.003887

```text
roots d0:box d3:a d4:b
d0:box: {value: 'a} -> box 'a = <missing>
my d3:a: box int = e3:(e0:r0:box->d0:box e2:{value: e1:7})
my d4:b: box text = e4:r1:a->d3:a
root exprs e6:(e5:r2:b->d4:b.s0.value->d1)
runtime roots d3:a e6:(e5:r2:b->d4:b.s0.value->d1)
detached {
  d1: box 'a -> 'a = <missing>
  d2: std::control::var::ref('a, box 'b) -> std::control::var::ref 'a 'b = <missing>
}

```

## 117. x18-box-nocast-fixed

```yulang
type text
struct box 'a {value:'a}
my a: box int = box {value:7}
my b: box text = a
b.value
```

`/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit2-types/x18-box-nocast-fixed.yu`

Exit: 1; seconds: 0.006125

```text
conflicting type candidates: int vs text

```

## Existing Rust unit tests

```text
COMMAND cargo test -p infer --lib merge_cons_by_path_combines_interval_lower_and_upper_bounds -- --nocapture --test-threads=1
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
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.10s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 1 test
test compact::tests::case_02::merge_cons_by_path_combines_interval_lower_and_upper_bounds ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1392 filtered out; finished in 0.00s

EXIT:0
COMMAND cargo test -p infer --lib sandwich_lifts_list_and_reuses_common_interval_var -- --nocapture --test-threads=1
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
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.04s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 1 test
test compact::tests::case_02::sandwich_lifts_list_and_reuses_common_interval_var ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1392 filtered out; finished in 0.00s

EXIT:0
COMMAND cargo test -p infer --lib constructor_args_propagate_invariant_neutral_bounds -- --nocapture --test-threads=1
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
test constraints::tests::case_01::constructor_args_propagate_invariant_neutral_bounds ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1392 filtered out; finished in 0.00s

EXIT:0

```
