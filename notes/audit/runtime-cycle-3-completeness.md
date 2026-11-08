# Cycle3 completeness-side candidates: raw logs

Y2 binary main@d4c8bc8fc; no-prelude. These are concrete candidates, not general completeness proofs.

## poly-value / check

```yulang
our id = \x -> x
(id 7, id "seven")
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/poly-value.yu
```

UTC: 2026-11-08T13:31:18.734765+00:00; elapsed: 0.004709s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## poly-value / dump

```yulang
our id = \x -> x
(id 7, id "seven")
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/poly-value.yu
```

UTC: 2026-11-08T13:31:18.739656+00:00; elapsed: 0.004968s; exit: 0; timeout: False

stdout:
```text
roots d0:id
d0:id: 'a -> 'a = e1:(fn p0:d1:x -> e0:r0:x->d1:x)
root exprs e8:(e4:(e2:r1:id->d0:id e3:7), e7:(e5:r2:id->d0:id e6:"seven"))
runtime roots e8:(e4:(e2:r1:id->d0:id e3:7), e7:(e5:r2:id->d0:id e6:"seven"))
detached {
  d1:x arg
}

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## poly-value / run

```yulang
our id = \x -> x
(id 7, id "seven")
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/poly-value.yu
```

UTC: 2026-11-08T13:31:18.744773+00:00; elapsed: 0.007171s; exit: 0; timeout: False

stdout:
```text
run roots [(7, "seven")]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

```

## width-record / check

```yulang
our project r = r.x
(project {x: 7, y: "retained"}, project {x: "seven"})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/width-record.yu
```

UTC: 2026-11-08T13:31:18.752192+00:00; elapsed: 0.005431s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## width-record / dump

```yulang
our project r = r.x
(project {x: 7, y: "retained"}, project {x: "seven"})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/width-record.yu
```

UTC: 2026-11-08T13:31:18.757804+00:00; elapsed: 0.004837s; exit: 0; timeout: False

stdout:
```text
roots d0:project
d0:project: {x: 'a} -> 'a = e2:(fn p0:d1:r -> e1:(e0:r0:r->d1:r.s0.x#field))
root exprs e12:(e7:(e3:r1:project->d0:project e6:{x: e4:7, y: e5:"retained"}), e11:(e8:r2:project->d0:project e10:{x: e9:"seven"}))
runtime roots e12:(e7:(e3:r1:project->d0:project e6:{x: e4:7, y: e5:"retained"}), e11:(e8:r2:project->d0:project e10:{x: e9:"seven"}))
detached {
  d1:r arg
}

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## width-record / run

```yulang
our project r = r.x
(project {x: 7, y: "retained"}, project {x: "seven"})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/width-record.yu
```

UTC: 2026-11-08T13:31:18.762852+00:00; elapsed: 0.007375s; exit: 0; timeout: False

stdout:
```text
run roots [(7, "seven")]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

```

## spread-whole / check

```yulang
our keep {x, ..whole} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/spread-whole.yu
```

UTC: 2026-11-08T13:31:18.770541+00:00; elapsed: 0.006133s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## spread-whole / dump

```yulang
our keep {x, ..whole} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/spread-whole.yu
```

UTC: 2026-11-08T13:31:18.776908+00:00; elapsed: 0.004420s; exit: 0; timeout: False

stdout:
```text
roots d0:keep
d0:keep: ('a & {x: 'b}) -> 'a | {x: 'b, ..never} = e1:(fn p2:{x: p0:d1:x, ..d2:whole} -> e0:r0:whole->d2:whole)
root exprs e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
runtime roots e7:(e6:(e2:r1:keep->d0:keep e5:{x: e3:7, y: e4:"kept"}).s0.y#field)
detached {
  d1:x arg
  d2:whole arg
}

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## spread-whole / run

```yulang
our keep {x, ..whole} = whole
(keep {x: 7, y: "kept"}).y
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/spread-whole.yu
```

UTC: 2026-11-08T13:31:18.781605+00:00; elapsed: 0.005859s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.unsatisfied-subtype]: unsatisfied subtype constraint: {x: 'open2} <: {y: 'open0}
  hint: check that the value provides the fields or shape required by this use

```

## default-union / check

```yulang
our width {width = 1} = width
(width {}, width {width: "wide"})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/default-union.yu
```

UTC: 2026-11-08T13:31:18.787736+00:00; elapsed: 0.004703s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## default-union / dump

```yulang
our width {width = 1} = width
(width {}, width {width: "wide"})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/default-union.yu
```

UTC: 2026-11-08T13:31:18.792745+00:00; elapsed: 0.006485s; exit: 0; timeout: False

stdout:
```text
roots d0:width
d0:width: {width?: 'a} -> 'a | int = e2:(fn p1:{width: p0:d1:width = e0:1} -> e1:r0:width->d1:width)
root exprs e10:(e5:(e3:r1:width->d0:width e4:{}), e9:(e6:r2:width->d0:width e8:{width: e7:"wide"}))
runtime roots e10:(e5:(e3:r1:width->d0:width e4:{}), e9:(e6:r2:width->d0:width e8:{width: e7:"wide"}))
detached {
  d1:width arg
}

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## default-union / run

```yulang
our width {width = 1} = width
(width {}, width {width: "wide"})
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/default-union.yu
```

UTC: 2026-11-08T13:31:18.799505+00:00; elapsed: 0.007991s; exit: 0; timeout: False

stdout:
```text
run roots [(1, "wide")]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

```

## curried-pair / check

```yulang
our pair x y = (x, y)
our with_int = pair 7
(with_int "seven", pair(1, true))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/curried-pair.yu
```

UTC: 2026-11-08T13:31:18.807952+00:00; elapsed: 0.006502s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## curried-pair / dump

```yulang
our pair x y = (x, y)
our with_int = pair 7
(with_int "seven", pair(1, true))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/curried-pair.yu
```

UTC: 2026-11-08T13:31:18.814790+00:00; elapsed: 0.006905s; exit: 0; timeout: False

stdout:
```text
roots d0:pair d1:with_int
d0:pair: 'a -> 'b -> ('a, 'b) = e4:(fn p0:d2:x -> e3:(fn p1:d3:y -> e2:(e0:r0:x->d2:x, e1:r1:y->d3:y)))
d1:with_int: 'a -> (int, 'a) = e7:(e5:r2:pair->d0:pair e6:7)
root exprs e16:(e10:(e8:r3:with_int->d1:with_int e9:"seven"), e15:(e13:(e11:r4:pair->d0:pair e12:1) e14:true))
runtime roots d1:with_int e16:(e10:(e8:r3:with_int->d1:with_int e9:"seven"), e15:(e13:(e11:r4:pair->d0:pair e12:1) e14:true))
detached {
  d2:x arg
  d3:y arg
}

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## curried-pair / run

```yulang
our pair x y = (x, y)
our with_int = pair 7
(with_int "seven", pair(1, true))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/curried-pair.yu
```

UTC: 2026-11-08T13:31:18.822118+00:00; elapsed: 0.006420s; exit: 0; timeout: False

stdout:
```text
run roots [((7, "seven"), (1, true))]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

```

## composed-poly / check

```yulang
our compose f g x = f (g x)
our id x = x
our boxed x = {value: x}
((compose boxed id 7).value, (compose boxed id "seven").value)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/composed-poly.yu
```

UTC: 2026-11-08T13:31:18.828895+00:00; elapsed: 0.013476s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## composed-poly / dump

```yulang
our compose f g x = f (g x)
our id x = x
our boxed x = {value: x}
((compose boxed id 7).value, (compose boxed id "seven").value)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/composed-poly.yu
```

UTC: 2026-11-08T13:31:18.842731+00:00; elapsed: 0.014952s; exit: 0; timeout: False

stdout:
```text
roots d0:compose d1:id d2:boxed
d0:compose: ('a ['b#0[Empty]] -> ['c] 'd) -> ('e -> ['b#0[Empty]] 'a) -> 'e -> ['c#0] 'd#0 = e7:(fn p0:d3:f -> e6:(fn p1:d4:g -> e5:(fn p2:d5:x -> e4:(e0:r0:f->d3:f e3:(e1:r1:g->d4:g e2:r2:x->d5:x)))))
d1:id: 'a -> 'a = e9:(fn p3:d6:x -> e8:r3:x->d6:x)
d2:boxed: 'a -> {value: 'a} = e12:(fn p4:d7:x -> e11:{value: e10:r4:x->d7:x})
root exprs e29:(e20:(e19:(e17:(e15:(e13:r5:compose->d0:compose e14:r6:boxed->d2:boxed) e16:r7:id->d1:id) e18:7).s0.value#field), e28:(e27:(e25:(e23:(e21:r8:compose->d0:compose e22:r9:boxed->d2:boxed) e24:r10:id->d1:id) e26:"seven").s1.value#field))
runtime roots e29:(e20:(e19:(e17:(e15:(e13:r5:compose->d0:compose e14:r6:boxed->d2:boxed) e16:r7:id->d1:id) e18:7).s0.value#field), e28:(e27:(e25:(e23:(e21:r8:compose->d0:compose e22:r9:boxed->d2:boxed) e24:r10:id->d1:id) e26:"seven").s1.value#field))
detached {
  d3:f arg
  d4:g arg
  d5:x arg
  d6:x arg
  d7:x arg
}

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## composed-poly / run

```yulang
our compose f g x = f (g x)
our id x = x
our boxed x = {value: x}
((compose boxed id 7).value, (compose boxed id "seven").value)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/composed-poly.yu
```

UTC: 2026-11-08T13:31:18.858019+00:00; elapsed: 0.013358s; exit: 0; timeout: False

stdout:
```text
run roots [(7, "seven")]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

```

## nominal-phantom / check

```yulang
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom int = phantom::next (phantom::next phantom::end)
my b: phantom str = a
b
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/nominal-phantom.yu
```

UTC: 2026-11-08T13:31:18.871796+00:00; elapsed: 0.006168s; exit: 1; timeout: False

stdout:
```text
diagnostics:
  error [yulang.unresolved-type]: b: unresolved type name: str
    --> line 5, column 15
    5 | my b: phantom str = a
      |               ^^^
    hint: define type `str` before this annotation, or import it

```

stderr:
```text

```

## nominal-phantom / dump

```yulang
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom int = phantom::next (phantom::next phantom::end)
my b: phantom str = a
b
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/nominal-phantom.yu
```

UTC: 2026-11-08T13:31:18.878285+00:00; elapsed: 0.004808s; exit: 0; timeout: False

stdout:
```text
roots d0:phantom d3:a d4:b
d0:phantom mod {
  d1:"phantom.end": phantom 'a = <missing>
  d2:"phantom.next": phantom 'a -> phantom 'a = <missing>
}
my d3:a: phantom int = e4:(e0:r0:"phantom::next"->d2:"phantom.next" e3:(e1:r1:"phantom::next"->d2:"phantom.next" e2:r2:"phantom::end"->d1:"phantom.end"))
my d4:b: never = <missing>
root exprs e6:r4:b->d4:b
runtime roots d3:a e6:r4:b->d4:b

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
error: unresolved type name: str

```

## nominal-phantom / run

```yulang
enum phantom 'a:
    end
    next (phantom 'a)
my a: phantom int = phantom::next (phantom::next phantom::end)
my b: phantom str = a
b
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/nominal-phantom.yu
```

UTC: 2026-11-08T13:31:18.883377+00:00; elapsed: 0.006879s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved type name: str
  hint: run `yulang check` to see source ranges before running

```

## nominal-recursive-case / check

```yulang
enum tree:
    leaf int
    branch (tree, tree)
our pick t = case t:
    tree::leaf n -> n
    tree::branch l r -> pick l
pick (tree::branch (tree::leaf 7) (tree::leaf 8))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/nominal-recursive-case.yu
```

UTC: 2026-11-08T13:31:18.890628+00:00; elapsed: 0.009589s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## nominal-recursive-case / dump

```yulang
enum tree:
    leaf int
    branch (tree, tree)
our pick t = case t:
    tree::leaf n -> n
    tree::branch l r -> pick l
pick (tree::branch (tree::leaf 7) (tree::leaf 8))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/nominal-recursive-case.yu
```

UTC: 2026-11-08T13:31:18.900625+00:00; elapsed: 0.009078s; exit: 0; timeout: False

stdout:
```text
roots d0:tree d3:pick
d0:tree mod {
  d1:"tree.leaf": int -> tree = <missing>
  d2:"tree.branch": tree -> tree -> tree = <missing>
}
d3:pick: tree -> int = e6:(fn p0:d4:t -> e5:case e0:r0:t->d4:t { p2:r1:"tree::leaf"->d1:"tree.leaf"(p1:d5:n) -> e1:r2:n->d5:n; p5:r3:"tree::branch"->d2:"tree.branch"(p3:d6:l, p4:d7:r) -> e4:(e2:r4:pick->d3:pick e3:r5:l->d6:l) })
root exprs e17:(e7:r6:pick->d3:pick e16:(e12:(e8:r7:"tree::branch"->d2:"tree.branch" e11:(e9:r8:"tree::leaf"->d1:"tree.leaf" e10:7)) e15:(e13:r9:"tree::leaf"->d1:"tree.leaf" e14:8)))
runtime roots e17:(e7:r6:pick->d3:pick e16:(e12:(e8:r7:"tree::branch"->d2:"tree.branch" e11:(e9:r8:"tree::leaf"->d1:"tree.leaf" e10:7)) e15:(e13:r9:"tree::leaf"->d1:"tree.leaf" e14:8)))
detached {
  d4:t arg
  d5:n arg
  d6:l arg
  d7:r arg
}

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## nominal-recursive-case / run

```yulang
enum tree:
    leaf int
    branch (tree, tree)
our pick t = case t:
    tree::leaf n -> n
    tree::branch l r -> pick l
pick (tree::branch (tree::leaf 7) (tree::leaf 8))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/nominal-recursive-case.yu
```

UTC: 2026-11-08T13:31:18.910180+00:00; elapsed: 0.011915s; exit: 0; timeout: False

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

## variant-join / check

```yulang
our make flag = if flag: :some 7 else: :none
our consume x = case x:
    :some value -> value
    :none -> 0
(consume (make true), consume (make false))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/variant-join.yu
```

UTC: 2026-11-08T13:31:18.922594+00:00; elapsed: 0.005218s; exit: 1; timeout: False

stdout:
```text
diagnostics:
  error [yulang.unresolved-value]: make: unresolved value name: std::control::junction::junction::junction
    --> line 1, column 5
    1 | our make flag = if flag: :some 7 else: :none
      |     ^^^^
    hint: define `std::control::junction::junction::junction` before this use, or import the module that provides it

```

stderr:
```text

```

## variant-join / dump

```yulang
our make flag = if flag: :some 7 else: :none
our consume x = case x:
    :some value -> value
    :none -> 0
(consume (make true), consume (make false))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/variant-join.yu
```

UTC: 2026-11-08T13:31:18.928183+00:00; elapsed: 0.007907s; exit: 0; timeout: False

stdout:
```text
roots d0:make d1:consume
d0:make: never = <missing>
d1:consume: :{some 'a, none} -> 'a | int = e5:(fn p1:d3:x -> e4:case e1:r1:x->d3:x { p3::some(p2:d4:value) -> e2:r2:value->d4:value; p4::none -> e3:0 })
root exprs e16:(e10:(e6:r3:consume->d1:consume e9:(e7:r4:make->d0:make e8:true)), e15:(e11:r5:consume->d1:consume e14:(e12:r6:make->d0:make e13:false)))
runtime roots e16:(e10:(e6:r3:consume->d1:consume e9:(e7:r4:make->d0:make e8:true)), e15:(e11:r5:consume->d1:consume e14:(e12:r6:make->d0:make e13:false)))
detached {
  d2:flag arg
  d3:x arg
  d4:value arg
}

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
error: unresolved value name: std::control::junction::junction::junction

```

## variant-join / run

```yulang
our make flag = if flag: :some 7 else: :none
our consume x = case x:
    :some value -> value
    :none -> 0
(consume (make true), consume (make false))
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/variant-join.yu
```

UTC: 2026-11-08T13:31:18.936437+00:00; elapsed: 0.008240s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: std::control::junction::junction::junction
  hint: run `yulang check` to see source ranges before running

```

## record-first-wins / check

```yulang
our defaulted base = {..base, x: 7}
((defaulted {}).x, (defaulted {x: 9}).x)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3-completeness/record-first-wins.yu
```

UTC: 2026-11-08T13:31:18.945079+00:00; elapsed: 0.004419s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## record-first-wins / dump

```yulang
our defaulted base = {..base, x: 7}
((defaulted {}).x, (defaulted {x: 9}).x)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3-completeness/record-first-wins.yu
```

UTC: 2026-11-08T13:31:18.949965+00:00; elapsed: 0.006497s; exit: 0; timeout: False

stdout:
```text
roots d0:defaulted
d0:defaulted: 'a -> {..'a, x: int} = e3:(fn p0:d1:base -> e2:{..e0:r0:base->d1:base, x: e1:7})
root exprs e13:(e7:(e6:(e4:r1:defaulted->d0:defaulted e5:{}).s0.x#field), e12:(e11:(e8:r2:defaulted->d0:defaulted e10:{x: e9:9}).s1.x#field))
runtime roots e13:(e7:(e6:(e4:r1:defaulted->d0:defaulted e5:{}).s0.x#field), e12:(e11:(e8:r2:defaulted->d0:defaulted e10:{x: e9:9}).s1.x#field))
detached {
  d1:base arg
}

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)

```

## record-first-wins / run

```yulang
our defaulted base = {..base, x: 7}
((defaulted {}).x, (defaulted {x: 9}).x)
```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3-completeness/record-first-wins.yu
```

UTC: 2026-11-08T13:31:18.957059+00:00; elapsed: 0.006329s; exit: 0; timeout: False

stdout:
```text
run roots [(7, 9)]

```

stderr:
```text
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/source-key: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/compiled-unit: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/poly: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/mono: Read-only file system (os error 30)
warning: failed to create cache directory /home/agent/.cache/yulang/artifacts/control-ir: Read-only file system (os error 30)

```
