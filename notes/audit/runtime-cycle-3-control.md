# Cycle 3 raw log: control

新spec基点 `816ed8f1d`、旧実機 `d4c8bc8fc`。出力はそのまま。dump exit 0 は診断なしを意味しない。

## 1. label-case

```yulang
case 'again :next:
    :next -> 'again :end
    :end -> 7

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/label-case.yu
```

UTC start: 2026-11-08T13:39:30.652506+00:00; elapsed: 0.006279 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 2. label-case

```yulang
case 'again :next:
    :next -> 'again :end
    :end -> 7

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/label-case.yu
```

UTC start: 2026-11-08T13:39:30.659002+00:00; elapsed: 0.006000 s; exit: 0; timeout: False

stdout:
```text
roots
root exprs e10:block { let my p0:d1:"'again" = e7:(fn p1:d2:"#case-scrutinee" -> e6:case e1:r0:"#case-scrutinee"->d2:"#case-scrutinee" { p2::next -> e4:(e2:r1:"'again"->d1:"'again" e3::end); p3::end -> e5:7 }); e9:(e8:r2:"'again"->d1:"'again" e0::next) }
runtime roots e10:block { let my p0:d1:"'again" = e7:(fn p1:d2:"#case-scrutinee" -> e6:case e1:r0:"#case-scrutinee"->d2:"#case-scrutinee" { p2::next -> e4:(e2:r1:"'again"->d1:"'again" e3::end); p3::end -> e5:7 }); e9:(e8:r2:"'again"->d1:"'again" e0::next) }
detached {
  my d1:"'again": :{next, end} -> int = e7:(fn p1:d2:"#case-scrutinee" -> e6:case e1:r0:"#case-scrutinee"->d2:"#case-scrutinee" { p2::next -> e4:(e2:r1:"'again"->d1:"'again" e3::end); p3::end -> e5:7 })
  d2:"#case-scrutinee" arg
}

```

stderr:
```text

```

## 3. label-case

```yulang
case 'again :next:
    :next -> 'again :end
    :end -> 7

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/label-case.yu
```

UTC start: 2026-11-08T13:39:30.665162+00:00; elapsed: 0.002844 s; exit: 0; timeout: False

stdout:
```text
run roots [7]

```

stderr:
```text

```

## 4. label-case-method

```yulang
case 'again :next:
    :next -> 'again.again :end
    :end -> 7

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/label-case-method.yu
```

UTC start: 2026-11-08T13:39:30.668183+00:00; elapsed: 0.004147 s; exit: 1; timeout: False

stdout:
```text
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `function` is not compatible with required shape `record {again}`
    hint: check that the value provides the fields or shape required by this use

```

stderr:
```text

```

## 5. label-case-method

```yulang
case 'again :next:
    :next -> 'again.again :end
    :end -> 7

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/label-case-method.yu
```

UTC start: 2026-11-08T13:39:30.672626+00:00; elapsed: 0.004480 s; exit: 0; timeout: False

stdout:
```text
roots
root exprs e11:block { let my p0:d1:"'again" = e8:(fn p1:d2:"#case-scrutinee" -> e7:case e1:r0:"#case-scrutinee"->d2:"#case-scrutinee" { p2::next -> e5:(e3:(e2:r1:"'again"->d1:"'again".s0.again#field) e4::end); p3::end -> e6:7 }); e10:(e9:r2:"'again"->d1:"'again" e0::next) }
runtime roots e11:block { let my p0:d1:"'again" = e8:(fn p1:d2:"#case-scrutinee" -> e7:case e1:r0:"#case-scrutinee"->d2:"#case-scrutinee" { p2::next -> e5:(e3:(e2:r1:"'again"->d1:"'again".s0.again#field) e4::end); p3::end -> e6:7 }); e10:(e9:r2:"'again"->d1:"'again" e0::next) }
detached {
  my d1:"'again": :{next, end} -> int = e8:(fn p1:d2:"#case-scrutinee" -> e7:case e1:r0:"#case-scrutinee"->d2:"#case-scrutinee" { p2::next -> e5:(e3:(e2:r1:"'again"->d1:"'again".s0.again#field) e4::end); p3::end -> e6:7 })
  d2:"#case-scrutinee" arg
}

```

stderr:
```text
error: type shape `function` is not compatible with required shape `record {again}`

```

## 6. label-case-method

```yulang
case 'again :next:
    :next -> 'again.again :end
    :end -> 7

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/label-case-method.yu
```

UTC start: 2026-11-08T13:39:30.677262+00:00; elapsed: 0.005764 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `function` is not compatible with required shape `record {again}`
  hint: run `yulang check` to see source ranges before running

```

## 7. label-catch

```yulang
catch 'again :next:
    :next -> 'again :end
    :end -> 7

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/label-catch.yu
```

UTC start: 2026-11-08T13:39:30.683213+00:00; elapsed: 0.006330 s; exit: 1; timeout: False

stdout:
```text
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `int` is not compatible with required shape `polymorphic variant {next}`
    --> line 2, column 21
    2 |     :next -> 'again :end
      |                     ^^^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `polymorphic variant {next}` comes from this requirement
    --> line 2, column 14
    2 |     :next -> 'again :end
      |              ^^^^^^
  error [yulang.unsatisfied-subtype]: type shape `int` is not compatible with required shape `polymorphic variant {end}`
    --> line 2, column 21
    2 |     :next -> 'again :end
      |                     ^^^^
    hint: check that the value provides the fields or shape required by this use
    note: required shape `polymorphic variant {end}` comes from this requirement
    --> line 2, column 14
    2 |     :next -> 'again :end
      |              ^^^^^^

```

stderr:
```text

```

## 8. label-catch

```yulang
catch 'again :next:
    :next -> 'again :end
    :end -> 7

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/label-catch.yu
```

UTC start: 2026-11-08T13:39:30.689751+00:00; elapsed: 0.007275 s; exit: 0; timeout: False

stdout:
```text
roots
root exprs e10:block { let my p0:d1:"'again" = e7:(fn p1:d2:"#catch-scrutinee" -> e6:catch e1:r0:"#catch-scrutinee"->d2:"#catch-scrutinee" { p2::next -> e4:(e2:r1:"'again"->d1:"'again" e3::end); p3::end -> e5:7 }); e9:(e8:r2:"'again"->d1:"'again" e0::next) }
runtime roots e10:block { let my p0:d1:"'again" = e7:(fn p1:d2:"#catch-scrutinee" -> e6:catch e1:r0:"#catch-scrutinee"->d2:"#catch-scrutinee" { p2::next -> e4:(e2:r1:"'again"->d1:"'again" e3::end); p3::end -> e5:7 }); e9:(e8:r2:"'again"->d1:"'again" e0::next) }
detached {
  my d1:"'again": ('a & :{next, end}) ['b] -> ['b] 'a | int | :{end} = e7:(fn p1:d2:"#catch-scrutinee" -> e6:catch e1:r0:"#catch-scrutinee"->d2:"#catch-scrutinee" { p2::next -> e4:(e2:r1:"'again"->d1:"'again" e3::end); p3::end -> e5:7 })
  d2:"#catch-scrutinee" arg
}

```

stderr:
```text
error: type shape `int` is not compatible with required shape `polymorphic variant {next}`
error: type shape `int` is not compatible with required shape `polymorphic variant {end}`

```

## 9. label-catch

```yulang
catch 'again :next:
    :next -> 'again :end
    :end -> 7

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/label-catch.yu
```

UTC start: 2026-11-08T13:39:30.697233+00:00; elapsed: 0.007631 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `int` is not compatible with required shape `polymorphic variant {next}`
  detail: type shape `int` is not compatible with required shape `polymorphic variant {end}`
  hint: run `yulang check` to see source ranges before running

```

## 10. label-catch-method

```yulang
catch 'again :next:
    :next -> 'again.again :end
    :end -> 7

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/label-catch-method.yu
```

UTC start: 2026-11-08T13:39:30.705175+00:00; elapsed: 0.004438 s; exit: 1; timeout: False

stdout:
```text
diagnostics:
  error [yulang.unsatisfied-subtype]: type shape `int` is not compatible with required shape `polymorphic variant {next}`
    hint: check that the value provides the fields or shape required by this use
  error [yulang.unsatisfied-subtype]: type shape `int` is not compatible with required shape `polymorphic variant {end}`
    hint: check that the value provides the fields or shape required by this use
  error [yulang.unsatisfied-subtype]: type shape `function` is not compatible with required shape `record {again}`
    hint: check that the value provides the fields or shape required by this use

```

stderr:
```text

```

## 11. label-catch-method

```yulang
catch 'again :next:
    :next -> 'again.again :end
    :end -> 7

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/label-catch-method.yu
```

UTC start: 2026-11-08T13:39:30.709986+00:00; elapsed: 0.005656 s; exit: 0; timeout: False

stdout:
```text
roots
root exprs e11:block { let my p0:d1:"'again" = e8:(fn p1:d2:"#catch-scrutinee" -> e7:catch e1:r0:"#catch-scrutinee"->d2:"#catch-scrutinee" { p2::next -> e5:(e3:(e2:r1:"'again"->d1:"'again".s0.again#field) e4::end); p3::end -> e6:7 }); e10:(e9:r2:"'again"->d1:"'again" e0::next) }
runtime roots e11:block { let my p0:d1:"'again" = e8:(fn p1:d2:"#catch-scrutinee" -> e7:catch e1:r0:"#catch-scrutinee"->d2:"#catch-scrutinee" { p2::next -> e5:(e3:(e2:r1:"'again"->d1:"'again".s0.again#field) e4::end); p3::end -> e6:7 }); e10:(e9:r2:"'again"->d1:"'again" e0::next) }
detached {
  my d1:"'again": ('a & :{next, end}) ['b] -> ['b] 'a | int = e8:(fn p1:d2:"#catch-scrutinee" -> e7:catch e1:r0:"#catch-scrutinee"->d2:"#catch-scrutinee" { p2::next -> e5:(e3:(e2:r1:"'again"->d1:"'again".s0.again#field) e4::end); p3::end -> e6:7 })
  d2:"#catch-scrutinee" arg
}

```

stderr:
```text
error: type shape `int` is not compatible with required shape `polymorphic variant {next}`
error: type shape `int` is not compatible with required shape `polymorphic variant {end}`
error: type shape `function` is not compatible with required shape `record {again}`

```

## 12. label-catch-method

```yulang
catch 'again :next:
    :next -> 'again.again :end
    :end -> 7

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/label-catch-method.yu
```

UTC start: 2026-11-08T13:39:30.715909+00:00; elapsed: 0.004879 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
compile error [yulang.lowering]: source has lowering errors
  detail: type shape `int` is not compatible with required shape `polymorphic variant {next}`
  detail: type shape `int` is not compatible with required shape `polymorphic variant {end}`
  detail: type shape `function` is not compatible with required shape `record {again}`
  hint: run `yulang check` to see source ranges before running

```

## 13. enum-unqualified

```yulang
enum color = red | green | blue
case color::blue:
    red -> 1
    green -> 2
    blue -> 3

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/enum-unqualified.yu
```

UTC start: 2026-11-08T13:39:30.721096+00:00; elapsed: 0.003553 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 14. enum-unqualified

```yulang
enum color = red | green | blue
case color::blue:
    red -> 1
    green -> 2
    blue -> 3

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/enum-unqualified.yu
```

UTC start: 2026-11-08T13:39:30.724930+00:00; elapsed: 0.003903 s; exit: 0; timeout: False

stdout:
```text
roots d0:color
d0:color mod {
  d1:"color.red": color = <missing>
  d2:"color.green": color = <missing>
  d3:"color.blue": color = <missing>
}
root exprs e4:case e0:r0:"color::blue"->d3:"color.blue" { p0:d5:red -> e1:1; p1:d6:green -> e2:2; p2:d7:blue -> e3:3 }
runtime roots e4:case e0:r0:"color::blue"->d3:"color.blue" { p0:d5:red -> e1:1; p1:d6:green -> e2:2; p2:d7:blue -> e3:3 }
detached {
  d5:red arg
  d6:green arg
  d7:blue arg
}

```

stderr:
```text

```

## 15. enum-unqualified

```yulang
enum color = red | green | blue
case color::blue:
    red -> 1
    green -> 2
    blue -> 3

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/enum-unqualified.yu
```

UTC start: 2026-11-08T13:39:30.729131+00:00; elapsed: 0.002776 s; exit: 0; timeout: False

stdout:
```text
run roots [1]

```

stderr:
```text

```

## 16. enum-qualified

```yulang
enum color = red | green | blue
case color::blue:
    color::red -> 1
    color::green -> 2
    color::blue -> 3

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/enum-qualified.yu
```

UTC start: 2026-11-08T13:39:30.732237+00:00; elapsed: 0.003650 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 17. enum-qualified

```yulang
enum color = red | green | blue
case color::blue:
    color::red -> 1
    color::green -> 2
    color::blue -> 3

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/enum-qualified.yu
```

UTC start: 2026-11-08T13:39:30.736129+00:00; elapsed: 0.004414 s; exit: 0; timeout: False

stdout:
```text
roots d0:color
d0:color mod {
  d1:"color.red": color = <missing>
  d2:"color.green": color = <missing>
  d3:"color.blue": color = <missing>
}
root exprs e4:case e0:r0:"color::blue"->d3:"color.blue" { p0:r1:"color::red"->d1:"color.red" -> e1:1; p1:r2:"color::green"->d2:"color.green" -> e2:2; p2:r3:"color::blue"->d3:"color.blue" -> e3:3 }
runtime roots e4:case e0:r0:"color::blue"->d3:"color.blue" { p0:r1:"color::red"->d1:"color.red" -> e1:1; p1:r2:"color::green"->d2:"color.green" -> e2:2; p2:r3:"color::blue"->d3:"color.blue" -> e3:3 }

```

stderr:
```text

```

## 18. enum-qualified

```yulang
enum color = red | green | blue
case color::blue:
    color::red -> 1
    color::green -> 2
    color::blue -> 3

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/enum-qualified.yu
```

UTC start: 2026-11-08T13:39:30.740826+00:00; elapsed: 0.002420 s; exit: 0; timeout: False

stdout:
```text
run roots [3]

```

stderr:
```text

```

## 19. enum-imported

```yulang
enum color = red | green | blue
use color::*
case blue:
    red -> 1
    green -> 2
    blue -> 3

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/enum-imported.yu
```

UTC start: 2026-11-08T13:39:30.743652+00:00; elapsed: 0.003802 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 20. enum-imported

```yulang
enum color = red | green | blue
use color::*
case blue:
    red -> 1
    green -> 2
    blue -> 3

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/enum-imported.yu
```

UTC start: 2026-11-08T13:39:30.747824+00:00; elapsed: 0.004533 s; exit: 0; timeout: False

stdout:
```text
roots d0:color
d0:color mod {
  d1:"color.red": color = <missing>
  d2:"color.green": color = <missing>
  d3:"color.blue": color = <missing>
}
root exprs e4:case e0:r0:blue->d3:"color.blue" { p0:r1:red->d1:"color.red" -> e1:1; p1:r2:green->d2:"color.green" -> e2:2; p2:r3:blue->d3:"color.blue" -> e3:3 }
runtime roots e4:case e0:r0:blue->d3:"color.blue" { p0:r1:red->d1:"color.red" -> e1:1; p1:r2:green->d2:"color.green" -> e2:2; p2:r3:blue->d3:"color.blue" -> e3:3 }

```

stderr:
```text

```

## 21. enum-imported

```yulang
enum color = red | green | blue
use color::*
case blue:
    red -> 1
    green -> 2
    blue -> 3

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/enum-imported.yu
```

UTC start: 2026-11-08T13:39:30.752733+00:00; elapsed: 0.002518 s; exit: 0; timeout: False

stdout:
```text
run roots [3]

```

stderr:
```text

```

## 22. label-case-shadow

```yulang
case 'again :outer:
    :outer -> case 'again :inner:
        :inner -> 'again :end
        :end -> 11
    :end -> 22

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/label-case-shadow.yu
```

UTC start: 2026-11-08T13:39:30.755669+00:00; elapsed: 0.008222 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 23. label-case-shadow

```yulang
case 'again :outer:
    :outer -> case 'again :inner:
        :inner -> 'again :end
        :end -> 11
    :end -> 22

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/label-case-shadow.yu
```

UTC start: 2026-11-08T13:39:30.764285+00:00; elapsed: 0.006765 s; exit: 0; timeout: False

stdout:
```text
roots
root exprs e18:block { let my p0:d1:"'again" = e15:(fn p1:d2:"#case-scrutinee" -> e14:case e1:r0:"#case-scrutinee"->d2:"#case-scrutinee" { p2::outer -> e12:block { let my p3:d3:"'again" = e9:(fn p4:d4:"#case-scrutinee" -> e8:case e3:r1:"#case-scrutinee"->d4:"#case-scrutinee" { p5::inner -> e6:(e4:r2:"'again"->d3:"'again" e5::end); p6::end -> e7:11 }); e11:(e10:r3:"'again"->d3:"'again" e2::inner) }; p7::end -> e13:22 }); e17:(e16:r4:"'again"->d1:"'again" e0::outer) }
runtime roots e18:block { let my p0:d1:"'again" = e15:(fn p1:d2:"#case-scrutinee" -> e14:case e1:r0:"#case-scrutinee"->d2:"#case-scrutinee" { p2::outer -> e12:block { let my p3:d3:"'again" = e9:(fn p4:d4:"#case-scrutinee" -> e8:case e3:r1:"#case-scrutinee"->d4:"#case-scrutinee" { p5::inner -> e6:(e4:r2:"'again"->d3:"'again" e5::end); p6::end -> e7:11 }); e11:(e10:r3:"'again"->d3:"'again" e2::inner) }; p7::end -> e13:22 }); e17:(e16:r4:"'again"->d1:"'again" e0::outer) }
detached {
  my d1:"'again": :{outer, end} -> int = e15:(fn p1:d2:"#case-scrutinee" -> e14:case e1:r0:"#case-scrutinee"->d2:"#case-scrutinee" { p2::outer -> e12:block { let my p3:d3:"'again" = e9:(fn p4:d4:"#case-scrutinee" -> e8:case e3:r1:"#case-scrutinee"->d4:"#case-scrutinee" { p5::inner -> e6:(e4:r2:"'again"->d3:"'again" e5::end); p6::end -> e7:11 }); e11:(e10:r3:"'again"->d3:"'again" e2::inner) }; p7::end -> e13:22 })
  d2:"#case-scrutinee" arg
  my d3:"'again": :{inner, end} -> int = e9:(fn p4:d4:"#case-scrutinee" -> e8:case e3:r1:"#case-scrutinee"->d4:"#case-scrutinee" { p5::inner -> e6:(e4:r2:"'again"->d3:"'again" e5::end); p6::end -> e7:11 })
  d4:"#case-scrutinee" arg
}

```

stderr:
```text

```

## 24. label-case-shadow

```yulang
case 'again :outer:
    :outer -> case 'again :inner:
        :inner -> 'again :end
        :end -> 11
    :end -> 22

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/label-case-shadow.yu
```

UTC start: 2026-11-08T13:39:30.771449+00:00; elapsed: 0.002924 s; exit: 0; timeout: False

stdout:
```text
run roots [11]

```

stderr:
```text

```

## 25. case-guard-miss

```yulang
act ping:
    our get: () -> bool
catch (case 2:
    1 if ping::get() -> 10
    _ -> 20):
    ping::get(), k -> 99
    value -> value

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/case-guard-miss.yu
```

UTC start: 2026-11-08T13:39:30.774835+00:00; elapsed: 0.002808 s; exit: 1; timeout: False

stdout:
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 12
    5 |     _ -> 20):
      |            ^
  error [yulang.unresolved-value]: unresolved value name in root expression: std::control::junction::junction::junction
    hint: define `std::control::junction::junction::junction` before this use, or import the module that provides it

```

stderr:
```text

```

## 26. case-guard-miss

```yulang
act ping:
    our get: () -> bool
catch (case 2:
    1 if ping::get() -> 10
    _ -> 20):
    ping::get(), k -> 99
    value -> value

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/case-guard-miss.yu
```

UTC start: 2026-11-08T13:39:30.778040+00:00; elapsed: 0.003140 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping
d0:ping mod {
}
detached {
  d1:"ping.get": () -> [ping] bool = <missing>
}

```

stderr:
```text
error: unresolved value name in root expression: std::control::junction::junction::junction

```

## 27. case-guard-miss

```yulang
act ping:
    our get: () -> bool
catch (case 2:
    1 if ping::get() -> 10
    _ -> 20):
    ping::get(), k -> 99
    value -> value

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/case-guard-miss.yu
```

UTC start: 2026-11-08T13:39:30.781721+00:00; elapsed: 0.001753 s; exit: 1; timeout: False

stdout:
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 12
    5 |     _ -> 20):
      |            ^

```

stderr:
```text

```

## 28. case-guard-hit

```yulang
act ping:
    our get: () -> bool
catch (case 1:
    1 if ping::get() -> 10
    _ -> 20):
    ping::get(), k -> 99
    value -> value

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/case-guard-hit.yu
```

UTC start: 2026-11-08T13:39:30.783944+00:00; elapsed: 0.002487 s; exit: 1; timeout: False

stdout:
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 12
    5 |     _ -> 20):
      |            ^
  error [yulang.unresolved-value]: unresolved value name in root expression: std::control::junction::junction::junction
    hint: define `std::control::junction::junction::junction` before this use, or import the module that provides it

```

stderr:
```text

```

## 29. case-guard-hit

```yulang
act ping:
    our get: () -> bool
catch (case 1:
    1 if ping::get() -> 10
    _ -> 20):
    ping::get(), k -> 99
    value -> value

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --poly /tmp/audit3/case-guard-hit.yu
```

UTC start: 2026-11-08T13:39:30.786879+00:00; elapsed: 0.002917 s; exit: 0; timeout: False

stdout:
```text
roots d0:ping
d0:ping mod {
}
detached {
  d1:"ping.get": () -> [ping] bool = <missing>
}

```

stderr:
```text
error: unresolved value name in root expression: std::control::junction::junction::junction

```

## 30. case-guard-hit

```yulang
act ping:
    our get: () -> bool
catch (case 1:
    1 if ping::get() -> 10
    _ -> 20):
    ping::get(), k -> 99
    value -> value

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/case-guard-hit.yu
```

UTC start: 2026-11-08T13:39:30.790219+00:00; elapsed: 0.001703 s; exit: 1; timeout: False

stdout:
```text
diagnostics:
  error [yulang.syntax]: syntax error: unexpected token
    --> line 5, column 12
    5 |     _ -> 20):
      |            ^

```

stderr:
```text

```
