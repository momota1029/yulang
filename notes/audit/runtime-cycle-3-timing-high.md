# Cycle 3 raw log: timing-high

新spec基点 `816ed8f1d`、旧実機 `d4c8bc8fc`。出力はそのまま。dump exit 0 は診断なしを意味しない。

## 1. high-inferred-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/high-inferred-ignore.yu
```

UTC start: 2026-11-08T13:35:06.604287+00:00; elapsed: 0.012754 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 2. high-inferred-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/high-inferred-ignore.yu
```

UTC start: 2026-11-08T13:35:06.617339+00:00; elapsed: 0.014049 s; exit: 0; timeout: False

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

## 3. high-inferred-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/high-inferred-ignore.yu
```

UTC start: 2026-11-08T13:35:06.631721+00:00; elapsed: 0.004519 s; exit: 0; timeout: False

stdout:
```text
run roots [42]

```

stderr:
```text

```

## 4. high-inferred-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit3/high-inferred-ignore.yu
```

UTC start: 2026-11-08T13:35:06.636466+00:00; elapsed: 0.002573 s; exit: 0; timeout: False

stdout:
```text
run roots [42]

```

stderr:
```text

```

## 5. high-inferred-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/high-inferred-identity.yu
```

UTC start: 2026-11-08T13:35:06.639284+00:00; elapsed: 0.011213 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 6. high-inferred-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/high-inferred-identity.yu
```

UTC start: 2026-11-08T13:35:06.650794+00:00; elapsed: 0.011445 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d2 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> 99, d8 -> d8
m1 = d5 : (thunk[[ping], int] -> int) -> int
  \d13 -> (d13 (<effect-op ping::get> ()))
m2 = d4 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d12 -> d12)

```

stderr:
```text

```

## 7. high-inferred-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/high-inferred-identity.yu
```

UTC start: 2026-11-08T13:35:06.662476+00:00; elapsed: 0.005070 s; exit: 0; timeout: False

stdout:
```text
run roots [99]

```

stderr:
```text

```

## 8. high-inferred-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit3/high-inferred-identity.yu
```

UTC start: 2026-11-08T13:35:06.668096+00:00; elapsed: 0.002426 s; exit: 0; timeout: False

stdout:
```text
run roots [99]

```

stderr:
```text

```

## 9. high-pure-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/high-pure-ignore.yu
```

UTC start: 2026-11-08T13:35:06.670982+00:00; elapsed: 0.010439 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 10. high-pure-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/high-pure-ignore.yu
```

UTC start: 2026-11-08T13:35:06.681789+00:00; elapsed: 0.012736 s; exit: 0; timeout: False

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

## 11. high-pure-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/high-pure-ignore.yu
```

UTC start: 2026-11-08T13:35:06.694975+00:00; elapsed: 0.005724 s; exit: 0; timeout: False

stdout:
```text
run roots [42]

```

stderr:
```text

```

## 12. high-pure-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit3/high-pure-ignore.yu
```

UTC start: 2026-11-08T13:35:06.700965+00:00; elapsed: 0.002405 s; exit: 0; timeout: False

stdout:
```text
run roots [42]

```

stderr:
```text

```

## 13. high-pure-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/high-pure-identity.yu
```

UTC start: 2026-11-08T13:35:06.703672+00:00; elapsed: 0.011906 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 14. high-pure-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/high-pure-identity.yu
```

UTC start: 2026-11-08T13:35:06.715881+00:00; elapsed: 0.012098 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d2 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> 99, d8 -> d8
m1 = d5 : (thunk[[ping], int] -> int) -> int
  \d13 -> (d13 (<effect-op ping::get> ()))
m2 = d4 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d12 -> d12)

```

stderr:
```text

```

## 15. high-pure-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/high-pure-identity.yu
```

UTC start: 2026-11-08T13:35:06.728305+00:00; elapsed: 0.004704 s; exit: 0; timeout: False

stdout:
```text
run roots [99]

```

stderr:
```text

```

## 16. high-pure-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit3/high-pure-identity.yu
```

UTC start: 2026-11-08T13:35:06.733308+00:00; elapsed: 0.002904 s; exit: 0; timeout: False

stdout:
```text
run roots [99]

```

stderr:
```text

```

## 17. high-arg-row-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: [ping] int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/high-arg-row-ignore.yu
```

UTC start: 2026-11-08T13:35:06.736533+00:00; elapsed: 0.011237 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 18. high-arg-row-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: [ping] int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/high-arg-row-ignore.yu
```

UTC start: 2026-11-08T13:35:06.748085+00:00; elapsed: 0.013218 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((adapter[(thunk[[ping], int] -> int) -> int => (thunk[[ping], int] -> int) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m1) adapter[thunk[[ping], int] -> int => thunk[[ping], int] -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m2))))]
m0 = d2 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> 99, d8 -> d8
m1 = d5 : (thunk[[ping], int] -> int) -> int
  adapter[(thunk[[ping], int] -> int) -> int => (thunk[[ping], int] -> int) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](\d13 -> (d13 (<effect-op ping::get> ())))
m2 = d4 : thunk[[ping], int] -> int
  \d12 -> 42

```

stderr:
```text

```

## 19. high-arg-row-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: [ping] int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/high-arg-row-ignore.yu
```

UTC start: 2026-11-08T13:35:06.761840+00:00; elapsed: 0.004554 s; exit: 0; timeout: False

stdout:
```text
run roots [42]

```

stderr:
```text

```

## 20. high-arg-row-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: [ping] int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit3/high-arg-row-ignore.yu
```

UTC start: 2026-11-08T13:35:06.766829+00:00; elapsed: 0.003164 s; exit: 0; timeout: False

stdout:
```text
run roots [42]

```

stderr:
```text

```

## 21. high-arg-row-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: [ping] int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/high-arg-row-identity.yu
```

UTC start: 2026-11-08T13:35:06.770428+00:00; elapsed: 0.011686 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 22. high-arg-row-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: [ping] int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/high-arg-row-identity.yu
```

UTC start: 2026-11-08T13:35:06.782681+00:00; elapsed: 0.011535 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((adapter[(thunk[[ping], int] -> int) -> int => (thunk[[ping], int] -> int) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m1) adapter[thunk[[ping], int] -> int => thunk[[ping], int] -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](m2))))]
m0 = d2 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> 99, d8 -> d8
m1 = d5 : (thunk[[ping], int] -> int) -> int
  adapter[(thunk[[ping], int] -> int) -> int => (thunk[[ping], int] -> int) -> int; hygiene[arg[add_id[1, ping, own, resume-own]]]](\d13 -> (d13 (<effect-op ping::get> ())))
m2 = d4 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d12 -> d12)

```

stderr:
```text

```

## 23. high-arg-row-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: [ping] int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/high-arg-row-identity.yu
```

UTC start: 2026-11-08T13:35:06.794599+00:00; elapsed: 0.004309 s; exit: 0; timeout: False

stdout:
```text
run roots [99]

```

stderr:
```text

```

## 24. high-arg-row-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: [ping] int -> int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit3/high-arg-row-identity.yu
```

UTC start: 2026-11-08T13:35:06.799469+00:00; elapsed: 0.003522 s; exit: 0; timeout: False

stdout:
```text
run roots [99]

```

stderr:
```text

```

## 25. high-result-row-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/high-result-row-ignore.yu
```

UTC start: 2026-11-08T13:35:06.803465+00:00; elapsed: 0.011520 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 26. high-result-row-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/high-result-row-ignore.yu
```

UTC start: 2026-11-08T13:35:06.815368+00:00; elapsed: 0.012468 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 27. high-result-row-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/high-result-row-ignore.yu
```

UTC start: 2026-11-08T13:35:06.828235+00:00; elapsed: 0.011190 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 28. high-result-row-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit3/high-result-row-ignore.yu
```

UTC start: 2026-11-08T13:35:06.839882+00:00; elapsed: 0.003492 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 29. high-result-row-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/high-result-row-identity.yu
```

UTC start: 2026-11-08T13:35:06.844034+00:00; elapsed: 0.011851 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 30. high-result-row-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/high-result-row-identity.yu
```

UTC start: 2026-11-08T13:35:06.856315+00:00; elapsed: 0.010778 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 31. high-result-row-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/high-result-row-identity.yu
```

UTC start: 2026-11-08T13:35:06.867732+00:00; elapsed: 0.013522 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 32. high-result-row-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit3/high-result-row-identity.yu
```

UTC start: 2026-11-08T13:35:06.882224+00:00; elapsed: 0.002721 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 33. high-both-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: [ping] int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/high-both-ignore.yu
```

UTC start: 2026-11-08T13:35:06.885934+00:00; elapsed: 0.011778 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 34. high-both-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: [ping] int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/high-both-ignore.yu
```

UTC start: 2026-11-08T13:35:06.898666+00:00; elapsed: 0.011620 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 35. high-both-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: [ping] int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/high-both-ignore.yu
```

UTC start: 2026-11-08T13:35:06.911072+00:00; elapsed: 0.011729 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 36. high-both-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: [ping] int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit3/high-both-ignore.yu
```

UTC start: 2026-11-08T13:35:06.923347+00:00; elapsed: 0.003394 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 37. high-both-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: [ping] int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/high-both-identity.yu
```

UTC start: 2026-11-08T13:35:06.927250+00:00; elapsed: 0.011682 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 38. high-both-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: [ping] int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/high-both-identity.yu
```

UTC start: 2026-11-08T13:35:06.939877+00:00; elapsed: 0.013400 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 39. high-both-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: [ping] int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/high-both-identity.yu
```

UTC start: 2026-11-08T13:35:06.953990+00:00; elapsed: 0.011943 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 40. high-both-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: [ping] int -> [ping] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit3/high-both-identity.yu
```

UTC start: 2026-11-08T13:35:06.966635+00:00; elapsed: 0.003535 s; exit: 1; timeout: False

stdout:
```text

```

stderr:
```text
conflicting type candidates: [ping] vs []

```

## 41. high-wild-result-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: int -> [_] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/high-wild-result-ignore.yu
```

UTC start: 2026-11-08T13:35:06.970876+00:00; elapsed: 0.012358 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 42. high-wild-result-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: int -> [_] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/high-wild-result-ignore.yu
```

UTC start: 2026-11-08T13:35:06.983978+00:00; elapsed: 0.011937 s; exit: 0; timeout: False

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

## 43. high-wild-result-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: int -> [_] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/high-wild-result-ignore.yu
```

UTC start: 2026-11-08T13:35:06.996495+00:00; elapsed: 0.005096 s; exit: 0; timeout: False

stdout:
```text
run roots [42]

```

stderr:
```text

```

## 44. high-wild-result-ignore

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = 42
our higher(f: int -> [_] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit3/high-wild-result-ignore.yu
```

UTC start: 2026-11-08T13:35:07.002102+00:00; elapsed: 0.002773 s; exit: 0; timeout: False

stdout:
```text
run roots [42]

```

stderr:
```text

```

## 45. high-wild-result-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: int -> [_] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude check /tmp/audit3/high-wild-result-identity.yu
```

UTC start: 2026-11-08T13:35:07.005753+00:00; elapsed: 0.010890 s; exit: 0; timeout: False

stdout:
```text

```

stderr:
```text

```

## 46. high-wild-result-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: int -> [_] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude dump --mono /tmp/audit3/high-wild-result-identity.yu
```

UTC start: 2026-11-08T13:35:07.017279+00:00; elapsed: 0.012768 s; exit: 0; timeout: False

stdout:
```text
mono roots [(m0 make-thunk[int ! [] => thunk[[ping], int]]((m1 m2)))]
m0 = d2 : thunk[[ping], int] -> int
  \d6 -> catch marker[ping](force-thunk[thunk[[ping], int] => int ! [ping]](d6)): ping::get _, d7 -> 99, d8 -> d8
m1 = d5 : (thunk[[ping], int] -> int) -> int
  \d13 -> (d13 (<effect-op ping::get> ()))
m2 = d4 : thunk[[ping], int] -> int
  adapter[thunk[[ping], int] -> thunk[[ping], int] => thunk[[ping], int] -> int; hygiene[add_id[0, ping, own]]](\d12 -> d12)

```

stderr:
```text

```

## 47. high-wild-result-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: int -> [_] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --print-roots /tmp/audit3/high-wild-result-identity.yu
```

UTC start: 2026-11-08T13:35:07.030804+00:00; elapsed: 0.004259 s; exit: 0; timeout: False

stdout:
```text
run roots [99]

```

stderr:
```text

```

## 48. high-wild-result-identity

```yulang
act ping:
    our get: () -> int
our abort(action: [ping] int) = catch action:
    ping::get(), k -> 99
    value -> value
our resume(action: [ping] int) = catch action:
    ping::get(), k -> k 7
    value -> value
our actual(x: int): int = x
our higher(f: int -> [_] int) = f(ping::get())
abort(higher actual)

```

```sh
/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/release/yulang --std-root /workspace/scratch/1d0b4aaa3394/yulang-audit-y2/lib --no-prelude run --interpreter --print-roots /tmp/audit3/high-wild-result-identity.yu
```

UTC start: 2026-11-08T13:35:07.035833+00:00; elapsed: 0.002589 s; exit: 0; timeout: False

stdout:
```text
run roots [99]

```

stderr:
```text

```
