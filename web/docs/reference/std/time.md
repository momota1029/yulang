# `std::time`

`std::time` provides pure instant and duration values, wall-clock access, unit
constructors, arithmetic, comparison, and fixed UTC display.

An `instant` is a point on the timeline stored as nanoseconds from the Unix
epoch. A `duration` is a signed nanosecond count. Both are public data:

| Type | Public field | Meaning |
|---|---|---|
| `instant` | `epoch_nanos: int` | Nanoseconds from the Unix epoch |
| `duration` | `nanos: int` | A signed length of time in nanoseconds |

Constructing either value directly is deterministic and is useful for fixtures.
Acquiring the current time is effectful and goes through the host clock.

## Clock access

`clock::now()` has the signature `() -> [clock] instant`. The `clock` host act
is also re-exported as `std::time::now` and through the prelude.

```yulang
my current = std::time::clock::now()
(current.epoch_nanos, current.show)
```

The first result is the host's current Unix-epoch nanosecond count. The second
is the same instant in RFC 3339 UTC form. Both values change between runs.

`clock::now()` reads a wall clock. The value can move backward when the host
clock moves backward, so it must not be used for performance measurements.

## Instant arithmetic

The named instant operations add or subtract a duration and find the signed
duration between two instants.

```yulang
my start = std::time::instant { epoch_nanos: 10 }
my stop = std::time::instant { epoch_nanos: 25 }
my elapsed = std::time::instant_since stop start

(
    elapsed.nanos,
    (std::time::instant_add start elapsed).epoch_nanos,
    (std::time::instant_sub stop elapsed).epoch_nanos,
)
```

The result is `(15, 25, 10)`. Reversing the arguments to `instant_since`
produces a negative duration.

Use these named functions for instant arithmetic. `instant` does not currently
implement the `+` or `-` operators.

## Duration construction and arithmetic

Each unit constructor takes an `int` and returns a `duration`. Larger units are
exact integer multiples of nanoseconds.

```yulang
my total = std::time::days 1 + std::time::hours 2 + std::time::mins 3 + std::time::secs 4

(
    (std::time::nanos 5).nanos,
    (std::time::micros 2).nanos,
    (std::time::millis 3).nanos,
    total.nanos,
    (std::time::duration_add (std::time::secs 2) (std::time::secs 3)).nanos,
    (std::time::duration_sub (std::time::secs 5) (std::time::secs 3)).nanos,
    (std::time::hours 2 - std::time::mins 30).nanos,
)
```

The first three values are `5`, `2000`, and `3000000`. `duration` implements
`Add` and `Sub`, so `+` and `-` use the same behavior as `duration_add` and
`duration_sub`.

## Comparison and formatting

`instant` and `duration` implement `Eq` and `Ord`. Instants compare their
`epoch_nanos` fields, and durations compare their `nanos` fields.

```yulang
my epoch = std::time::instant { epoch_nanos: 0 }
my later = std::time::instant { epoch_nanos: 1 }
my gap = std::time::duration { nanos: 1 }

(
    epoch < later,
    gap == (std::time::nanos 1),
    epoch.show,
    epoch.debug,
    gap.debug,
)
```

The result is
`(true, true, "1970-01-01T00:00:00Z", "instant { epoch_nanos: 0 }", "duration { nanos: 1 }")`.
`instant.show` uses RFC 3339 UTC and trims unnecessary fractional-second
zeros. `Debug` preserves the public structural representation. `duration`
implements `Debug`, but not `Display`.

## Scope

`std::time` does not provide calendars, time zones, locale-sensitive
formatting, parsing, timers, sleep, deadlines, or a monotonic clock. Leap
second handling follows the host clock and is otherwise unspecified.

## Quick reference

| Operation | Signature |
|---|---|
| `clock::now()` | `() -> [clock] instant` |
| `instant_add(t, delta)` | `instant -> duration -> instant` |
| `instant_sub(t, delta)` | `instant -> duration -> instant` |
| `instant_since(later, earlier)` | `instant -> instant -> duration` |
| `duration_add(x, y)` | `duration -> duration -> duration` |
| `duration_sub(x, y)` | `duration -> duration -> duration` |
| `nanos(count)` | `int -> duration` |
| `micros(count)` | `int -> duration` |
| `millis(count)` | `int -> duration` |
| `secs(count)` | `int -> duration` |
| `mins(count)` | `int -> duration` |
| `hours(count)` | `int -> duration` |
| `days(count)` | `int -> duration` |
| `x + y` / `x - y` | `duration -> duration -> duration` |
| `x == y`, `x < y`, and related comparisons | `instant -> instant -> bool` or `duration -> duration -> bool` |
| `t.show` | `instant -> str` |
| `t.debug` | `instant -> str` or `duration -> str` |

## See also

- [`std::io::file`](./fs) — file metadata can contain `opt instant`
- [Effects](../effects) — host acts and effect handlers
- [Standard Library Catalogue](./) — the full module inventory
