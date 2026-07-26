# Numeric and Boolean Standard Library

This page covers `std::bool`, `std::int`, `std::float`, `std::num`, and
`std::num::frac`. It distinguishes primitive operations from the role methods
used by overloaded operators.

## `std::bool`

`std::bool` provides equality, negation, and lowercase string conversion for
the built-in `bool` type.

```yulang
(
    std::bool::eq true false,
    std::bool::not false,
    std::bool::to_string true,
    not true,
)
```

The result is `(false, true, "true", false)`.

### Quick reference

| Operation | Signature |
| --- | --- |
| `eq(x, y)` | `bool -> bool -> bool` |
| `not(x)` | `bool -> bool` |
| `to_string(x)` | `bool -> str` |

## `std::int`

`std::int` provides comparison, integer arithmetic, truncating division,
remainder, and decimal and hexadecimal string conversion for `int`.

```yulang
(
    std::int::add 2 3,
    std::int::sub 7 2,
    std::int::mul 3 4,
    std::int::div 7 2,
    17 mod 5,
    std::int::to_string (-42),
    std::int::to_hex 255,
    std::int::to_upper_hex 255,
)
```

The result is `(5, 5, 12, 3, 2, "-42", "ff", "FF")`. The `div` and `mod`
operators call the integer primitives. Division or remainder by zero fails at
runtime.

The `/` operator has different behavior for integers: it resolves through
`std::num::Div` and returns an exact `frac`. For example, `2 / 4` is `1/2`,
while `2 div 4` is `0`.

### Quick reference

| Operation | Signature |
| --- | --- |
| `eq(x, y)` | `int -> int -> bool` |
| `lt(x, y)` / `le(x, y)` | `int -> int -> bool` |
| `gt(x, y)` / `ge(x, y)` | `int -> int -> bool` |
| `add(x, y)` | `int -> int -> int` |
| `sub(x, y)` | `int -> int -> int` |
| `mul(x, y)` | `int -> int -> int` |
| `div(x, y)` / `x div y` | `int -> int -> int` |
| `mod(x, y)` / `x mod y` | `int -> int -> int` |
| `to_string(x)` | `int -> str` |
| `to_hex(x)` / `to_upper_hex(x)` | `int -> str` |

## `std::float`

`std::float` provides comparison, arithmetic, and string conversion primitives
for `float`.

```yulang
(
    std::float::lt 1.0 2.0,
    std::float::add 1.5 2.0,
    std::float::sub 5.0 1.5,
    std::float::mul 2.0 3.5,
    std::float::div 7.0 2.0,
    std::float::to_string 1.5,
)
```

The result is `(true, 3.5, 3.5, 7, 3.5, "1.5")`.

### Quick reference

| Operation | Signature |
| --- | --- |
| `eq(x, y)` | `float -> float -> bool` |
| `lt(x, y)` / `le(x, y)` | `float -> float -> bool` |
| `gt(x, y)` / `ge(x, y)` | `float -> float -> bool` |
| `add(x, y)` | `float -> float -> float` |
| `sub(x, y)` | `float -> float -> float` |
| `mul(x, y)` | `float -> float -> float` |
| `div(x, y)` | `float -> float -> float` |
| `to_string(x)` | `float -> str` |

## `std::num`

`std::num` defines the arithmetic roles used by `+`, `-`, `*`, and `/`, plus
the hexadecimal-formatting roles used by string interpolation.

| Role | Member |
| --- | --- |
| `Add 'a` | `a.add: 'a -> 'a` |
| `Sub 'a` | `a.sub: 'a -> 'a` |
| `Mul 'a` | `a.mul: 'a -> 'a` |
| `Div 'a` | `a.div: 'a -> Div::out` |
| `LowerHex 'a` | `a.lower_hex: str` |
| `UpperHex 'a` | `a.upper_hex: str` |

`int`, `float`, and `frac` implement the four arithmetic roles. Integer
`Div::out` is `frac`; the other two division implementations return their
receiver type. `str` and `list 'a` implement `Add` as concatenation. Only
`int` implements the two hexadecimal roles.

```yulang
my half = std::num::frac::new 1 2

(
    2.add 3,
    2.div 4,
    (7.0).div 2.0,
    half.mul half,
    "a".add "b",
    [1].add [2],
    255.lower_hex,
    255.upper_hex,
)
```

The result is `(5, 1/2, 3.5, 1/4, "ab", [1, 2], "ff", "FF")`.

## `std::num::frac`

`frac` is a public `{ num: int, den: int }` value for exact rational
arithmetic. `new` reduces both fields by their greatest common divisor and
moves a negative sign to `num`.

```yulang
my x = std::num::frac::new 6 (-8)
my y = std::num::frac::new 1 2

(
    (x.num, x.den),
    std::num::frac::add x y,
    std::num::frac::sub x y,
    std::num::frac::mul x y,
    std::num::frac::div x y,
    x < y,
    std::num::frac::to_float x,
    x.show,
)
```

The result is `((-3, 4), -1/4, -5/4, -3/8, -3/2, true, -0.75, "-3/4")`.
Comparison operators come from the `Eq` and `Ord` implementations, and
`Display` uses `to_string`.

Pass a nonzero denominator to `new`. The current implementation does not
validate this invariant: a nonzero numerator with denominator `0` produces a
value whose `den` remains `0`, while `new 0 0` fails at runtime. Constructing
`frac { num, den }` directly also bypasses normalization.

### Quick reference

| Operation | Signature |
| --- | --- |
| `new(n, d)` | `int -> int -> frac` |
| `add(x, y)` / `x + y` | `frac -> frac -> frac` |
| `sub(x, y)` / `x - y` | `frac -> frac -> frac` |
| `mul(x, y)` / `x * y` | `frac -> frac -> frac` |
| `div(x, y)` / `x / y` | `frac -> frac -> frac` |
| `eq(x, y)` / `x == y` | `frac -> frac -> bool` |
| `lt(x, y)` / `le(x, y)` | `frac -> frac -> bool` |
| `gt(x, y)` / `ge(x, y)` | `frac -> frac -> bool` |
| `to_float(x)` | `frac -> float` |
| `to_string(x)` / `x.show` | `frac -> str` |

## See also

- [Operators](../operators) — operator declarations and precedence
- [Strings](../strings) — numeric display and hexadecimal interpolation
- [Casts](../casts) — implicit conversions among `int`, `frac`, and `float`
- [Standard Library Catalogue](./) — the full module inventory
