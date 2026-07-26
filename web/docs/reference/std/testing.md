# `std::testing`

`std::testing` provides lazy assertion operators and the `assertion` effect
used by `yulang test`. The prelude re-exports both operators.

The module introduces no data type. Test discovery belongs to the surrounding
test facility; see [Modules](../modules#test-modules) for that mechanism.

## Lazy assertion operators

`assert condition` requires a Boolean result. `expected assert_eq actual`
requires both operands to have the same inferred type.

```yulang
mod test assertions:
    my truth = assert (2 + 2 == 4)
    my equality = (2 + 2) assert_eq 4
```

Running this file with `yulang test --show-passes` reports two passing tests.
The left operand of `assert_eq` is the expected value, and the right operand is
the actual value.

Both operators are lazy. `assert condition` packages the condition as a thunk,
while `assert_eq` packages each operand as a separate thunk. The test runner
evaluates those thunks while handling the `assertion` effect.

## Assertion effect

The operator expansions call the two operations of the `assertion` effect:

| Operation | Signature |
|---|---|
| `assertion::assert check` | `(() -> [_] bool) -> [assertion] ()` |
| `assertion::assert_eq (expected, actual)` | `(() -> [_] 'a, () -> [_] 'a) -> [assertion] ()` |

The operations can also be called directly by passing thunks:

```yulang
mod test direct_operations:
    my truth = assertion::assert (\() -> true)
    my equality =
        assertion::assert_eq ((\() -> 4), (\() -> 4))
```

The built-in test runner handles `assertion`. Code that runs these operations
under another entry point needs a matching handler.

## Failure reporting

`assert` fails the current test when its thunk returns `false`. `assert_eq`
fails when its two thunks return unequal values. The test runner points to the
operator and, for `assert_eq`, labels the left value as `expected` and the right
value as `actual`.

The current `assert_eq` signature has no `Eq`, `Display`, or `Debug`
prerequisite. Its operands must still have the same inferred type.

## Quick reference

| Surface | Result |
|---|---|
| `assert condition` | Lazily emit `assertion` for a `bool` expression |
| `expected assert_eq actual` | Lazily emit `assertion` for two values of the same type |
| `assertion::assert check` | Run a Boolean thunk through `[assertion]` |
| `assertion::assert_eq (expected, actual)` | Run two same-typed thunks through `[assertion]` |

## See also

- [Modules → Test modules](../modules#test-modules) — test discovery and execution
- [Effects](../effects) — effect declarations, operations, and handlers
- [Standard Library Catalogue](./) — the full module inventory
