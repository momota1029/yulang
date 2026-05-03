# Diagnostics Snippet Survey 2026-05-04

Small broken programs collected before starting the diagnostics pass.

## 1. Unknown variable

```yu
x
```

Current output:

```text
error: undefined name `x`
  at <unknown>
```

Notes:

- Message is good enough.
- Span is missing.

## 2. Missing method

```yu
1.foo
```

Current output:

```text
error: no field or method named `.foo` could be resolved
  at 2:2
```

Notes:

- Message is acceptable.
- Span points at the field name area, but there is no code frame yet.

## 3. Basic type mismatch

```yu
1 + true
```

Previous output:

```text
failed to lower runtime IR: type mismatch while applying a function: expected bool -> bool, got int -> int
```

Current output after the first cleanup:

```text
error: function application type mismatch: expected bool -> bool, got int -> int
```

Notes:

- This is still the most important first diagnostic target.
- It no longer leaks the runtime lowering phase name.
- It still does not explain that `+` / the right operand caused the mismatch.
- A better target diagnostic would mention `+`, `int`, `bool`, and ideally point at
  `true`.

## 4. Bad if branch

```yu
if true:
    1
else:
    false
```

Current output:

```text
error: branch result type mismatch: expected bool, got int
```

Notes:

- The new runtime type mismatch wording makes this less internal.
- It still lacks a source span / code frame.

## 5. Missing else

```yu
if true:
    1
```

Current output:

```text
error: branch result type mismatch: expected int, got unit
```

Notes:

- This is technically accurate if missing `else` lowers to unit.
- A user-facing parser/language diagnostic should eventually say that the `if`
  expression has an implicit unit else branch, or require an explicit else if that
  is the intended language rule.

## Immediate Regression Target

Start with `1 + true`.

Minimal current regression:

- output contains `function application type mismatch`
- output contains `int`
- output contains `bool`
- output does not contain `failed to lower runtime IR`
- output does not contain Rust debug type dumps such as `Named {`

Next improvement target:

- mention `+` or the selected operator/function
- point to `true` or the application argument span
