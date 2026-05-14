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

Output after the first cleanup:

```text
error: function application type mismatch: expected bool -> bool, got int -> int
```

Output as of 2026-05-14:

```text
error: callee type mismatch in call to `+`: expected bool, got int
  at 2:3
   2 | 1 + true
     |   ^^^^^^
```

Notes:

- ✅ No longer leaks the runtime lowering phase name.
- ✅ Mentions the operator (`+`).
- ✅ Has a source span and a code frame pointing at the offending expression.
- The "Next improvement target" below has been met for this snippet.

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

Minimal regression (still applies):

- output mentions `int` and `bool`
- output does not contain `failed to lower runtime IR`
- output does not contain Rust debug type dumps such as `Named {`

Next improvement target — **met as of 2026-05-14**:

- ✅ mentions `+` (or the selected operator/function)
- ✅ points to `true` (or the application argument span) with a code frame

Remaining diagnostic gaps from this survey:

- snippets 1, 4, 5 still lack source spans / code frames.
- snippet 1 still reports `at <unknown>` for top-level identifiers.
