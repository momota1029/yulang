# Parenthesized expression elements admit same-line ML application

Status: Authoritative
Scope: same-line whitespace application inside expression elements owned by `ParenthesizedExpression`
Approved-by: user through the explicit `compose` principal-scheme acceptance source
Approved-at: 2026-10-04
Reviewed-by: independent pre-write source/spec audit
Supersedes: the parenthesized-expression E6 expectation in `2026-09-02-yumark-gate3b-recovery-adoption-matrix.md`, and the parenthesized-expression `LayoutOnly` exception in the 2026-09-04 implementation record

## Decision

The accepted principal-scheme source is:

```yulang
my compose f g x = f (g x)
```

It requires `(g x)` to be one grouped expression whose `OperatorChain` contains
same-line ML application. Therefore expression elements inside
`ParenthesizedExpression` use the existing `MlArgumentSeparator` rule for
same-line non-empty trivia, in addition to the existing deeper-newline rule.
The separator and whole nested argument retain the ownership specified by the
authoritative fixed-tail design.

As a result, `(a b)` is one parenthesized element containing the application
`a b`; it is not two expression elements with a missing comma. A comma still
separates tuple/list-style parenthesized elements: `(a, b)` has two elements.
The existing equal-or-shallower newline boundary still separates elements,
while a deeper newline remains a continuation of the current element.

## Authority reconciliation

This decision follows the user's explicit principal-scheme acceptance of the
`compose` source and supersedes the older malformed-source witness at
E6 (`R((a b))`) in the Gate 3b recovery adoption matrix. The older E6 row is
retained there as historical evidence and is no longer a current expectation
for expression parsing. The 2026-09-04 implementation choice to pass
`MlMode::LayoutOnly` for parenthesized expressions is superseded only for
expression elements; the shared `MlArgumentSeparator` and enclosing layout
baseline remain unchanged.

This amendment does not change parenthesized pattern parsing, call/index or
projection ownership, type-expression delimiters, comma ownership, or the
meaning of the resulting application in type inference. It selects no new
effect or Function rule.

## Required parser and regression contract

- `(a b)` contains one direct `OperatorChain` and no separator `Missing`;
  that chain contains an `MlArgument` for `b`.
- `(a, b)` retains two direct `OperatorChain` elements and no recovery.
- `(a\nb)` at the parenthesized base retains two elements through the existing
  implicit newline boundary.
- `(a\n  b)` retains one element with a deeper-indentation ML continuation.
- Opaque newlines inside block comments do not become layout boundaries; the
  existing trivia-classification rule determines whether the surrounding
  non-empty trivia is an ML separator.
- `f (g x)` retains an outer ML argument containing one parenthesized
  expression, with the inner `g x` application represented in that element's
  `OperatorChain`.

The fix belongs at the parenthesized expression's mode supplied to the shared
delimited parser. It must not special-case `compose`, declaration names, or
parenthesized source text. Existing typed recovery ownership and exact source
trivia ownership remain in force.

## Implementation and rollback boundary

The implementation may use the existing `MlMode::All` and existing
`OperatorChain`/`MlArgument` nodes; this amendment adds no parser carrier or
special recovery kind. Roll back only if a focused regression shows that the
selected comma/newline boundaries, operator ownership, or source preservation
cannot be maintained under that existing machinery. A rollback cannot restore
the superseded `compose` rejection; it must first present the concrete
contradiction to the user and retain this amendment as the governing source
until it is superseded.
