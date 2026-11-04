# Numeric literals

## 1. Authority and scope

This page defines integer and floating-point literals in expression position for `syntax-v0`.
The accepted float spellings and their lexical boundaries follow WP-4 of the 2026-11-04 parser-gap-closure addendum.
The page covers expression syntax and direct Rowan CST only.
It does not admit floating-point literals in patterns or type expressions, or define numeric types, precision, range, or evaluation.

## 2. Accepted syntax

```text
Digit := "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
IntegerLiteral := Digit+
FloatLiteral := Digit+ "." Digit+ [ Exponent ]
              | Digit+ Exponent
Exponent := ("e" | "E") [ "+" | "-" ] Digit+
```

The decimal point must be followed by a digit.
An exponent marker and an optional sign must be followed by a digit.
The forms `1.5`, `0.25`, `1e3`, `2.5e-3`, and `1E3` are float literals.

## 3. Admission and boundaries

An expression value position admits an integer or float literal as one primary.
A valid exponent extends the same float token.
If an exponent is incomplete, the preceding valid integer or decimal float ends before `e` or `E`, and ordinary recovery owns the suffix.

Two dots are never part of a float token.
Thus `0..10`, `0..`, `0..<10`, and `1..` begin with an integer and retain the existing `..` boundary.
The forms `1.` and `1.e3` also begin with an integer because the dot is not followed by a digit.

After a field-tail dot, an adjacent integer is a positional field name rather than the start of a float.
The [fixed-tail page](call-field-path-tails.md) defines that local boundary.

## 4. Direct Rowan CST

`IntegerLiteral` directly contains one `Integer` token.
`FloatLiteral` directly contains one `Float` token carrying the complete float spelling.

```xml
<OperatorChain>
  <FloatLiteral><Float text="2.5e-3" /></FloatLiteral>
</OperatorChain>
```

## 5. Recovery

`1e` remains an integer followed by recovery for `e`.
`1e+` remains an integer followed by recovery for `e+`.
`1.` remains an integer followed by the existing dot-tail recovery.
Floating-point pattern syntax is not admitted; a float-shaped spelling in a pattern follows the existing integer-pattern and arm recovery paths.

## 6. Composition

Numeric literals compose with prefix operators, dynamic operator chains, ML application, calls, indexes, and other expression positions that admit an ordinary primary.
[Dynamic operator chains](operator-chain.md) define those surrounding positions.
