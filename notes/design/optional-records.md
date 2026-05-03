# Optional Records

## Current Semantics

- Empty brace expression `{}` is an empty record literal.
- Record pattern defaults mark fields as optional in inferred types.
- `my f({x = 1}) = ...` accepts both `f {}` and `f {x: ...}`.
- Defaults are evaluated only when the field is missing.
- Defaults are evaluated in the pattern-binding environment, so an earlier bound field can be used by a later default.

## Current Implementation

- Infer lowering recognizes `{}` as an empty record literal.
- Runtime type compatibility allows a missing actual field when the expected field is optional.
- Runtime lowering keeps `RecordPatternField.default` instead of dropping it.
- VM pattern binding evaluates missing-field defaults before binding the nested pattern.
- Monomorphization reachability scans default expressions so functions used only in defaults are kept.

## Example

```yu
my area({width = 1, height = 2}) = width * height

area { width: 3 }          // 6
area {}                    // 2
area { width: 3, height: 4 } // 12

my next_area({width = 2, height = width + 1}) = width * height

next_area { width: 3 }     // 12
```

## Open Questions

- Whether defaults should be allowed to depend only on earlier fields, or on all fields.
- Whether record pattern defaults should be allowed to perform user effects.
- How optional record defaults should interact with record spreads in patterns.
- Whether call-site sugar for named arguments should be added later, or whether record arguments are enough.
