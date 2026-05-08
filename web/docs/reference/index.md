# Language Reference

This section documents Yulang's syntax and semantics in detail.

## Structure of a program

A Yulang program is a sequence of top-level statements. Statements include declarations (`my`, `our`, `pub`, `struct`, `act`, `role`, `impl`, `enum`, `error`, `cast`, `type`, `use`, `mod`) and bare expressions whose values are shown.

## Visibility

| Keyword | Meaning |
|---------|---------|
| `my`    | Private binding, local or top-level |
| `our`   | Public, appears in the enclosing module's companion |
| `pub`   | Exported binding; also shown in the type pane of the playground |

## Comments

```yulang
// This is a line comment.

-- This is a single-line doc comment (not a line comment).

---
This is a multi-line doc block.
It can contain markdown and ```yulang fences.
---
```

`//` is the only ordinary line comment. `--` and `---` blocks are documentation comments — they may appear in syntax trees and tooling, so they are not interchangeable with `//`.

## See also

- [Values & Types](./types)
- [Functions](./functions)
- [Structs & Roles](./structs)
- [Effects](./effects)
- [Pattern Matching](./patterns)
- [Modules](./modules)
