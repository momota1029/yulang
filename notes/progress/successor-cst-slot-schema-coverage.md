# Successor CST slot-schema source coverage

Status: non-authoritative coverage manifest

Date: 2026-09-10

Purpose: reproducibly locate current recovery-publication evidence while the
Draft CST slot-schema catalog is mapped. This is not a grammar schema, a
semantic-slot ledger, parser diagnostic authority, or a public-reference input.
Source sites are evidence links, not slot identity.

## Reproducible census

Run from the repository root:

```sh
rg -n --glob '*.rs' 'emit_recovery_(missing|error_item|error_run)\(|emit_structured_recovery_error_from_item\(' crates/yu-syntax/src | rg -v 'cursor/recovery|src/tests'
```

At this manifest's creation, the command yields 123 matching call sites in 39
source files. That is a publication-site census only: neither number is a
count of semantic slots.

There is one known exception outside this four-emitter census:
`rule/expression_list.rs::emit_leading_newline_separators` calls
`emit_required_slots_before_newlines` with a callback which creates
`ExpressionList(Item)` Missing. It is a required evidence link and must be
mapped with its separator/newline phase; it is intentionally excluded from the
123-call census.

## Matching rule

Map a source helper/caller to a semantic slot only when the evidence establishes
the same `(production, ordered child phase, necessary ancestor context)` as the
catalog. The helper name, recovery role, parent syntax kind, emitter choice,
or source range alone is insufficient. Record all caller-specific stop,
delimiter/opener, sequence phase, retry, and boundary facts needed to make the
row unambiguous. One helper may contribute evidence to several slots, and one
slot may require several helper/caller sites.

## Manifest status vocabulary

| Status | Meaning |
| --- | --- |
| `untriaged` | census site has not yet been assigned a candidate family/row |
| `candidate` | a likely row exists, but child phase or ancestor context is unproven |
| `linked` | source evidence is linked to a named catalog row; schema facts remain incomplete unless separately marked |
| `delegated` | evidence belongs to a separately named child production/slot |
| `exception` | required recovery evidence intentionally outside the four-emitter census |
| `excluded` | intentionally outside this manifest's source scope |

No status means a call count, file count, or family count equals semantic slots.

## Family-level source coverage

All 39 files below are `untriaged` evidence links at catalog-scaffold start.
The groups are source-navigation families, not semantic schema families.

| Family | Files | Census calls |
| --- | ---: | ---: |
| declarations and headers | 16 | 46 |
| expression forms and tails | 10 | 18 |
| type expression | 5 | 34 |
| pattern | 2 | 8 |
| literal and rule | 3 | 6 |
| root, statement, and virtual layout | 3 | 11 |
| **total** | **39** | **123** |

### Declarations and headers — 16 files / 46 calls

- `crates/yu-syntax/src/declaration/act_decl.rs`
- `crates/yu-syntax/src/declaration/binding.rs`
- `crates/yu-syntax/src/declaration/cast_decl.rs`
- `crates/yu-syntax/src/declaration/declaration_companion.rs`
- `crates/yu-syntax/src/declaration/declaration_variant.rs`
- `crates/yu-syntax/src/declaration/derives.rs`
- `crates/yu-syntax/src/declaration/enum_decl.rs`
- `crates/yu-syntax/src/declaration/error_decl.rs`
- `crates/yu-syntax/src/declaration/fields.rs`
- `crates/yu-syntax/src/declaration/impl_tail.rs`
- `crates/yu-syntax/src/declaration/mod_decl.rs`
- `crates/yu-syntax/src/declaration/operator_header.rs`
- `crates/yu-syntax/src/declaration/role_decl.rs`
- `crates/yu-syntax/src/declaration/struct_decl.rs`
- `crates/yu-syntax/src/declaration/type_decl.rs`
- `crates/yu-syntax/src/declaration/use_decl.rs`

### Expression forms and tails — 10 files / 18 calls

- `crates/yu-syntax/src/expression/case_like.rs`
- `crates/yu-syntax/src/expression/delimited.rs`
- `crates/yu-syntax/src/expression/for_decl.rs`
- `crates/yu-syntax/src/expression/if_expr.rs`
- `crates/yu-syntax/src/expression/required_operand.rs`
- `crates/yu-syntax/src/expression/tails/assignment.rs`
- `crates/yu-syntax/src/expression/tails/colon.rs`
- `crates/yu-syntax/src/expression/tails/fixed_access.rs`
- `crates/yu-syntax/src/expression/tails/inline_slot.rs`
- `crates/yu-syntax/src/expression/tails/with_body.rs`

### Type expression — 5 files / 34 calls

- `crates/yu-syntax/src/type_expr/delimited.rs`
- `crates/yu-syntax/src/type_expr/forall.rs`
- `crates/yu-syntax/src/type_expr/mod.rs`
- `crates/yu-syntax/src/type_expr/record.rs`
- `crates/yu-syntax/src/type_expr/variants.rs`

### Pattern — 2 files / 8 calls

- `crates/yu-syntax/src/pattern/delimited.rs`
- `crates/yu-syntax/src/pattern/mod.rs`

### Literal and rule — 3 files / 6 calls

- `crates/yu-syntax/src/literal/mod.rs`
- `crates/yu-syntax/src/rule/mod.rs`
- `crates/yu-syntax/src/rule/expression_list.rs`

### Root, statement, and virtual layout — 3 files / 11 calls

- `crates/yu-syntax/src/root_statement.rs`
- `crates/yu-syntax/src/statement.rs`
- `crates/yu-syntax/src/virtual_statement_block.rs`

`rule/expression_list.rs` contributes two census calls and the separate
newline-Missing `exception` above. Its placement in this source-navigation
group does not classify the exception as a root/layout semantic slot.

## Boundaries

The manifest deliberately excludes `cursor/recovery` implementation sites and
`src/tests` from the census. It does not enumerate non-emitter recovery facts,
direct token construction, public syntax-reference pages, or legacy parser
diagnostic ledgers. A family row becomes useful schema evidence only after the
catalog's required facts and the governing authority have been attached.
