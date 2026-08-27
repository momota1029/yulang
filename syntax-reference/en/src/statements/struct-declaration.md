# `struct` declaration

## 1. Status, authority, and last verification

This page summarizes the Authoritative **canonical `Statement` / root
`Declaration` `struct` declaration grammar**, lines 17400–18359 of
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its normative
sections are `SD-G`, `SD-J`, `SD-T`, and `SD-R` (17497–18359).

Approval is `238e0250`. The implementation sequence is `47ed2c99`,
`62ea8a31`, `fd401a26`, `eeedc5a1`, `05358e72`, `4c52d048`, `cecba259`, and
`1900e076`. Observable review findings were fixed by `668c9b19` and
`7f47d9a7`; both are part of the verified behavior described here. This page
was checked against `b080c022`.

## 2. Scope and non-scope

The grammar accepts visibility, exact `struct`, mandatory raw name, and one of
bodyless `;`, named braced fields, named indented fields, or tuple fields.
Named fields own `Identifier : TypeExpression`; tuple fields own one required
TypeExpression.

Declaration generics, derives/`with:` companions, methods, constructors,
literals, defaults, shorthand, field visibility, docs, layout/ABI, semantic
field validation, HIR, resolver, inference, formatter, and diagnostics are
deferred.

## 3. BNF-equivalent grammar

```text
StructDeclaration :=
    [ VisibilityKw Gstruct+ ] StructKw Gstruct+ StructName Gstruct* StructBody
StructBody :=
    Semicolon
  | LBrace StructOpeningTrivia [ StructNamedField { StructBracedFieldBoundary StructNamedField } ] RBrace
  | Colon StructIndentedOpeningTrivia StructNamedField { StructIndentedFieldBoundary StructNamedField }
  | LParen StructOpeningTrivia [ StructTupleField { StructBracedFieldBoundary StructTupleField } ] RParen
StructNamedField := Identifier Gfield-name Colon Gfield-type RequiredTypeExpression(Struct::FieldType)
StructTupleField := RequiredTypeExpression(Struct::FieldType)
```

`Gstruct` permits same-line or strictly-deeper continuation trivia. Braced and
tuple lists use `struct_list_base`; indented fields use `block_indent`.

## 4. Judge, priority, and owner boundary

Exact `struct`, bare or visibility-led, cuts before Binding; `structure`,
`structural`, and `my_struct` are ordinary words. After a complete/recovered
name, only exact `;`, `{`, `(`, and lone `:` choose a body. A following type
word never invents a missing body container.

Field layout owns commas and qualifying newlines. A deeply indented line
continues a field type; qualifying equal-or-shallower lines are field/list or
outer boundaries. `::` is never split into a field colon. The field owner uses
full mandatory TypeExpression with the `StructRole::FieldType` outer role.

## 5. Byte-exact CST worked examples

```text
pub struct Marker;
```

```text
StructDeclaration
  PubKw "pub" 0..3
  StructKw "struct" 4..10
  Identifier "Marker" 11..17
  Semicolon ";" 17..18
```

```text
struct Point { x: Int, y: List Int }
```

has `StructDeclaration 0..36`, two `StructField` nodes, and the second field's
`List Int` TypeApply range ending at `34`; the brace closes at `35..36`.

```text
struct Point:
  x: Int
  y: String
```

has `StructDeclaration 0..34`; opening and inter-field newline/indent trivia
belong directly to it, not to an implicit separator wrapper.

```text
struct S { x Int, y: Bool }
```

places `Missing(Struct::FieldColon, Colon)` at `13..13`, then retries
`Int` as the field type; `y: Bool` remains a separate field.

## 6. Parser-side AST shape

```rust
pub(crate) struct StructDeclaration<'source> {
    visibility: Visibility,
    name: Recovered<WordSpan<'source>>,
    derives: Vec<DerivesAttachment<'source>>,
    body: Recovered<StructBody<'source>>,
    range: Range<usize>,
}

pub(crate) enum StructBody<'source> {
    Bodyless { semicolon: Range<usize> },
    NamedBraced(StructNamedBracedBody<'source>),
    NamedIndented(StructNamedIndentedBody<'source>),
    Tuple(StructTupleBody<'source>),
}

pub(crate) struct StructNamedField<'source> {
    name: Recovered<WordSpan<'source>>,
    colon: Recovered<Range<usize>>,
    type_expr: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}

pub(crate) struct StructTupleField<'source> {
    type_expr: Recovered<Box<TypeExpression<'source>>>,
    range: Range<usize>,
}
```

`derives` is a later shared attachment; this grammar selects `StructBody` and
preserves incomplete slots rather than synthetic fields.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| keyword at boundary | one `Missing(StructRole::Name, Identifier)`; no body cascade |
| malformed name then name | one maximal `Error(StructRole::Name)` and same-slot retry |
| complete name without body starter | one `Missing(StructRole::BodyIntroducer)`; next word stays outer-owned |
| malformed starter then real starter | one body-introducer error and same-slot retry |
| field lacks colon before reusable type | one `Missing(StructRole::FieldColon, Colon)` and same-position type retry |
| accepted colon at boundary | one `Missing(StructRole::FieldType, TypeExpression)` |
| malformed Type primary reaches boundary | inner `Error(Type::Primary)` only; no FieldType cascade |
| separator before EOF | distinct incomplete field and closing-delimiter slots |
| outer-owned mismatched close | missing local close; outer close remains non-consuming |
| repeated tuple comma | one missing tuple field type, then separator retry |

The body, named-field, tuple-field, and close rows preserve no-cascade and one
range = one recovery node = one record.

## 8. Boundary and state-restoration contract

Root, indented canonical statements, braced blocks, With, Binding/Mod bodies,
and nested structs share the adapter. Normal, recovery, and rollback exits
restore delimiter/stop state, `TypeDelimitedOwner`, list/indent baselines,
`inline`, `ml_arg`, `type_ml_arg`, positional fence, scanner state, and sink.
The findings fixes specifically preserve body-judge handoff and no-cascade
ownership.

## 9. Yulang2 divergences

Yulang3 preserves the principal struct surface but defers Y2 whitespace type
variables and companions, accepts bodyless `struct S;` while bare EOF is
incomplete, uses typed recovery rather than `InvalidToken`, creates no
`TypeVars` or synthetic `Separator`, keeps `()` fieldless, and uses the
approved standalone TypeExpression entry instead of Y2 type stops.

## 10. Known residual / deferred surface

No accepted Struct-specific residual is recorded. The non-scope list in
section 2, especially declaration generics and companion/derives semantics,
remains deferred.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/declaration.rs`:
`recognize_struct_statement_intro`, `parse_struct_declaration`,
`commit_struct_declaration`, `parse_struct_body_ast`,
`commit_struct_body_introducer`, `parse_struct_named_field_ast`,
`commit_struct_named_field`, `parse_struct_tuple_body_ast`,
`commit_struct_tuple_body`, and `struct_outer_owned_mismatched_close_pending`.

Fixtures include `struct_intro_commits_exact_keywords_before_binding_and_expression_fallback`,
`struct_header_recovery_hands_a_body_starter_forward_without_cascading`,
`struct_named_brace_fields_keep_their_own_layout_and_type_apply_boundary`,
`struct_named_fields_recover_colon_skeletons_without_cascading`,
`struct_named_indented_fields_keep_their_block_baseline_and_boundaries`,
`struct_tuple_fields_keep_type_apply_and_tuple_close_ownership_distinct`, and
`struct_lists_leave_ambient_if_companions_for_the_statement_owner`.

