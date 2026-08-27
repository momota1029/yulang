# Equality `type` declaration

## 1. Status, authority, and last verification

This page summarizes the Authoritative addendum **canonical `Statement` / root
`Declaration` type equality declaration grammar**, lines 19162–19676 of
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its normative
sections are `TD-G`, `TD-J`, `TD-T`, and `TD-R` (lines 19286–19674).

The implementation gates landed as `f1681594`, `78d09b74`, `cf2ecd32`,
`dec5b7cf`, `c23e870d`, `c48086a5`, `263a99cc`, `be1d1dcb`, and
`8284e4fe`. The addendum itself was finalized by `4037c69e`. This page was
last checked against `96d98da4`.

## 2. Scope and non-scope

This covers the equality form: visibility, `type`, name, optional same-line
declaration parameters, an equality introducer, and one required
`TypeExpression`. It deliberately did not define a nominal bodyless form,
companion `impl` or `with:` tails, colon/brace role-like bodies, derives,
associated types, or semantic alias/nominal meaning. The later nominal addendum
supplies the nominal form; the current `TypeDeclarationForm` keeps both forms
under one header.

## 3. BNF-equivalent grammar

```text
TypeDeclaration :=
    [ VisibilityKw Gtype+ ]
    TypeKw Gtype+ TypeName
    [ DeclarationTypeParameterList ]
    Gtype* Equals Gtype-rhs
    RequiredTypeExpression(TypeDeclaration::Rhs)

VisibilityKw := MyKw | OurKw | PubKw
TypeName := Identifier
DeclarationTypeParameterList :=
    Gtype-param DeclarationTypeParameter
    { Gtype-param DeclarationTypeParameter }
DeclarationTypeParameter := Identifier | SigilIdentifier
Gtype+ := non-empty TypeContinuationTrivia(type_base)
Gtype* := empty or one TypeContinuationTrivia(type_base)
Gtype-rhs := empty or one TypeContinuationTrivia(type_base)
```

`TypeContinuationTrivia` accepts same-line trivia, or trivia followed by a
line strictly deeper than `type_base`; declaration parameters are same-line only.

## 4. Judge, priority, and owner boundary

An exact `type`, or a visibility prefix followed by the required continuation
trivia and exact `type`, selects the Type introduction. Once selected, the
header is cut even if a later slot recovers. The same declaration shape applies
at root and in canonical `Statement`; header discovery stops and creates no
Type header fact.

A lone exact `=` is header evidence. A non-parameter type primary without
`=` may retry as the RHS after a missing introducer; EOF, a separator, an
equal-or-shallower newline, and an ambient owner boundary are non-consuming.
Before the RHS, the parser installs the declaration indentation base and
`Semicolon` / `With` stops, and consults the ambient-owner boundary predicate.

## 5. Byte-exact CST worked examples

```text
type Pair 'left 'right = ('left, 'right)
```

```text
TypeDeclaration 0..40
  TypeKw 0..4 "type"
  Trivia 4..5 " "
  Identifier 5..9 "Pair"
  DeclarationTypeParameterList 9..22
  Trivia 22..23 " "
  Equals 23..24 "="
  Trivia 24..25 " "
  TypeExpression 25..40
```

```text
type Result 'a = ;
```

```text
TypeDeclaration 0..17
  TypeKw 0..4 "type"
  Identifier 5..11 "Result"
  DeclarationTypeParameterList 11..14
  Equals 15..16 "="
  TypeExpression 17..17
    Missing(TypeDeclaration::Rhs, TypeExpression) 17..17
Semicolon 17..18 ";"
```

For `type Id 'a 'a`, both sigil identifiers are greedy parameters, producing
one `Missing(TypeDeclaration::DefinitionIntroducer, Equals)` at EOF rather
than a reusable RHS. `type Id 'a ('a)` is the contrasting missing-`=` retry.

## 6. Parser-side AST shape

The current parser represents equality as a form of the shared declaration:

```rust
pub(crate) struct TypeDeclaration<'source> {
    visibility: Visibility,
    name: Recovered<WordSpan<'source>>,
    parameters: Vec<DeclarationTypeParameter<'source>>,
    derives: Vec<DerivesAttachment<'source>>,
    form: Recovered<TypeDeclarationForm<'source>>,
    range: Range<usize>,
}

pub(crate) enum TypeDeclarationForm<'source> {
    Nominal,
    Equality {
        equals: Recovered<Range<usize>>,
        rhs: Recovered<Box<TypeExpression<'source>>>,
    },
}
```

`derives` and `Nominal` are later additions. This page concerns
`Complete(TypeDeclarationForm::Equality { .. })` and its recovered form.

## 7. Typed recovery table

| Slot / condition | Record and continuation |
| --- | --- |
| name absent at boundary | one zero-width `Missing(TypeDeclaration::Name, Identifier)`; no equality/RHS cascade |
| malformed name then name | one maximal `Error(TypeDeclaration::Name)` and same-slot retry |
| missing `=` before reusable type | zero-width `Missing(TypeDeclaration::DefinitionIntroducer, Equals)` and same-position RHS retry |
| malformed introducer reaches `=` or type | one maximal introducer error; continue without another missing record |
| accepted/recovered `=` then RHS boundary | one zero-width `Missing(TypeDeclaration::Rhs, TypeExpression)`; boundary stays owned outside |
| malformed RHS then type primary | existing `Error(Type::Primary, TypeExpression)` and same-slot retry |
| malformed RHS reaches boundary | the inner Type error is sole; no outer RHS-missing cascade |

Nested type slots keep their `TypeRole`; only a wholly absent RHS primary uses
the declaration-owned `Rhs` role.

## 8. Boundary and state-restoration contract

The gates prove AST/direct parity across root and nested canonical statements,
`Semicolon` / `With` boundaries, equal-or-shallower newlines, ambient gaps,
active delimiters, malformed tails, and rollback. Every RHS exit restores input,
line state, stop set, indentation baseline, delimiter state, expectation sink,
and TypeExpression-local state.

## 9. Yulang2 divergences

The surface retains Yulang2 visibility spelling, exact `type`, whitespace
parameters, exact `=`, and full RHS types. Deliberate differences are neutral
`TypeDeclaration` rather than semantic `TypeAlias`, private default
normalization, outer semicolon ownership, no empty `TypeVars`, typed recovery,
no declaration-local colon/brace stop, current `_a` lexical classification,
and no newly accepted `$` or `&` type-reference atom.

## 10. Known residual / deferred surface

`TD-R` records no equality-specific accepted residual. The historical
complete-header terminal family is superseded by the later nominal form;
genuine equality evidence and recovery remain. Type semantics, companion tails,
role-like bodies, docs/where attachment, HIR, resolver, and formatter work are
outside this syntax contract.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/declaration.rs`:
`recognize_type_statement_intro`, `parse_type_declaration_header_slots`,
`parse_type_declaration_shared_header_phase`,
`parse_type_declaration_definition_phase`,
`commit_type_declaration_header_slots`, `parse_type_declaration_rhs`,
`commit_type_declaration_rhs`, `parse_type_declaration`,
`commit_type_declaration`, and `classify_type_declaration_form`.

Fixtures:
`type_declaration_header_slots_follow_td_r_name_and_equals_recovery`,
`type_declaration_td_r_worked_examples_are_lossless_and_byte_exact`, and
`type_declaration_rhs_wiring_is_atomic_typed_and_state_balanced`.

