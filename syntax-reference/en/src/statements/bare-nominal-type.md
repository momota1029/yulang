# Bare nominal `type` declaration

## 1. Status / authoritative source / last verified commit

- Status: Authoritative; user-approved on 2026-08-26.
- Authoritative source: `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`, the section named `canonical Statement / root Declarationのbare nominal type declaration grammar`, currently lines 19677–20277. `TND-G` is the grammar source, `TND-J` defines the judge, `TND-T` defines TypeExpression / ASOB composition, and `TND-R` defines typed recovery.
- Design finalization commit: `9cee84e5`.
- Implementation series: Gate 1 `538af5d8`, Gate 2 `fa9a3a11`, Gate 3 `d88694bd`, Gate 4 `f42a5929`, Gate 5 `b3b07727`, Gate 6 `26e5b030`, Gate 8 `ff215ce9`, and Gate 9 `fec43734`. Gate 7 was a read-only equality-fixture audit and has no separate `bare-nominal-type Gate 7` commit in reachable history. The Gate 9 closing message records completion of all nine gates.
- Last verified: `4b8c4c91`. The implementation symbols and fixture names below were checked in the current tree.

## 2. Scope and non-scope

This page covers the rule that selects a bare nominal form with no RHS after a shared `TypeDeclaration` header. Its surface consists of optional visibility, exact `type`, a mandatory raw name, and same-line declaration type parameters.

The scope is the nominal-versus-equality priority, AST/direct-CST shape, typed recovery, ASOB/layout/separator ownership, and the same declaration child at root and in nested canonical Statements.

The TND addendum does not define `impl` / `with`, colon or brace role-like bodies, associated types, constructor or module registration, nominal identity, visibility semantics, HIR lowering, resolver, or formatter behavior. Pre- or post-body `derives` was also outside this addendum; the current `derives` attachment is defined separately by the later shared derives addendum.

## 3. BNF-equivalent grammar

```text
TypeDeclaration :=
    TypeDeclarationHeader TypeDeclarationForm

TypeDeclarationHeader :=
    [ VisibilityKw Gtype+ ]
    TypeKw Gtype+ TypeName
    [ DeclarationTypeParameterList ]

TypeDeclarationForm :=
    NominalTypeDeclarationEnd
  | EqualityTypeDeclarationDefinition

NominalTypeDeclarationEnd :=
    Gtype-terminal NominalStatementBoundary
  | MaximalStrictlyDeeperTrailingTriviaBeforeEOF EOF

EqualityTypeDeclarationDefinition :=
    Gtype* Equals Gtype-rhs
    RequiredTypeExpression(TypeDeclaration::Rhs)

NominalStatementBoundary :=
    EOF
  | OuterStatementSemicolon
  | EqualOrShallowerStatementNewline(type_base)
  | BracedStatementSequenceNewline
  | CatchArmSequenceNewlineThroughInlineCanonicalStatement
  | ActiveOuterFixedStatementBoundary
  | AmbientStatementOwnerBoundary

ActiveOuterFixedStatementBoundary :=
    ActiveStop(Comma)
  | ActiveStop(RightParenthesis)
  | ActiveStop(RightBracket)
  | ActiveStop(RightBrace)
```

`VisibilityKw`, type parameters, `Gtype*`, `Gtype-rhs`, and `type_base` reuse the shared header and RHS grammar for equality `type` declarations. `NominalStatementBoundary` is an owner-handoff result, not a source child.

## 4. Judge / priority / owner boundary

The form judge runs sink-free immediately after a complete header. It probes only the original trivia gap and following token, then rolls back exactly. It does not search arbitrarily far for `=` or speculatively parse a full TypeExpression.

The priority order is:

1. If the name is Incomplete, do not grant nominal authority. Exact `=` evidence selects equality recovery; otherwise preserve shared header recovery.
2. After a complete header, if the original gap is not claimed by an ambient owner and an accepted `Gtype*` is followed by an exact lone `=`, select Equality. Local exact `=` wins before terminal inference from a braced or Catch newline.
3. After a complete header, select Nominal at EOF, an outer semicolon, an equal-or-shallower newline, a typed braced/Catch newline, an active comma/right delimiter, an ambient owner, or EOF after strictly-deeper trivia. Do not consume boundary bytes.
4. Otherwise hand off to shared `DefinitionIntroducer` recovery. A reusable TypePrimary yields a zero-width Missing `=` and same-position RHS retry; a malformed run yields a maximal Error and its selected retry.

The outer canonical Statement sequence owns semicolons. An active fixed boundary is only an incoming active stop among `Comma | RightParenthesis | RightBracket | RightBrace`; punctuation spelling by itself is not enough.

## 5. Byte-exact CST worked examples

### Complete nominal

Source:

```text
type Point
```

```text
TypeDeclaration 0..10
  TypeKw 0..4 "type"
  Trivia 4..5 " "
  Identifier 5..10 "Point"
```

The AST has `name = Complete(Point)`, zero parameters, `form = Complete(Nominal)`, and range `0..10`. It creates no Missing, Error, or TypeExpression.

### Visibility and parameter with outer semicolon

Source:

```text
pub type Phantom 'a;
```

```text
TypeDeclaration 0..19
  PubKw 0..3 "pub"
  Trivia 3..4 " "
  TypeKw 4..8 "type"
  Trivia 8..9 " "
  Identifier 9..16 "Phantom"
  DeclarationTypeParameterList 16..19
    Trivia 16..17 " "
    SigilIdentifier 17..19 "'a"
Semicolon 19..20 ";"
```

The semicolon is neither a `TypeDeclaration` child nor part of its range; it is the outer statement separator.

### Nominal before the next root statement

Source:

```text
type value
our x = 1
```

The first `TypeDeclaration` closes at `0..10`; the newline at `10..11` returns to the outer root sequence. `our x = 1` is a separate Binding at `11..20`, and the first declaration creates neither Missing `=` nor an RHS.

## 6. Parser-side AST shape

The current shape in `declaration.rs` is below. The `derives` field is an attachment from the later shared derives addendum; `form` remains the nominal/equality choice.

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

A valid nominal form does not contain dummy `equals = Incomplete` or an empty RHS. `form = Incomplete` is limited to a name that is incomplete or a malformed `DefinitionIntroducer` run reaching a terminal boundary without positive nominal or equality evidence.

Valid nominal CST uses the existing `TypeDeclaration` node. It adds no `NominalTypeDeclaration`, empty body, empty RHS, or nominal-only wrapper node.

## 7. Typed recovery table

This is a summary of TND-R's principal slot transitions. Name, `DefinitionIntroducer`, and Rhs use shared type-declaration recovery roles; there is no nominal-specific recovery role.

| Input state | Result / recovery | Ownership or retry |
| --- | --- | --- |
| complete header + EOF / `;` / terminal newline / ambient owner / active fixed boundary | `Complete(Nominal)`, zero recovery | Return the boundary non-consumingly to its outer owner. Only strictly-deeper trivia + EOF is owned by the declaration. |
| complete header + exact `=` | `Complete(Equality)` | Cut to the shared mandatory RHS. |
| complete header + reusable non-parameter TypePrimary without `=` | one zero-width Missing `DefinitionIntroducer`, `Complete(Equality)` | Retry the RHS at the same position. |
| malformed post-header run + exact `=` or reusable TypePrimary | one maximal Error `DefinitionIntroducer`, `Complete(Equality)` | Consume the actual `=` or retry the RHS at the same position. |
| malformed post-header run + terminal boundary | one maximal Error `DefinitionIntroducer`, form Incomplete | Do not upgrade to Nominal; emit no additional Missing. |
| `type` + terminal boundary | one Missing Name, form Incomplete | Do not cascade nominal, equals, or RHS Missing. |
| malformed name + valid raw name + terminal boundary | one maximal Error Name, retried name Complete, `Complete(Nominal)` | Do not add a Name Missing. |
| `type Point = ;` | `Complete(Equality)`, one Missing Rhs | Do not attempt a nominal fallback. |

The cardinality rule is one source range = one recovery node = one record. Do not cascade following-slot Missing for the same terminal cause. AST and direct CST have the same form decision, Complete/Incomplete slot, source range, and recovery record.

## 8. Boundary/state-restoration contract

The nominal path opens no TypeExpression RHS slot. Only exact `=` or equality recovery reuses the shared TD-T RHS episode.

When probing from root, indented, braced, inline canonical Statement, or depth-2+ ambient / If-companion contexts, the form judge restores input, line state, sink, ambient / If state, delimiter stack, stop set, indentation, type owner, ML state, and positional fence to their entry depth. Gate 6 fixes the boundary matrix for EOF, semicolon, comma, every active right delimiter, equal-or-shallower newline, braced newline, Catch arm newline, strictly-deeper continuation, and EOF.

## 9. Yulang2 divergences

- Y2 silently closed the same `TypeDecl` and had no typed distinction from a missing equals. Y3 treats a terminal owner boundary as positive Nominal evidence and does not fold malformed post-header bytes into Nominal.
- At root / indented positions, Y3 preserves type-base discipline; directly under a braced Statement sequence, it uses an indentation-independent typed newline-owner query.
- Y2 role-like bodies consumed semicolons inside `TypeDecl`. In Y3, the outer statement sequence owns them.
- Y3 creates neither an always-present empty `TypeVars`, an empty body, nor a nominal-only CST wrapper.
- `Nominal` is a syntax-only form label. The parser does not decide nominal identity, constructor registration, opaque / alias meaning, or default visibility.

## 10. Known residual / deferred surface

The TND addendum declares no known residual specific to the bare nominal form.

Its deferred surface includes companion `impl` / `with`, colon / brace role-like bodies, `struct self`, associated-type ownership, constructor / module registration, nominal semantics, HIR / resolver / formatter, and kind / bound / default / `where`. Surfaces implemented by later addenda, such as the shared `derives` attachment and standalone `impl` shell, are not defined as part of this bare-nominal form decision.

## 11. Implementation functions and regression fixtures

Implementation: `crates/yu-syntax/src/grammar/declaration.rs`.

- `recognize_type_statement_intro`
- `parse_type_declaration_header_slots` / `commit_type_declaration_header_slots`
- `parse_type_declaration` / `commit_type_declaration`
- `classify_type_declaration_form`
- `type_declaration_terminal_boundary_pending`
- `type_declaration_active_fixed_statement_boundary_pending`

Regression fixtures:

- `type_declaration_form_judge_follows_tnd_j_and_restores_every_probe_state`
- `type_declaration_form_aware_ast_construction_reuses_tnd_j_once`
- `type_declaration_form_aware_direct_cst_is_byte_exact_and_parity_checked`
- `type_declaration_form_aware_tnd_r_recovery_matrix_is_complete_and_non_cascading`
- `type_declaration_form_aware_boundary_matrix_restores_deep_parser_state`
- `nominal_type_declaration_final_public_boundary_matrix_preserves_ast_direct_parity`
- `type_declaration_scope_gate_keeps_deferred_yulang2_family_surfaces_outside_the_grammar`
