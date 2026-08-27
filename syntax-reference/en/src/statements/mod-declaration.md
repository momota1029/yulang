# `mod` declaration

## 1. Status, authority, and last verification

This page summarizes the Authoritative **canonical `Statement` / root
`Declaration` `mod` declaration extension**, lines 11624–12156 of
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its normative
sections are the authoritative surface grammar/layout, typed recovery contract,
statement-intro judge, and owner scope.

The design was approved in `2a1a7367`; implementation landed in `d4d58d13`.
This page was checked against `b080c022`.

## 2. Scope and non-scope

A module has optional visibility, `mod`, an ordinary or contextual `test`
identity, and one body form: bodyless semicolon, braced statement block, or
colon inline/indented canonical statement body. Root and nested statements use
the same `ModDeclaration`.

Module paths/loading, namespaces, exports, test execution, nested header
planning, `with:`, derives, module-specific members, brace-local spread,
unimplemented statement kinds, HIR, resolver, and diagnostics are outside this
syntax contract.

## 3. BNF-equivalent grammar

```text
ModDeclaration :=
    [ VisibilityKw Gmod ] ModKw Gmod ModIdentity Gmod ModBody
VisibilityKw := MyKw | OurKw | PubKw
ModIdentity := NamedModule | TestModule
NamedModule := Name
TestModule := TestMarker TestModuleIdentityTail
TestModuleIdentityTail := EmptyTestName | Gmod Name
EmptyTestName := ε, only before ; / { / :
BodyStarter := Semicolon | LBrace | Colon
ModBody := Semicolon | BracedStatementBlockExpression | ModColonBody
ModColonBody := Colon G0* Statement [ Semicolon ] | Colon IndentedStatementBlock
```

`Gmod` admits same-line trivia or trivia ending in indentation strictly deeper
than `mod_base`; equal-or-shallower newlines belong to the outer owner.

## 4. Judge, priority, and owner boundary

Bare exact `mod`, or visibility plus continuation trivia and exact `mod`, wins
before Binding; `module` and `modular` do not split. The intro commits
independently of identity/body success. Exact `test` only after `mod` is a
marker: it is anonymous only before `;`, `{`, or `:`; `mod test` at EOF instead
has an incomplete second-name slot.

The body judge owns only exact `;`, lone `{`, and lone `:`. A valid statement
candidate without a starter may recover a missing colon at the same position;
outer EOF, comma, close, dedent, companion stop, and equal-or-shallower newline
remain non-consuming.

## 5. Byte-exact CST worked examples

The Mod addendum does not provide byte-range-annotated CST trees. The following
are its own cited source strings; their stated CST ownership is summarized
without inventing ranges.

```text
mod error;
```

(lines 11708–11711) has a `ModDeclaration` with `ModKw`, one raw
`Identifier` for `error`, and the bodyless `Semicolon`. `error` is contextual
elsewhere but an ordinary module name in this slot.

```text
mod test;
```

(lines 11704–11705 and 12013) has a `TestModuleMarker` containing the
`Identifier` `test`, followed immediately by the bodyless `Semicolon`. The
body-starter lookahead proves the anonymous test-module form, so no name child
or placeholder is created.

```text
mod test {}
```

(lines 11704–11705 and 12013) has the same `TestModuleMarker` followed by the
existing `BracedStatementBlockExpression`. The brace owner keeps its open,
close, and inner separators; `ModDeclaration` does not create a synthetic
`ModBody` CST wrapper.

```text
my mod test internals:
```

(line 11705) has visibility, `ModKw`, the contextual `TestModuleMarker`, the
second raw `Identifier` `internals`, and `Colon`. It demonstrates named
test-module identity and the colon body starter; inline versus strictly-deeper
indented layout is judged after that literal colon.

In root output `ModDeclaration` is a `Root` child; in a nested sequence it is
the sole selected child below one `Statement` wrapper. This container difference
does not alter declaration token ownership.


## 6. Parser-side AST shape

```rust
pub(crate) struct ModDeclaration<'source> {
    visibility: Visibility,
    test_marker: Option<WordSpan<'source>>,
    name: Option<Recovered<WordSpan<'source>>>,
    body: Recovered<ModBody<'source>>,
    range: Range<usize>,
}

pub(crate) enum ModBody<'source> {
    Bodyless { semicolon: Range<usize> },
    Braced { block: BracedStatementBlockExpression<'source> },
    Colon { colon: Recovered<Range<usize>>, body: Recovered<ModColonBody<'source>> },
}

pub(crate) enum ModColonBody<'source> {
    Inline { statement: Box<Statement<'source>> },
    Indented { block: IndentedStatementBlock<'source> },
}
```

`test_marker: Some(_)` with no name is a proven anonymous test module;
`Some(Incomplete)` distinguishes `mod test` at EOF from that valid form.

## 7. Typed recovery table

| condition | recovery and ownership |
| --- | --- |
| `mod` at boundary | one `Missing(ModRole::Name, Identifier)`; no body-introducer cascade |
| malformed name then raw name | one maximal `Error(ModRole::Name)` and same-slot retry |
| `mod test` at boundary | one `Missing(ModRole::TestName, Identifier)`; no body cascade |
| complete identity at boundary | one `Missing(ModRole::BodyIntroducer)`; boundary stays outside |
| malformed introducer then `;` / `{` / `:` | one maximal body-introducer error and same-slot starter retry |
| literal/recovered colon with no body | one `Missing(ModRole::Body, Statement)`; outer boundary stays available |
| malformed colon body then statement | one maximal body error and same-slot retry |
| deeper empty/malformed first block statement | block owner emits `ModRole::IndentedStatement`; Mod does not duplicate |
| missing brace close | existing `ClosingDelimiter` recovery; outer-owned closer is non-consuming |

Every `Missing` is zero-width; every `Error` is maximal and non-empty. One
range maps to one recovery node and one record.

## 8. Boundary and state-restoration contract

The same adapter is safe in root, indented, braced, With, Binding, and nested
Mod bodies. It restores `mod_base`, indentation, delimiter/stop state,
`inline`, `ml_arg`, scanner state, and sink state on normal, recovery, and
rollback exits. Body separators and closes remain owned by their block/outer
sequence exactly once.

## 9. Yulang2 divergences

Yulang3 keeps the `test` marker spelling and body-starter family, but gives
equal-or-shallower newlines to the outer statement owner, uses typed
role-specific recovery instead of silent close/`InvalidToken`, retains
`BracedStatementBlockExpression` rather than Y2 block nodes, and does not
restore Y2 brace-local `ExprSpread` or empty separator nodes. Mod creates no
Y2-equivalent header-planning fact.

## 10. Known residual / deferred surface

No accepted Mod-specific residual is recorded. The deferred module and test
semantic surfaces listed in section 2 remain intentionally absent.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/declaration.rs`:
`recognize_mod_statement_intro`, `parse_mod_declaration_with_operators`,
`commit_mod_declaration`, `mod_statement_error_retry_ast`,
`mod_body_starter_pending`, `mod_trivia`, `mod_word_error_retry`,
`mod_body_introducer_error_retry`, and `mod_body_error_retry`.
The indented adapters are `parse_indented_mod_body` and
`commit_indented_mod_body` in `crates/yu-syntax/src/grammar/expression.rs`.

Fixtures include `mod_declaration_keeps_named_and_test_identity_shapes_distinct`,
`mod_ast_keeps_each_of_the_three_body_forms_distinct`,
`mod_test_at_eof_keeps_the_mandatory_second_name_slot`,
`mod_direct_retries_malformed_introducer_and_colon_body_under_their_own_roles`,
`mod_colon_body_missing_keeps_outer_comma_and_close_available`, and
`mod_brace_body_reuses_the_shared_owner_safe_close_recovery`.
