# `mod` declaration

## 1. 状態・根拠・最終照合

このページは `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の
Authoritative な「canonical `Statement` / root `Declaration` `mod` declaration
extension」（11624–12156行）を要約する。規範節は authoritative surface grammar/layout、
typed recovery contract、statement-intro judge、owner scope である。

design approval は `2a1a7367`、implementation は `d4d58d13`。このページは
`b080c022` に対して照合した。

## 2. 対象と非対象

module は optional visibility、`mod`、ordinary または contextual `test` identity、
bodyless semicolon / braced statement block / colon inline・indented canonical statement
body のいずれかを持つ。root と nested statement は同じ `ModDeclaration` を使う。

module path/loading、namespace、export、test execution、nested header planning、`with:`、
derives、module-specific member、brace-local spread、未実装 statement kind、HIR、resolver、
diagnostics はこの syntax contract の外である。

## 3. BNF 相当の grammar

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

`Gmod` は same-line trivia、または `mod_base` より strictly deeper な末尾 indent を
受ける。equal-or-shallower newline は outer owner が所有する。

## 4. Judge・priority・owner boundary

bare exact `mod`、または visibility と continuation trivia 後の exact `mod` は Binding
より先に選ばれる。`module` と `modular` は split しない。identity/body の成否に関係なく
intro は commit する。exact `test` は `mod` の直後だけ marker になり、`;` / `{` / `:`
直前だけ anonymous である。EOF の `mod test` は incomplete second-name slot になる。

body judge は exact `;`、lone `{`、lone `:` だけを所有する。starter のない valid
statement candidate は same position の missing colon として recovery できる。一方 outer
EOF、comma、close、dedent、companion stop、equal-or-shallower newline は non-consuming である。

## 5. byte-exact CST worked examples

Mod 追補には byte-range-annotated CST tree がない。以下は追補自身が引用する source
string であり、range を発明せず記載済みの CST ownership だけを要約する。

```text
mod error;
```

（11708–11711行）は `ModDeclaration` の `ModKw`、raw `Identifier` の `error`、
bodyless `Semicolon` からなる。`error` は他の位置では contextual でも、この slot では
ordinary module name である。

```text
mod test;
```

（11704–11705、12013行）は `Identifier` の `test` を持つ `TestModuleMarker` の直後に
bodyless `Semicolon` を置く。body-starter lookahead が anonymous test-module form を証明するため、
name child / placeholder は作らない。

```text
mod test {}
```

（11704–11705、12013行）は同じ `TestModuleMarker` の後に existing
`BracedStatementBlockExpression` を置く。brace owner が open / close / inner separator を所有し、
`ModDeclaration` は synthetic `ModBody` CST wrapper を作らない。

```text
my mod test internals:
```

（11705行）は visibility、`ModKw`、contextual `TestModuleMarker`、second raw
`Identifier` の `internals`、`Colon` を持つ。named test-module identity と colon body
starter を示し、inline / strictly-deeper indented layout は literal colon 後に judge する。

root output では `ModDeclaration` は `Root` child、nested sequence では一つの
`Statement` wrapper の sole selected child になる。この container 差は declaration token
ownership を変えない。


## 6. parser 側 AST shape

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

name のない `test_marker: Some(_)` は proven anonymous test module である。
`Some(Incomplete)` は EOF の `mod test` と valid form を区別する。

## 7. typed recovery table

| condition | recovery と ownership |
| --- | --- |
| `mod` at boundary | `Missing(ModRole::Name, Identifier)` 一件。body-introducer は cascade しない |
| malformed name then raw name | maximal `Error(ModRole::Name)` 一件と same-slot retry |
| `mod test` at boundary | `Missing(ModRole::TestName, Identifier)` 一件。body は cascade しない |
| complete identity at boundary | `Missing(ModRole::BodyIntroducer)` 一件。boundary は外側に残す |
| malformed introducer then `;` / `{` / `:` | maximal body-introducer error 一件と same-slot starter retry |
| literal/recovered colon with no body | `Missing(ModRole::Body, Statement)` 一件。outer boundary は使用可能 |
| malformed colon body then statement | maximal body error 一件と same-slot retry |
| deeper empty/malformed first block statement | block owner が `ModRole::IndentedStatement` を emit。Mod は重複しない |
| missing brace close | existing `ClosingDelimiter` recovery。outer-owned closer は non-consuming |

すべての `Missing` は zero-width、`Error` は maximal non-empty である。一つの range は
一つの recovery node と一つの record に対応する。

## 8. boundary と state-restoration contract

同じ adapter は root、indented、braced、With、Binding、nested Mod body で安全に使える。
normal / recovery / rollback exit は `mod_base`、indentation、delimiter/stop state、`inline`、
`ml_arg`、scanner state、sink state を restore する。body separator と close は block / outer
sequence が一度だけ所有する。

## 9. Yulang2 divergences

Yulang3 は `test` marker spelling と body-starter family を保つが、
equal-or-shallower newline を outer statement owner に渡す。silent close / `InvalidToken` の代わりに
typed role-specific recovery を使い、Y2 block node ではなく
`BracedStatementBlockExpression` を使う。Y2 brace-local `ExprSpread` / empty separator node は戻さず、
Mod は Y2-equivalent header-planning fact を作らない。

## 10. known residual / deferred surface

accepted Mod-specific residual は記録されていない。section 2 の module / test semantic surface は
意図的に absent のままである。

## 11. implementation と regression fixture cross-reference

`crates/yu-syntax/src/grammar/declaration.rs`:
`recognize_mod_statement_intro`, `parse_mod_declaration_with_operators`,
`commit_mod_declaration`, `mod_statement_error_retry_ast`,
`mod_body_starter_pending`, `mod_trivia`, `mod_word_error_retry`,
`mod_body_introducer_error_retry`, `mod_body_error_retry`。
`crates/yu-syntax/src/grammar/expression.rs` の indented adapter は
`parse_indented_mod_body`、`commit_indented_mod_body`。

fixture:
`mod_declaration_keeps_named_and_test_identity_shapes_distinct`,
`mod_ast_keeps_each_of_the_three_body_forms_distinct`,
`mod_test_at_eof_keeps_the_mandatory_second_name_slot`,
`mod_direct_retries_malformed_introducer_and_colon_body_under_their_own_roles`,
`mod_colon_body_missing_keeps_outer_comma_and_close_available`,
`mod_brace_body_reuses_the_shared_owner_safe_close_recovery`。
