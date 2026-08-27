# Canonical Binding / Use

## 1. Status, authority, and last verification

This page summarizes the Authoritative addendum **canonical `Statement` binding /
use declaration extension**, lines 11086–11623 of
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its companion
source, **Complete `use` declaration grammar and projection**, lines 933–1924,
defines the detailed recursive `UseTree` grammar and projection.

The design approval is `fe6f06c2`; canonical parser integration is
`49c08530`. This page was last checked against `96d98da4`.

## 2. Scope and non-scope

The addendum makes Binding and Use alternatives of canonical `Statement` at
root and in supported nested statement owners. Binding has a visibility prefix,
a mandatory Pattern target, and an optional definition body. Use reuses its
structured use-tree grammar, including root header projection where applicable.

It does not define later declaration kinds, `for`, operator definitions, a
`where` statement, lexical import scope, module resolution, or export semantics.

## 3. BNF-equivalent grammar

```text
Statement := ExpressionStatement | BindingStatement | UseStatement
ExpressionStatement := OperatorChain
BindingStatement := BindingDeclaration
UseStatement := UseDeclaration

BindingDeclaration := VisibilityKw Gbind Pattern [ Gbind Equals BindingBody ]
VisibilityKw := MyKw | OurKw | PubKw
BindingBody := G0* OperatorChain | IndentedStatementBlock
Gbind := maximal same-line trivia | trivia followed by strictly deeper indent
```

`UseDeclaration` and `UseTree` use lines 933–1924: paths, `::` or `/`,
recursive groups, aliases, globs, versions, exclusions, and anchors retain their
source structure.

## 4. Judge, priority, and owner boundary

Canonical recognition first leaves caller-owned EOF, separators, dedent,
matching closes, and companion stops untouched. A sink-free word probe then
selects bare `use`, or visibility-led Use only with a valid use-tree
candidate; otherwise `my`, `our`, or `pub` selects Binding. Thus
`my use path` is Use, while `my use = value` is Binding with Pattern
`use`; `myx` and `useful` are never split.

Binding adds `Equal` only while reading its Pattern. After exact `=`,
same-line input is inline `OperatorChain`, a strictly deeper newline is
`IndentedStatementBlock`, and an equal-or-shallower newline remains with the
outer statement owner.

## 5. Byte-exact CST worked examples

The addendum fixes source ownership and prohibits synthetic wrappers.

```text
pub x
```

is a bodyless `BindingStatement`: it has `BindingHeader` and no empty
`BindingBody`.

```text
my x =
  my y = 1
  y
```

is one outer binding with an `IndentedStatementBlock` holding two canonical
statements. Its opening indentation trivia belongs to the block.

```text
my x = y with:
  my y = 1
```

is the documented generic `WithBodyTail` example: the inline body holds one
canonical `Statement` wrapper around the selected declaration.

```text
use realm/tools::format
```

has declaration range `0..23`. The detailed Use grammar classifies it as
`Realm` and stores `tools`, `format` as its normalized path. Root output
places `BindingStatement` or `UseDeclaration` directly under `Root`;
nested output adds exactly one `Statement` wrapper. Separators and matching
closes remain with the enclosing sequence.

## 6. Parser-side AST shape

The current enum includes later variants; the relevant shape is:

```rust
pub(crate) enum Statement<'source> {
    Expression(OperatorChain<'source>),
    Binding(BindingDeclaration<'source>),
    Use(UseDeclaration<'source>),
}

pub(crate) struct BindingDeclaration<'source> {
    visibility: Visibility,
    target: Recovered<Pattern<'source>>,
    definition: Option<BindingDefinition<'source>>,
    range: Range<usize>,
}

pub(crate) struct BindingDefinition<'source> {
    equals: Range<usize>,
    body: Recovered<BindingBody<'source>>,
    range: Range<usize>,
}

pub(crate) enum BindingBody<'source> {
    Inline { expression: OperatorChain<'source> },
    Indented { block: IndentedStatementBlock<'source> },
}

pub(crate) struct UseDeclaration<'source> {
    range: Range<usize>,
    visibility: Visibility,
    tree: UseTree<'source>,
}
```

`definition: None` means valid bodyless Binding; an incomplete accepted body
remains inside `Some(BindingDefinition { .. })`. `UseTree` preserves the
recursive structure for later projection and semantic validation.

## 7. Typed recovery table

| Slot / condition | Record and continuation |
| --- | --- |
| Binding visibility with no target | one zero-width `Missing(BindingRole::Target, Pattern)`; boundary is non-consuming |
| malformed Binding target then Pattern | one maximal target error and same-slot retry |
| invalid target reaches `=` or boundary | one target error; `=` stays available; no duplicate target missing |
| exact `=` with no body | one zero-width `Missing(BindingRole::Body, Expression)` inside `BindingBody` |
| malformed inline body then expression | one maximal body error and same-slot retry |
| malformed nested indented statement | one `BindingRole::IndentedStatement` record; outer body does not duplicate it |
| accepted Use with no path | one zero-width `Missing(ImportRole::Path)`; boundary is non-consuming |
| malformed Use path/suffix then candidate | existing Import error and same-slot retry |
| missing group item or close | group owner records it; it does not take an outer statement boundary |

Every `Missing` is zero-width and every `Error` is a non-empty maximal run:
one recovery range produces one node and one record.

## 8. Boundary and state-restoration contract

The shared canonical entry serves indented and braced blocks and inline With
bodies. It preserves ownership of commas, semicolons, newlines, dedents,
matching closes, and If companions. Normal, recovery, and rollback exits restore
scanner input, line state, stop/delimiter scopes, indentation, expression state,
and diagnostic sink state exactly.

## 9. Yulang2 divergences

Surface acceptance follows the oracle's contextual statement-head rule and
detailed Use scanner grammar. Yulang3 instead uses typed role-specific recovery,
one canonical statement entry, and keeps nested Use syntax separate from header
facts and import semantics. An absent Use prefix and explicit `my` both
normalize to private visibility while CST spelling stays lossless.

## 10. Known residual / deferred surface

The addendum records no accepted syntax residual for Binding or Use. Deferred
work includes lexical import scope, module resolution, export semantics,
semantic validation/projection policy, and the declaration kinds excluded from
this expansion.

## 11. Implementation and regression cross-reference

In `crates/yu-syntax/src/grammar/declaration.rs`:
`recognize_statement_intro`, `recognize_binding_statement_intro`,
`parse_binding_declaration_with_operators`, `parse_binding_body_ast`,
`commit_binding_declaration`, `commit_binding_body`,
`parse_use_declaration`, `parse_use_tree`, `commit_use_declaration`, and
`commit_use_tree`. In `crates/yu-syntax/src/grammar/expression.rs`:
`parse_canonical_statement` and `commit_canonical_statement`.

Fixtures:
`bindings_accept_every_visibility_optional_definition_and_pattern_target`,
`binding_indented_body_reuses_the_canonical_statement_dispatch`,
`visibility_prefixed_use_is_selected_only_with_a_valid_use_tree`,
`direct_binding_missing_body_closes_the_statement_and_emits_one_missing_node`,
`direct_binding_missing_target_uses_the_binding_owner_role`,
`direct_use_missing_target_closes_the_declaration_and_emits_one_missing_node`,
and `direct_use_declaration_has_header_full_fact_parity_and_lossless_groups`.

