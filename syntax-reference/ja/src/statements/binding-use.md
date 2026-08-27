# canonical Binding / Use

## 1. 状態・根拠・最終照合

このページは `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` の
Authoritative な追補「canonical `Statement` の binding / use declaration extension」
（11086–11623行）を要約する。補助となる Complete `use` declaration grammar and
projection（933–1924行）が recursive `UseTree` grammar と projection を定める。

design approval は `fe6f06c2`、canonical parser integration は `49c08530`。
このページは `96d98da4` に対して最終照合した。

## 2. 対象と非対象

この追補は Binding と Use を root および nested statement owner の canonical
`Statement` alternative にする。Binding は visibility prefix、mandatory Pattern target、
optional definition body を持つ。Use は structured use-tree grammar を再利用し、root
header projection を含む。

後続 declaration kind、`for`、operator definition、`where` statement、lexical import
scope、module resolution、export semantics は対象外である。

## 3. BNF 相当の grammar

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

`UseDeclaration` と `UseTree` は 933–1924行の定義を使う。`::` / `/` path、
recursive group、alias、glob、version、exclusion、anchor は source structure を保持する。

## 4. Judge・priority・owner boundary

canonical recognition は caller-owned EOF、separator、dedent、matching close、companion stop を
先に non-consuming で残す。その後の sink-free word probe は bare `use`、または valid
use-tree candidate がある visibility-led Use を選ぶ。それ以外の `my`、`our`、`pub` は
Binding を選ぶ。したがって `my use path` は Use、`my use = value` は Pattern が
`use` の Binding、`myx` / `useful` は split されない。

Binding は Pattern を読む間だけ `Equal` を加える。exact `=` 後の same-line input は
inline `OperatorChain`、strictly deeper newline は `IndentedStatementBlock`、
equal-or-shallower newline は outer statement owner のままである。

## 5. byte-exact CST worked examples

追補は source ownership を固定し、synthetic wrapper を許さない。

```text
pub x
```

は bodyless `BindingStatement` であり、`BindingHeader` は持つが empty
`BindingBody` は作らない。

```text
my x =
  my y = 1
  y
```

は outer binding 一つと、canonical statement 二つを持つ `IndentedStatementBlock` 一つで
ある。opening indentation trivia は block が所有する。

```text
my x = y with:
  my y = 1
```

は documented generic `WithBodyTail` 例であり、inline body は選択済み declaration の
canonical `Statement` wrapper 一つを持つ。

```text
use realm/tools::format
```

は declaration range `0..23` を持つ。detailed Use grammar はこれを `Realm` と分類し、
normalized path に `tools`、`format` を持つ。root output は `BindingStatement` /
`UseDeclaration` を `Root` 直下に置き、nested output だけが `Statement` wrapper を
ちょうど一つ加える。separator と matching close は enclosing sequence が所有する。

## 6. parser 側 AST shape

現在の enum には後続 variant があるが、対象 shape は次である。

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

`definition: None` は valid bodyless Binding を表す。accepted body が incomplete の場合は
`Some(BindingDefinition { .. })` に残る。`UseTree` は後続の projection と semantic
validation のため recursive structure を保持する。

## 7. typed recovery table

| slot / condition | record と continuation |
| --- | --- |
| Binding visibility 後に target なし | zero-width `Missing(BindingRole::Target, Pattern)` 一件。boundary は non-consuming |
| malformed Binding target 後に Pattern | maximal target error 一件と same-slot retry |
| invalid target が `=` / boundary に到達 | target error 一件。`=` は使用可能で target Missing は重複しない |
| exact `=` 後に body なし | `BindingBody` 内に zero-width `Missing(BindingRole::Body, Expression)` 一件 |
| malformed inline body 後に expression | maximal body error 一件と same-slot retry |
| malformed nested indented statement | `BindingRole::IndentedStatement` record 一件。outer body は重複しない |
| accepted Use 後に path なし | zero-width `Missing(ImportRole::Path)` 一件。boundary は non-consuming |
| malformed Use path/suffix 後に candidate | existing Import error と same-slot retry |
| group item / close が欠落 | group owner が record し、outer statement boundary を取らない |

すべての `Missing` は zero-width、`Error` は non-empty maximal run である。一つの
recovery range は一つの node と一つの record を作る。

## 8. boundary と state-restoration contract

shared canonical entry は indented / braced block と inline With body から使われる。comma、
semicolon、newline、dedent、matching close、If companion の ownership を保つ。normal、
recovery、rollback exit は scanner input、line state、stop/delimiter scope、indentation、
expression state、diagnostic sink state を exact restore する。

## 9. Yulang2 divergences

surface acceptance は oracle の contextual statement-head rule と detailed Use scanner grammar に従う。
Yulang3 は typed role-specific recovery と canonical statement entry 一つを使い、nested Use syntax を
header fact / import semantics から分離する。Use prefix absence と explicit `my` は private visibility
へ normalize するが、CST spelling は lossless に保つ。

## 10. known residual / deferred surface

Binding / Use に accepted syntax residual は記録されていない。lexical import scope、module
resolution、export semantics、semantic validation/projection policy、またこの expansion から除外された
declaration kind は deferred である。

## 11. implementation と regression fixture cross-reference

`crates/yu-syntax/src/grammar/declaration.rs`:
`recognize_statement_intro`、`recognize_binding_statement_intro`、
`parse_binding_declaration_with_operators`、`parse_binding_body_ast`、
`commit_binding_declaration`、`commit_binding_body`、
`parse_use_declaration`、`parse_use_tree`、`commit_use_declaration`、
`commit_use_tree`。`crates/yu-syntax/src/grammar/expression.rs`:
`parse_canonical_statement`、`commit_canonical_statement`。

fixture:
`bindings_accept_every_visibility_optional_definition_and_pattern_target`、
`binding_indented_body_reuses_the_canonical_statement_dispatch`、
`visibility_prefixed_use_is_selected_only_with_a_valid_use_tree`、
`direct_binding_missing_body_closes_the_statement_and_emits_one_missing_node`、
`direct_binding_missing_target_uses_the_binding_owner_role`、
`direct_use_missing_target_closes_the_declaration_and_emits_one_missing_node`、
`direct_use_declaration_has_header_full_fact_parity_and_lossless_groups`。

