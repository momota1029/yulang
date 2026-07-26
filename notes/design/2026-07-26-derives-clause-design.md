# Yulang `derives` clause 設計

決定日: 2026-07-26
状態: **設計案／ユーザ承認前**

この文書は、型宣言へ明示的な role 実装を付与する `derives` clause の意味論と、
parser、module map、lowering、role solver、compiled-unit cache の接続方法を定める。
実装時の指示書として使える粒度を目標とする。

本設計でいう「生成される impl」は、source に実在する文字列を CST へ差し込むという意味ではない。
通常の `impl` と同じ `RoleImplCandidate`、method `Def`、prerequisite、runtime body を持つ
compiler-generated impl を指す。

## 0. 承認済みの固定決定

この節の D1〜D6 は supervising agent が決定し、ユーザが承認した入力である。
本設計では変更しない。

### D1. deriving は常に明示的である

`derives` を書いた role だけを生成する。「明示 impl が無ければ自動 derive」という規則は持たない。

理由は impl の優先順位を導入しないためである。現行 solver は適合候補がちょうど一つのときだけ
解決する。`crates/infer/src/role_solve/mod.rs`:

```rust
if candidates.len() != 1 {
    if candidates.len() > 1 {
        stats.ambiguous_demands += 1;
    }
    PureRoleDemandOutcome::Unresolved {
        candidate_matches: candidates.len(),
    }
} else {
    // one candidate
}
```

したがって derived impl と手書き impl の間に priority / specificity を追加しない。

### D2. surface grammar

```text
DerivesClause ::= "derives" RoleRef ("," RoleRef)* ["via" ViaTarget]
```

`via` は clause 全体へ掛かる。role ごとに異なる field を使う場合は clause を分ける。

```yu
struct sample { key: int, label: str }
    derives Eq via key
    derives Debug via label
```

### D3. attachment position は三つある

三つとも同じ `DerivesClause` を受け付け、意味論も同じである。

```yu
-- (a) brace body の後ろ
struct point { x: int, y: int } derives Eq, Debug

-- (b) with: companion block の中
struct point { x: int, y: int } with:
    derives Eq, Debug

-- (c) declaration header、indent body の前
struct point derives Eq, Debug:
    x: int
    y: int
```

indent body の後ろへ同じ column の trailing clause を置くと宣言から視覚的に離れるため、
header position を持つ。brace body では trailing position が自然である。

複数 position に分散して書かれても、source 順に一つの derive request 列へ正規化する。
同じ role の重複を暗黙に消さない。

### D4. `derives` は contextual keyword である

`derives` を一般 keyword table へ追加しない。

```yu
my derives = 1
```

これは引き続き有効である。型宣言 header、`finish_with_or_stmt_stop` が扱う trailing slot、
companion block の statement slot だけで、`Ident` の text が `derives` かを認識する。

現行の trailing 接続点は `crates/parser/src/stmt/type_decl.rs` にある。

```rust
pub(super) fn finish_with_or_stmt_stop(...) {
    if with_kw.is_none() {
        if let Some(next) = peek_stmt_lex(...) {
            if next.kind == SyntaxKind::With {
                with_kw = scan_stmt_lex(...);
            }
        }
    }
    // ...
}
```

### D5. `via` は field delegation である

```yu
struct meters { v: float } derives Eq, Ord via v
```

これは role method を field `v` へ委譲する、という意味である。
Haskell の `DerivingVia` のような別表現型との共有でも、`eq via ord` のような
role-to-role derivation でもない。role-to-role derivation を将来入れるなら role 宣言側へ置く。

### D6. 既存の `via` token を再利用する

`via` 自体は既に keyword である。`crates/parser/src/scan/mod.rs`:

```rust
pub const KEYWORDS: &[&str] = &[
    // ...
    "via", "rule", "prefix", "infix", "suffix", "nullfix", "lazy",
];
```

現行 parser は `impl Target via Source` を受理する。`crates/parser/src/stmt/impl_decl.rs`:

```rust
match stop.kind {
    SyntaxKind::Via => {
        i.env.state.sink.lex(&stop);
        parse_via_after_kw(i.rb(), stop.trailing_trivia_info())
    }
    // ...
}
```

しかし lowering が読むのは最初の `TypeExpr` と `ImplDescription` の中の `TypeExpr` だけである。
`crates/infer/src/lowering/mod.rs`:

```rust
fn impl_head_type_expr(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::TypeExpr)
}

fn impl_description_type_expr(node: &Cst) -> Option<Cst> {
    crate::child_node(node, SyntaxKind::ImplDescription)?
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeExpr)
}
```

つまり `via` 後の二番目の型は現在完全に無視される。repository の `.yu` source に
`impl ... via ...` の使用例も無い。

**判断:** `derives` parser slice と同時に、`impl ... via ...` の受理を廃止し、明示的な
syntax diagnostic にする。推奨文言は
`impl ... via ... is not implemented; use via only in a derives clause` とする。
互換動作として無視し続ける案は、書いた operand と実行意味が一致しないため棄却する。
deprecation period は実使用が無く、現行意味も未実装なので設けない。

## 1. 現行実装から確定した前提

### 1.1 `Eq` と `Debug` の正確な形

`Eq` は一つの必須 method を持つ。`lib/std/core/cmp.yu`:

```yu
pub role Eq 'a:
    pub a.eq: 'a -> bool
```

同ファイルの `Eq` impl は `int`、`float`、`frac`、`bool`、`str`、`char` と
`list int` に対する concrete impl である。generic conditional `Eq` impl はまだ無い。
`list int` も element prerequisite を持つ conditional impl ではない。

```yu
impl (list int): Eq:
    our xs.eq ys = case (std::data::list::view_raw xs, std::data::list::view_raw ys):
        (std::data::list::list_view::empty, std::data::list::list_view::empty) -> true
        (std::data::list::list_view::leaf x, std::data::list::list_view::leaf y) -> std::int::eq x y
        (std::data::list::list_view::node(xl, xr), std::data::list::list_view::node(yl, yr)) ->
            if xl.eq yl: xr.eq yr else false
        _ -> false
```

`Debug` は必須 `debug` と、body を持つ既定 method `dd` から成る。
`lib/std/core/fmt.yu`:

```yu
pub role Debug 'a:
    pub a.debug: str
    pub a.dd = std::io::err::write: a.debug + "\n"
```

同ファイルには `Display` と `Debug` の conditional impl があり、生成 impl の
prerequisite 表現の規範になる。`Display` の全 conditional head は次の通りである。

```yu
impl (list 'a): Display:
    where 'a: Display
    our xs.show = "[" + show_list_items xs + "]"

impl (opt 'a): Display:
    where 'a: Display
    our value.show = case value:
        std::data::opt::opt::nil -> "nil"
        std::data::opt::opt::just inner -> "just " + inner.show

impl (result 'ok 'err): Display:
    where 'ok: Display
    where 'err: Display
    our value.show = case value:
        std::data::result::result::ok inner -> "ok " + inner.show
        std::data::result::result::err inner -> "err " + inner.show

impl ('a, 'b): Display:
    where 'a: Display
    where 'b: Display
    our value.show = case value:
        (a, b) -> "(" + a.show + ", " + b.show + ")"
```

3〜5 要素 tuple も、各型変数へ一つずつ同じ prerequisite を置く。
`lib/std/core/fmt.yu`:

```yu
impl ('a, 'b, 'c): Display:
    where 'a: Display
    where 'b: Display
    where 'c: Display
    our value.show = case value:
        (a, b, c) -> "(" + a.show + ", " + b.show + ", " + c.show + ")"

impl ('a, 'b, 'c, 'd): Display:
    where 'a: Display
    where 'b: Display
    where 'c: Display
    where 'd: Display
    our value.show = case value:
        (a, b, c, d) -> "(" + a.show + ", " + b.show + ", " + c.show + ", " + d.show + ")"

impl ('a, 'b, 'c, 'd, 'e): Display:
    where 'a: Display
    where 'b: Display
    where 'c: Display
    where 'd: Display
    where 'e: Display
    our value.show = case value:
        (a, b, c, d, e) -> "(" + a.show + ", " + b.show + ", " + c.show + ", " + d.show + ", " + e.show + ")"
```

`Debug` 側も同じ prerequisite 構造で、body だけ `.debug` を使う。

```yu
impl (list 'a): Debug:
    where 'a: Debug
    our xs.debug = "[" + debug_list_items xs + "]"

impl (opt 'a): Debug:
    where 'a: Debug
    our value.debug = case value:
        std::data::opt::opt::nil -> "nil"
        std::data::opt::opt::just inner -> "just " + inner.debug

impl (result 'ok 'err): Debug:
    where 'ok: Debug
    where 'err: Debug
    our value.debug = case value:
        std::data::result::result::ok inner -> "ok " + inner.debug
        std::data::result::result::err inner -> "err " + inner.debug

impl ('a, 'b): Debug:
    where 'a: Debug
    where 'b: Debug
    our value.debug = case value:
        (a, b) -> "(" + a.debug + ", " + b.debug + ")"
```

3〜5 要素 tuple も各型変数へ一つずつ `Debug` prerequisite を置く。
`lib/std/core/fmt.yu`:

```yu
impl ('a, 'b, 'c): Debug:
    where 'a: Debug
    where 'b: Debug
    where 'c: Debug
    our value.debug = case value:
        (a, b, c) -> "(" + a.debug + ", " + b.debug + ", " + c.debug + ")"

impl ('a, 'b, 'c, 'd): Debug:
    where 'a: Debug
    where 'b: Debug
    where 'c: Debug
    where 'd: Debug
    our value.debug = case value:
        (a, b, c, d) -> "(" + a.debug + ", " + b.debug + ", " + c.debug + ", " + d.debug + ")"

impl ('a, 'b, 'c, 'd, 'e): Debug:
    where 'a: Debug
    where 'b: Debug
    where 'c: Debug
    where 'd: Debug
    where 'e: Debug
    our value.debug = case value:
        (a, b, c, d, e) -> "(" + a.debug + ", " + b.debug + ", " + c.debug + ", " + d.debug + ", " + e.debug + ")"
```

module map は `where` を source-level advertised prerequisite として保存する。
`crates/infer/src/module_map/mod.rs`:

```rust
fn role_impl_advertised_prerequisites(block: &Cst) -> Vec<StoredRoleImplPrerequisite> {
    block
        .children()
        .filter(|child| child.kind() == SyntaxKind::WhereClause)
        // ...
        .map(|predicate| StoredRoleImplPrerequisite { /* subject, role, span */ })
        .collect()
}
```

### 1.2 `error` の compiler-generated `Display` impl

型 lowering の entrypoint は `error` だけ synthetic declarations を追加する。
`crates/infer/src/lowering/body/type_decl.rs`:

```rust
self.lower_type_constructors(node, module, &decl);
self.lower_type_decl_with_body(node, &decl);
if decl.kind == ModuleTypeKind::Error {
    self.lower_error_synthetic_decls(node, &decl);
}
```

`crates/infer/src/lowering/body/error_decl.rs` の生成順は次の通りである。

```rust
pub(super) fn lower_error_synthetic_decls(&mut self, node: &Cst, decl: &ModuleTypeDecl) {
    // ...
    self.lower_error_operations(node, decl, &error);
    self.lower_error_throw_impl(node, decl, &error);
    self.lower_error_display_impl(node, decl, &error);
    self.lower_error_wrap_helper(node, decl, &error);
    self.lower_error_up_helper(node, decl, &error);
}
```

`Display` は canonical path `std::core::fmt::Display` を解決し、input が一つで
`show` method を持つ場合だけ生成する。生成 body は variant ごとの `case` である。

```rust
fn synthetic_error_display_source(error: &ErrorDecl) -> Option<String> {
    let mut out = "our __error_value.show = case __error_value:\n".to_string();
    for (index, variant) in error.variants.iter().enumerate() {
        let pattern = error_variant_pattern_source(&variant.name, &variant.payload, index)?;
        let body = error_display_expr(&variant.name.0, &variant.payload, index, variant.from)?;
        // append `pattern -> body`
    }
    Some(out)
}
```

unit variant は `"name"`、通常の一 payload は `"name: " + payload.show`、
`from` 一 payload は `payload.show`、複数 payload は `"name(" + ... + ")"` になる。
同ファイル:

```rust
match constructor_payload_arity(payload) {
    0 => Some(quoted_string_literal(name)),
    1 if from => Some(format!("{}.show", error_payload_name(index, 0).0)),
    1 => Some(format!(
        "{} + {}.show",
        quoted_string_literal(&format!("{name}: ")),
        error_payload_name(index, 0).0
    )),
    // multiple payloads: name(a, b)
}
```

この impl は普通の `ImplDecl` として module map へ登録されない。
`impl_def` と `method_def` を lowering 中に直接採番し、
`register_role_impl_candidate` を直接呼ぶ。

```rust
self.session
    .register_role_impl_candidate(RoleImplCandidate {
        impl_def: Some(impl_def),
        role: role_path,
        inputs,
        associated,
        prerequisites: Vec::new(),
        methods: Vec::new(),
    });
```

一方、method body は通常 impl と同じ `lower_role_impl_method_binding` へ渡す。

```rust
self.lower_role_impl_method_binding(
    &binding,
    impl_def,
    error.companion,
    &RoleImplMethodDecl { /* show */ },
    &context.target_ann,
    &context.type_var_bindings,
    &mut context.ann_solver_vars,
    requirement,
    None,
);
```

したがって precedent の正確な評価は「通常の module-map registration は通らないが、
candidate table、role requirement、method lowering、residual prerequisite 回収は共有する」である。

### 1.3 普通の `impl` と companion block

普通の `ImplDecl` は module map で `impl_def`、匿名 body module、method defs、
advertised prerequisites を先に登録する。`crates/infer/src/module_map/mod.rs`:

```rust
fn register_role_impl_decl(&mut self, node: &Cst, module: ModuleId) -> Option<DefId> {
    let order = self.modules.next_order(module);
    let def = self.arena.defs.fresh();
    let body_module = self.modules.new_anonymous_child_module(module, order);
    // register prerequisites and methods
    self.modules.insert_role_impl(RoleImplDecl {
        def,
        module,
        body_module,
        order,
        advertised_prerequisites,
        methods,
    });
    Some(def)
}
```

body lowering はその登録済み宣言を順に取り出し、candidate を登録してから各 method を
共通の method lowerer へ渡す。`crates/infer/src/lowering/body/impl_decl.rs`:

```rust
let Some(impl_decl) = self.next_role_impl_decl(module) else {
    return;
};
let mut context = match self.register_role_impl_candidate(
    node,
    impl_decl.def,
    module,
    impl_decl.order,
    self_alias,
) {
    // ...
};

// ...
let requirement =
    self.role_impl_method_requirement(&context, method_info.name.clone());
self.lower_role_impl_method_binding(
    &child,
    impl_decl.def,
    impl_decl.body_module,
    // ...
    requirement,
    conformance_shadow_target,
);
```

`with:` body の nested `ImplDecl` も同じ関数で登録される。
`crates/infer/src/module_map/finish.rs`:

```rust
SyntaxKind::ImplDecl => {
    if let Some(def) = self.register_role_impl_decl(&child, module) {
        children.push(def);
    }
}
```

lowering では enclosing type の `AnnSelfAlias` を渡す。
`crates/infer/src/lowering/body/type_decl.rs`:

```rust
let self_alias = AnnSelfAlias {
    owner: decl.id,
    type_vars: crate::type_var_names(node),
};

// ...
SyntaxKind::ImplDecl => {
    self.lower_role_impl_decl(&child, companion, Some(self_alias.clone()))
}
```

この self alias と companion module が、三 attachment position を同じ意味へ正規化する際の
基準になる。

### 1.4 impl table と重複時の現行診断

final poly 側の `RoleImplTable` は role path ごとの flat candidate list であり、
priority を持たない。`crates/poly/src/roles.rs`:

```rust
pub struct RoleImplTable {
    candidates: FxHashMap<Vec<String>, Vec<RoleImplCandidate>>,
}

pub fn insert(&mut self, candidate: RoleImplCandidate) {
    self.candidates
        .entry(candidate.role.clone())
        .or_default()
        .push(candidate);
}
```

同じ target / role の impl を二つ宣言しても、宣言地点では専用 duplicate diagnostic が出ない。
method demand が二候補へ適合した地点で通常の ambiguity になる。
`crates/yulang/tests/cli.rs` の回帰 source:

```yu
role R 'a:
    our a.foo: int

impl int: R:
    our x.foo = 1

impl int: R:
    our x.foo = 2

1.foo
```

同テストが固定する診断は次である。

```text
compile error [yulang.ambiguous-method]: more than one role implementation satisfies this method call
hint: make the receiver type more specific or keep only one matching impl in scope
```

「ordinary duplicate-impl error」は現行実装ではこの use-site ambiguity を意味する。
`derives Eq` と手書き `impl point: Eq` の組にも特別な優先順位を付けず、この通常挙動を適用する。

### 1.5 finalized artifact と role impl

final poly arena は role impl を後段用 metadata として保持する。
`crates/poly/src/expr.rs`:

```rust
/// source lowering で解決された role impl candidate。
///
/// downstream stages need role impls to materialize role-constrained schemes without
/// depending on infer's mutable solver tables.
pub role_impls: RoleImplTable,
```

通常 finalization は infer table の全候補を final poly type arena へ clone する。
`crates/infer/src/analysis/session/instantiate.rs`:

```rust
pub fn finalize_poly_role_impls(&mut self) {
    let candidates = self
        .role_impls
        .iter()
        .map(|candidate| clone_role_impl_candidate_between_arenas(/* ... */))
        .collect::<Vec<_>>();
    self.poly.role_impls = RoleImplTable::new();
    for candidate in candidates {
        self.poly.role_impls.insert(candidate);
    }
}
```

canonical cache handoff も frozen candidates から `poly.role_impls` を作る。
`crates/infer/src/analysis/cache_interface.rs`:

```rust
let mut role_impls = RoleImplTable::new();
for candidate in candidates.candidates {
    role_impls.insert(candidate.candidate);
}
poly.role_impls = role_impls;
```

同ファイルは candidate 一つだけを落とすと source impl が suffix role resolution から消えるため、
一候補の freeze failure でも unit-level fallback にする、と明記している。

```rust
/// Dropping only a failed candidate would remove a source impl from suffix role resolution.
/// Until a semantics-preserving per-candidate fallback exists, unit-level fallback is the safe
/// compiled-artifact granularity.
```

prefix を使う新 session は artifact の候補を freshen して通常 table へ再登録する。
`crates/infer/src/analysis/session/lifecycle.rs`:

```rust
let role_impls = self.poly.role_impls.iter().cloned().collect::<Vec<_>>();
for candidate in role_impls {
    let candidate = freshen_role_impl_candidate(/* ... */);
    self.register_role_impl_candidate(candidate);
}
```

runtime surface の reachability も candidate の `impl_def` と各 method implementation を選ぶ。
`crates/infer/src/compiled_runtime.rs`:

```rust
for candidate in source.role_impls.iter() {
    if let Some(def) = candidate.impl_def {
        self.select_def(source, external_defs, def);
    }
    for method in &candidate.methods {
        self.select_def(source, external_defs, method.requirement);
        self.select_def(source, external_defs, method.implementation);
    }
}
```

### 1.6 現在の `assert_eq` workaround

2026-07-26 の作業ツリーでは `lib/std/testing.yu` が二つの thunk を effect payload に載せる。

```yu
pub lazy infix(assert_eq) 1.0.0 1.0.1 = \left -> \right -> assertion::assert_eq (left, right)

pub act assertion:
    pub assert_eq: (() -> [_] 'a, () -> [_] 'a) -> ()
```

`crates/evidence-vm/src/runtime.rs` の current path は両 thunk を force したあと、
Rust の `PartialEq` である `expected == actual` を使い、`format_value` で表示する。

```rust
#[derive(Debug, Clone, PartialEq)]
enum RuntimeEvidenceValue {
    // ...
}

// ...
if expected == actual {
    Ok(())
} else {
    Err(RuntimeEvidenceRunError::AssertionEqualityFailed {
        site: request.site,
        expected: format_value(expected.as_ref()),
        actual: format_value(actual.as_ref()),
    })
}
```

このため source language の `Eq` / `Debug` 契約を通らず、constructor 値は
`<ctor d1>({v: 1})` のような VM 内部表現になりうる。

## 2. 解決した意味論と integration decision

### 2.1 RoleRef の解決と compiler-known identity

**決定:** `RoleRef` は普通の role 名参照であり、derive clause 専用の綴りを一切持たない。
`derives Eq`、`derives std::core::cmp::Eq`、import alias 経由の名前は、通常の type namespace と
visibility 規則で解決する。同じ `TypeDeclId` へ解決するなら、どの綴りでも同じ derive strategy を使う。

role 名の文字列を inference の途中で比較して型を決めない。derive lowering の入口で
canonical `TypeDeclId` を `DeriveStrategy::{Eq, Debug}` へ変換し、それ以後は enum identity を使う。
未知の `TypeDeclId` は §2.8 の diagnostic になる。

**棄却した代案:** derive clause の中だけ `eq` / `debug` を小文字で書ける shorthand を持つ案。
一箇所だけ名前解決規則が違う状態は、以後 role が増えるたびに shorthand 表を保守する義務を生み、
「なぜここだけ小文字なのか」を説明できない。std の role が `Eq` / `Debug` と大文字始まりである以上、
derive clause でもその綴りをそのまま使う。

全 type lookup を case-insensitive にする案も、derive と無関係な言語全体の名前解決を
変えるため棄却する。

### 2.2 展開 stage は lowering とする

**決定:** parser は dedicated `DerivesClause` CST を保持する。module map は clause の
enclosing `TypeDeclId`、companion module、source order、RoleRef / `via` span を保持する。
実際の impl candidate と method body の合成は type body lowering で行う。

処理順は次である。

1. parser が三 position を `DerivesClause` として lossless に保持する。
2. module map が三 position の clause を enclosing type ごとの source-order list に正規化する。
3. `BodyLowerer::lower_type_decl` が constructor と ordinary `with:` body を lower したあと、
   derive request を source 順に展開する。
4. RoleRef を canonical `TypeDeclId` と `DeriveStrategy` へ解決する。
5. field / variant payload から一度だけ `DerivePlan` を作る。plan は target annotation、
   prerequisite、method body、diagnostic span を持つ。
6. synthetic `impl_def` / method `Def` を作り、通常と同じ
   `register_role_impl_candidate`、`role_impl_method_requirement`、
   `lower_role_impl_method_binding` を使う。
7. method generalization が回収した residual prerequisite と plan の advertised prerequisite を
   同じ candidate へ統合し、通常 finalization / cache handoff へ流す。

`error` の synthetic `Display` と derives のために
`lower_synthetic_role_impl` 相当の共通 helper を抽出してよい。
ただし error の既存表示意味を変更しない。`derives` 専用の二つ目の impl table は作らない。

#### parser desugaring を棄却する理由

parser は role identity、role methods、field type、generic prerequisite を知らない。
そこで完全な `ImplDecl` CST を合成すると、文字列ベースの role 判定、偽 source span、
synthetic source の再 parse が parser に入り込む。lossless CST の責務から外れる。

#### module-map registration 時の完全展開を棄却する理由

module map は普通の `impl` なら source body から method を先に採番できるが、
`derives RoleRef` の method 集合は RoleRef 解決後でなければ決まらない。
任意の path / alias をまだ canonical role identity にしていない段階で、
method 名を `eq` / `debug` の文字列から決めるべきではない。

#### lowering に独立 shortcut を作る案を棄却する理由

runtime primitive として構造比較・表示を追加すると、普通の role resolution、
prerequisite、duplicate ambiguity、cache candidate を迂回する。
`error Display` が既に共有している candidate / method lowering machineryへ乗せる。

### 2.3 対象 declaration

first implementation で対象にするのは nominal algebraic declarations である。

- named-field `struct`
- tuple `struct`
- `enum`
- `error`

`type` alias は新しい nominal representation ではなく、underlying type と impl head が重なるため
対象外とする。`role` と `act` も値の field / variant 構造を持たないため対象外とする。
対象外 declaration に clause を書いた場合は `yulang.invalid-derive-target` を clause span に出す。

`error` の既存 automatic `Display` は互換性のため残す。D1 は新しい `derives` feature が
implicit fallback を持たない、という決定であり、既存 error sugar の削除を意味しない。

### 2.4 `Eq` の生成規則

#### named-field struct

全 field を declaration 順に比較し、最初の false で終了する。zero-field struct は true とする。

```yu
struct pair 'a { l: 'a, r: 'a } derives Eq
```

これは次と意味的に等価である。

```yu
impl (pair 'a): Eq:
    where 'a: Eq
    our x.eq y =
        if x.l.eq y.l:
            x.r.eq y.r
        else:
            false
```

同じ prerequisite は重複排除するため、`l` と `r` がともに `'a` でも
`where 'a: Eq` は一つだけである。これは `fmt.yu` の
`where 'a: Debug` / `where 'a: Display` と同じ conditional impl 表現である。

#### tuple struct

payload を position 順に同じ方法で比較する。tuple struct 自体には named projection が無くても、
constructor pattern で payload を束縛して method body を作れる。

#### enum / error

同じ variant 同士なら payload を declaration 順に比較する。異なる variant は false。
unit variant 同士は true。variant declaration order を equality の意味へ使わない。

#### prerequisite

derive plan が実際に比較する各 field / payload type `F` に対し `F: Eq` を要求する。
`F` が declaration type parameterそのものなら `where 'a: Eq` になる。
`F` が `container 'a` なら prerequisite は `where (container 'a): Eq` であり、
勝手に `where 'a: Eq` へ強めない。

closed concrete `F` に適合 candidate が無ければ declaration 時の derive failure にする。
open `F` は conditional candidate として保持する。後の具体化で prerequisite を満たせなければ、
通常の unresolved role method になる。

比較は field role method を呼ぶ。VM-level structural equalityを使わない。

### 2.5 `Debug` の生成規則

`Debug` は source declaration の構造を一行で表す。既存の
`lib/std/time.yu` は named struct の手書き precedent を持つ。

```yu
impl instant: Debug:
    our x.debug = "instant { epoch_nanos: " + std::int::to_string x.epoch_nanos + " }"
```

first implementation の exact format を次に固定する。

| declaration/value shape | output |
|---|---|
| `struct point { x, y }` | `point { x: <debug>, y: <debug> }` |
| zero-field `struct marker {}` | `marker { }` |
| tuple `struct meters(float)` | `meters(<debug>)` |
| enum/error unit variant | `type_name::variant` |
| enum/error tuple payload | `type_name::variant(<debug>, <debug>)` |
| enum/error named payload | `type_name::variant { field: <debug> }` |

field と payload は declaration 順に出す。型名、variant 名、field 名は source declaration の
semantic name を使い、runtime `DefId` や `<ctor d1>` を出さない。
各値は `.debug` で表示し、`Display` へ fallback しない。
synthetic impl が生成する method は必須の `debug` だけである。`dd` は role 宣言に body を持つ
既定 method なので、手書き `Debug` impl と同じく上書きせず継承する。

prerequisite 規則は Eq と同じで、実際に表示する各 type `F` に `F: Debug` を要求する。
同じ predicate は重複排除する。

### 2.6 `via` の詳細

**決定:** `ViaTarget` は一つの unqualified field identifier とする。

- target は enclosing named-field struct が直接宣言した field でなければならない。
- `via a.b` の nested path は認めない。
- ordinary external visibility lookup は行わない。clause は宣言自身に attached しているため、
  その declaration の direct field table から解決する。
- multi-field struct で `via v` を書いた場合、他 field は Eq / Debug の意味へ一切参加しない。
- tuple struct には field 名が無いため `via` を認めない。`via 0` の positional syntax も
  first implementation では導入しない。
- enum / error は全 variant に共通する一つの direct field を保証できないため `via` を認めない。

`struct meters { v: float } derives Eq via v` の生成形は次である。

```yu
impl meters: Eq:
    our x.eq y = x.v.eq y.v
```

generic field なら通常と同じ prerequisite を持つ。

```yu
struct key_box 'a { key: 'a, ignored: int } derives Eq, Debug via key

-- semantic equivalent
impl (key_box 'a): Eq:
    where 'a: Eq
    our x.eq y = x.key.eq y.key

impl (key_box 'a): Debug:
    where 'a: Debug
    our x.debug = x.key.debug
```

Debug via は wrapper 名を付けず、field の debug text そのものを返す。これが「delegation」の意味である。

named field が closed concrete typeで、その role を持たない場合は
`yulang.unsatisfied-derive` を `via` target span に出す。open type なら conditional
prerequisite にする。

### 2.7 first implementation の derivable role

#### in scope

- `std::core::cmp::Eq`
- `std::core::fmt::Debug`

どちらも `assert_eq` の language-level equality と failure rendering に必要であり、
method の構造的意味が一意に定まる。

#### out of scope

- `Ord`
- `Display`
- `Cast`
- `Len` / `IsEmpty`
- arithmetic roles (`Add`, `Sub`, `Mul`, `Div`)
- `LowerHex` / `UpperHex`
- その他の std role
- arbitrary user-defined role

**Ord の判断:** first implementation から外す。`lib/std/core/cmp.yu` の `Ord` は
`lt` / `le` / `gt` / `ge` の四 method を持つ。

```yu
pub role Ord 'a:
    pub a.lt: 'a -> bool
    pub a.le: 'a -> bool
    pub a.gt: 'a -> bool
    pub a.ge: 'a -> bool
```

product / enum の順序を declaration-order lexicographic とするか、`Eq` も prerequisite にするか、
四 method の整合をどの law に依存させるかが別の意味論決定になる。
D5 の `derives Eq, Ord via v` は delegation の意味を固定する規範例だが、
v1 で `ord` を受理するという scope 決定ではない。

**Display の判断:** 構造表示は `Debug` の責務である。人間向け `Display` は
`instant` の RFC 3339 のように domain semantics を必要とし、field structure から一意に決まらない。

**任意 role の判断:** compiler は未知 role method の意味を合成できない。
`via` で全 method を機械 forwarding する案も、receiverless method、associated type、
default method、複数 role input の扱いを別途定義する必要があるため v1 では採らない。
derive strategy は固定 registry とし、既知 role の canonical identity だけを受け付ける。

### 2.8 failure mode と diagnostic

diagnostic は synthetic body の偽 span ではなく、実 source の RoleRef、field、`via` span に付ける。

| failure | diagnostic |
|---|---|
| RoleRef が type namespace で解決しない | 既存 `yulang.unresolved-type`: `unresolved type name: <role>` |
| role は解決するが derivable registry に無い | `yulang.unsupported-derive-role`: `role <R> cannot be derived` |
| target declaration kind が対象外 | `yulang.invalid-derive-target` |
| direct field / closed payload が role を持たない | `yulang.unsatisfied-derive`: `cannot derive <R> for <T>: field <f> does not implement <R>` |
| `via` field が存在しない | `yulang.unknown-derive-field`: `type <T> has no field named <f>` |
| tuple struct / enum / error に `via` | `yulang.invalid-derive-via-target` |
| derived impl と explicit impl が重なる | 現行の通常 `yulang.ambiguous-method` |

既存 unresolved type diagnostic の公開形は `tests/yulang/cases.toml` が次のように固定している。

```text
error [yulang.unresolved-type]: x: unresolved type name: missing_type
hint: define type `missing_type` before this annotation, or import it
```

derive 用では label を RoleRef text にし、hint は
`define or import role <R>, or use a supported derive role` とする。

closed field failure には field declaration span を related information として付ける。
generic/open field は failure ではなく `where` prerequisite になるため、この診断を出さない。

derived + explicit duplicate を derive 時だけ先回りして消したり、explicit を優先したりしない。
現行の exact message は 1.4 の通りである。一般的な declaration-time coherence check を
将来追加するなら derived / explicit を区別せず RoleImplTable 全体へ適用する。

### 2.9 std-prefix cache boundary

derived impl は finalized artifact に必ず永続化する。
保存対象は少なくとも次の全てである。

- candidate role identity と target inputs
- prerequisite
- `impl_def`
- requirement method → implementation method mapping
- implementation method `Def`、scheme、body

展開は canonical cache interface capture より前に完了させる。
prefix route は artifact の `poly.role_impls` を `seed_existing_poly_surface` で再登録するため、
cold route と prefix route は同じ source derive request から同じ candidate set を持つべきである。

具体的な回帰 risk は、synthetic candidate だけを artifact に入れ、method `Def` / body が
runtime reachability から落ちることである。もう一つは generic prerequisite の binder が
candidate head / cache boundary と一緒に freeze されず、unit-level fallbackになることである。

実装完了条件は、少なくとも次の parity test を含む。

1. derived `Eq` / `Debug` candidate 数、role path、target、prerequisite、method mapping が
   cold と prefix で一致する。
2. artifact serialize → deserialize → prefix seed 後も derived method call が動く。
3. generic derived impl の prerequisite binder が canonical handoff を通る。
4. explicit + derived duplicate が cold / prefix の両方で同じ二候補 ambiguity になる。
5. runtime selection が synthetic impl / method defs を保持する。

`crates/yulang/src/cache.rs` には prefix role impl reuse の既存回帰がある。

```rust
#[test]
fn compiled_unit_reachable_external_refs_reuse_prefix_role_impls() {
    // prefix declares Display and `impl int: Display`
    // suffix evaluates `1.display`
    // extended prefix must retain the suffix value
}
```

derived impl parity はこの test family に追加する。

### 2.10 `assert_eq` への downstream consequence

`derives Eq, Debug` が利用可能になった時点で、`assert_eq` を source role 上に組み直す。
VM は source values の Rust `PartialEq` を equality semantics として使わず、
raw `format_value` を failure representation として使わない。

schematic な公開型は次になる。

```text
assert_eq:
    (() -> ['left_eff] 'a)
    -> (() -> ['right_eff] 'a)
    -> [std::testing::assertion] ()
    where 'a: std::core::cmp::Eq
    where 'a: std::core::fmt::Debug
```

surface call では lazy operator が両 operand を thunk 化する。test handler が force した経路で
一度ずつ値を得て、`Eq.eq` で比較し、不一致時は両値の `Debug.debug` text を報告する。
通常実行で root handler が assertion を捨てる性質は維持する。

generic helper なら prerequisite は公開型へ残る。

```text
check_same: 'a -> 'a -> [std::testing::assertion] ()
    where 'a: Eq
    where 'a: Debug
```

一方、concrete type を比較する普通の test には外へ出る型変数が無い。

```yu
pub checked() =
    point { x: 1, y: 2 } assert_eq point { x: 1, y: 2 }
```

`point` の derived candidates が prerequisites を解決するため、`checked` の公開型は引き続き
次でよい。

```text
() -> [std::testing::assertion] ()
```

したがって ordinary concrete test code への prerequisite 負担は無い。
generic test utility が `Eq` / `Debug` を公開するのは、その utility が実際に要求する能力を
正直に表すため受け入れる。

## 3. implementation slicing plan

各 slice は単独 commit 可能にし、stop condition を満たすまで次へ進まない。

### DERIVE-A: CST と contextual grammar

三 attachment position、複数 clause、clause-wide `via` を dedicated CST として parse する。
`my derives = 1` を維持し、既存 `impl ... via ...` は明示 syntax error にする。

Stop condition: parser golden が三 position と複数 clause で同じ clause tree を示し、
identifier regression と `impl via` rejection が通る。

### DERIVE-B: declaration ownership と normalized `DeriveRequest`

module map に enclosing `TypeDeclId`、companion、source order、RoleRef / via spans を持つ
structured request を追加する。三 position を一列へ正規化する。まだ impl は生成しない。

Stop condition: module-map test が named struct、tuple struct、enum、errorについて、
attachment position に依存しない request と正しい self owner / span を示す。

### DERIVE-C: synthetic role impl 共通入口

`error Display` と derives が共有できる `lower_synthetic_role_impl` 境界を作る。
candidate registration、requirement lookup、method lowering、residual prerequisite integration を
通常 impl と共有する。error の既存 output は変えない。

Stop condition: 既存 error Display tests が無変更で通り、synthetic test candidate が
final `poly.role_impls` に method mapping と prerequisite を持つ。

### DERIVE-D: `Eq`

named / tuple struct、enum、error の structural Eq、zero-field / unit / different-variant、
generic prerequisite、via delegation を実装する。

Stop condition: `pair 'a` が exact `where 'a: Eq` candidate を一つ持ち、concrete positive /
negative runtime tests と via multi-field test が通る。

### DERIVE-E: `Debug`

2.5 の exact structural format と via delegation を実装する。全 field / payload で
`.debug` を使い、VM formatting へ fallback しない。

Stop condition: named / zero / tuple struct、unit / tuple / named enum variant、error、
generic prerequisite、via の golden output が exact match する。

### DERIVE-F: diagnostics と ordinary duplicate behavior

unknown / unsupported role、invalid target、missing closed prerequisite、unknown via field、
invalid via declaration kind を real source span へ出す。explicit + derived を
通常 candidate ambiguity に乗せる。

Stop condition: CLI `check` と source diagnostics の code / primary range / related field range が
一致し、duplicate test が既存 `yulang.ambiguous-method` 文言を保つ。

### DERIVE-G: canonical cache parity

derived candidate と method defs を canonical artifact に閉じ、cold/prefix parity tests を追加する。

Stop condition: 2.9 の五 parity 条件が serialize round-trip を含めて通り、
候補 freeze failure 時に derived candidate だけが silent drop されない。

### DERIVE-H: `assert_eq` role migration

`assert_eq` を `Eq` / `Debug` prerequisite 付きの source-level comparison / renderingへ移す。
evidence VM の assertion equality path から `RuntimeEvidenceValue` の直接 `==` と raw constructor
formatting への依存を外す。

Stop condition: primitive、derived struct、generic helper の success/failure、lazy non-test route、
公開型を確認し、failure が `point { x: 1, y: 2 }` のような derived Debug text を出す。

## 4. 判断と棄却した代案の一覧

| 判断 | 採用 | 棄却した代案 |
|---|---|---|
| expansion stage | lowering | parser で fake `ImplDecl` CST、module-map で文字列 role 判定 |
| generated impl machinery | ordinary candidate / method lowering と共有 | derives 専用 impl table、VM structural primitive |
| RoleRef identity | 普通の role 名参照 → canonical `TypeDeclId` + fixed strategy | derive 節専用の小文字 shorthand、inference 内の path string 分岐、全名前の case-insensitive lookup |
| first roles | Eq / Debug | Ord / Display / arbitrary user role まで同時導入 |
| via target | direct named field 一つ | nested path、tuple index、representation type |
| explicit conflict | ordinary two-candidate ambiguity | explicit priority、derived candidate の silent removal |
| cache failure | complete candidate を保存、失敗時 unit fallback | candidate だけ、または失敗 candidate だけを drop |

## 5. 決めていないこと

依頼された steps 3〜8 には、source から解けず実装を止める未解決点は残っていない。
次は意図的に first implementation の外へ置き、この文書では決めない。

- `Ord` の structural ordering、law、`Eq` prerequisite の有無。
- role 宣言自身が derive recipe や role-to-role derivation を宣言する構文。
- associated type / multiple input / receiverless method を含む user-defined role の forwarding derive。
- tuple struct の positional `via 0`。
- multiline / pretty-print option を持つ configurable `Debug`。
- RoleImplTable 全体に対する declaration-time coherence diagnostic。
  現行および v1 derives は use-site `yulang.ambiguous-method` を維持する。
- type alias、role、act へ deriving を広げる意味論。

著者: Claude (Opus 5)
ユーザ承認: 未
