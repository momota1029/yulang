# Yulang `my` visibility 統一 enforcement 設計

決定日: 2026-07-27
状態: **ユーザ承認済み。実装指示書として有効**

この文書は、値、型、module、act operation、method、`use` の全名前解決経路で
`my` の意味を一つに揃えるための実装指示書である。可視性の意味論を再検討する文書ではない。
固定済みの規則を、direct path、import view、compiled prefix のどこでも失わないことを目的とする。

調査と実測は 2026-07-27 の `ac2f0290c60c` を基準に行った。

## 0. 固定決定

### D1. `my` は declaring module とその子孫だけに見える

ユーザが決定済みの規則は次の通りである。本設計では変更しない。

> `my` declaration は、その declaration を持つ module 自身と、その module の内側に
> 任意の深さで入れ子になったすべての module から見える。それ以外からは、direct path、
> alias、glob、re-export、compiled prefix、method selection を含むどの綴りでも見えない。
> Rust の private item と同じ規則である。

したがって可視性は「同じ file か」「同じ band か」「`use` か direct path か」ではなく、
requester module と declaring module の ancestry で決まる。

## 1. 現行実装から確定した前提

### 1.1 ancestry は既存 `ModuleNode.parent` だけで判定できる

各 module node は親 `ModuleId` を既に持つ。`crates/infer/src/lib.rs:104-124`:

```rust
struct ModuleParent {
    module: ModuleId,
    order: ModuleOrder,
}

struct ModuleNode {
    parent: Option<ModuleParent>,
    // ...
}
```

子 module を挿入すると、その node の `parent` が設定される。
`crates/infer/src/module_table/mod.rs:417-438`:

```rust
self.nodes[sub.0].parent = Some(ModuleParent { module, order });
```

**決定:** 新しい hierarchy、path prefix 比較、band table は作らない。次の一つを
`ModuleTable` の共通 predicate とする。

```rust
fn is_descendant_or_same(
    &self,
    requester: ModuleId,
    declaring_module: ModuleId,
) -> bool {
    let mut current = Some(requester);
    while let Some(module) = current {
        if module == declaring_module {
            return true;
        }
        current = self.nodes[module.0].parent.map(|parent| parent.module);
    }
    false
}
```

lookup 中に lexical parent を歩く cursor と、最初の requester を混同してはならない。
全 query は requester を不変のまま持ち、target / declaring module だけを更新する。

### 1.2 companion に特別な規則は要らない

type companion は `ensure_child_module` で作られる
（`crates/infer/src/module_map/finish.rs:37-52`）。role companion も同じ入口である
（`crates/infer/src/module_map/mod.rs:1079-1094`）。act companion も同じ入口である
（`crates/infer/src/module_map/mod.rs:1196-1215`）。

`ensure_child_module` は `new_module` の後に通常の `insert_module` を呼ぶ
（`crates/infer/src/module_map/finish.rs:179-199`）。`insert_module` が parent chain を設定するため、
type / act / role companion はすべて ordinary child module である
（`crates/infer/src/module_table/mod.rs:417-438`）。

**決定:** companion kind、owner type、method family による ancestry shortcut は作らない。
companion 内の `my` も、普通の module 内 declaration と同じ predicate を使う。

### 1.3 direct lookup と import lookup は現在非対称である

値の direct qualified path は target module を求めた後、無条件の `value_at` を先に引く。
`crates/infer/src/module_table/mod.rs:675-690`:

```rust
let target = self.module_path_with_imports_from(module, prefix, site)?;
self.value_at(target, last, module_path_site())
    .or_else(|| self.exported_value_at(target, last))
```

`value_at`、`type_at`、`module_at` は共通の `select_decl` を使う
（`crates/infer/src/module_table/mod.rs:620-653`）。`select_decl` が見るのは source order だけで、
visibility と requester は見ない（`crates/infer/src/module_table/query.rs:904-923`）。
型の qualified path も同じ順序で `type_at` を先に引く
（`crates/infer/src/module_table/mod.rs:692-707`）。module prefix の降下も
`module_at` / `exported_module_at` を使い、`my` ancestry を判定しない
（`crates/infer/src/module_table/query.rs:425-440`）。

act operation lookup は、act type を `type_path_at` で解決し、companion の operation def を
無条件の `value_at` で引く（`crates/infer/src/module_table/mod.rs:709-741`）。
したがって act operation は独立した例外ではなく、type/value path の未統一を引き継いでいる。

一方、`use` 用 `select_decl_for_import` は `import_vis_allows` で先に filter する
（`crates/infer/src/module_table/query.rs:924-945`）。現行 `SameBand` は `Vis::My` を
requester に関係なく拒否する（`crates/infer/src/module_table/query.rs:986-1000`）。

```rust
ImportVisibility::SameBand => vis != Vis::My,
ImportVisibility::CrossBand => vis == Vis::Pub,
```

これは「direct path が緩すぎる」だけでなく、「同一 module / 子孫からの明示 `use` が
厳しすぎる」という両方向の不一致である。

### 1.4 `my mod` は存在する

`notes/bugs/2026-07-25-module-visibility-qualified-path-leak.md` は
「`my mod child:` は module declaration として解釈されない」と述べるが、この記述は誤りである。
parser は `My` の直後が `Mod` なら `parse_mod_decl` へ送る
（`crates/parser/src/stmt/mod.rs:159-180`）。

```rust
if vis_kw.kind == SyntaxKind::My {
    // ...
    if nud.lex.kind == SyntaxKind::Mod {
        return mod_decl::parse_mod_decl(i, Some(vis_kw), nud.lex);
    }
}
```

実測でも次は `run roots [43]` になった。

```yu
my mod child:
    pub visible = 43

child::visible
```

ここで requester は private module の declaring module と同じ root なので、D1 と整合する。

### 1.5 `lib/std/control/flow.yu` は D1 を満たす

private な `last` / `next` / `redo` act は `loop` companion の中で宣言され
（`lib/std/control/flow.yu:18-28`）、それらを使う `for_in` も同じ `loop` companion にある
（`lib/std/control/flow.yu:30-38`）。

同様に二組目は `label_loop` companion の中で宣言され
（`lib/std/control/flow.yu:45-61`）、`control_label` と `for_in` も同じ companion にある
（`lib/std/control/flow.yu:63-83`）。

companion-specific exception が無くても、どちらも `requester == declaring_module` で通る。

### 1.6 persistent compiled-unit format は現在 19 である

`COMPILED_UNIT_CACHE_FORMAT` は 19 である
（`crates/yulang/src/cache.rs:25-36`）。decoder は envelope 本体を deserialize する前に
先頭の format word を読み、不一致なら cache miss を返す
（`crates/yulang/src/cache.rs:519-537`）。

## 2. Q1: private method selection は今日漏れるか

### 2.1 実測結果

`target/debug/yulang --std-root lib --no-cache run --print-roots -e <source>` で、
type companion method を実際に実行した。

#### outside companion: private dot selection

```yu
mod child:
    pub struct point { x: int } with:
        my p.secret = 41

(child::point { x: 1 }).secret
```

結果:

```text
exit 1
runtime error [yulang.missing-field]: record does not contain field `secret`
```

private method は呼ばれていない。body lowering は unresolved selection を record field として
解決する fallback を実行するため（`crates/infer/src/lowering/body/mod.rs:899-903`）、
現状は private 専用 compile diagnostic ではなく runtime missing-field になる。

#### public control

```yu
mod child:
    pub struct point { x: int } with:
        pub p.visible = 42

(child::point { x: 1 }).visible
```

結果:

```text
exit 0
run roots [42]
```

#### same companion control

```yu
mod child:
    pub struct point { x: int } with:
        my p.secret = 41
        pub p.expose = p.secret

(child::point { x: 1 }).expose
```

結果:

```text
exit 0
run roots [41]
```

#### descendant module

```yu
mod child:
    pub struct point { x: int } with:
        my p.secret = 41
        pub mod nested:
            pub call p = p.secret

child::point::nested::call (child::point { x: 1 })
```

結果:

```text
exit 1
runtime error [yulang.missing-field]: record does not contain field `secret`
```

D1 では通るべき子孫が、現状は拒否される。

#### outside companion: private act method

effect receiverをhandlerで0へ戻し、selectionまで実行した。

```yu
act e:
    pub ping: () -> int
    my x.secret = 41

catch (e::ping()).secret:
    e::ping(), k -> k 0
```

結果:

```text
exit 1
runtime error [yulang.not-record]: tried to read fields from non-record value 0
```

`my` を `pub` に変えてmethod名を`visible`にしたcontrolは次になった。

```text
exit 0
run roots [42]
```

private act methodは呼ばれず、handler後の値へのrecord-field fallbackになった。

#### outside companion: private role method

```yu
role R 'a:
    my a.secret: int

impl int: R:
    our x.secret = 41

1.secret
```

結果:

```text
exit 1
runtime error [yulang.not-record]: tried to read fields from non-record value 1
```

role methodを`pub a.visible`、implを`our x.visible = 42`にしたcontrolは次になった。

```text
exit 0
run roots [42]
```

private role methodもoutside companionからは選ばれていない。

#### qualified value spelling

```yu
mod child:
    pub struct point { x: int } with:
        my p.secret = 41

child::point::secret (child::point { x: 1 })
```

結果:

```text
exit 0
run roots [41]
```

dot method selector 自体は外へ漏らさないが、同じ method body を qualified value path で
綴ると、1.3 の value-path leak により到達できる。

### 2.2 静的説明と method slice の正確な範囲

global type / act / role method registration は `Vis::My` を skip する
（`crates/infer/src/lowering/body/register.rs:5-30`,
`crates/infer/src/lowering/body/register.rs:81-99`,
`crates/infer/src/lowering/body/register.rs:172-190`）。

private method を含む companion-local table は companion `ModuleId` を key にする
（`crates/infer/src/lowering/body/register.rs:102-169`）。selection は
`local_method_scope` と同じ key の candidates だけを先に見る
（`crates/infer/src/analysis/session/selection.rs:828-910`）。
`CompanionMethodTable` 自身も exact `ModuleId` lookup であり、ancestor walk をしない
（`crates/infer/src/methods.rs:206-210`, `crates/infer/src/methods.rs:270-320`）。

**結論:** type / act / role のprivate dot method selectionは、実プログラム上いずれも
今日outside companionへ漏れない。
method slice を「漏洩を閉じる medium slice」として扱う案は棄却する。

ただし method work を完全に外すこともできない。残る範囲は次の三点に限定する。

1. selection use-site に実際の requester `ModuleId` を保持する。
2. private method candidate に declaring companion を保持し、同じ ancestry predicate で
   same / descendant を許可して outside を拒否する。
3. outside の hidden candidate を record fieldへ黙って落とさず、§5 の
   `yulang.private-access` を出す。

qualified value spellingは method selector ではなく、共通 value-path slice で閉じる。

## 3. 共通 visibility decision

### 3.1 一つの predicate を direct path と `use` の両方に使う

visibility decision の入力を次に固定する。

```rust
visibility_allows(
    requester: ModuleId,
    declaring_module: ModuleId,
    vis: Vis,
    route: VisibilityRoute,
) -> bool
```

意味は次の通りである。

```rust
match vis {
    Vis::My => modules.is_descendant_or_same(requester, declaring_module),
    Vis::Our => route.is_same_band(),
    Vis::Pub => true,
}
```

`VisibilityRoute` は現行 `SameBand` / `CrossBand` の `our` / `pub` 判定を保持するための情報である。
`my` の判定には route spelling を使わない。同じ requester と declaration なら
direct path、relative `use`、`band::`、将来の別 spelling で結果を変えてはならない。

### 3.2 lookup は `Option` ではなく denial を失わない

現行 query は `Option<T>` を返すため、missing と private denial を区別できない。
visibility filter 後に再走査して hidden candidate を探す案は、名前解決の hot path を
二度歩くため棄却する。

**決定:** declaration selection は一回の走査で次を返す。

```rust
enum Lookup<T> {
    Found(T),
    Private(PrivateAccess),
    Missing,
}

struct PrivateAccess {
    kind: NamespaceKind,
    name: Name,
    origin: PrivateOriginId,
}
```

visible candidate があれば `Found` を優先し、visible candidate が無いが source-order 上の
candidate が private なら `Private`、候補自体が無ければ `Missing` とする。
これにより既存 unresolved diagnostics と private diagnostics を混同せず、再走査もしない。

### 3.3 enforcement point

| namespace / spelling | 共通 decision を置く場所 | 現行入口 |
|---|---|---|
| unqualified value | lexical cursor ごとの declaration / import entry selection | `lexical_value_at` (`crates/infer/src/module_table/mod.rs:657-673`) |
| qualified value | prefix の各 module stepと terminal value | `value_path_at` (`crates/infer/src/module_table/mod.rs:675-690`) |
| unqualified / qualified type | prefix の各 module stepと terminal type | `lexical_type_at`, `type_path_at` (`crates/infer/src/module_table/mod.rs:692-707`, `crates/infer/src/module_table/mod.rs:765-781`) |
| module prefix | first lexical step、以後の各 child / imported child | `module_path_with_imports_from` (`crates/infer/src/module_table/query.rs:425-459`) |
| act operation | act type path と companion operation value の両方 | `act_operation_decls_at` (`crates/infer/src/module_table/mod.rs:709-741`) |
| `use` alias / glob / re-export | path の各 step、terminal、glob collection、upstream imported entry | `import_alias` と import helpers (`crates/infer/src/module_table/query.rs:57-237`, `crates/infer/src/module_table/query.rs:370-575`) |
| type / act / role dot method | candidate eligibility | method selection (`crates/infer/src/analysis/session/selection.rs:828-910`) |

`value_at` / `type_at` / `module_at` の caller が requester を省略できる API は残さない。
signature、pattern、constructor、builtin helper なども同じ query API を呼ぶため、
「expression path だけを直す」実装は stop condition を満たさない。

## 4. private provenance

### 4.1 何を保持するか

`my` の意味論に必要なのは、現在の alias visibility ではなく、最も狭い private origin である。
fixed-point の各 copy で `SourceSpan` と module path を clone しないよう、entry は interned id だけを持つ。

```rust
struct PrivateOriginId(u32);

struct PrivateOrigin {
    scope: ModuleId,
    declaration_span: Option<SourceSpan>,
}
```

- `scope`: `my` declaration または `my use` を置いた module。
- `declaration_span`: user-authored origin の名前 segment。§5 の related location に使う。
  compiler-generated で source が無い場合だけ `None` を許す。

`ModuleTable` は `PrivateOriginId -> PrivateOrigin` の intern table を一つ持つ。
direct `ModuleDecl` と `AliasDecl`、runtime の `ImportedValueDecl`、`ImportedTypeDecl`、
`ImportedModuleDecl` はそれぞれ `private_origin: Option<PrivateOriginId>` を持つ。
現行 `ModuleDecl` は name / vis / order / kind だけである
（`crates/infer/src/lib.rs:208-214`）。source registration時にname spanを渡し、
`Vis::My` のときだけoriginをinternする。
現行 imported 三 struct は alias 自身の `vis` しか
保持しない（`crates/infer/src/lib.rs:575-596`）。

origin の合成規則を次に固定する。

1. direct `Vis::My` declaration を import target にするときは
   `PrivateOrigin { scope: declaring_module, declaration_span }` を一度 intern する。
2. upstream import entry に `private_origin` があれば、そのまま運ぶ。
3. 今回の alias 自身が `my use` なら、upstream origin を
   alias registration 時に intern 済みの origin id で置き換える。
4. alias が `our` / `pub` なら upstream origin を変えない。

既存 private origin を読める alias module は、その origin scope の same / descendant に限られる。
したがって新しい `my use` scope は必ず既存 scope の子孫であり、二つの incomparable な
private scope の intersection を表す集合は要らない。最も新しい一個で十分である。

### 4.2 target からの再構成では足りない

次を考える。

```yu
mod public_source:
    pub value = 1

mod owner:
    my use public_source::value as local
    pub mod nested:
        pub use local
```

`local` の target def は public である。しかし `local` 自身は `owner` に宣言された
private alias なので、`owner` 外へ出してはならない。target declaration の `Vis` と
declaring module を逆引きするだけでは、この origin を再構成できない。

compiled namespace に raw alias も保存されている
（`CompiledNamespaceModule.aliases`, `crates/infer/src/compiled_namespace.rs:16-29`;
`CompiledNamespaceAlias`, `crates/infer/src/compiled_namespace.rs:104-109`）。しかし復元は raw alias を再実行せず、
materialized `imported_values` / `imported_types` / `imported_modules` を直接
`ModuleTable` にコピーする（`crates/infer/src/module_table/compiled.rs:186-236`）。

**判断:** cache hit 時だけ raw alias fixed point を再実行して origin を復元する案は棄却する。
それは現在 materialized import view を canonical surface としている cache semantics を変え、
merged prefix の order / route resolution をもう一度名前解決することになる。
provenance を materialized entry と一緒に serialize する方が局所的である。

### 4.3 runtime copy site の完全な一覧

現行 runtime import entry の constructor は次だけである。

| copy | value | type | module |
|---|---:|---:|---:|
| named alias | `crates/infer/src/module_table/query.rs:72-76` | `crates/infer/src/module_table/query.rs:83-87` | `crates/infer/src/module_table/query.rs:94-98` |
| glob: direct declaration | `crates/infer/src/module_table/query.rs:117-121` | `crates/infer/src/module_table/query.rs:128-132` | `crates/infer/src/module_table/query.rs:144-148` |
| glob: re-exported entry | `crates/infer/src/module_table/query.rs:172-176` | `crates/infer/src/module_table/query.rs:197-201` | `crates/infer/src/module_table/query.rs:227-231` |
| operator alias | `crates/infer/src/module_table/query.rs:303-307` | — | — |

すべて `crates/infer/src/module_table/query.rs` の行番号である。
特に re-export copy は現在 `def` / `decl` / `module` だけを一時 vector へ抜き、
upstream entry の情報を落とす（`crates/infer/src/module_table/query.rs:155-234`）。実装時は一時 vector に entry 全体、
少なくとも target と `private_origin` の組を clone する。

named alias と operator alias が受け取る `ImportPathTarget` も、現在は raw
`DefId` / `ModuleTypeDecl` / `ModuleId` しか持たない
（`crates/infer/src/lib.rs:598-603`）。ここを namespace ごとの resolved import target とし、
origin を terminal lookup から constructor まで運ぶ。

fixed-point の重複除去は entry 全体の `PartialEq` を使う
（`crates/infer/src/module_table/query.rs:238-271`）。`private_origin` も equality に含め、
同じ target でも origin が異なる entry を誤って同一視しない。

### 4.4 compiled copy site の完全な一覧

runtime entry から compiled surface までの copy は次の一経路である。

1. public summary:
   `module_imported_value_decls` / `module_imported_type_decls` /
   `module_imported_module_decls`
   （`crates/infer/src/module_table/query.rs:754-795`）。
2. serialized entry:
   `module_imported_value_entries` / `module_imported_type_entries` /
   `module_imported_module_entries`
   （`crates/infer/src/compiled_namespace.rs:765-837`）。
3. prefix merge:
   `merge_imported_values` / `merge_imported_types` / `merge_imported_modules`
   （`crates/infer/src/compiled_namespace.rs:374-429`）。
4. `ModuleTable` restore:
   imported value / type / module の三 loop
   （`crates/infer/src/module_table/compiled.rs:186-236`）。

`ModuleImportedValueDecl` / `ModuleImportedTypeDecl` / `ModuleImportedModuleDecl` には
opaque な `PrivateOriginId` を追加し、`NamespaceSurfaceBuilder` が
`ModuleTable::private_origin(id)` で `CompiledPrivateOrigin` へ展開する。
現行 public summary 三種も name / alias vis / order / target しか持たない
（`crates/infer/src/lib.rs:505-530`）。

compiled entry は現在 alias visibility と target symbol/module しか持たない
（`crates/infer/src/compiled_namespace.rs:76-102`）。三 entry に
`private_origin: Option<CompiledPrivateOrigin>` を追加する。

```rust
struct CompiledPrivateOrigin {
    scope_module: u32,
    declaration_span: Option<SourceSpan>,
}
```

`scope_module` は `CompiledNamespaceModule.id` と同じ namespace-local id とする。
prefix merge は target symbol/module と同時に
`module_remap[(prefix, origin.scope_module)]` で remap する。
namespace stable hash も三 imported entry の origin module と span を含める。
現行 hash は name / target / alias visibility / order までしか含めない
（`crates/yulang/src/cache.rs:1998-2023`）。

direct private access の related span も cache hit で失わないよう、
`CompiledNamespaceModuleValue`、`CompiledNamespaceModuleType`、
`CompiledNamespaceModuleChild` にそれぞれ `declaration_span: Option<SourceSpan>` を追加する。
現行三 entry は span を持たない（`crates/infer/src/compiled_namespace.rs:47-74`）うえ、
compiled value restore は明示的に `None` を `insert_value_with_span` へ渡している
（`crates/infer/src/module_table/compiled.rs:141-151`）。
type / module restore も span 引数を持たない
（`crates/infer/src/module_table/compiled.rs:157-183`）。
source-time builder、prefix merge、restore、stable hash の全てでこの三 span を運ぶ。
imported entry の `CompiledPrivateOrigin.declaration_span` は、target が public でも private になる
`my use` origin のために別途必要であり、direct declaration spanの逆引きで代用しない。

compiled lowering / typed / runtime surface は provenance を持たなくてよい。
suffix の名前解決用 `ModuleTable` を復元する入口は namespace + lowering である
（`crates/infer/src/module_table/compiled.rs:11-22`）。名前解決が target id を確定した後、
private origin は poly ref / select、typed arena、runtime artifact へ伝播させず捨ててよい。
raw `AliasDecl` も materialized import entry を作り終えた後は upstream origin を保持しなくてよい。
`CompiledNamespaceAlias` の layout は変えず、cacheでは materialized entryを正本とする。

### 4.5 completeness の確認方法

実装時の audit command を固定する。

```console
rg -n \
  'ImportedValueDecl \{|ImportedTypeDecl \{|ImportedModuleDecl \{|ModuleImportedValueDecl \{|ModuleImportedTypeDecl \{|ModuleImportedModuleDecl \{|CompiledNamespaceImportedValue \{|CompiledNamespaceImportedType \{|CompiledNamespaceImportedModule \{' \
  crates/infer/src crates/yulang/src
```

2026-07-27 の結果は、struct definition を除くと §4.3 の十 constructor、
public summary 三 constructor、serialized 三 constructor、restore 三 constructorだけだった。
merge は clone-and-push のため struct literal 検索には出ないので、
`merge_imported_(values|types|modules)` を別に確認した
（`crates/infer/src/compiled_namespace.rs:374-429`）。

stop condition ではこの検索結果を review checklist とし、新しい constructor が増えていたら
provenance copy または「ここで安全に drop できる理由」のどちらかを必須にする。

## 5. diagnostic contract

### 5.1 共通 code と message

全 namespace で code を **`yulang.private-access`** に統一する。
同じ D1 violation を spelling ごとに別 code にする案は、tooling が同じ修正可能性を
別問題として扱うため棄却する。

共通 hint:

```text
move this access into `<scope>` or one of its nested modules, or widen the declaration's visibility
```

related information の `origin` は `None` とする。現行 enum は
`TypeAnnotation` / `Expression` / `ImplCandidate` だけで
（`crates/yulang/src/source/mod.rs:1765-1770`）、private declaration を既存三種へ
誤分類しない。message 自体で declaration kind を示す。

| namespace | message shape | primary span | related message / span |
|---|---|---|---|
| value | `value \`<name>\` is private to module \`<scope>\`` | 拒否を決めた name segment | `private value declared here` / 元の `my` name、private aliasならその `use` segment |
| type | `type \`<name>\` is private to module \`<scope>\`` | terminal type name、prefixで止まればその module segment | `private type declared here` / type declaration name または private alias |
| module prefix | `module \`<name>\` is private to module \`<scope>\`` | path を最初に拒否した module segment | `private module declared here` / `my mod` name または private alias |
| act operation | `act operation \`<name>\` is private to module \`<scope>\`` | operation name segment | `private act operation declared here` / operation declaration name |
| method | `method \`<name>\` is private to module \`<scope>\`` | dot の method name。`.` は含めない | `private method declared here` / companion method declaration name |
| `use` segment | `cannot import private <kind> \`<name>\` from outside module \`<scope>\`` | `use` path を最初に拒否した segment | 上記 kind ごとの message / private declaration または private alias segment |

`use` は alias が後で未使用でも、その statement 自体に diagnostic を出す。import を黙って
drop し、後続の利用だけを `yulang.unresolved-value` にする現行形は採用しない。

### 5.2 現在ある span と追加量

追加量の表記は、小 = infer 内の一 table / field と formatter 程度、
中 = CST/sources と複数 resolver または cache surface をまたぐ変更、とする。

#### value

unqualified value use は `lower_name_at` が token range を受け、`UnresolvedName` に保持する
（`crates/infer/src/lowering/name_ref.rs:45-68`）。ordinary source value の declaration span は
`insert_value_with_span` が `DefId` table に保存する
（`crates/infer/src/module_table/mod.rs:90-107`, `crates/infer/src/module_table/mod.rs:152-162`）。

qualified expression path は現在 path 全体の range 一個だけを渡す
（`crates/infer/src/lowering/expr/chain.rs:104-109`）。

追加:

- terminal / prefix segment range を `expr_path_prefix` から運ぶ: **小**。
- private origin を `LoweringError` / `BodyLoweringError` へ運ぶ: **小**。
- compiled prefix の origin span serialization: §4.4 の **中** に含める。

#### type

unresolved type は terminal `Name` を CST 内で探して primary range にする
（`crates/infer/src/lowering/error.rs:126-133`）。しかし type insertion は
`TypeDeclId`、name、kind、vis だけで source span を受けない
（`crates/infer/src/module_table/mod.rs:109-123`）。
annotation prefix resolution も `Vec<Name>` だけを使う
（`crates/infer/src/annotation/builder.rs:344-390`）。

追加:

- type registrationから`ModuleDecl` private originへname spanを渡し、direct compiled entryにも
  serializeする: **中**。
- annotation / negative signature path の segment range と structured private error: **中**。

#### module prefix

module insertion は name / child / def / vis を受けるが source span を保存しない
（`crates/infer/src/module_table/mod.rs:417-438`）。expression、annotation、signature の
prefix resolver はいずれも `Name` 列だけで降下する
（`crates/infer/src/lowering/expr_syntax.rs:49-80`,
`crates/infer/src/annotation/builder.rs:384-390`,
`crates/infer/src/lowering/neg_signature.rs:320-329`）。

追加:

- module registrationから`ModuleDecl` private originへname spanを渡し、direct compiled entryにも
  serializeする: **中**。
- 共通 range-aware path segment representation: **中**。value/type/act と共有し、別々に作らない。

#### act operation

direct act companion operation は `source_range_for_name` を
`insert_value_with_span` へ渡す（`crates/infer/src/module_map/mod.rs:1235-1261`）。
copied act body は `ActCompanionBlockMode` により source span を記録しない場合がある
（`crates/infer/src/module_map/mod.rs:1363-1372`）。

追加:

- operation path segment range: module-prefix workと共有するため **小**。
- copied act が original operation origin span を保持する bridge: **中**。

#### method

dot selection は `DotField` token から `.` を除いた exact range を既に作る
（`crates/infer/src/lowering/expr/tail.rs:1109-1118`）。その span は
`SelectId` ごとに保存される（`crates/infer/src/lowering/expr/tail.rs:315-332`;
`crates/infer/src/uses.rs:146-175`）。source companion method の declaration span も
value def span として保存される
（type method: `crates/infer/src/module_map/finish.rs:68-98`;
act method: `crates/infer/src/module_map/mod.rs:1263-1297`;
role method: `crates/infer/src/module_map/mod.rs:1109-1132`）。

追加:

- selection requester と private candidate origin: **中**。
- primary range は追加不要。compiled origin span は §4.4 に含める。

#### `use`

`UseImport` は name/path/route/version/anchor だけを持ち、range を持たない
（`crates/sources/src/lib.rs:65-88`）。collector も token text だけを受けて
`Name` を作る（`crates/sources/src/lib.rs:518-565`）。`AliasDecl` も import/vis/order だけである
（`crates/infer/src/lib.rs:564-573`）。`add_alias` は source span を受けず、
`build_import_views` は diagnostic を返さない
（`crates/infer/src/module_table/mod.rs:584-608`）。

追加:

- collectorに`SpannedUseImport { import, segment_ranges, alias_range, glob_range }`を返す
  source-only APIを追加する: **中**。header/cache用の既存`UseImport` serialized layoutへ
  source rangeを混ぜず、現行`use_imports`はspanned結果からraw importだけをprojectする。
- `AliasDecl` の source file + segment spans と module-map namespace diagnostic lane: **中**。
- private `use` origin の related span は同じデータから作るため追加 clone scan はしない。

### 5.3 diagnostic を出す stage

direct value/type/module/operation denial は resolver の `Lookup::Private` を structured lowering error にし、
既存 `SourceDiagnostic` surfaceへ変換する。現行 lowering diagnostic は code、primary range、
message、hint、related を一箇所で組み立てる
（`crates/yulang/src/source/mod.rs:4179-4207`）。

method denial は selection resolution が private candidate を確定した時点で structured
analysis diagnostic にする。後段の `yulang.unresolved-method` と record-field fallbackに
任せない。

`use` denial は import-view fixed point の中で source alias に紐づけた namespace diagnostic として
一度だけ記録する。fixed point の各周回で同じ diagnostic を push しない。
entry dedup と同じ identity を使って diagnostic key を dedup する。

## 6. Q3: cache-format bump

**結論:** bump は避けられない。`COMPILED_UNIT_CACHE_FORMAT` を 19 から 20 へ上げる。

理由は次の二点である。

1. `my use` の private origin は public target から再構成できない（§4.2）。
2. compiled restoration は materialized import entries を直接コピーするため、
   source-time alias chain は復元時に存在しない
   （`crates/infer/src/module_table/compiled.rs:186-236`）。

三 `CompiledNamespaceImported*` の serialized layout と namespace stable hash が変わるため、
schema saltだけを変えて bincode layoutを据え置くこともできない。

ユーザへのコストは既存 v19 compiled-unit artifact が一度 cache miss になり、source から
cold rebuild されることだけである。format mismatch は decode error ではなく `Ok(None)` になる
（`crates/yulang/src/cache.rs:519-537`）。source syntax、公開 artifact、runtime data の
互換性を変えるものではない。古い cache file の自動削除は本 slice の要件にしない。

## 7. Q5: descendant からの `use`

**結論:** descendant から ancestor の `my` declaration を `use` できなければならない。
`import_vis_allows` の `SameBand => vis != Vis::My` は廃止し、§3.1 の共通 predicateへ置き換える。

実測では次の alias は same module、descendant のどちらでも現在 unresolved になる。

```yu
mod outer:
    my hidden = 41
    pub mod inner:
        use hidden as local
        pub expose = local
```

結果:

```text
compile error [yulang.lowering]: source has lowering errors
  detail: unresolved value name: local
```

alias を使わず descendant が `hidden` を lexical lookup すると現在も `41` を返す。
現行 `lexical_value_at` は parent chain を歩く
（`crates/infer/src/module_table/mod.rs:657-673`）ためである。
同じ requester / declaration が `use` を選んだだけで拒否されるのは D1 に反する。

`use` だけを direct path より厳しく保つ案は棄却する。D1 は「declaring module と
その子孫から見える」と access form を限定していない。一方、widening だけを先に入れると
descendant の `pub use` が private item を外へ出すため、§4 の provenance と同じ slice、
または provenance 完了後にだけ有効化する。

## 8. corpus impact

read-only static scan の対象は `lib/`, `examples/`, `tests/` とした。

```console
rg -n '^\s*my\s+(mod|type|struct|enum|error|role|act)\b' \
  --glob '*.yu' lib examples tests
```

nominal/module declarationとして該当したのは
`lib/std/control/flow.yu:23,27,28,56,60,61` の六件だけで、§1.5 のとおり requester は
同じ companion である。

top-level private valueについては、各 `lib/**/*.yu` の module path と declaration nameから
`std::...::<name>` を作り、`lib/`, `examples/`, `tests/` 全体を fixed-string searchした。
outside module からの fully-qualified reference は 0 件だった。explicit nested source module は
`lib/std.yu:1-12`, `lib/std/core.yu:1-5`, `lib/std/data.yu:1-6`,
`lib/std/control.yu:1-5`, `lib/std/io.yu:1-3`, `lib/std/text.yu:1-7`,
`lib/std/num.yu:1` の public file modulesが中心で、private child module declarationへの
依存は見つからなかった。

**測定結果:** D1 を全 direct lookup に適用して新しく拒否される corpus site は 0 件と予測する。
これは静的測定であり、実装 slice の完了条件では cold / cached の全既存 testを実行して
0 regressionを確認する。

別 workstream が同じ repository を共有するため、実装直前に同じ scan を再実行し、
新しい private declaration / qualified reference が増えていないかを見る。

## 9. implementation slicing plan

各 slice は単独 commit可能にし、stop conditionを満たすまで次へ進まない。
最も危険な silent re-export と cache parityを先に閉じ、可視性の有効化はその後に行う。

### MYVIS-A: runtime private provenance

`PrivateOrigin`、range-aware import target、runtime imported entry三種を追加し、
§4.3 の全 constructorで originを生成・copyする。まだ `SameBand` の `my` rejection と
direct-path behaviorは変えない。

Stop condition: value/type/moduleそれぞれで named alias、direct glob、glob re-export、
`my use public_target` を通した後の origin scope/spanが一致し、operator alias valueも
同じ contractを満たす。§4.5 の constructor auditに未説明のsiteが0件である。

### MYVIS-B: compiled provenance と format 20

public summary、`CompiledNamespaceImported*`、namespace merge、restore、stable hashへ
originを通し、compiled-unit formatを20へ上げる。

Stop condition: value/type/moduleのprivate alias→public re-export chainがserialize round-tripと
merged-prefix round-trip後も同じoriginを持ち、v19 fixtureがdecode errorではなくcache missになり、
cold/prefix checkが同じlookup resultを返す。

### MYVIS-C: common predicate と direct namespace lookup

`is_descendant_or_same`、一回走査の`Lookup`、requester-threaded value/type/module queryを導入し、
expression、annotation、signature、pattern、constructorのdirect pathを有効化する。
declaration span tableとrange-aware path segmentsもこのsliceで接続する。

Stop condition: value/type/module各namespaceでsame、child、grandchildが通り、parentからchild、
sibling、unrelatedがdirect/qualifiedの両方で`yulang.private-access`になる。
private moduleがprefix途中にあるcaseも、terminal unresolvedではなく最初のprivate segmentを指す。

### MYVIS-D: `use` widening と re-export closure

`use` segment spans、namespace diagnostic laneを追加し、`SameBand`一律拒否を共通 predicateへ
置き換える。MYVIS-A/Bのoriginをalias/glob/fixed pointのeligibilityに使う。

Stop condition: same/child/grandchildからのnamed aliasとglobが通り、siblingは拒否される。
descendantの`pub use`をunrelated moduleからnamed/glob/二段re-exportで引く全caseが拒否され、
cold/cachedでcode、primary、relatedが一致する。

### MYVIS-E: act operation と method parity

act operation terminalを共通queryへ乗せる。type/act/role method candidateへrequesterと
private originを接続し、exact companion限定のlocal lookupをancestry predicateへ置き換える。
qualified method-body value spellingはMYVIS-Cで既に閉じていることを確認する。

Stop condition: private type/act/role methodとact operationのsame/child/grandchildが通り、
sibling/unrelatedは`yulang.private-access`になる。§2.1のoutside dot programは
runtime missing-fieldではなくmethod primary/related付きcompile diagnosticになり、
public controlとsame-companion controlの出力は42/41を保つ。

### MYVIS-F: diagnostic matrix と corpus gate

§5の六namespaceについてCLI check、source diagnostics、LSP related information、
cold/prefix cache parityをgolden/contract testで固定し、§8のscanと既存suiteを実行する。

Stop condition: 六namespaceすべてがexact code/message/primary/relatedを満たし、
`lib/`, `examples/`, `tests/`の新規failureが0件である。static scanで新規candidateが出た場合は
期待値を書き換えず、D1違反か測定false positiveかを分類する。

## 10. 判断と棄却した代案

| 判断 | 採用 | 棄却した代案 |
|---|---|---|
| `my` semantics | requesterがdeclaring moduleのsame/descendant | access form別の例外、file/bandだけの判定 |
| hierarchy | 既存`ModuleNode.parent` walk | 新しいmodule tree、path文字列prefix |
| direct / `use` | 一つのpredicate | `use`だけ`my`を常時拒否 |
| lookup result | 一回走査の`Found/Private/Missing` | miss後のhidden candidate再走査、unresolvedへcollapse |
| import provenance | 最も狭い`PrivateOrigin`一個 | alias visibilityだけ、target declarationから再構成、scope集合 |
| compiled provenance | materialized imported entryへserialize | cache hit時だけraw aliasを再解決 |
| cache | format 20へbump | layout変更をsaltだけで隠す |
| method | outside leak fixは不要、descendant parityとdiagnosticに限定 | method workを全削除、またはglobal private candidateを無条件公開 |
| diagnostic code | 全namespaceで`yulang.private-access` | value/type/methodごとの別code、既存unresolved codeの流用 |
| related origin | `None` +明示message |既存`Expression`/`TypeAnnotation`/`ImplCandidate`への誤分類 |

## 11. 決めていないこと

依頼されたD1、Q1〜Q5、enforcement point、provenance、cache bump、diagnostic contractには、
実装を止める未解決点を残していない。

次は意図的に本設計の外へ置き、この文書では決めない。

- `our` の将来のband境界 semantics。現行 `SameBand` / `CrossBand` contractを維持する。
- visibility modifier自体の新しいsyntax、friend module、package-private相当の追加。
- unused private import warning。
- private denial以外の一般的な unresolved value/type/method diagnosticの文言変更。
- v19 cache fileの自動削除policy。format mismatchは安全なmissなので、別のcache maintenance課題とする。

著者: Claude (Opus 5)
ユーザ承認: 済（2026-07-27）
