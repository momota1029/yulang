# Realm / Band Pro Review

Date: 2026-06-26

This note stores external review feedback for the realm / band source identity
design. It is a working note, not the source of truth. Accepted decisions should
be copied into `notes/design/source-realm-band-plan.md` or a future `spec/`
document.

## Prompt Context

Yulang の realm/band 仕様を詰めたい。

前提:
- realm は versioned source universe。
- 編集中 realm がトップにあり、release snapshot は realm@v として解決される。
- band は realm 内の import/build boundary。
- band root は、同じ realm 内でどの親 source からも mod edge で到達されない source root。
- mod は同じ band の module tree を伸ばす。
- use realm@v/path/to/band::module::item は別 band への依存。
- band 間依存は DAG。相互参照・cycle は禁止。
- compiled artifact cache key は resolved realm identity, version/source hash, band path, source SCC, dependency interface hash を含む。
- std のような single-band realm は表面上 std::... と書けるが、内部 canonical identity は std@v/std::... にする案。

相談したいこと:
1. band root を「mod edge で到達されない source root」と定義することで、曖昧さや悪い edge case はあるか。
2. same-realm shorthand `path/to/band::module` と local module / companion module の名前衝突をどう解決すべきか。
3. physical snapshot を `@v/` に置く案と `.yulang/versions/v/` に置く案の tradeoff。
4. single-band realm の canonical identity を `realm@v/realm::...` にするのは妥当か。
5. cache key / lockfile / diagnostics 上、今の realm/band split に抜けがあるか。

## Pro Response

かなり筋がいいよ〜。私なら realm / band split 自体は維持して、次の3つを仕様上はっきり分けるねぇ。

```text
G_mod     : source containment graph
            mod が作る。各 connected component は rooted tree

G_source  : source semanti 存。SCC を許す

G_band    : cross-band dependency graph
            use / reexport が作る。DAG を強制
```

今のメモも「mod が module tree を伸ばす」「compiled unit は source dependency SCC」という区別を暗黙には持ってる。ここを名前付きの別 graph として固定すると、かなりの曖昧さが消えると思うよ〜。

## 結論だけ先に

1. **band root = mod indegree 0** は方向として正しい。ただし `G_mod` が単なる graph でなく **rooted forest** であることまで要求した方がいい。
2. bare な `foo::bar` に local と band の fallback lookup を混ぜない方がいい。same-realm band は **専用の字句的マーカー**を持たせたい。私は `/foo::bar` を推す。
3. snapshot は **`.yulang/versions/<version>/` を維持**。`@v` は user cache / registry protocol の物理 layout に使う方が相性がいい。
4. `std@v/std::...` は妥当。むしろ explicit band segment を常に残す方が将来壊れにくい。
5. 大きな抜けは **band index、完全な resolved realm key、interface hash の層分け、portable lock、三種類の graph の区別**あたりだねぇ。

---

# 1. band root を「mod edge で到達されない source root」とする件

## 判定

**indegree 0 だけでは少し弱い**ねぇ。次の不変条件を加えて、`G_mod` を rooted forest にするときれいに閉じる。

```text
For each resolved realm snapshot R:

G_mod(R) = (SourceId, resolved mod edges)

- G_mod is acyclic.
- Each source has at most one incoming mod edge.
- Each weakly connected component has exactly one zero-indegree source.
- That zero-indegree source is the band root.
- The component reachable from that root is the band's module tree.
```

つまり、単に

```text
band root := indegree_mod(source) == 0
```

ではなく、

```text
each G_mod component must be an arborescence
```

まで言うのが大事だねぇ。

現行メモでは `mod child` の候補を隣の `child.yu` または `current_file_stem/child.yu` に限定し、未到達ファイルを band root としている。ここには「両方存在した場合」「同じファイルを二つの親が参照した場合」の規則がまだ足りない。

## 明示的に reject したい edge case

### 複数親

```text
a.yu --mod shared--> shared.yu
b.yu --mod shared--> shared.yu
```

これは module tree の merge として扱わず、**same source claimed by multiple module parents** でエラーにした方がいい。

そうしないと `shared.yu` の canonical module path が

```text
a::shared
b::shared
```

のどちらなのか決められなくなる。

現行 collector も、一つの物理ファイルが異なる module path に割り当てられる場合や、一つの module path に異なるファイルが割り当てられる場合を reject する形になっている。

### mod cycle

```text
a.yu --mod b--> a/b.yu
a/b.yu --mod a--> a.yu
```

indegree だけ見ると root が消える。reachable component の SCC を band にするのではなく、**structural module cycle** として即エラーがいい。

source semantic dependency の cycle は `G_source` の SCC にできるけど、module containment の cycle は別物だねぇ。

### 二つの physical candidate

```text
foo.yu
foo/bar.yu

# foo.yu
mod bar
```

さらに同じ場所に

```text
bar.yu
```

もある場合、候補が

```text
bar.yu
foo/bar.yu
```

の二つになる。

ここは precedence を決めるより、**ambiguous mod target** としてエラーにする方が安全。ファイルを追加しただけで既存の module identity が静かに変わるのは避けたい。

### band として import された後に mod-owned と判明する場合

```text
use /foo/bar::x

# foo.yu
mod bar
```

`foo/bar.yu` を最初は band root として読み、後から `foo` band の child だと分かる、という discovery order 依存を作らない方がいい。

realm の source index を作る段階で、

```text
BandPath -> root SourceId
SourceId -> owning BandId + ModulePath
```

を確定してから、ordinary `use` を解決する形が堅い。

`foo/bar.yu` が `foo` の child なら、`/foo/bar::x` は

```text
`foo/bar` is not a band root;
it belongs to band `/foo` as module `bar`
help: use `/foo::bar::x`
```

のように落とせる。

### 孤立した `.yu` を全部 band にするか

これは仕様として選択が必要だねぇ。

```text
scratch.yu
tests/helper.yu
examples/old.yu
```

まで「mod されていないから band」とするなら、**realm 内の全 `.yu` は、mod-owned でない限り importable band** になる。

これは manifestless で分かりやすい反面、内部ファイルを置くだけで public な band address が生える。

私なら次のどちらかを明記する。

* シンプル案: realm source index に入る全 `.yu` は band candidate
* 制御案: `realm.toml` の include/exclude、または source root 規則に入るものだけ band candidate

現行 freeze は `.yulang` と `target` を除いた `.yu` を再帰収集しているので、今の延長なら前者に近い。

### symlink / case collision

snapshot 内の logical path を identity にして、

```text
Foo.yu
foo.yu
```

や、同じ target を指す symlink は freeze 時に reject したい。OS ごとに別の realm graph が生えるのを防げる。

### conditional mod

`mod` が feature、型推論、operator import、macro expansionで増減すると、band ownership 自体が build configuration 依存になる。

なので structural `mod` は、

* baseline grammar だけで preparse 可能
* feature に依存しない
* operator table に依存しない

としておくのが良いと思う。

## 用語上の小さな修正

「source root」がまだ別に定義されていないなら、少し循環的に聞こえる。

私はこう書くかなぁ。

> A band root is an externally addressable source entry that has no incoming resolved `mod` edge. The resolved `mod` graph of a realm must be a forest; each tree defines exactly one band.

snapshot には derived metadata として、

```text
BandIndex {
    band_path,
    root_source_path,
    module_tree_hash,
}
```

を持たせると、resolver が毎回 realm 全体を手探りしなくて済む。

---

# 2. same-realm shorthand と local / companion collision

## fallback lookup は避けたい

例えば、

```yulang
use ui::widget
```

について、

1. local module `ui` を探す
2. companion module `ui` を探す
3. なければ same-realm band `ui` を探す

のような lookup は危ない。

後から

```yulang
struct ui ...
```

を一つ追加しただけで import target が別物になるからねぇ。

companion module は declaration と同名で生成されるので、普通の module head と衝突しやすい。現行 reference でも `struct`、`type ... with:`、`enum`、`act`、`error`、`role` が同名 companion module を作る形になっている。

## 私なら `/` を current-realm qualifier にする

```yulang
foo::bar
```

は常に current-band namespace。

```yulang
use /foo::bar
use /path/to/foo::bar
```

は current realm の別 band。

```yulang
use user/ui@1.2.0/widget::button
```

は resolved cross-realm band。

つまり canonical form の

```text
realm@version/band::module
```

から realm 部分だけ省略した形として、

```text
/band::module
```

を使う。

これなら single-segment band も multi-segment band も同じ規則になる。

```text
/foo::bar
/path/to/foo::bar
```

`path/to/band::module` のように先頭 `/` を省く案だと、multi-segment band は `/` が含まれるので判別できても、single-segment の `foo::bar` だけ曖昧なまま残る。

`./foo::bar` でも解決はするけど、physical filesystem relative path に見えるので、logical realm-relative identity なら `/foo::bar` の方が私は好きだねぇ。

Rust も `self`、`super`、`crate` のような leading qualifier で resolution root を字句的に切り替え、canonical path と alias を分けている。この種の ambiguity は lookup priority より qualifier で消す方が長持ちしやすい。 ([Rustドキュメント][1])

## source module と companion module 自体の衝突

これは同じ module namespace に置き、declaration-time error が良いと思う。

```yulang
mod point

struct point { ... }
```

を merge したり precedence で片方を選んだりせず、

```text
duplicate module name `point`
- source module declared here
- companion module generated here
```

にする。

内部 ID では namespace kind を残す。

```text
ModuleDef::Source
ModuleDef::Companion(TypeDefId)
ModuleDef::ImportedBandAlias(ResolvedBandId)
```

文字列が同じでも、cache artifact や diagnostics が起源を説明できる。

## `std::...` は generic lookup rule にしない

`std::...` は、

```text
prebound realm alias `std`
    -> resolved default band
```

として扱うのが良い。

つまり「single-band realm だから先頭 identifier を勝手に realm とみなす」のではなく、resolver environment にある明示的な alias とする。

```text
surface alias:
std::data::list

resolved:
std@0.1.4/std::data::list
```

local に `std` companion/module が必要なら、

```text
self::std::...
```

のような local qualifier を用意するか、少なくとも band root での `std` 宣言を衝突エラーにする方がいい。

---

# 3. `@v/` と `.yulang/versions/v/`

私は **project-local snapshot は `.yulang/versions/<version>/` を維持**する方に寄るねぇ。

| 観点                     | `@v/` at realm root     | `.yulang/versions/v/`       |
| ---------------------- | ----------------------- | --------------------------- |
| canonical 表記との近さ       | 強い                      | 弱い                          |
| source scanner からの隔離   | 毎回特別扱いが必要               | `.yulang` 全体を除外できる          |
| LSP / grep / formatter | duplicate source を拾いやすい | 原則拾わずに済む                    |
| freeze の再帰             | `@v/@old/...` を防ぐ必要あり   | `.yulang` 除外で自然に止まる         |
| band path との衝突         | special segment 規則が必要   | metadata namespace なので衝突しない |
| snapshot metadata      | source と混ざる             | `snapshot.json` 等をまとめやすい    |
| discoverability        | 高い                      | やや低い                        |

現行実装はすでに `.yulang/versions/<version>` に atomic に freeze し、同じ version に異なる source hash が来た場合を reject している。

さらに freeze 対象の探索から `.yulang` 自体を除外しているので、snapshot の自己複製も避けられている。

## 二層にするとさらにきれい

```text
editable project-local snapshots:
    <realm>/.yulang/versions/<version>/

machine-wide immutable resolved store:
    ~/.cache/yulang/realms/<escaped-realm>/<version>/<source-digest>/
```

canonical identity はどちらの physical path にも依存しない。

```text
realm identity
+ resolved version/revision
+ source digest
```

が同じなら、local snapshot から読んでも global cache から読んでも同じ realm。

`@v` はむしろ、

```text
cache/proxy protocol:
<realm>/@v/<version>.snapshot
<realm>/@v/<version>.manifest
```

のような配布側 namespace と相性がいい。Go でも `@v` は proxy/download cache の version namespace に使われ、project source tree や build artifact cache とは分離されている。 ([Go][2])

## 今の freeze hash で気になる点

現行実装は `yulang.lock` が存在すると freeze 対象に含め、その bytes も realm source hash に含めている。

これは lock が完全に portable なら成立するけど、次のように分けた方が扱いやすいと思う。

```text
realm_content_hash
    = source files + realm.toml + derived band index

resolution_hash
    = normalized yulang.lock graph

snapshot_hash
    = H(realm_content_hash, resolution_hash)
```

特に lock に local absolute path が入ると、同じ source が machine ごとに別 snapshot hash になる。

---

# 4. `realm@v/realm::...` は妥当か

**妥当だし、empty/default band を特別扱いするより良い**と思う。

```text
std@0.1.4/std::prelude
```

のように realm 名と band 名が重複しても、内部モデルは素直になる。

```text
ResolvedRealmKey + BandPath + ModulePath + ItemPath
```

single-band だから band segment を省略すると、

* 後から二つ目の band を追加したとき既存 identity が変わる
* cache key で empty band の特別扱いが要る
* diagnostics が surface と canonical の境界を説明しにくい
* generic resolver と std resolver が別コードになりやすい

ので、重複の方が安い。

## ただし「single-band だから band 名を推測」は避けたい

snapshot metadata に明示的に持つ方がいい。

```text
default_band = "std"
bands = ["std"]
```

「現在一つしか band がないので、それを default とする」だと、二つ目を追加した release で shorthand の意味が変わる。

## 現行メモとの差分

今の repository の design note は、

```text
realm: yulang@0.1.3
band:  std
canonical: yulang@0.1.3/std::prelude
```

としている。

なので、

```text
std@v/std::...
```

へ移るなら、単なる表示変更ではなく、

```text
old: std is a band of the yulang realm
new: std is its own single-band realm
```

という realm boundary の変更になる。

どちらも成立する。

### std を yulang realm の band にする場合

```text
yulang@v/std::...
```

* compiler / language distribution と std の version を一体化しやすい
* bootstrap が単純
* compatibility matrix が少ない

### std を独立 realm にする場合

```text
std@v/std::...
```

* std の source/cache/release を独立させられる
* compiler と std を別 revision で試せる
* browser / embedded std の差し替えが自然

ただし後者なら、lock/cache に

```text
required language edition
compiler ABI/schema compatibility
builtin contract version
```

を入れたい。

## internal canonical identity は string にしない

表示は

```text
std@0.1.4/std::data::list::map
```

で良いけど、内部ではこうしたい。

```rust
struct ResolvedRealmKey {
    authority: RealmAuthority,
    identity: RealmIdentity,
    version_or_revision: ResolvedRevision,
    source_digest: SourceDigest,
}

struct ResolvedBandId {
    realm: ResolvedRealmKey,
    band: BandPath,
}
```

現行の `ResolvedRealmId` は identity と optional version だけで、snapshot source hash は別構造に置かれている。ここを「表示用 ID」と「完全解決 key」に分けるのが良さそうだねぇ。

---

# 5. cache key / lockfile / diagnostics の抜け

## Cache key

今の構成に足したいのはこの形かなぁ。

```text
CompiledUnitKey = H(
    key_schema_version,
    compiler_build_id,
    language_edition,
    artifact_layer_and_format,
    parser_operator_format,
    resolved_realm_key,
    band_path,
    band_topology_hash,
    source_scc_key,
    source_content_hashes,
    direct_dependency_surfaces,
    ambient_query_fingerprints,
    features_and_cfg,
    implicit_prelude_identity,
    target_and_abi_if_relevant
)
```

現行 plan にも compiler version、artifact/parser format、realm/band identity、source hashes、dependency interface hashes、feature/environment knobs は挙がっている。

### source SCC の ID

persistent key に Tarjan 後の `usize` index を使わないことが重要。

現行 helper の `SourceCompilationUnit` は file index と dependency unit index を持ち、unit を計算後に dependency order へ並べ替えている。これは process-local representation としては良いけど、persistent identity にはできない。

例えば、

```text
SourceSccKey = H(
    sorted canonical source logical paths,
    per-file source hashes,
    sorted intra-SCC semantic edges,
    module paths,
    visibility/export metadata
)
```

が良い。

### dependency interface hash は一個でなく層分け

Yulang は syntax export が downstream parse に影響するので、一個の「public interface hash」だけだと粗すぎる。

```text
DependencySurfaceHashes {
    syntax_hash,
    namespace_hash,
    typed_hash,
    coherence_hash,
    runtime_abi_hash,
}
```

特に `coherence_hash` は、

* role impl candidates
* cast candidates
* method lookup surface
* effect operation lookup
* negative lookup result

あたりを含む。

current cache note も cast lookup を ambient dependency として記録する必要を挙げている。この考えを impl/method/role lookup に広げる形だねぇ。

### dependency hash だけでなく dependency identity も含める

```text
(interface_hash_A, interface_hash_B)
```

だけでなく、

```text
(
  canonical ResolvedBandId,
  dependency edge kind,
  selected features/cfg,
  imported/reexported surface,
  interface hashes
)
```

を canonical sort して hash したい。

同じ interface bytes でも `foo@1/T` と `foo@2/T` は別 nominal identity になりうるからねぇ。

### artifact layer を分離

parse/type artifact と native codegen artifact で必要な key が違う。

```text
front-end artifact:
    no target triple unless semantics depends on it

runtime/codegen artifact:
    target triple
    ABI
    backend version
    optimization
    runtime/GC/control-VM mode
```

全部を一つの key に押し込むと、不要な invalidation が増える。

現行 cache plan でも realm/band-qualified key と dependency interface hash はまだ未実装項目として残っている。

## Lockfile

lock は physical source path の一覧ではなく、**resolved realm graph** にしたい。

```text
[[realm]]
node = "r17"
identity = "user/ui"
version = "2.4.0"
source_kind = "registry"
source_locator = "..."
revision = "..."
source_digest = "sha256:..."
manifest_digest = "sha256:..."
band_index_digest = "sha256:..."

[[dependency]]
from = "r2"
requirement = "^2"
to = "r17"
features = [...]
```

### absolute cache path を identity にしない

archive に見える初期 lock schema では、realm source が `Local(PathBuf)` / `Cached(PathBuf)` を直接持っている。これは machine-local で、lock portability を壊しやすい。

lock には、

```text
logical source locator
revision/version
content digest
```

を置き、実際にどの cache directory に展開されているかは resolver runtime state にしたい。

local path dependency だけは、

```text
workspace-relative path
mutable = true
```

のように別扱いが良い。

### source digest は algorithm-tagged strong digest

現行 snapshot hash は `u64` で、実装も FNV 系の stable hash になっている。

これは local cache lookup 用 fingerprint なら軽くて良いけど、

* 同じ version の改竄検出
* lock integrity
* registry content identity
* remote artifact verification

に使うなら弱い。

```text
blake3:<hex>
```

または

```text
sha256:<hex>
```

のような algorithm-tagged digest にした方がいい。

### `with` anchor は BandPath だけで足りない

初期 schema の `LockedWithConstraint` は target realm identity、anchor `BandPath`、resolved realm を持っている。

anchor は少なくとも、

```text
ResolvedBandId
+ public dependency/reexport slot
```

まで持たせたい。

```text
with program
```

が「program という band 名」なのか、「どの realm snapshot の program band」なのかを lock 単体で再現できる必要がある。

### multiple versions policy

一つの build graph に、

```text
ui@1
ui@2
```

が同居可能かを先に固定したい。

* 可能なら lock node は `(identity, version, source digest)` 単位
* 不可能なら realm identity ごとに一意 version であることを validator が明示的に保証

canonical identity は coexistence 可能な形になっているので、私は lock graph 側も複数 node を許す方へ寄る。

## Diagnostics

diagnostics は **surface spelling を先、canonical identity を補足**にすると読みやすい。

### 名前衝突

```text
ambiguous path `ui::button`

`ui` may refer to:
  local companion module `app::ui`
  same-realm band `/ui`

write one of:
  self::ui::button
  /ui::button
```

ただし最終仕様では、そもそも bare path が cross-band lookup をしないなら ambiguity は起きず、

```text
no local module `ui`
help: same-realm bands require `/ui::...`
```

で済む。

### band cycle

```text
band dependency cycle:

app@work/main
  -- use /ui at src/main.yu:4
app@work/ui
  -- pub use /model at ui.yu:8
app@work/model
  -- use /main at model.yu:2
app@work/main
```

SCC の node 一覧だけでなく、**最小 cycle + 各 edge の source span + edge kind** を出したい。

### mod ownership

専用 diagnostics が欲しい。

```text
source `shared.yu` has multiple module parents
ambiguous module file: both `bar.yu` and `foo/bar.yu` exist
module containment cycle
source is not a band root; owned by `/foo::bar`
logical source paths differ only by case
```

### lock mismatch

```text
locked realm source mismatch:
  realm:    ui@2.4.0
  expected: blake3:abc...
  found:    blake3:def...
  source:   .yulang/versions/2.4.0
```

physical path は説明用で、identity の一部にはしない。

### cache diagnostics

通常の compile error と混ぜず、

```text
--explain-cache
```

で理由を出すのが良い。

```text
miss: dependency typed interface changed
miss: parser format changed
miss: band topology changed
hit: source SCC and all dependency surfaces matched
```

raw cache key だけ出すより圧倒的に役立つ。

---

# 最小限、仕様に追加したい文

そのまま design note に近い形で置くなら、私はこう書くねぇ。

```text
A resolved realm snapshot defines three distinct dependency graphs.

1. The mod graph is a structural source-containment graph.
   It must be a forest. Each source has at most one mod parent,
   and each tree has exactly one root. Each tree defines one band.

2. The source dependency graph records semantic dependencies between
   source files inside a band. It may contain cycles; its SCCs are
   compilation and cache units.

3. The band dependency graph records cross-band imports and reexports.
   It must be acyclic.

A bare `::` path never crosses a band boundary.
Same-realm band imports use an explicit current-realm qualifier:

    /band::module
    /path/to/band::module

Cross-realm imports use:

    realm@version/band::module

Source modules and companion modules occupy the same module-name
namespace. A collision is an error.

Every band has an explicit non-empty BandPath, including the only band
of a single-band realm. A default-band alias is resolver metadata and
does not alter canonical identity.

Resolved realm identity is structured and includes the canonical realm
identity, resolved version or revision, and immutable source digest.
Physical snapshot or cache locations are not part of canonical identity.
```

大枠としては、**realm / band / source SCC の三段分割はかなり良い**。今いちばん効く修正は、「未到達 root」という局所条件を **mod forest + derived BandIndex** へ引き上げることと、bare path に cross-band fallback を入れないことだと思うよ〜。

[1]: https://doc.rust-lang.org/reference/paths.html "Paths - The Rust Reference"
[2]: https://go.dev/ref/mod "Go Modules Reference - The Go Programming Language"

## Extracted Decisions

- Keep the realm / band / module split:
  - realm: versioned distribution and snapshot boundary;
  - band: import / namespace / build/cache boundary;
  - module: local source organization.
- Model source identity with three separate graphs:
  - `G_mod`: structural source containment graph created by `mod`;
  - `G_source`: semantic source dependency graph inside a band, where SCCs are
    compilation/cache units;
  - `G_band`: cross-band dependency graph created by imports/reexports.
- Require `G_mod` to be a forest:
  - every source file has at most one `mod` parent;
  - every tree has exactly one root;
  - each tree defines one band.
- Reject structural module ambiguity instead of choosing by precedence:
  - multiple module parents for one source;
  - `mod` containment cycles;
  - two physical candidates for one `mod`;
  - logical source paths that differ only by case or symlink identity.
- Build a realm-level `BandIndex` before ordinary `use` resolution:
  - `BandPath -> root SourceId`;
  - `SourceId -> owning BandId + ModulePath`.
- Do not let bare `foo::bar` cross a band boundary.
- Use the reserved `band` qualifier for current-band absolute paths:
  - `band::path::to::func`.
- Use an explicit current-realm band qualifier for same-realm cross-band imports.
  The chosen spelling is a reserved `realm` qualifier:
  - `realm/foo::bar`;
  - `realm/path/to/band::foo::bar`.
  The reviewed `/foo::bar` spelling is rejected because it reserves leading
  slash too aggressively and conflicts with possible future absolute realm
  forms such as `/local_realm/foo::bar`.
- Keep the separator rule explicit: everything before the band boundary uses
  `/`, and everything inside the band uses `::`. A prebound alias such as
  `std::foo` already resolves to the `std` band, so it continues with `::`.
- Treat all unowned `.yu` source roots in a realm snapshot as band roots for
  the first design. A helper source that is not reached through `mod` is an
  importable dependency unit and therefore should be distributable.
- Keep source modules and generated companion modules in the same module-name
  namespace; collisions are declaration errors.
- Treat `std::...` as a prebound realm/band alias, not as a generic fallback
  rule.
- Allow `@v`-style snapshot directories such as `std/@v/...` for realm storage
  when that is the natural repository/cache layout. If the snapshot contains a
  `realm.yu` root, a single-band realm can make `realm = band` without using an
  empty band path.
- Keep project-local `.yulang/versions/<version>/` snapshots as an
  implementation route, not as canonical source identity.
- Keep explicit non-empty band paths in canonical identity, even for
  single-band realms.
- Prefer `std@v/std::...` or `yulang@v/std::...` over an empty/default band in
  canonical identity.
- Require explicit aliases when two versions from the same realm family are
  imported into one local scope. The preferred order is:
  - `use theme/colors as theme1 v2`
- Treat a source-level version suffix such as `v2` as a version family request.
  The lock records the resolved exact version or revision.
- Apply `with` only to public dependency / reexport surfaces, such as
  `pub use theme/...`. Private dependencies are not visible alignment anchors.
- Do not put human-written versions in `realm.toml`. The manifest may declare
  the current realm identity and source providers, while dependency requests
  live at each `use` site.
- Store exact source-site resolutions in a persistent per-file resolution cache
  so single-file Yulang execution can resolve `std` and local/cached realms
  without requiring a project lock file.
- Treat `snapshot.json` / `yulang.lock` as reproducibility and audit artifacts.
  They can record or constrain observed exact resolutions, but they are not the
  only machine-readable exact resolution store.
- Keep canonical identity structured rather than stringly typed:
  - resolved realm identity;
  - version or revision;
  - immutable source digest;
  - band path;
  - module/item path.
- Split hashes by responsibility:
  - realm content hash;
  - per-file resolution cache hash;
  - resolution/lock hash for reproducibility;
  - snapshot hash;
  - dependency syntax / namespace / typed / coherence / runtime ABI surfaces.
- Do not use machine-local absolute cache paths as lock identity.
- Repository source providers should preserve repository-level identity, while
  selected revision / commit / digest information belongs in `yulang.lock`.
  Git-oriented resolution still needs an explicit spec before implementation.
- Use strong algorithm-tagged digests for lock / snapshot integrity.
- Cache diagnostics should be explainable by route and invalidation reason,
  not only by raw cache keys.

## Open Questions

- How exactly should `std/@v/...`, `.yulang/versions/<version>/`, persistent
  cache entries, and future registry archives relate as physical layouts?
- How should git repository source providers and locked commits be represented
  in `realm.toml`, `yulang.lock`, snapshots, diagnostics, and cache keys?
- What is the minimal `BandIndex` format to freeze in snapshots without
  overcommitting to current source collector internals?
- Which dependency surfaces belong to `coherence_hash`:
  role impls, casts, effect operations, negative lookup results, method lookup,
  or all of them?
- How much of the cache miss explanation should be visible by default versus
  hidden behind `--explain-cache`?
- How much of the per-file resolution graph should be emitted into
  human-readable lock files versus surfaced through LSP / diagnostics only?
