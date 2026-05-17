うん、ぶっちゃけ **多いと思う**。
しかも単発の凡ミスというより、`substitution.rs` が「置換」「推論」「principal elaboration」「effect row 残差計算」「候補解決」「正規化」を全部抱え込んでいて、局所ルールが互いに踏み合ってる感じだねぇ。

今回は実ファイルを読んだ静的レビューだよ〜。実行で赤テスト化まではしてないけど、下のうちいくつかはかなり濃いバグ候補。

---

## バグ / 危険箇所リスト

### 1. `substitute_type` が推移的置換になってない

`Type::Var(var)` の場合、`substitutions.get(var).cloned()` を返すだけで、返った型に再度 `substitute_type` をかけてない。つまり `{ a ↦ b, b ↦ int }` で `a` を置換しても `int` じゃなくて `b` で止まる。

これは `insert_substitution` 側も「新しい値を既存 substitution で正規化してから入れる」形になってないから、普通に非冪等な substitution map ができる。

**症状例**

```rust
subst = { a: Var(b), b: int }
substitute_type(Var(a), subst) == Var(b) // たぶん現状
// 期待は int
```

**影響**
principal elaboration の complete 判定、specialization key、runtime projection が「まだ var が残ってる」と見たり、逆に古い alias を完成済み扱いしたりする。

---

### 2. `Recursive` の束縛変数まわりが capture-avoiding じゃない

`substitute_type` は `Recursive { var, body }` で substitution map から `var` を消している。これは「`var` は binder」という理解だねぇ。

でも、置換される型の中に `var` と同名の自由変数がある場合、alpha-renaming しないから捕獲が起きる。

**症状例**

```rust
// subst: a ↦ x
Recursive { var: x, body: Var(a) }
```

これを素朴に置換すると、

```rust
Recursive { var: x, body: Var(x) }
```

になって、`a` の置換結果として入った自由な `x` が、recursive binder に捕獲される。

さらに `collect_type_vars` は `Recursive { body, .. }` で body の変数を集めるだけで、binder を取り除いてない。
つまり、`substitute_type` だけは binder として扱うのに、free-var collection では free var 扱いしてる。ここはかなり危ない。

**影響**
`type_has_vars`、`type_contains_var`、`principal_plan_substitution_type_usable`、runtime/non-runtime 判定が recursive type を誤判定する。

---

### 3. 関数 effect slot が推論でも互換性判定でも落ちやすい

`TypeSubstitutionInferOptions` には `include_function_effects` があるけど、公開 entry point から true にする経路が見えない。デフォルトは false で、関数型の推論時も `if options.include_function_effects` の中だけで `param_effect` / `ret_effect` を見る。

さらに `type_compatible` の `Fun` ケースは `param` と `ret` だけ見て、`param_effect` / `ret_effect` を無視してる。

**症状例**

```rust
[A] Int ->{io} Bool
[A] Int ->{never} Bool
```

この2つが substitution merge や candidate satisfaction の文脈で同じっぽく扱われる可能性がある。

**影響**
effect polymorphism の specialization、handler boundary、Thunk 挿入あたりで「型は合ってるのに effect が違う」バグが出る。

---

### 4. effect row matching が「head だけ一致」で actual を消費する

`infer_effect_row_substitutions` と `project_closed_effect_row_substitutions` は、`same_effect_head(template, actual)` が true なら actual を matched にして残差から外す。

でも `same_effect_head` は Named の path だけを見る。型引数の整合性は後段の推論に投げるだけで、失敗しても `matched_actual[index] = true` になる。

**症状例**

```rust
template: Row { items: [sub[int]], tail: e }
actual:   Row { items: [sub[bool]], tail: never }
```

`sub` という head は同じなので actual 側の `sub[bool]` が消費される。
中身の `int` vs `bool` が合わなくても、残差から消える。

**影響**
effect row の残差が過小になる。つまり「本当は未処理の effect が残ってるのに empty 扱い」になる危険がある。これは handler / thunk 周りでめちゃくちゃ怖い。

---

### 5. 複数 row var に同じ residual を代入してる

`infer_effect_row_substitutions` は `template_items` 内の `Var` を全部 `row_vars` に集めて、最後に全 var へ同じ `residual` を入れる。
`project_closed_effect_row_substitutions` も同じ構造。

**症状例**

```rust
template: [e1, e2 | tail]
actual:   [io, state]
```

この場合、`e1 = [io, state]` かつ `e2 = [io, state]` になり得る。
本当は分割不能なので、少なくとも ambiguous として解かないほうが安全。

**影響**
effect を重複保持した substitution ができる。後続の `project_runtime_effect` が dedup して隠す可能性もあるから、バグが見えにくい。

---

### 6. `Union` / `Inter` からの推論が雑に全枝へ降りる

`infer_type_substitutions_inner` の `Union(items) | Inter(items)` ケースは、actual に対して全 item を再帰推論する。

**症状例**

```rust
template: Union[T, Int]
actual:   Bool
```

この形だと `T = Bool` が入り得る。
でも `Bool` が union のどの枝に対応するかは、本来は互換性や polarity を見ないと危ない。

面白いことに、closed projection 側には「union actual から principal var を解かない」テストがある。
つまり、この危険性はどこかで認識されてるのに、通常の `infer_type_substitutions_inner` には同じ安全策が入ってない。

---

### 7. row compatibility が effect row の実態とズレてる

`type_compatible` の Row ケースは `items.len() == actual_items.len()` かつ zip 順で比較する。

でも effect 関連の他のコードは、effect を順序なし集合っぽく扱っている。`effect_compatible` は path 集合で見るし、`project_runtime_effect` は push_unique で重複を消している。

**症状例**

```rust
[io, state]
[state, io]
```

effect としては同じっぽいのに、`type_compatible` では違う扱いになる可能性がある。

**影響**
`substitution_satisfies_candidate` や `choose_substitution_type` が row order に引きずられる。バグが「順番を変えたら直る」系になる。

---

### 8. hard-coded `for _ in 0..4` が複数ある

principal elaboration の候補投影や role requirement 投影で、固定 4 回ループが入ってる。

これは小さい例では通るけど、associated type の依存鎖が 5 段以上になった時に突然閉じなくなる。

**症状例**

```text
A -> B -> C -> D -> E -> F
```

4 回では足りない。
本来は「進捗がなくなるまで」か「依存グラフ上の worklist」で回すべきところだねぇ。

---

### 9. `Any` / `Unknown` / `Never` の意味がまだ境界で混ざってる

`meaning.rs` では `Unknown` は evidence/projection hole、`Any` は top type と明確に分けようとしている。
でも `substitution.rs` 内では、`Any` を candidate から落とす、precision merge では concrete に負けさせる、effect wildcard として扱う、runtime fallback と絡む、みたいな用途が散らばってる。

この問題はリポジトリ内の設計メモにも既に書かれていて、`Any` / `_` が runtime shape になること、`Thunk` や effect rows 周りの情報が後段で復元されることが高リスク症状として挙げられてる。

**影響**
「`Any` は top なのか wildcard なのか recovery hole なのか」が関数ごとに違って、局所修正が別の場所を壊す。

---

### 10. depth limit が silent failure / silent success になってる

推論は depth 0 で単に return。
互換性判定は depth 0 で true。

深い型で、

* 推論は必要な substitution を落とす
* compatibility は互換と誤判定する

という逆向きの危険がある。

これは実用上の guard としてはわかるけど、少なくとも debug/test では「depth exhausted」を検出したほうがいい。

---

## `types` リファクタ案

### 方針

`types` は今、「型代数」と「runtime projection」と「principal elaboration repair」が同じ鍋に入ってる。
ここは分けたほうがいい。

今の `mod.rs` は `choice`, `compat`, `core_view`, `effect`, `meaning`, `project`, `runtime`, `shape`, `substitution` を全部 re-export していて、どの helper がどの不変条件に依存するか見えにくい。

おすすめ構成はこんな感じ。

```text
types/
  algebra/
    walk.rs          // fold/visit/map, free vars, alpha rename
    subst.rs         // Subst struct, apply/compose/restrict
    normalize.rs     // canonical form
    compat.rs        // position-aware compatibility
  effects/
    row.rs           // EffectRow canonicalization, residual matching
    compat.rs        // effect-compatible only
  projection/
    runtime.rs       // runtime type projection
    diagnostic.rs    // diagnostic-only projection
  principal/
    plan.rs          // PrincipalElaborationPlan normalization
    constraints.rs   // candidates / lower / upper / exact
    solver.rs        // worklist solver
  evidence/
    apply.rs
    join.rs
```

---

## まず作るべき中核 API

### 1. raw `BTreeMap<TypeVar, Type>` をやめて `Subst` に包む

```rust
pub struct Subst {
    map: BTreeMap<TypeVar, Type>,
}

impl Subst {
    pub fn apply(&self, ty: &Type) -> Type;
    pub fn apply_fixpoint(&self, ty: &Type) -> Type;
    pub fn insert_checked(&mut self, var: TypeVar, ty: Type) -> Result<(), SubstError>;
    pub fn compose(&mut self, other: &Subst);
    pub fn restrict_to_free_vars(&self, ty: &Type) -> Subst;
    pub fn without_bound(&self, var: &TypeVar) -> Subst;
}
```

ここで保証する不変条件はこの3つ。

```text
1. substitution map は idempotent
2. occurs check は free vars で見る
3. Recursive binder では capture-avoiding
```

今のコードはこの3つが分散していて、全部が微妙に守れてない。

---

### 2. `free_vars` と `all_vars` を分ける

今の `collect_type_vars` は recursive binder を落とさない。
必要なのは少なくとも2種類。

```rust
fn free_type_vars(ty: &Type) -> BTreeSet<TypeVar>;
fn mentioned_type_vars(ty: &Type) -> BTreeSet<TypeVar>;
```

用途別にこう分ける。

| 用途                         | 使う関数                   |
| -------------------------- | ---------------------- |
| occurs check               | `free_type_vars`       |
| principal params discovery | たぶん `free_type_vars`   |
| diagnostics / debug dump   | `mentioned_type_vars`  |
| alpha rename               | binder-aware traversal |

これだけで recursive type 周りのバグがだいぶ減る。

---

### 3. `TypePosition` を入れる

`type_compatible` が value 型にも effect 型にも使われていて、関数 effect slot を無視しているのが危ない。

```rust
enum TypePosition {
    Value,
    Effect,
    FunctionSignature {
        include_effects: bool,
    },
    TypeArg,
    PrincipalCandidate,
}
```

みたいにして、

```rust
fn compatible(expected: &Type, actual: &Type, pos: TypePosition) -> bool;
```

に寄せるといい。

特に `Fun` は、

* runtime value compatibility なら effects を別判定
* principal substitution なら effects 込み
* diagnostic choice なら shape 優先

みたいに分けるべきだねぇ。

---

### 4. `EffectRow` を正規化された構造にする

今は `Type::Row { items, tail }`、`Type::Named` 単体、`Never` が全部 effect として出入りする。
そのせいで `same_effect_head`、`effect_row_from_items_and_tail`、`merge_projected_effect_rows`、`project_runtime_effect` がそれぞれ独自に正規化している。

```rust
struct EffectRow {
    atoms: Vec<EffectAtom>, // canonical order, dedup済み
    tail: EffectTail,       // Closed | Var(v) | Any
}

struct EffectAtom {
    path: Path,
    args: Vec<TypeArg>,
}
```

この形にしてから、

```rust
fn match_effect_row(template: &EffectRow, actual: &EffectRow) -> RowMatchResult;
```

を返す。

```rust
enum RowMatchResult {
    Matched {
        substitutions: Subst,
        residual: EffectRow,
    },
    Ambiguous,
    Conflict,
}
```

これで「head だけ合ったから消費」みたいな危険を止められる。

---

### 5. principal elaboration は `substitution.rs` から出す

`substitution.rs` が巨大なのは、principal elaboration の正規化まで入ってるから。
`normalize_principal_elaboration_plan*`、candidate projection、role requirement projection、associated type 解決は `types/principal/` に逃がすのがよさそう。

今の関数群は、置換というより **constraint solver** に近い。

```text
principal/
  plan.rs
  candidate.rs
  requirement.rs
  solver.rs
```

solver は固定4回ループじゃなくて、worklist にする。

```rust
while let Some(task) = worklist.pop() {
    let progress = solver.step(task)?;
    if progress {
        worklist.extend(progress.new_tasks);
    }
}
```

終了条件は、

```text
- no progress
- conflict
- max steps reached with diagnostic
```

にする。

---

## 先に追加したいテスト

ここは refactor 前に赤テストとして置くのがいい。
名前は雑にこんな感じ。

```rust
#[test]
fn substitution_is_transitive() { ... }

#[test]
fn substitution_does_not_capture_recursive_binder() { ... }

#[test]
fn free_vars_ignore_recursive_binder() { ... }

#[test]
fn infer_function_effect_substitution_when_effect_var_is_principal() { ... }

#[test]
fn function_compatibility_distinguishes_effect_slots_for_principal_candidates() { ... }

#[test]
fn effect_row_matching_does_not_consume_same_head_with_conflicting_args() { ... }

#[test]
fn effect_row_multiple_vars_are_ambiguous_not_duplicate_residuals() { ... }

#[test]
fn effect_row_compatibility_is_order_insensitive() { ... }

#[test]
fn union_inference_does_not_solve_var_from_unmatched_branch() { ... }

#[test]
fn principal_solver_handles_associated_type_chain_longer_than_four() { ... }
```

---

## 実装順のおすすめ

### Phase 1: テストと不変条件だけ入れる

まだ refactor しない。
上の赤テストを足して、「何を壊してるか」を固定する。

ついでに debug-only invariant を足す。

```text
- substitution map is idempotent
- no captured recursive vars
- no Unknown in completed principal substitution
- no Any in runtime value slot
- effect rows canonical after projection
```

---

### Phase 2: `free_vars` / traversal を置き換える

`collect_type_vars` 系があちこちに散ってるから、まず visitor を作る。

```rust
trait TypeVisitor {
    fn enter_binder(&mut self, var: &TypeVar);
    fn leave_binder(&mut self, var: &TypeVar);
    fn visit_var(&mut self, var: &TypeVar);
}
```

これで recursive binder 問題を一気に潰す。

---

### Phase 3: `Subst` 導入

`BTreeMap<TypeVar, Type>` を public helper の引数から少しずつ消す。
最初は互換用に `impl From<&BTreeMap<_, _>> for SubstView` みたいな軽い wrapper でもいい。

重要なのは `insert_substitution` を raw helper から method に変えること。

```rust
subst.insert_inferred(var, ty, InsertPolicy::PreferNonNever)?;
subst.apply_fixpoint(&ty)
```

---

### Phase 4: effect row matcher を差し替える

`same_effect_head` で matched にする流れをやめる。
`match_effect_row` が `Conflict` を返したら residual から消さない、もしくは plan incomplete にする。

この段階で handler / thunk 系のバグがかなり露出すると思う。

---

### Phase 5: compatibility を position-aware にする

まず `type_compatible` を残しつつ deprecated 的にして、

```rust
compatible_value(...)
compatible_effect(...)
compatible_principal(...)
```

へ逃がす。

その後に `choose_substitution_type` / `substitution_satisfies_candidate` から順に差し替える。

---

## 私の優先順位

まず直すならこの順だねぇ。

1. **推移的 substitution / idempotent Subst**
2. **recursive binder の free var / capture**
3. **function effect slot を principal substitution で見る**
4. **effect row matching が head だけで消費する問題**
5. **複数 row var の residual 代入**
6. **Union / Inter 推論の過剰さ**
7. **fixed 4 iteration の worklist 化**

一番怖いのは 4。
`same_effect_head` で actual を消費して残差から消すのは、handler と runtime effect の健全性に直撃する。
次に怖いのは 1 と 2。ここが壊れてると、どれだけ後段で正規化しても substitution が信用できない。
