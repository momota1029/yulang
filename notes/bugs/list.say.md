見た感じ、芯はかなりはっきりしているよ〜。

`infer` 単体というより、**型推論の証拠 → runtime lowering → principal elaboration / monomorphize → VM erase** のつなぎ目で、`std::prelude::Display::say` の型変数 `'a` が具体化されないまま残っている。最後に VM 側の `erase_binding` が `binding.type_params` の残留を見つけて落としている、という流れだねぇ。エラー文自体は `RuntimeError::ResidualPolymorphicBinding` の表示で、`Source: binding type parameters` は `binding.type_params` が空になっていないことを指している。 VM 直前の `erase_binding` も `binding.type_params` が残っていたら `VmError::ResidualPolymorphicBinding` を返す実装になっている。

## この式で本来起きるべきこと

`std::undet::each` は nondeterministic な値を返し、`.list` は `[_] _` の computation を `list` に集める。`std::undet` では `each`, `list`, `(x: [_] _).list` が定義されている。

一方、`Display` は role で、`say` は default method として `std::out::out::write a.show` になっている。`Display int`、`Display (list 'a) where 'a: Display` も prelude にある。だからこの式は最終的にこう具体化されるのが自然だねぇ。

```text
each [1,2,3]        : [_] int
each [1,2]          : [_] int
each ... + each ... : [_] int
(...).list          : list int
(...).list.say      : Display::say specialized at 'a = list int
```

ところが現状では `Display::say<'a>` が `Display::say<list int>` に置き換わらず、generic binding のまま runtime に到達している。

---

# バグ一覧

## 1. `principal_elaborate` と言いながら、実際はまだ shape-based infer に戻っている

`principal_elaborate_module` のコメントには「main path should execute exported principal elaboration evidence, not infer substitutions from runtime IR shapes」とあるのに、実装は `principal_unify_module(module)` を呼んでいる。つまり、証拠を実行する専用パスになっておらず、runtime IR の形からまた推測している。

これは今回の根本設計バグだと思うよ〜。`ApplyEvidence` 側には `principal_elaboration: Option<PrincipalElaborationPlan>`、`substitutions`、`substitution_candidates`、`role_method` など、ちゃんと証拠を渡すためのフィールドがある。 それなのに後段が「証拠を source of truth として実行する」より「証拠 + runtime shape から再推測」になっているから、`.list.say` みたいな effect / role / generic が重なる場所で情報が落ちる。

**修正方針**

`principal_elaborate_module` は本当に evidence executor に寄せるべきだねぇ。

```rust
pub(super) fn principal_elaborate_module(module: Module) -> Module {
    execute_principal_elaboration_evidence(module)
}
```

`principal_unify_module` は fallback / repair pass に降格。名前も `principal_repair_from_runtime_shape` くらいにした方が危険度が見える。

---

## 2. incomplete な spine plan が、complete な ApplyEvidence plan を覆い隠す

`principal_elaboration_plan_for_expr` はまず call spine から plan を作り、complete なら返す。ここまではよい。でも **spine plan が incomplete でも即 return** していて、その後にある `ApplyEvidence.principal_elaboration` の complete plan を見る前に終わる構造になっている。

これはかなり濃いバグだよ〜。lower / infer 側が complete な plan を作っていても、runtime 側で再構成した incomplete plan が勝ってしまう。

今の形は概念的にこう。

```rust
let spine_plan = complete_principal_elaboration_plan_from_spine(...);

if spine_plan.complete {
    return spine_plan;
}

if spine_plan.is_some() {
    return spine_plan; // ここで evidence 側の complete plan を見ない
}

return evidence_plan;
```

**修正案**

優先順位を逆にする。

```rust
// 1. explicit evidence の complete plan
if let Some(plan) = complete_plan_from_apply_evidence(&spine, binding) {
    return Some(plan);
}

// 2. spine 由来 plan を作る
let spine_plan = complete_principal_elaboration_plan_from_spine(&spine, binding, result_contextual);

// 3. evidence と spine を merge して normalize
merge_and_normalize_principal_plans(spine_plan, evidence_plan, binding)
```

incomplete spine plan は、complete evidence plan を絶対に潰さない、という invariant を置くとよいねぇ。

---

## 3. `principal_apply_spine` が wrapper を十分に剥がしていない

`principal_apply_spine` は `Apply` を辿り、callee 側の `BindHere` だけ剥がしている。 でも runtime lowering では `Coerce`、`Pack`、`AddId`、effect boundary、空 effect thunk のような wrapper が入る。VM erase 側でも thunk や `BindHere` を消す処理があるので、runtime IR に wrapper が挟まること自体は想定済みだねぇ。

つまり、generic call が

```text
Apply(Coerce(Var(Display::say)), arg)
Apply(Pack(Var(...)), arg)
Apply(BindHere(AddId(... Var(...))), arg)
```

みたいな形になると、spine が取れず、specialization が走らない。

**修正案**

call spine 取得を `Var` 直下に依存させない。

```rust
fn peel_principal_callee_wrappers(expr: &Expr) -> &Expr {
    match &expr.kind {
        ExprKind::BindHere { expr }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => peel_principal_callee_wrappers(expr),

        ExprKind::AddId { thunk, .. } => peel_principal_callee_wrappers(thunk),

        _ => expr,
    }
}
```

さらに理想は `ApplyEvidence` に `target` を明示して、IR shape から target を再発見しない設計だねぇ。

---

## 4. `.say` の receiver context が role dispatch に届く前に落ちている

`rewrite_role_method_from_receiver` は receiver 型から role impl を選ぶ。でも receiver が `Unknown` / `Any` だと skip する分岐がある。

今回だと `.list` の戻り値が `list int` として閉じる前に `.say` を解決しようとすると、receiver が `list 'a` や `Unknown` っぽく見えて `Display::say` の specialization が止まる。そのまま generic `Display::say` が生き残る。

**修正案**

role method の receiver が imprecise のとき、すぐ skip しない。次の順で補完するのがよさそうだねぇ。

1. result context から receiver を逆算
2. `ApplyEvidence.principal_elaboration` から receiver を取得
3. role requirement から associated / impl を使って補完
4. それでも ambiguous なら、その時点で diagnostics を出す

“skip して generic を残す” は、VM で残留 polymorphic binding になるので危ない。

---

## 5. surviving template binding を rewrite するとき、binding scheme の context を渡していない

`PrincipalUnifier::run` は普通の binding body では `binding_body_runtime_context(&binding)` を作って `rewrite_expr` に渡している。 でも `rewrite_surviving_template_bindings` では、template binding の body を `rewrite_expr(body, None)` で書き換えている。

これは `Display::say` みたいな default role method にかなり刺さる。`say` の body は `a.show` なので、`a : 'a` という scheme context が必要なのに、`None` で rewrite すると `a.show` の receiver 情報が弱くなる。

**局所修正**

ここはまずこれで直す価値が高いよ〜。

```rust
let binding = &module.bindings[index];
let body_context = Self::binding_body_runtime_context(binding);

let body = module.bindings[index].body.clone();
let body = refresh_local_expr_types(body);

self.push_rewrite_context("surviving-template");
let body = self.rewrite_expr(body, body_context);
self.pop_rewrite_context();

module.bindings[index].body = project_runtime_expr_types(body);
```

---

## 6. structural node で expected context を捨てすぎている

`rewrite_expr_inner` では `Record` の field、`Variant` の payload、`Select` の base、`Coerce` の inner、`Pack` の inner などをかなり `None` context で rewrite している。

`.list.say` は method chain なので、`Select` / role method / apply の間で context が必要になる。ここで context が切れると、後段の plan completion が “runtime shape から頑張る” しかなくなる。

**修正案**

最低限、こういう context slicing を入れる。

* `Select { base, field }`: result context から base record context を作る
* `Coerce { from, to, expr }`: `expr` に `from` または `to` を渡す
* `Pack`: pack 先の expected type を inner に伝える
* `Variant`: tag が分かるなら payload context を渡す
* `Record`: expected record type から field context を渡す

---

## 7. `principal_plan_runtime_arg_bounds` が thunk / effect shape を潰している

`complete_principal_elaboration_plan_from_spine` は runtime arg bounds を作って plan に入れている。 でも `principal_plan_runtime_arg_bounds(arg)` は `runtime_core_type(&arg.ty)` だけ見ている。つまり `RuntimeType::Thunk { effect, value }` の **effect 側**や thunk 境界が plan から消える。

`std::undet::list` はまさに `x: [_] _` を受ける関数なので、value だけでなく effect/thunk shape が重要だよ〜。

**修正案**

`PrincipalElaborationArg.expected_runtime` / `intrinsic` を core type だけで表さず、runtime slot を明示する。

```rust
enum PrincipalRuntimeSlot {
    Value(typed_ir::Type),
    Thunk {
        effect: typed_ir::Type,
        value: typed_ir::Type,
    },
    Function {
        param: Box<PrincipalRuntimeSlot>,
        ret: Box<PrincipalRuntimeSlot>,
    },
}
```

既存 `TypeBounds` に押し込むなら、少なくとも `expected_runtime` に thunk shape を入れる。

---

## 8. lowerer 側の polymorphic arg hint が `Variant` に偏っている

lowerer の apply 処理では `polymorphic_arg_hint` を使って polymorphic callee の arg hint を補っているけど、条件が `RuntimeType::Core(typed_ir::Type::Variant(_))` に限定されている。

これは `list`、`thunk`、effect handler 系の generic 関数には効かない。今回の `each` / `.list` は `Variant` ではなく `[_] _` / `list int` / effect shape が中心なので、ここでも情報が落ちる。

**修正案**

`Variant` 専用ではなく、「runtime slot として precise なら使う」に広げる。

```rust
fn precise_runtime_hint_for_polymorphic_arg(ty: &RuntimeType) -> bool {
    !runtime_type_contains_unknown(ty)
        && !hir_type_has_vars(ty)
        && !runtime_type_is_imprecise_runtime_slot(ty)
}
```

---

## 9. one-sided bounds を exact として扱っている

`principal_plan_bounds_single_closed_type` は lower だけ、または upper だけでも closed type として返している。 `principal_plan_arg_type` / `principal_plan_result_type` も bounds から slot type を取って plan completion に使っている。

でも lower-only / upper-only は exact ではない。たとえば `T <: int` と `T = int` は違う。これを exact 扱いすると、誤 specialization と false complete の両方が起きる。

**修正案**

`single_closed_type` という名前をやめて、極性を保持する。

```rust
enum ProjectedBound {
    Exact(Type),
    Lower(Type),
    Upper(Type),
}
```

`Exact` だけ substitution に直結させる。`Lower` / `Upper` は constraint set に入れる。

---

## 10. candidate projection が「制約ソルバ」ではなく「unique candidate heuristic」になっている

`project_substitutions_from_candidates` は、exact が一意なら採用、lower と upper が一致したら採用、特殊な effect residual だけ例外、という作りになっている。既存 substitution が candidate を満たさないと conflict にする分岐もある。

これは脆いねぇ。`Display (list 'a)` みたいに role requirement と receiver type と result context が段階的に閉じる場面では、候補を一回で exact にできないことがある。そこで missing のまま残る。

**修正案**

`BTreeMap<TypeVar, Type>` を直接いじるのではなく、こういう中間表現にする。

```rust
struct VarConstraints {
    exact: Option<Type>,
    lowers: Vec<Type>,
    uppers: Vec<Type>,
    sources: Vec<ConstraintSource>,
}

enum SolveResult {
    Solved(Type),
    Ambiguous(Vec<Type>),
    Conflict(Vec<ConstraintSource>),
    Open,
}
```

normalize は「候補を拾う」と「解く」を分ける。今はその2つが混ざっている。

---

## 11. union lower bound から全 item の type variable に actual を入れるのは unsound

`project_choice_var_items_from_bound` は lower bound が `Union(items)` のとき、union 内の各 `Type::Var` に同じ actual を入れている。

でも `actual <: A | B` から `A = actual` と `B = actual` は導けない。これは過剰制約で、別の候補と conflict したり、逆に変な substitution を作ったりする。

**修正案**

union / intersection は shape で item が一意に選べるときだけ投影する。

```rust
let matching_items = items.iter()
    .filter(|item| projection_choice_item_matches_actual(item, actual, allow_never))
    .collect::<Vec<_>>();

if matching_items.len() == 1 {
    project(matching_items[0], actual);
}
```

---

## 12. `project_closed_substitutions_from_type_arg` が `allow_never` を無視している

この関数は引数名が `_allow_never` になっていて、内部では全部 `false` を渡している。 effect slot では `Never` が空 effect として有効なのに、type arg 経由だと落ちる可能性がある。

これは明確な実装バグだねぇ。

**修正案**

```rust
fn project_closed_substitutions_from_type_arg(
    ...
    allow_never: bool,
    ...
) {
    ...
    project_closed_substitutions_from_type(
        template,
        actual,
        params,
        substitutions,
        conflicts,
        allow_never,
        depth,
    );
}
```

effect type arg と value type arg を区別したいなら、`TypeArg` 側にも slot kind を渡す。

---

## 13. `Any` を exact bounds match として扱っている

`type_matches_exact_bounds` は `actual == expected || matches!(actual, typed_ir::Type::Any)` を true にしている。

`Any` は “何でもよい” であって “exact に一致した” ではない。ここで exact 扱いすると、principal plan が precise だと誤認しやすい。

**修正案**

`Any` は exact 判定では false。別途 `CompatibleButImprecise` として扱う。

```rust
enum BoundsMatch {
    Exact,
    CompatibleImprecise,
    Mismatch,
}
```

---

## 14. reachability が syntactic free vars だけを見ていて、evidence / role requirement を dependency として扱っていない

`root_reachable_binding_paths` は root expr から `collect_expr_vars` で free vars を集めて、binding body の `Var` を辿る。 `collect_expr_vars` の実装も基本的に `ExprKind::Var` と構文木だけを辿っていて、`ApplyEvidence.principal_elaboration.target`、role impl requirement、specialization target を dependency としては集めていない。

role method や generated specialization は「構文上の Var」だけでは依存が見えないことがある。`Display::say` → `Display::show` → `Display(list int)` impl → `Display int` みたいな依存は、role graph / evidence graph も見ないと安全に追えない。

**修正案**

monomorphize 用の dependency graph を別に作る。

```text
Expr Var edge
ApplyEvidence target edge
PrincipalElaborationPlan target edge
RoleRequirement edge
RoleImpl selected binding edge
Handler adapter edge
Generated specialization edge
```

prune はこの graph の後にだけ走らせる。

---

## 15. final audit が任意扱いで、失敗が VM まで遅延している

principal pipeline の後に `YULANG_PRINCIPAL_ELABORATE_STRICT` があると strict failure を返すが、通常 path では optional になっている。 その結果、monomorphize が incomplete なまま通過し、VM erase で初めて `ResidualPolymorphicBinding` になる。

これは diagnostics としてもかなり悪い。ユーザーには `Display::say` に注釈を足せと言うけど、本当は `.list` / `each` / role dispatch の specialization 失敗だねぇ。

**修正案**

少なくとも test/debug では mandatory にする。

```rust
audit_no_reachable_residual_polymorphism(&module)?;
audit_no_reachable_runtime_type_vars(&module)?;
audit_no_incomplete_principal_plans(&module)?;
```

そして diagnostics には、最後に残った binding だけでなく、失敗した call site と incomplete reason を出す。

---

# このケースの最短修正セット

まずこの順で直すのがよさそうだよ〜。

## A. `principal_elaboration_plan_for_expr` の優先順位を直す

complete evidence plan を最優先。

```rust
pub(super) fn principal_elaboration_plan_for_expr(
    expr: &Expr,
    binding: &Binding,
    result_contextual: Option<&typed_ir::TypeBounds>,
) -> Option<typed_ir::PrincipalElaborationPlan> {
    let spine = principal_apply_spine(expr)?;
    if spine.target != &binding.name {
        return None;
    }

    if let Some(plan) = complete_evidence_plan_for_binding(&spine, binding) {
        return Some(plan);
    }

    let spine_plan =
        complete_principal_elaboration_plan_from_spine(&spine, binding, result_contextual);

    merge_evidence_and_spine_plan(spine_plan, &spine, binding)
}
```

## B. surviving template に binding context を渡す

`Display::say` への効果が大きいはず。

```rust
let binding = module.bindings[index].clone();
let body_context = Self::binding_body_runtime_context(&binding);

let body = refresh_local_expr_types(binding.body);
self.push_rewrite_context("surviving-template");
let body = self.rewrite_expr(body, body_context);
self.pop_rewrite_context();

module.bindings[index].body = project_runtime_expr_types(body);
```

## C. `principal_apply_spine` を wrapper-insensitive にする

`BindHere` だけでなく `Coerce` / `Pack` / boundary wrapper を剥がす。

## D. `principal_plan_bounds_single_closed_type` を exact-only にする

lower-only / upper-only を exact にしない。これを入れないと、別の場所で変な specialization が出る危険がある。

## E. role receiver が imprecise のとき skip で終わらせない

`Display::say` なら receiver context を plan / result / role requirement から補完して、それでも曖昧なら diagnostic。

---

# リファクタリング案

今の `principal_unify.rs` は責務が多すぎる。plan 実行、constraint projection、role dispatch、handler adapter、specialization cache、diagnostics、profiling が同じ巨大な流れに入っている。`complete_plan_from_*` が増え続ける構造になっているから、バグが局所化しにくいねぇ。

おすすめの分割はこれ。

```text
monomorphize/
  evidence_executor.rs
  constraint_solver.rs
  runtime_shape.rs
  role_dispatch.rs
  specialization_graph.rs
  specialization_cache.rs
  residual_audit.rs
  diagnostics.rs
```

## `evidence_executor.rs`

`ApplyEvidence.principal_elaboration` を source of truth として実行する。runtime IR shape から再推測しない。

役割:

* apply spine を読む
* evidence plan を取り出す
* substitutions を適用
* adapter hole を実行
* specialization request を発行

## `constraint_solver.rs`

今の `project_substitutions_from_candidates`、`project_closed_substitutions_from_type`、`principal_plan_bounds_single_closed_type` 周辺をまとめる。

大事な invariant:

```text
one-sided bound は exact substitution ではない
Any / Unknown は precise ではない
Union から複数 var へ同時代入しない
Never は effect slot だけで許可
```

## `runtime_shape.rs`

`runtime_core_type` で value だけ取り出す処理を減らす。`Thunk(effect, value)` を一つの shape として扱う。

```rust
enum RuntimeShape {
    Unknown,
    Value(Type),
    Thunk { effect: Type, value: Box<RuntimeShape> },
    Fun { param: Box<RuntimeShape>, ret: Box<RuntimeShape> },
}
```

`std::undet::list` 系はここが大事。

## `role_dispatch.rs`

`rewrite_role_method_from_receiver` を切り出す。receiver が imprecise の場合も、context と requirements を使って候補を閉じる。

```text
receiver intrinsic
receiver contextual
result contextual
role impl graph
associated requirements
```

これを同じ scoring で処理する。

## `specialization_graph.rs`

reachability と specialization を分ける。構文上の `Var` だけではなく、evidence / role / handler / generated binding の edge を graph に入れる。

## `residual_audit.rs`

VM に行く前に必ず残留 polymorphism を止める。

```rust
pub fn audit_no_residual_polymorphism(module: &Module) -> RuntimeResult<()> {
    for binding in reachable_bindings(module) {
        if !binding.type_params.is_empty() {
            return Err(...);
        }
        if runtime_type_has_vars(&binding.body.ty) {
            return Err(...);
        }
    }
    Ok(())
}
```

---

# 回帰テスト

まずこのへんを入れるとよさそうだねぇ。

```yu
(each [1,2,3] + each [1,2]).list.say
```

期待はたぶんこの list 表示。

```text
[2, 3, 3, 4, 4, 5]
```

さらに分解テストも入れる。

```yu
(each [1,2,3]).list.say
(each [1,2,3] + 1).list.say
[1,2,3].say
(each ["a", "b"]).list.say
```

加えて、monomorphize 後の IR に対してこの invariant を assert するのが重要だよ〜。

```rust
assert_no_reachable_binding_type_params(&module);
assert_no_reachable_runtime_type_vars(&module);
assert_no_incomplete_principal_elaboration_plans(&module);
```

---

## まとめ

一番怪しい直接原因は、**`Display::say` の default role method が `list int` receiver で specialization されず、generic `'a` を持ったまま VM erase に到達していること**だねぇ。

優先して直すなら、この4つ。

1. `principal_elaboration_plan_for_expr` で complete evidence plan を incomplete spine plan より優先
2. `rewrite_surviving_template_bindings` に binding scheme context を渡す
3. role receiver が imprecise のとき skip せず、context / evidence / requirement から補完
4. one-sided bounds を exact substitution として扱わない

この4つを入れると、今回の `.list.say` はかなりの確率で通ると思うよ〜。
