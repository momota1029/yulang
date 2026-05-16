あるよ〜。ただし、**「ファイルを分ける」だけだとたぶん救われない**。Yulang の Native は、今の形を見る限り、複雑さの本体がファイルサイズじゃなくて **判定順序・effect boundary・thunk/handler/resumption の状態遷移が同じ関数に重なっていること** にあるねぇ。

特に `lower_expr` は、inline handler、local expr apply、effect request、`BindHere`、primitive、partial/direct apply、resume apply、通常 `ExprKind` match が順序依存で並んでいて、ここが「条件が増えるたびに世界が割れる」場所になってる。`FunctionLowerer` 自体も `active_handler`、`effect_guards`、`resumptions`、`force_effectful_apply_depth`、`sync_apply_for_immediate_force_depth` みたいな横断状態を抱えているから、局所修正がすぐ別の経路へ波及しやすい構造だねぇ。

## 結論

やるなら、方針はこれが一番堅いと思うよ〜。

> **意味論を変えずに、条件分岐を「分類」と「実行」に分ける。**
> そのあと Cranelift 側を「値」「呼び出し」「handler/resumption」「terminator」に分ける。

いきなり大規模再設計じゃなくて、**seam carving**、つまり切れ目を作るリファクタが向いてる。

---

## まず絶対に守る軸

Native 設計メモにもある通り、VM を behavioral oracle として残し、unsupported は structured reason で返す方針が既に立っているよねぇ。これはリファクタ時の命綱になる。Native 側の変更は、基本的に

```text
VM result == native result
```

を守る形に寄せるのがよさそう。

さらに failure matrix 側でも、unsupported 判定は source syntax や関数名じゃなく、**型変換後 runtime IR / CPS IR / evidence / lane / value kind** を基準にする方針が書かれている。これはリファクタの設計原則としてかなり良い軸だよ〜。

---

# 1. `lower_expr` を「分類器 + 実行器」に分ける

今の `lower_expr` は実質こういう形だねぇ。

```rust
fn lower_expr(&mut self, expr: &runtime::Expr) -> CpsLowerResult<CpsValueId> {
    if inline_thunk_handler_apply(...) { ... }
    if lower_local_expr_apply(...) { ... }
    if effect_apply_body_request(...) { ... }
    if BindHere { ... }
    if primitive_apply(...) { ... }
    if partial_direct_apply_path(...) { ... }
    if direct_apply_path(...) { ... }
    if resume_apply(...) { ... }

    match &expr.kind {
        ...
    }
}
```

これをまずこうしたい。

```rust
fn lower_expr(&mut self, expr: &runtime::Expr) -> CpsLowerResult<CpsValueId> {
    match self.classify_expr(expr)? {
        ExprLowerCase::InlineThunkHandler(case) => self.lower_inline_thunk_handler(case),
        ExprLowerCase::LocalExprApply(case) => self.lower_local_expr_apply_case(case),
        ExprLowerCase::EffectRequest(case) => self.lower_effect_request(case),
        ExprLowerCase::BindHere(case) => self.lower_bind_here(case.expr),
        ExprLowerCase::Primitive(case) => self.lower_primitive_apply(case),
        ExprLowerCase::PartialDirectApply(case) => self.lower_partial_direct_apply_case(case),
        ExprLowerCase::DirectApply(plan) => self.lower_direct_apply_plan(plan),
        ExprLowerCase::ResumeApply(case) => self.lower_resume_apply_case(case),
        ExprLowerCase::PlainExprKind => self.lower_expr_kind(expr),
    }
}
```

このとき大事なのは、`classify_expr` をなるべく **副作用なし** にすること。`self.current` に statement を積んだり、handler stack をいじったりしない。分類だけを返す。

たとえば概念的にはこう。

```rust
enum ExprLowerCase<'a> {
    InlineThunkHandler(InlineThunkHandlerCase<'a>),
    LocalExprApply(LocalExprApplyCase<'a>),
    EffectRequest(EffectRequestCase<'a>),
    BindHere { expr: &'a runtime::Expr },
    Primitive(PrimitiveApplyCase<'a>),
    PartialDirectApply(PartialDirectApplyCase<'a>),
    DirectApply(DirectCallPlan<'a>),
    ResumeApply(ResumeApplyCase<'a>),
    PlainExprKind,
}
```

これだけで、今の「この `if let` は上に置かないと壊れるのか？ 下でもいいのか？」という怖さがかなり減る。

---

# 2. direct call 周りは `DirectCallPlan` に押し込める

一番危ないのは direct apply の部分だと思う。ここには今、

* target が thunk を返すか
* target が perform しうるか
* active handler 中か
* inline すべきか
* arg を thunk として lower すべきか
* handler reentry のために depth を増やすか
* 呼び出し後に force すべきか
* `EffectfulCall` にするか `DirectCall` にするか

が混ざってる。

ここは `DirectCallPlan` を作るのが効く。

```rust
struct DirectCallPlan<'a> {
    target_path: &'a typed_ir::Path,
    target_name: String,
    args: Vec<ArgLoweringPlan<'a>>,
    call_mode: DirectCallMode,
    result_demand: ResultDemand,
    inline_policy: InlinePolicy,
    marks_external_handler_call: bool,
}

enum DirectCallMode {
    SyncDirect,
    EffectfulWithResume,
}

enum ArgLoweringPlan<'a> {
    Plain {
        expr: &'a runtime::Expr,
        expected: runtime::Type,
    },
    AsThunk {
        expr: &'a runtime::Expr,
        expected: runtime::Type,
    },
    ForceEffectful {
        expr: &'a runtime::Expr,
        expected: runtime::Type,
    },
}
```

すると `lower_expr` の direct call 部分は、

```rust
let plan = self.plan_direct_call(expr, target_path, info, args)?;
self.lower_direct_call_plan(plan)
```

にできる。

これは挙動を変えずにできる最初の大物リファクタ候補だねぇ。
理由は、今の boolean 群をそのまま `plan_*` に移すだけでも価値があるから。

---

# 3. depth counter は RAII guard にする

今のような形は、あとから分岐が増えると壊れやすい。

```rust
self.force_effectful_apply_depth += 1;
let result = lowerer(self);
self.force_effectful_apply_depth -= 1;
result
```

ここは Rust らしく guard にするのが安全だよ〜。

```rust
let _guard = self.enter_force_effectful_apply();
lowerer(self)
```

実装イメージはこう。

```rust
struct DepthGuard<'a> {
    value: &'a mut usize,
}

impl Drop for DepthGuard<'_> {
    fn drop(&mut self) {
        *self.value -= 1;
    }
}
```

ただし borrow が面倒になるなら、`Cell<usize>` にするか、専用メソッドで小さく閉じると良い。

```rust
fn with_force_effectful_apply_depth<T>(
    &mut self,
    f: impl FnOnce(&mut Self) -> CpsLowerResult<T>,
) -> CpsLowerResult<T> {
    self.force_effectful_apply_depth += 1;
    let result = f(self);
    self.force_effectful_apply_depth -= 1;
    result
}
```

この形でも十分。panic safety まで見るなら guard、借用の扱いやすさ優先なら `with_*` だねぇ。

---

# 4. Cranelift 側は巨大 match を「dispatch は一箇所、処理は分割」にする

`cps_repr_cranelift.rs` は、`lower_effect_stmt` と `lower_effect_terminator` がかなり重い。`Literal`、`ForceThunk`、tuple/record/variant、primitive、direct call、closure apply、resume、handler install が同じ match に並んでいる。

ただ、ここでいきなり visitor trait にすると逆に見通しが悪くなりそう。おすすめはこれ。

```rust
fn lower_effect_stmt<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, M, L>,
    stmt: &CpsStmt,
) -> CpsReprCraneliftResult<()> {
    match stmt {
        CpsStmt::Literal { .. }
        | CpsStmt::Primitive { .. }
        | CpsStmt::Tuple { .. }
        | CpsStmt::Record { .. }
        | CpsStmt::Variant { .. } => lower_value_stmt(cx, stmt),

        CpsStmt::DirectCall { .. }
        | CpsStmt::ApplyClosure { .. }
        | CpsStmt::ForceThunk { .. } => lower_call_stmt(cx, stmt),

        CpsStmt::Resume { .. }
        | CpsStmt::ResumeWithHandler { .. } => lower_resumption_stmt(cx, stmt),

        CpsStmt::InstallHandler { .. }
        | CpsStmt::UninstallHandler { .. } => lower_handler_stmt(cx, stmt),

        _ => lower_misc_stmt(cx, stmt),
    }
}
```

つまり、

* `match CpsStmt` は一箇所に残す
* exhaustive check は Rust にやらせる
* 各 arm の中身だけ module に逃がす
* 共通引数は `CpsCraneliftLowerCx` に束ねる

という形。

`lower_effect_terminator` も同じ。

```rust
mod stmt_lowering {
    mod value;
    mod calls;
    mod handlers;
    mod resumptions;
}

mod terminator_lowering {
    mod pure_control;
    mod perform;
    mod effectful_call;
    mod effectful_force;
    mod effectful_apply;
}
```

`EffectfulApply` の closure/resumption dynamic dispatch はかなり独立した論理だから、専用ファイルに出す価値が高い。今も runtime helper への移譲、resume continuation env、resumption/closure branch が全部ひと塊になっているから、ここは分離効果が大きい。

---

# 5. `LowerCx` を作って引数地獄を止める

今の Cranelift lowering は関数引数が多い。

```rust
module_backend,
builder,
function,
functions,
handlers,
literals,
values,
```

これを毎回渡すと、関数分割した瞬間にさらに見づらくなる。だから先に context を作ると良い。

```rust
struct CpsCraneliftLowerCx<'a, M: Module, L: CpsLiteralStore> {
    module_backend: &'a mut M,
    builder: &'a mut FunctionBuilder<'a>,
    function: &'a CpsReprAbiFunction,
    functions: &'a DeclaredFunctions,
    handlers: &'a HandlerRegistry,
    literals: &'a mut L,
    values: &'a mut LocalValueCache,
}
```

ただし `FunctionBuilder<'_>` の lifetime が面倒なら、最初は無理に全部まとめず、

```rust
struct CpsCraneliftEnv<'a> {
    function: &'a CpsReprAbiFunction,
    functions: &'a DeclaredFunctions,
    handlers: &'a HandlerRegistry,
}
```

くらいからでも良いよ〜。

---

# 6. fixed arity helper の選択を共通化する

Native 実装にはこういう形が何度も出てくる。

```rust
match env_len {
    0 => "..._0",
    1 => "..._1",
    2 => "..._2",
    3 => "..._3",
    4 => "..._4",
    _ => "..._many",
}
```

これは小さいけど、増殖すると魔境の燃料になる。

```rust
enum HelperArity {
    Fixed(usize),
    Many,
}

fn select_i64_arity_helper(prefix: &'static str, len: usize) -> (&'static str, HelperArity) {
    match len {
        0 => (concat_helper(prefix, "0"), HelperArity::Fixed(0)),
        1 => (concat_helper(prefix, "1"), HelperArity::Fixed(1)),
        2 => (concat_helper(prefix, "2"), HelperArity::Fixed(2)),
        3 => (concat_helper(prefix, "3"), HelperArity::Fixed(3)),
        4 => (concat_helper(prefix, "4"), HelperArity::Fixed(4)),
        _ => (concat_helper(prefix, "many"), HelperArity::Many),
    }
}
```

Rust だと `concat_helper` は実行時 String になるから、実際には static table のほうが楽かも。

```rust
struct FixedManyHelpers {
    fixed: [&'static str; 5],
    many: &'static str,
}

impl FixedManyHelpers {
    fn select(&self, len: usize) -> &'static str {
        self.fixed.get(len).copied().unwrap_or(self.many)
    }
}
```

これは地味だけど、handler env / thunk env / resumption env / install helper あたりで効く。

---

# 7. backend selection / unsupported reason は「能力表」に寄せる

Native CPS Mainline Plan では、native の本線を CPS repr に寄せ、value backend は effect-free fast path と helper 供給元として扱う方針が書かれている。さらに unsupported は structured reason を持つ方針になっている。

ここはリファクタ時にかなり大事。
条件分岐が増える理由の一つは、

```rust
if this_std_shape { ... }
if this_effectful_case { ... }
if this_value_backend_hole { ... }
```

みたいな「その場判定」が増えることだから、root / function / value ごとに能力表を先に作ると良い。

```rust
struct NativeCapability {
    has_effectful_control: bool,
    has_handler_boundary: bool,
    has_resumption_value: bool,
    has_thunk_value: bool,
    has_runtime_value_ptr: bool,
    has_structural_pattern_binding: bool,
    requires_cps_mainline: bool,
    value_backend_reason: Option<NativeBackendReason>,
}
```

ただし、これは雑に boolean を増やすとまた地獄になる。
本当はこういう enum のほうが良い。

```rust
enum NativeRequirement {
    EffectfulControl,
    HandlerBoundary,
    ResumptionValue,
    ThunkBoundaryEvidence,
    RuntimeValuePtr,
    ClosureValue,
    StructuralPatternBinding,
}
```

そして selection は、

```rust
requirements -> backend decision
```

にする。

---

# 8. direct-style islands は「最終整理」じゃなく「次の大きい逃げ道」

Direct-style islands の設計メモはかなり良い方向だと思う。CPS を捨てず、handler / resumption / thunk hygiene / local return は CPS に残し、effect-free な continuation subgraph だけ SSA として下ろす、という方針だねぇ。

これはリファクタとしても意味がある。

今は Cranelift 側が「すべての CPS node を同じ制御表現として扱う」から、effect-free な場所にも handler/resumption の文脈が染み込む。
island classifier が入ると、

```text
control boundary
direct-style island
control boundary
```

という切れ目ができる。

その結果、コード生成側も

```rust
lower_control_region(...)
lower_direct_island(...)
```

に分かれる。

ただし、これは最初にやると危険。まずは `lower_expr` と Cranelift lowering の分割で足場を作ってからがよさそう。

---

# 9. やっちゃ危ないリファクタ

ここははっきり止めたほうがよさそうだねぇ。

## 危ない 1: ファイル分割だけ

`cps_repr_cranelift.rs` を 10 ファイルに分けても、巨大 match と状態遷移がそのままなら、ただの分散魔境になる。

## 危ない 2: effectful / non-effectful を雑に trait で統合

見た目は似ていても、handler frame、eval context、scope return、abort routing が違う。
雑に抽象化すると「型は通るが意味論が割れる」タイプのバグが出ると思う。

## 危ない 3: std の関数名ベースの特例

failure matrix 側でも「関数名や module 名の文字列特例にしない」とあるけど、これは本当に守ったほうがいい。最初は楽でも、標準ライブラリの形が変わった瞬間に stale optimization になる。

## 危ない 4: optimizer と lowering を同時に触る

`cps_optimize` と Cranelift lowering を同時に変えると、どっちで壊れたか見えなくなる。
リファクタ初期は「IR は同じ、出力も同じ」を狙うのが安全だよ〜。

---

# 私なら最初の PR はこう切る

## PR 1: `DirectCallPlan` 抽出

対象は `cps_lower.rs` の direct apply 部分だけ。

* `plan_direct_call(...)` を作る
* boolean 群を `DirectCallPlan` に集める
* 実際の lowering はまだ同じ処理を呼ぶ
* regression は既存 native tests を回すだけ

これは挙動差分を小さくできる。

## PR 2: depth counter / handler context の guard 化

* `force_effectful_apply_depth`
* `sync_apply_for_immediate_force_depth`
* active handler scope

このへんを `with_*` にする。

## PR 3: `classify_expr` 導入

* `lower_expr` の上半分を `classify_expr` に移す
* `PlainExprKind` に落ちたら既存 match へ
* 分類順序は現状維持
* ここでも意味論は変えない

## PR 4: Cranelift `LowerCx` 導入

まだ分割しない。
まず引数束ねだけやる。

## PR 5: `lower_effect_stmt` をカテゴリ別 helper に分割

dispatch match は残す。
中身だけ `lower_value_stmt` / `lower_call_stmt` / `lower_handler_stmt` へ逃がす。

## PR 6: `lower_effect_terminator` を分割

`Perform`、`EffectfulCall`、`EffectfulForce`、`EffectfulApply` を専用 helper にする。
ここは壊れやすいから一個ずつがいい。

---

# 目標の形

最終的には、Native 実装をこういう責務に分けたい。

```text
cps_lower/
  classify_expr.rs        // runtime Expr を lowering case に分類
  direct_call_plan.rs     // direct/effectful call の判定
  demand.rs               // thunk/plain demand と force policy
  effect_context.rs       // handler / guard / depth state
  lower_expr.rs           // 実行本体

cps_repr_cranelift/
  mod.rs
  context.rs              // LowerCx
  symbols.rs              // runtime helper symbols
  helper_arity.rs          // _0.._4 / _many 選択
  stmt/
    value.rs
    call.rs
    handler.rs
    resumption.rs
  term/
    pure_control.rs
    perform.rs
    effectful_call.rs
    effectful_force.rs
    effectful_apply.rs
  island/
    classify.rs
    codegen.rs
```

これくらい切れると、「新しい条件を追加する場所」がかなり限定される。

---

## かなり短く言うと

Yulang Native のリファクタはできる。
ただし、狙うべきは **分割** じゃなくて **判定のデータ化** だねぇ。

最初の一手はこれが良さそう。

> `lower_expr` の direct apply 分岐から `DirectCallPlan` を抜く。

ここが抜けると、魔境の中心に最初の通路ができると思うよ〜。
