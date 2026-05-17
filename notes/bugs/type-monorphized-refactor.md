うん、リファクタの方向を変えた方がいいと思う。
今のバグ取りはかなり頑張っているけど、構造的には **「漏れたフィールドを見つけたら refresh / detector に足す」** になっていて、次の型付きフィールドが増えた瞬間また同じ形で壊れる。

あと、メモを見る限り私の前回指摘のうち `Lambda.param_effect_annotation` / `param_function_allowed_effects` は Type を持たないから detector 対象外、ここは私の前提がズレていたねぇ。`AddId.allowed`、`HandleEffect.residual_*`、evidence、pattern、global var refresh はもうかなり潰してあるっぽい。進捗メモでも、detector 強化、evidence refresh、pattern refresh、global `Var` refresh は DONE になっている。残りは `pass_through_associated_type_signature` の本実装と、fallback-to-old-`expr.ty` の失敗扱いが未着手として残っているねぇ。

## 結論：`monomorphize` は「型を直す pass 群」から「型契約を守る pipeline」へ寄せる

今の pipeline は、principal 経路だとだいたい

```text
inline wrappers
→ principal_elaborate
→ refresh closed schemes
→ prune
→ refresh_monomorphic_evidence
→ ensure_monomorphic_bindings
→ runtime invariant
→ validate
```

という流れだねぇ。出口で `refresh_monomorphic_evidence`、`ensure_monomorphic_bindings`、`check_runtime_invariants`、`validate_module` を走らせている。
でも、ここに後付け refresh が増えている時点で、pipeline の各 pass が同じ型契約を共有していないのが見えている。`refresh_monomorphic_evidence` も「証拠メタデータの inference vars が残るから出口で上書きする」という目的の pass になっていて、これは応急処置としては正しいけど、型情報の所有権が分散している問題は残る。

だから、リファクタの軸はこれ。

> **全 pass が直接 IR の型フィールドを好きに触るのをやめて、型付きフィールドの列挙・置換・投影・検査を一箇所に集める。**

## 提案 1：`type_surface.rs` を作る

まず `crates/yulang-runtime/src/monomorphize/pipeline/type_surface.rs` みたいなモジュールを足すのがよさそう。

役割は「runtime IR のどこに型が入っているか」を一元管理すること。

### 入れるもの

```rust
pub enum TypeSurfaceKind {
    ExprTy,
    PatternTy,
    BindingScheme,
    ApplyEvidence,
    JoinEvidence,
    TypeInstantiation,
    HandleEffect,
    ResumeBinding,
    ThunkEffect,
    ThunkValue,
    AddIdAllowed,
    CoerceFromTo,
}
```

みたいな分類を持たせて、以下を全部ここに寄せる。

```rust
pub fn collect_type_vars_in_module(module: &Module) -> BTreeSet<TypeVar>;
pub fn substitute_types_in_module(module: Module, subst: &Subst) -> Module;
pub fn project_runtime_types_in_module(module: Module, policy: ProjectPolicy) -> Module;
pub fn assert_no_residual_type_vars(module: &Module) -> RuntimeResult<()>;
pub fn assert_no_runtime_fallbacks(module: &Module, policy: FallbackPolicy) -> RuntimeResult<()>;
```

今は `collect_expr_type_vars` が `types/shape.rs` 側、`substitute_expr` が `pipeline/substitute.rs`、`project_expr_runtime_types` が `local_refresh.rs`、`refresh_monomorphic_evidence` が `refresh.rs` に散っている。これだと「collect は見るけど substitute は見ない」「substitute は見るけど project は見ない」が起きる。型付き surface の列挙だけは一箇所に置くのがいい。

## 提案 2：visitor じゃなく、最初は “型 surface 専用 walker” にする

いきなり汎用 IR visitor にすると重い。
最初は `TypeSurfaceWalker` だけでいいと思う。

```rust
trait TypeSurfaceFolder {
    fn fold_runtime_type(&mut self, ty: RuntimeType, site: TypeSurfaceSite) -> RuntimeType;
    fn fold_core_type(&mut self, ty: typed_ir::Type, site: TypeSurfaceSite) -> typed_ir::Type;
    fn fold_type_bounds(
        &mut self,
        bounds: typed_ir::TypeBounds,
        site: TypeSurfaceSite,
    ) -> typed_ir::TypeBounds;
}
```

これを使って、

```rust
SubstituteTypes
ProjectRuntimeTypes
CollectResidualVars
RefreshEvidence
RejectFallbacks
```

を同じ traversal から派生させる。

ポイントは **同じ traversal を使う** こと。
collector と substitutor と projector が別々の match を持っている限り、また漏れる。

## 提案 3：`refresh_monomorphic_evidence` を “出口の小細工” から “evidence lowering” に昇格する

今の `refresh_monomorphic_evidence` は正直かなりよく効く応急処置だと思う。Apply/If/Match/Handle の evidence を周囲の `Expr.ty` に合わせて書き換えて、`principal_elaboration` など VM が使わないものを落としている。

ただし名前と位置が弱い。
これは `refresh` じゃなくて **monomorphized IR における evidence の正規化** だよねぇ。

名前をこう変えるのがよさそう。

```rust
normalize_monomorphized_metadata(module)
```

または

```rust
lower_monomorphized_evidence(module)
```

そして契約を明文化する。

```text
Monomorphized IR では:
- ApplyEvidence は validate/runtime に必要な最小情報だけ保持
- principal_elaboration / substitution_candidates は消す
- TypeInstantiation は VM が読まないなら消すか、完全 concrete にする
- JoinEvidence.result は Expr.ty と一致
- Handle.evidence.result は Expr.ty と一致
```

`refresh_monomorphic_evidence` は今すでにこの方向なので、これは大改造というより「役割の格上げ」だねぇ。

## 提案 4：`ensure_monomorphic_bindings` を `audit_monomorphized_module` に置き換える

今の `ensure_monomorphic_bindings` は、binding の `type_params`、body の型変数、scheme、requirements を見る。
でも本当に欲しいのは「monomorphized IR として成立しているか」の総合監査。

新しい出口はこうしたい。

```rust
pub fn audit_monomorphized_module(module: &Module) -> RuntimeResult<()> {
    audit_no_type_params(module)?;
    audit_no_residual_type_vars(module)?;
    audit_no_runtime_unknown_in_required_sites(module)?;
    audit_evidence_is_normalized(module)?;
    audit_scheme_matches_body(module)?;
    audit_runtime_shapes(module)?;
    Ok(())
}
```

特に大事なのは `Unknown` の扱い。

型変数が消えていても `Unknown` / fallback `Any` が残っていたら「型が入ってない」ことがある。今の invariant checker は `BeforeVm` では strict value types を見られるけど、monomorphize 通常出口では別関数扱いになっている。

おすすめは `FallbackPolicy` を分けること。

```rust
enum FallbackPolicy {
    AllowRuntimeFallback,        // lowered/refine 中
    AllowEffectOnlyFallback,     // monomorphize 中間
    RejectValueFallback,         // monomorphized 出口
    RejectAllFallback,           // before VM
}
```

これで「いつから Unknown を許さないか」を pass ごとに明示できる。

## 提案 5：fallback-to-old-`expr.ty` を “明示的な Error” に変える

未着手に残っている #8 は、リファクタの中核だと思う。

今の `project_expr_runtime_type_from_kind` は、Apply の戻り型が取れないと fallback の古い型を残す。Match は最初の arm body 型で済ませる。Lambda は body 側が弱いと古い return を温存する。

これを全部いきなり strict にすると壊れそうだから、二段階がよさそう。

### Phase A: 計測

```rust
enum TypeProjectionFallbackReason {
    ApplyCalleeNotFunction,
    MatchNoArms,
    MatchArmMismatch,
    LambdaBodyImprecise,
    SelectBaseNotRecord,
}
```

を作って、fallback したら profile に入れる。

```rust
TypeProjectionReport {
    fallbacks: Vec<TypeProjectionFallback>,
}
```

### Phase B: monomorphized 出口だけ strict

中間 pass では許す。出口では落とす。

```rust
YULANG_STRICT_MONO_TYPE_FALLBACK=1
```

を先に足して、green になったら default ON。

Effect hole collapse で既に「計測→strict opt-in」のパターンが入っているから、それと同じ進め方でいい。メモでも strict effect hole は production 影響が薄そう、という計測が出ている。

## 提案 6：principal 経路と legacy demand 経路の契約を分ける

今は `MonomorphizeMode` が `PrincipalElaborate` と `LegacyDemandFixpoint` を切り替えている。default は principal、環境変数で legacy。

リファクタではこの2つを同じ品質基準で混ぜない方がいい。

```text
principal/
  plan.rs
  complete.rs
  specialize.rs
  rewrite.rs

legacy_demand/
  collect.rs
  check.rs
  emit.rs
  queue.rs

common/
  type_surface.rs
  normalize_metadata.rs
  audit.rs
  paths.rs
```

大事なのは、**common の audit を両方に通す**こと。
legacy は多少 lenient でもいいけど、出口の monomorphized IR 契約だけは同じにする。

## 提案 7：`principal_unify.rs` を分割する

`principal_unify.rs` は今かなり巨大で、役割が混ざっている。
ここはバグ温床になりやすい。

分け方はこう。

```text
principal/
  mod.rs
  engine.rs              // PrincipalUnifier の top-level run
  plan.rs                // principal_elaboration_plan_for_expr 系
  complete.rs            // complete_plan_from_* 系
  rewrite_expr.rs        // rewrite_expr / rewrite_stmt / local context
  emit.rs                // intern_specialization / emit_pending_specialization
  role.rs                // role impl dispatch
  handler.rs             // handler adapter
  profile.rs             // stats/timing
```

特に `rewrite_expr` と `complete_plan_from_*` は分けたい。
今は「式を書き換える」「plan を補完する」「specialization を emit する」「profile を取る」が一つの構造体に絡んでいる。これだと、型 fallback をどこで許したか追跡しにくい。

## 提案 8：`BindingEnv` と `TypeEnv` を明示する

今の principal rewrite は、local type、emitted specialization、monomorphic binding type を個別関数で引いている。`Var` arm も local → emitted → fallback みたいな構造になっていた。メモを見ると monomorphic binding fallback は保守的に入れたっぽいねぇ。

ここは環境を明示すると壊れにくい。

```rust
struct MonoEnv {
    bindings: BindingEnv,
    locals: LocalTypeEnv,
    specializations: SpecializationEnv,
    active: ActiveSpecializationStack,
}

impl MonoEnv {
    fn resolve_value_path(&self, path: &typed_ir::Path, current_ty: &RuntimeType)
        -> ResolvedValueType;
}
```

戻り値も `Option<RuntimeType>` じゃなくて理由付きにする。

```rust
enum ResolvedValueType {
    Local(RuntimeType),
    EmittedSpecialization(RuntimeType),
    MonomorphicBinding(RuntimeType),
    KeepCurrent { reason: KeepCurrentReason },
    Unknown,
}
```

こうすると「なぜ古い `Expr.ty` を温存したか」が profile に残る。

## 提案 9：`scheme` refresh を “body.ty から再構成” しすぎない

`refresh_closed_specialized_schemes` は specialized path や一部 helper の scheme を body 型から作り直す。
これは便利だけど、body 型がまだ揺れている段階で scheme を作ると、間違った scheme が正規化済み扱いになる。

提案は、scheme refresh に policy を足すこと。

```rust
enum SchemeRefreshPolicy {
    PreserveIfExistingPrecise,
    RefreshFromBodyIfClosed,
    RequireBodySchemeAgreement,
}
```

monomorphize 中間では `RefreshFromBodyIfClosed`、出口では `RequireBodySchemeAgreement`。

```rust
fn audit_binding_scheme_matches_body(binding: &Binding) -> RuntimeResult<()> {
    let body_core = runtime_core_type(&binding.body.ty);
    if !core_types_compatible(&binding.scheme.body, &body_core) {
        return Err(...);
    }
    Ok(())
}
```

「scheme を直す pass」と「scheme が正しいか見る audit」を分けるのが肝だねぇ。

## 提案 10：テストは “個別バグ再現” より “surface の網羅性” を見る

ここが一番効く。

### 1. surface parity test

`collect`、`substitute`、`project`、`audit` が同じ型付き surface を見ることをテストする。

```rust
#[test]
fn type_surface_collector_and_substituter_cover_same_sites() {
    let module = fixture_with_every_type_surface();
    let collected_sites = collect_type_surface_sites(&module);
    let substituted_sites = substitute_type_surface_sites(&module);
    assert_eq!(collected_sites, substituted_sites);
}
```

### 2. poison type test

すべての型付きフィールドに `Type::Var("__poison")` を入れる fixture を作る。
monomorphized audit が全部拾うことを見る。

```rust
#[test]
fn monomorphized_audit_rejects_poison_in_every_type_surface() {
    for module in poison_each_type_surface_fixture() {
        assert!(audit_monomorphized_module(&module).is_err());
    }
}
```

### 3. fallback telemetry test

fallback-to-old-`expr.ty` が発生したら profile に出ることを見る。

```rust
#[test]
fn type_projection_reports_apply_fallback() {
    let report = project_runtime_types_with_report(bad_apply_fixture());
    assert!(report.has(TypeProjectionFallbackReason::ApplyCalleeNotFunction));
}
```

### 4. golden “normalization removes inference metadata” test

`refresh_monomorphic_evidence` 改め `normalize_monomorphized_metadata` が、evidence の inference candidates や principal plan を落とすことを snapshot で固定する。

## 移行順

### Step 1: `type_surface.rs` だけ足す

既存 pass は触らず、まず collector だけ作る。

```rust
collect_type_surfaces(&module) -> Vec<TypeSurfaceSite>
collect_residual_type_vars_via_surface(&module)
```

今の `collect_expr_type_vars` と比較して、差分を出すテストを入れる。

### Step 2: `ensure_monomorphic_bindings` を surface collector ベースに置き換える

ここは比較的安全。
現状の checker と同じ結果を出しつつ、site 情報をエラーに載せる。

```rust
ResidualType {
    path: BindingPath,
    site: TypeSurfaceSite,
    vars: Vec<TypeVar>,
}
```

これで「どこに残ったか」が分かる。デバッグ効率が上がる。

### Step 3: `refresh_monomorphic_evidence` を `normalize_monomorphized_metadata` に改名・拡張

今の機能は残す。
ただし evidence だけでなく、TypeInstantiation / JoinEvidence / Handle evidence を “monomorphized metadata contract” として扱う。現状すでに Apply/If/Match/Handle の evidence を触っているので、ここは自然。

### Step 4: `project_runtime_expr_types` を report 付きにする

`project_runtime_expr_types(expr)` を残しつつ、

```rust
project_runtime_expr_types_with_report(expr) -> (Expr, TypeProjectionReport)
```

を足す。最初は report だけで落とさない。

### Step 5: strict fallback を opt-in にする

`YULANG_STRICT_MONO_TYPE_FALLBACK=1` で落とす。
CI ではまず nightly 的に回す。green になったら default ON。

### Step 6: `principal_unify.rs` 分割

これは最後でいい。
先に surface/audit を作っておくと、分割時に壊しても出口で拾える。

## かなり具体的な新しい pipeline

principal 経路はこうしたい。

```text
inline_polymorphic_wrappers
→ principal_elaborate
→ normalize_local_runtime_types
→ refresh_closed_schemes
→ normalize_monomorphized_metadata
→ prune_unreachable
→ audit_monomorphized_module
→ validate_module
```

legacy 経路はこう。

```text
legacy_demand_fixpoint
→ refine_types
→ refresh_closed_schemes
→ normalize_monomorphized_metadata
→ prune_unreachable
→ audit_monomorphized_module
→ validate_module
```

今の code では principal 経路が `InlinePolymorphicWrappers → PrincipalElaborate → RefreshClosedSchemes → PruneUnreachable` で、legacy は demand/refine/refresh/prune の fixpoint を持っている。
この構造自体は残して、**両経路の最後に同じ normalize/audit を通す**のがいい。

## やらない方がよさそうなリファクタ

### 1. `Expr.ty` を消して毎回再計算

一見きれいだけど、Yulang の runtime IR は thunk shape / effect hygiene を保持する必要がある。pipeline のコメントにも「runtime lowering が導入した thunk shape と effect hygiene を消した型から再構成するな」とある。
だから `Expr.ty` を消すより、`Expr.ty` と metadata の契約を強くする方が安全。

### 2. legacy demand を今すぐ全削除

気持ちは分かるけど、比較対象として残っている価値がある。
ただし `legacy_demand/` に隔離して、出口契約は principal と同じにするのがよさそう。

### 3. すべてを validate に押し込む

validate は「言語意味として型が合うか」を見る場所。
monomorphize 固有の「inference metadata が残っていない」「fallback を温存していない」は、`audit_monomorphized_module` の責務にした方が読みやすい。

## 最終的な狙い

このリファクタのゴールはこれだねぇ。

```text
バグ修正前:
  型が残っている場所を見つける
  → その場所だけ refresh / detector に足す

リファクタ後:
  型が存在する場所は TypeSurface で列挙済み
  → substitute / project / refresh / audit が同じ surface を見る
  → 新しい型付きフィールドを足したら compile/test が落ちる
```

今の失敗は、たぶん実装者の不注意じゃなくて、構造が「漏れやすい」んだと思う。
だから一番効くのは、`monomorphize` の賢さを上げることじゃなくて、**型付きフィールドの網羅性を機械的に保つ足場**を作ることだよ〜
