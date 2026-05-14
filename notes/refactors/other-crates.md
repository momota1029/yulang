# 余剰コンパイラクレートのコード臭レポート

Yulang コンパイラの周辺クレート群からは、段階的な拡張による積層化の跡が目立ちます。CPS表現の Cranelift 統合は機械的な記号定義が冗長に詰まっており、large-file 臭（8600 行）と マッチ網羅の爆発が目立ちます。CLI（main.rs）は 5880 行で、パイプライン制御が複雑に分散しており、boolean 群の管理が脆弱です。ネイティブ側では大型関数（200+ 行）が構造的パターンマッチの深さで複雑化しており、特に effectful/non-effectful 系統の二重実装が疑わしいです。

---

# yulang-native

## 1. cps_repr_cranelift.rs: 503 行の単一大型関数 + 記号定義の機械的繰り返し

- **場所**: `crates/yulang-native/src/cps_repr_cranelift.rs:205`
- **匂い**: 単一ファイル 8680 行、大型関数、機械的ボイラープレート

```rust
pub fn compile_cps_repr_abi_module(
    module: &CpsReprAbiModule,
) -> CpsReprCraneliftResult<CpsReprJitModule> {
    validate_scalar_subset(module)?;

    let mut builder =
        JITBuilder::new(cranelift_module::default_libcall_names()).map_err(cranelift_error)?;
    builder.symbol(
        "yulang_cps_make_resumption_i64_0",
        yulang_cps_make_resumption_i64_0 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_resumption_i64_1",
        yulang_cps_make_resumption_i64_1 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_resumption_i64_2",
        yulang_cps_make_resumption_i64_2 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_resumption_i64_3",
        yulang_cps_make_resumption_i64_3 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_resumption_i64_4",
        yulang_cps_make_resumption_i64_4 as *const u8,
    );
    // ... 60+ more near-identical builder.symbol() calls
```

**所感**: ファイル自体が責務を持ちすぎており、「型バリアント毎の Cranelift 生成」「記号テーブル構築」「実行ロジック」が混在してます。記号群は macro か別ファイルへ抽出するかもね。

---

## 2. cps_repr_cranelift.rs: 348 行の効果マッチ分散

- **場所**: `crates/yulang-native/src/cps_repr_cranelift.rs:1321,1698`
- **匂い**: 重複したマッチ分岐（effectful/non-effectful 両系統）

```rust
// lower_effect_stmt: 348 lines with full CpsStmt match
fn lower_effect_stmt<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    stmt: &CpsStmt,
    functions: &DeclaredFunctions,
    handlers: &HandlerRegistry,
    literals: &mut L,
    values: &mut LocalValueCache,
) -> CpsReprCraneliftResult<()> {
    match stmt {
        CpsStmt::Literal { dest, literal } => { ... }
        CpsStmt::FreshGuard { dest, .. } => { ... }
        CpsStmt::PeekGuard { dest } => { ... }
        CpsStmt::FindGuard { dest, guard } => { ... }
        CpsStmt::MakeThunk { dest, entry } => { ... }
        // ... 20+ more arms
    }
}

// lower_effect_terminator: 348 lines with another big match
fn lower_effect_terminator<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    continuation: &CpsReprAbiContinuation,
    functions: &DeclaredFunctions,
    handlers: &HandlerRegistry,
    _values: &mut LocalValueCache,
) -> CpsReprCraneliftResult<()> {
    match &continuation.terminator {
        CpsTerminator::Return(value) => { ... }
        CpsTerminator::Continue { target, args } => { ... }
        CpsTerminator::Branch { cond, then_cont, else_cont } => { ... }
        CpsTerminator::Perform { ... } => { ... }
        // ... 多くの arms は lower_stmt の対応物と実質同じロジック
    }
}
```

**所感**: effectful 版と普通版が parallel に存在してて、arm 対応がプリペアド状態。ポリモルフィズムか特性化で統一できそうかな。

---

## 3. cps_lower.rs: 246 行の lower_expr メソッド内の条件爆発

- **場所**: `crates/yulang-native/src/cps_lower.rs:1276`
- **匂い**: 大型関数、深い条件判定の塔、状態フラグの跨ぎ

```rust
fn lower_expr(&mut self, expr: &runtime::Expr) -> CpsLowerResult<CpsValueId> {
    if let Some((body, arms)) = inline_thunk_handler_apply(expr, self.functions, self.bindings) {
        return self.lower_handle(&body, &arms);
    }
    if let Some(value) = self.lower_local_expr_apply(expr)? {
        return Ok(value);
    }
    if let Some(request) = effect_apply_body_request(expr) {
        let (expected_effects, handler) =
            self.effect_context_for_request(&request, &[], dynamic_handler_id());
        let (_, value) =
            self.begin_resume_after_perform(request, &expected_effects, handler)?;
        return Ok(value);
    }
    if let runtime::ExprKind::BindHere { expr } = &expr.kind {
        return self.lower_bind_here(expr);
    }
    if let Some((op, args)) = primitive_apply(expr) {
        // ... arity check, lowering, ...
    }
    if let Some((target_path, info, args)) = direct_apply_path(expr, self.functions)? {
        // ... 100+ lines of direct call decision logic
        if should_inline_direct { ... }
        let should_inline_direct = ...;
        let force_handler_reentry_args = ...;
        // ... マッチが入れ子化、状態トラッキング複雑
    }
    // ... さらに if let が続く
}
```

**所感**: 「どのパターンに該当するか」の検査が順序依存で並んでて、reachability が曖昧に。early-return のチェーンも保守性悪いかも。

---

## 4. cps_eval.rs: legacy 関数の存在

- **場所**: `crates/yulang-native/src/cps_eval.rs:1928`
- **匂い**: 名前の "_legacy"、古い実装の存続

```rust
fn inject_extra_handlers_legacy(
    frames: &[CpsReturnFrame],
    extra: &[CpsHandlerFrame],
) -> Vec<CpsReturnFrame> {
    if extra.is_empty() {
        return frames.to_vec();
    }
    frames
        .iter()
        .map(|frame| {
            let mut adjusted = frame.clone();
            for handler in extra {
                if !adjusted
                    .active_handlers
                    .iter()
                    .any(|h| h.prompt == handler.prompt)
                {
                    adjusted.active_handlers.push(handler.clone());
                }
            }
            adjusted
        })
        .collect()
}

// すぐ下に更新版がある:
fn merge_extras_into_frames(
    frames: &[CpsReturnFrame],
    current: &[CpsHandlerFrame],
    anchor: Option<CpsHandlerAnchor>,
) -> Vec<CpsReturnFrame> { ... }
```

**所感**: legacy 版と新版が同じモジュール内に並存。移行済みなら削除、未完なら TODO コメント欲しいなぁ。

---

## 5. cps_repr_cranelift.rs: expect/unwrap の鎖

- **場所**: `crates/yulang-native/src/cps_repr_cranelift.rs:6569,7394` (テストでも多数)
- **匂い**: テストでの無条件 expect、前提条件が不明確

```rust
let meta = meta.as_ref().expect("is_real implies meta");
let top = frames.last().expect("pre-force called with no frame");

// テスト内:
let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");
jit.run_roots_i64().expect("ran")
```

**所感**: テスト内は許容として、ランタイム呼び出し時の expect（"compiled"）は不自然。エラーハンドリング経路が隠れやすい。

---

# yulang (CLI binary)

## 6. main.rs: 5881 行の単一ファイル、パイプライン制御が分散

- **場所**: `crates/yulang/src/main.rs` (全体)
- **匂い**: CLI setup / inference / runtime / native が全て同一ファイル

```rust
fn run(options: &CliOptions) {
    if options.install_std { ... return; }
    if options.server { ... return; }
    
    for iteration in 0..options.profile_repeat {
        let emit_output = iteration + 1 == options.profile_repeat;
        
        if let Some(mode) = options.parse_mode {
            if emit_output { run_parser_view(mode, &source); }
            continue;
        }
        
        let run_semantic_pipeline = options.requests_semantic_pipeline();
        if run_semantic_pipeline && has_invalid_token(&root) { ... }
        
        if run_semantic_pipeline {
            run_infer_views(options.path.as_deref(), &root, &source, options, emit_output);
            continue;
        }
    }
}
```

**所感**: 各パイプライン段階の判定（requests_semantic_pipeline, requests_runtime_pipeline）が options の boolean 群から動的に決定され、flow が追いづらい。モード列挙 + match ベースにしたら堅牢になりそう。

---

## 7. main.rs: 436 行の run_infer_views 関数

- **場所**: `crates/yulang/src/main.rs:659`
- **匂い**: 大型関数、複数の出力フェーズが混在

```rust
fn run_infer_views(
    path: Option<&str>,
    root: &SyntaxNode<YulangLanguage>,
    source: &str,
    options: &CliOptions,
    emit_output: bool,  // <- boolean 引数
) {
    let (mut state, diagnostic_source, lower_profile) =
        lower_infer_sources(path, root, source, options);
    
    let finalized = with_infer_profile_enabled(options.infer_phase_timings, || {
        state.finalize_compact_results_profiled()
    });
    
    let errors = state.infer.type_errors();
    let (rendered, render_duration, binding_names, quantified_counts) = 
        if options.infer {
            // 120 lines of collection + formatting
        } else {
            (None, Duration::ZERO, None, None)
        };
    
    let infer_program = 
        if errors.is_empty() && surface_diagnostics.is_empty() && requests_runtime_pipeline {
            Some(export_core_program(&mut state))
        } else {
            None
        };
    
    if emit_output {
        // 50+ lines of output generation
    }
    // ... runtime pipeline branch continues
}
```

**所感**: emit_output という boolean で「表示するか」を制御する設計、テストと実行が分岐してる。出力フェーズを分離したら読みやすくなりそう。

---

## 8. main.rs: print_principal_elaborate_profile など、プロファイル出力関数の重複コード

- **場所**: `crates/yulang/src/main.rs:2092,2308,2499`
- **匂い**: 反復的なソート + フォーマット + eprintln パターン

```rust
fn print_principal_elaborate_profile(profile: &runtime::MonomorphizePassProfile) {
    let subst = &profile.principal_elaborate;
    if subst.stats.is_empty() && subst.timings.is_empty()
        && subst.target_skips.is_empty() && subst.target_rewrites.is_empty() {
        return;
    }
    let mut stats = subst.stats.iter().collect::<Vec<_>>();
    stats.sort_by(|(left_key, left_count), (right_key, right_count)| {
        right_count.cmp(left_count).then_with(|| left_key.cmp(right_key))
    });
    let stats = stats.into_iter().take(16)
        .map(|(key, count)| format!("{key}={count}"))
        .collect::<Vec<_>>().join(", ");
    eprintln!("            principal_elaborate: {stats}");
    
    if !subst.timings.is_empty() {
        let mut timings = subst.timings.iter().collect::<Vec<_>>();
        timings.sort_by(|(left_key, left_duration), (right_key, right_duration)| {
            right_duration.cmp(left_duration).then_with(|| left_key.cmp(right_key))
        });
        let timings = timings.into_iter().take(12)
            .map(|(key, duration)| format!("{key}={}", format_duration(*duration)))
            .collect::<Vec<_>>().join(", ");
        eprintln!("                timings: {timings}");
    }
    // ...
}

// 類似の函数が multiple times（print_runtime_phase_timings など）
```

**所感**: ソート+フォーマット+出力のパターンがコピペ化。generic table formatter とか trait で抽象化できたら DRY になりそう。

---

# yulang-sources

## 9. lib.rs: 102 行の collect_use_group_imports など、深い再帰的 AST 遍歩

- **場所**: `crates/yulang-sources/src/lib.rs:1928`
- **匂い**: 複雑な use-import parsing logic の局所化

```rust
fn collect_use_group_imports(
    node: &SyntaxNode<YulangLanguage>
) -> Vec<UseImport> {
    // 102 行で use グループをパース、プレフィックス計算、
    // 再帰的な子 tree 遍歩を同時実行
    // 末尾 collector パターンで state を pass-through
}
```

**所感**: 構文木遍歩と semantic 変換が混在。visitor pattern か fold signature で分離できそうかな。

---

# yulang-wasm

## 10. lib.rs: shared mutable state (SOURCE_LOWER_CACHE) の不透明な使用

- **場所**: `crates/yulang-wasm/src/lib.rs:52`
- **匂い**: thread_local RefCell への write-through cache

```rust
#[wasm_bindgen]
pub fn clear_std_cache() {
    SOURCE_LOWER_CACHE.with(|cache| {
        *cache.borrow_mut() = SourceLowerCache::default();
    });
}

// どこで populated されるのか、invalidation ルールが不明確
```

**所感**: キャッシュの有効期限や invalidation invariant が暗黙的。concurrent access に弱いし、テスタビリティも落ちやすいです。

---

## 11. semantic_tokens.rs: 1043 行で色付けルール網羅

- **場所**: `crates/yulang-editor/src/semantic_tokens.rs`
- **匂い**: 大型ファイル、token kind → color のマッピングが命令的

```rust
pub fn compute_with_op_table_and_highlights(
    source: &str,
    op_table: Option<OpTable>,
    highlights: Option<&ResolvedHighlightInfo>,
) -> Vec<u32> {
    let green = yulang_parser::parse_module_to_green_with_ops(
        source,
        op_table.unwrap_or_else(standard_op_table),
    );
    let root = SyntaxNode::<YulangLanguage>::new_root(green);
    let line_starts = line_starts(source);

    let mut raw: Vec<(u32, u32, u32, u32)> = Vec::new();
    raw.extend(lexical_tokens(source, &line_starts));

    for node_or_token in root.descendants_with_tokens() {
        // ... 100+ 行の match stmt on SyntaxKind
    }
}
```

**所感**: token kind の match が長くて、新しい種別追加時に一箇所の change でいいのか不明確。data-driven approach（lookup table）だと保守性上がりそう。

---

# yulang-typed-ir

## 12. types.rs / expr.rs: 小型だが高密度な型定義

- **場所**: `crates/yulang-typed-ir/src/types.rs:401`, `expr.rs:613`
- **匂い**: enum が大きく、variant 数が多い（都度 match 疲れ）

構造的には健全だが、新機能追加時に全 match 網羅の負担が大。

---

# 横断的な観察

### boolean パラメータの過多（main.rs CliOptions）
- `show_cst: bool, parse_mode: Option<ParserMode>, infer: bool, core_ir: bool, runtime_ir: bool, ...` × 14 個
- state machine か mode enum に統合したら制御流が明確化するかも。

### 効果系とスカラー系の二重実装
- `lower_effect_stmt` / `lower_stmt`、`lower_effect_terminator` / `lower_terminator` が cps_repr_cranelift に両存
- ポリモルフィズムで統一化できる匂いが濃い。

