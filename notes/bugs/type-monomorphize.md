## 進捗メモ（2026-05-17）

**strict fallback 削減デバッグ（effect payload / tuple context）— PARTIAL**

- handler adapter plan の consumed effect refinement で、signature 由来の
  precise payload effect と call-site 由来の coarse / unknown 同一 path effect を
  並べて残さないようにした。`out` と `out<str>` のような row では、同じ path の
  precise item を優先する。
- 空 arg の effect item を payload `unit` と決め打ちする変更は戻した。
  coarse effect は「payload が unit」ではなく「payload 情報が無い」場合があるため、
  unit は `Pattern::Wildcard` の補助 context にだけ使う。
- handler adapter 適用後に、handler の `residual_before` から arm payload pattern を
  再同期する pass を追加した。adapter が body rewrite より後で handler residual を
  concrete 化する経路のための同期。
- tuple expression の result context を item context に分解するようにした。
  `(result, entries)` のような tail tuple で、外側 expected tuple から local-use context を
  回収できるようにするため。
- 試したが戻したもの:
  - `rewrite_first_handle` を `Block` / `Thunk` へ深く降ろして
    `plan.consumes` と一致する handler を探す変更。`vm_runs_source_handler_guard_falls_through_to_next_arm`
    の normal test で residual polymorphic binding を作ったため、この turn では採用しない。
- 確認:
  - `RUSTC_WRAPPER= cargo test -q -p yulang-runtime` → **364 passed**
  - `YULANG_STRICT_MONO_RUNTIME_TYPES=1 RUSTC_WRAPPER= cargo test -q -p yulang-runtime`
    → **308 passed / 56 failed**
- 残りの観測:
  - `runtime_lowers_handler_wildcard_result_join_after_let_bind` は strict で
    `handle.arm[0].payload: Core(Unknown)` まで進む。
  - `run_into_strings` の handler plan 自体は `log<str>` を持つが、local ref handler
    などが絡むと、生成済み log handle へ adapter を当てる順序がまだ足りない。
    次は「handler adapter をどの生成段階の handle に適用するか」を、first-handle
    探索ではなく handler boundary の所有情報として整理するのがよさそう。

**strict fallback 削減デバッグ（contextual projection / handler payload）— PARTIAL**

- strict bucket の単発個数ではなく、`YULANG_STRICT_MONO_RUNTIME_TYPES=1`
  で通る VM test 数を指標にして小さく進めた。
- 追加した一般規則:
  - monomorphic binding rewrite に、閉じた binding scheme body を
    result context として渡す。
  - `BindHere` / `Handle` は、上位 result context があるとき
    `Unknown` fallback を concrete value 型で埋めてから子を rewrite する。
  - Apply / force projection は、callee / thunk value から再投影した型が
    `Unknown` で、既存 `Expr.ty` が concrete なら既存型を温存する。
  - contextual specialization key に output shape を含め、handler adapter
    適用後の emitted binding scheme/body にも output shape を戻す。
  - handler arm payload は `handler.residual_before` の consumed effect row から
    operation payload 型を引ける場合、payload pattern にその expected 型を流す。
- handler binding の input shape は body thunk の abort value（`Never`）に引っ張られると
  effect payload 推定を壊すため、handler body context へは押し込まない。
- 確認:
  - `RUSTC_WRAPPER= cargo test -q -p yulang-runtime` → **364 passed**
  - `YULANG_STRICT_MONO_RUNTIME_TYPES=1 RUSTC_WRAPPER= cargo test -q -p yulang-runtime`
    → **298 passed / 66 failed**（baseline **289 passed / 70 failed** から 4 件改善）
- 残りの代表 bucket:
  - handler arm payload がまだ `Core(Unknown)` になる経路
  - effectful helper / var ref helper の `apply.callee` parameter `Unknown`
  - `undet::each` の thunk value `Unknown`
  - list / opt / result helper の item payload `Unknown`
- `vm_runs_source_sub_return_nullfix_unit` はまだ strict では落ちる。
  現在の先頭 failure は `binding f/lambda/bind_here: Thunk { effect: Never, value: Unknown }`。
  ここは source の `return` thunk が abort value `Never` を持つことと、
  handler output / payload の concrete 化が途中で再び `Unknown` へ戻ることが絡んでいる。

**TypeSurface collector の入口化（refactor #1）— DONE**

- `monomorphize/pipeline/type_surface.rs` を追加し、binding の runtime 型付き surface
  （binding scheme / requirements / `Expr.ty` / pattern / evidence / instantiation /
  handler residual / resume / thunk / `AddId.allowed` / coerce）を一箇所で走査する
  collector に切り出した。
- `ensure_monomorphic_bindings` の residual type-var 検査を、この collector 経由に変更。
  既存の意味論は変えず、今後 substitute / project / audit を同じ surface 定義へ寄せる
  足場にする。
- `TypeSurfaceResidual { site, vars }` を導入し、collector が site 付き residual を
  返すようにした。通常の error は従来通り vars の union だけを使うが、
  `YULANG_DEBUG_MONO_PIPELINE=1` では binding ごとの residual site を追える。
- regression として、`AddId.allowed` と pattern の残留型変数が正しい
  `TypeSurfaceSite` で報告されることを固定した。
- 確認:
  - `RUSTC_WRAPPER= cargo check -q -p yulang-runtime`
  - `RUSTC_WRAPPER= cargo test -q -p yulang-runtime` → **361 passed**
  - `YULANG_STRICT_MONO_RUNTIME_TYPES=1 RUSTC_WRAPPER= cargo test -q -p yulang-runtime`
    → **289 passed / 70 failed**（baseline から変化なし）

**monomorphized metadata 正規化 pass の命名整理（refactor #2）— DONE**

- `refresh_monomorphic_evidence` を `normalize_monomorphized_metadata` に rename。
  これは型推論ではなく、monomorphized IR の evidence / instantiation metadata を
  validate/runtime が読む最小 concrete 形へ正規化する pass なので、役割名を合わせた。
- pipeline 出口の呼び出し名も `ensure_monomorphic_bindings` から
  `audit_monomorphized_module` に寄せた。現時点の実体は既存 residual type-var
  検査だが、ここへ strict fallback / scheme-body agreement を足していく。
- 既存挙動は維持。次に TypeSurface walker へ寄せる対象として、この pass の責務を
  明文化した。

**type projection fallback telemetry（refactor #3）— DONE**

- `monomorphize/type_projection_metrics.rs` を追加し、runtime type projection が
  rewritten children から型を導けず、既存 `Expr.ty` を温存した箇所を opt-in で
  数えられるようにした。
- `YULANG_REPORT_TYPE_PROJECTION_FALLBACKS=1` で `monomorphize_module` /
  `monomorphize_module_profiled` ごとに以下の counter を出す：
  - `if_branch_mismatch`
  - `match_no_arms`
  - `apply_callee_not_function`
  - `bind_here_not_thunk`
  - `lambda_projected_unknown`
  - `lambda_projected_unit`
- 通常実行では counter 自体を無効化するため、projection の hot path に
  atomic increment を乗せない。挙動変更なしの観測口として使う。
- 単発確認:
  - `YULANG_REPORT_TYPE_PROJECTION_FALLBACKS=1 RUSTC_WRAPPER= cargo test -q -p yulang-runtime vm_runs_source_sub_return_nullfix_unit -- --nocapture`
  - `monomorphize_module_profiled: total=2 ... lambda_projected_unknown=2`
  - strict bucket の `binding f/lambda: Unknown` は、少なくとも
    lambda return 型の fallback 温存経路に乗っている。

**monomorphized audit の module 分離（refactor #4）— DONE**

- `monomorphize/pipeline/audit.rs` を追加し、monomorphized IR の出口監査を
  reachability/prune から分離した。
- `audit_monomorphized_module` は現時点で以下を順に見る：
  - binding の residual `type_params`
  - TypeSurface collector 経由の residual runtime type vars
- TypeSurface 側に `collect_module_binding_runtime_type_residuals` と
  `BindingTypeSurfaceResidual` を追加し、module-level の入口でも binding owner を
  保持するようにした。今後 audit / substitute / project を同じ surface 定義へ
  寄せる足場。
- regression:
  - module-level residual が binding owner を保持すること
  - audit が `TypeParams` と `RuntimeTypes` を別 source として返すこと

**metadata 正規化 / projection telemetry の配置整理（refactor #5）— DONE**

- `monomorphize/pipeline/refresh.rs` を `metadata.rs` に rename。
  `normalize_monomorphized_metadata` の役割名と file 名を揃えた。
- `type_projection_metrics` を `monomorphize/` 直下から `pipeline/` 配下へ移動。
  projection fallback telemetry は pipeline 内部の観測口なので、外へ
  `pub(crate)` module として出さない形にした。
- どちらも挙動変更なし。metadata 正規化と fallback telemetry の責務境界だけを整理。

**principal projection helper の分離（refactor #6）— DONE**

- `principal_unify.rs` から `principal_rewrite_type_from_kind` 周辺を
  `principal_unify/type_projection.rs` に切り出した。
- 移した対象：
  - expression kind から runtime type を再投影する helper
  - apply callee から result 型を読む helper
  - lambda body 型が弱いとき既存 return 型を温存する helper
  - projection fallback telemetry の記録箇所
- `principal_unify.rs` 側には呼び出しだけ残し、巨大ファイル内で
  “rewrite orchestration” と “type projection fallback policy” が混ざる度合いを下げた。
- 挙動変更なし。次に `local_refresh` 側の projection helper と共通化できるかを見る。

**Detector 強化（#5 の一部）— DONE**

- `collect_expr_type_vars` を以下のフィールドにも降ろした：
  - `AddId.allowed`（runtime が consume するエフェクト row 型）
  - `HandleEffect.residual_before` / `residual_after`（同じく runtime が consume）
- 既存テスト全 0 failed で着地。`Lambda` の `param_effect_annotation` /
  `param_function_allowed_effects` は値が `Name` / `Path` だけで `Type` を
  持たないので detector 対象外（メモ #1 の前提誤り）。

**Apply / If / Match / Handle の evidence（#3）— DONE**

- 原因確定：`#xs` の binding scheme に type_params が無いため、
  monomorphize substitute pass は空の `substitutions` で動き、
  ボディの Apply evidence に残った inference 中間変数（例 `t11448`）が
  そのまま落ちる。`substitute_apply_evidence` 自体は bounds を
  ちゃんと書き換えているが、上流から渡される置換マップが空なら
  何も起きない。
- 解決策：`monomorphize/pipeline/refresh.rs` を新設して
  pipeline 出口に `normalize_monomorphized_metadata` を 1 pass 足した。
  全 binding body と root expr を回って、
  - `Apply.evidence.callee` / `.arg` / `.result` →
    `TypeBounds::exact(runtime_core_type(子 / 自身の .ty))`
  - `Apply.evidence.expected_*` / `principal_callee` /
    `substitutions` / `substitution_candidates` /
    `principal_elaboration` → drop（validate は `.result` しか読まず、
    runtime は何も触らない）
  - `Apply.instantiation.args.ty` → 解決済み arg 型に書き換え
  - `If.evidence.result` / `Match.evidence.result` /
    `Handle.evidence.result` → 周囲 `Expr.ty` の core projection
- これに伴い `collect_expr_type_vars` の evidence detector を strict
  に戻し、ヘルパー群の `#[allow(dead_code)]` を剥がした。
- 全テスト 0 failed で着地。

**#7 `close_known_associated_type_signature_with_semantics` — DONE**

- 関数名と挙動が乖離していた（実装は `signature` をそのまま返す
  no-op）ので、`pass_through_associated_type_signature` に rename して
  doc comment に TODO（実装するなら #7 / #11 でこの一箇所だけ手を入れる）
  を残した。14 call sites も追従。

**Pattern refresh の再帰（#5）— DONE**

- `refresh_pattern_value_local_types` の Variant / List / Or arm が
  外側の `value_ty` を内側 bind に伝えていなかった。
  - Variant: value_ty が `Type::Variant` のとき該当 tag の payloads[0]
    を取り出して payload pattern に再帰
  - List: value_ty が `Named { args: [Type(item)] }` のとき item を
    prefix / suffix に渡す、spread は list 全体型で再帰
  - Or: left / right 両方に value_ty で再帰
- 同根の `push_pattern_bindings` の list arm も prefix/spread/suffix に
  `None` を渡していた → `list_expected_item` helper で expected の
  element 型を取り出して prefix/suffix に伝播、spread は list 全体を維持。
- 全テスト 0 failed。

**Global `Var` 型 refresh（#4）— DONE（保守版）**

- `principal_unify::rewrite_expr` の `Var` arm が、`local_value_type` と
  `known_binding_runtime_type` のみで refresh していた。`emitted_by_path`
  に出てこない普通の monomorphic binding（specialization fan-out が無いやつ）
  への参照は pre-monomorphize `Expr.ty` のままで、scheme で touch されない
  TypeVar slot が残る経路があった。
- `monomorphic_binding_type` を 3 番目のフォールバックに追加。ただし
  scheme body は plain core type なので、call site が持つ runtime-layer
  情報（thunk shape、function arrow）を素直に上書きすると handler 関連の
  effect が落ちる（`vm_runs_handler_function_without_join_evidence` で
  即座に再現）。
- そこで `hir_type_has_vars(&ty)` ガードで「現 `ty` が stale（TypeVar 残）
  のときだけ上書き」に絞った。concrete だけど形が違う（thunk-wrapped 等）
  ケースはそのまま温存。

**Effect hole の `Empty` 潰し計測 + opt-in 厳格化（#6 / #12）— 計測 DONE / fix 保留**

- `monomorphize::effect_hole_metrics` に 3 経路の counter（`close_default`、
  `unifier_expected`、`unifier_actual`）を仕掛けた。
- `YULANG_REPORT_EFFECT_HOLE_COLLAPSES=1` で `monomorphize_module` 呼び毎に
  集計を吐く。workspace test 全体（205 回 monomorphize）で **total=0 / 0 / 0**。
- 結論：principal-elaborate（default）経路は Hole→Empty masking を
  まったく経由していない。`close_default_effect_holes` は legacy
  demand fixpoint からしか呼ばれないので、std テスト含めて発火しない。
- `YULANG_STRICT_EFFECT_HOLE_COLLAPSE=1` で同じ 3 経路を即 error / panic に
  変換するオプトインを追加。strict mode で workspace を回しても落ちるのは
  「lenient 挙動を直接検証している既存テスト 2 件」だけで、それ以外は
  すべて green。
- 残作業：legacy 経路を畳むか、strict をデフォルト ON にするかの判断。
  どちらも測定上 production 影響なし。先送り可。

**fallback-to-old-`expr.ty` の strict 検出（#8）— opt-in DONE / fix 保留**

- `check_strict_runtime_value_types` を `RuntimeStage::Monomorphized` でも使えるように拡張し、
  value position の `RuntimeType::Unknown` / `typed_ir::Type::Unknown` を
  expr / pattern 境界で検出するようにした。
- `monomorphize_module` / `monomorphize_module_profiled` の出口から
  `YULANG_STRICT_MONO_RUNTIME_TYPES=1` のときだけ strict 検査を呼ぶ。
  デフォルトでは既存挙動を保つ。
- 観測：この strict 検査をデフォルト ON 相当にすると、`yulang-runtime`
  の VM 系テストで多数落ちる。代表例は handler payload pattern、
  `apply.callee`、ref helper の `bind_here/apply.callee`。つまり #8 は単発の
  fallback ではなく、まだ複数の monomorphize 経路に `Unknown` が残る。
- 追加観測：`YULANG_STRICT_MONO_RUNTIME_TYPES=1` で
  `vm_runs_source_sub_return_nullfix_unit` を回すと
  `binding f/lambda: Unknown` で落ちる。`my f() = sub: return` の
  monomorphized IR では binding scheme は `unit -> unit` まで閉じているが、
  lambda body 側の `bind_here (std::flow::sub::sub__mono0 ...)` が `?` のまま残る。
  つまり scheme / outer lambda は閉じていても、内側 continuation の `Expr.ty`
  へ expected result が伝わっていない。
- 2026-05-17 baseline:
  `YULANG_STRICT_MONO_RUNTIME_TYPES=1 RUSTC_WRAPPER= cargo test -q -p yulang-runtime`
  は **289 passed / 70 failed**。以後はこの failed count を #8 の進捗指標にする。
  単一テスト内の `Unknown` 個数は多すぎるので、まず「strict mode で通るテスト数」を見る。

  | bucket | count | first context shape |
  | --- | ---: | --- |
  | handler arm payload pattern | 24 | `.../handle.arm[0].payload: Core(Unknown)` |
  | var ref update helper | 13 | `var_ref__mono*/.../record.update_effect/.../apply.callee` |
  | prefix `fail` apply callee | 6 | `std::prelude::#op:prefix:fail__mono*/lambda/apply.callee` |
  | undet `each` callback | 5 | `std::undet::undet::each__mono0/.../bind_here/apply.arg` |
  | sub / label sub return Unknown | 4 | `std::flow::sub::sub__mono*` / `binding f/lambda: Unknown` |
  | loop / callback pattern | 3 | `for_in__mono*/.../stmt[0]/pattern` |
  | handler wildcard tuple value | 2 | `Tuple([Unknown, list[str]])` under handler-local ref/log |
  | list / fold option item | 4 | `std::list::uncons__mono*`, `Fold::contains`, `Fold::find` |
  | variant / result / opt isolated | 5 | variant constructor, result helper, opt item tuple, typed handler annotation |
  | other higher-order apply | 4 | nested callback `apply.callee` with `Core(Unknown)` parameter |
- 追加した regression:
  - `rejects_unknown_expression_type_after_monomorphize`
  - `rejects_unknown_pattern_type_after_monomorphize`

**未着手**

- #11 `pass_through_associated_type_signature` の本実装
- #8 fallback-to-old-`expr.ty` の原因側修復と strict 検査のデフォルト ON 化

---

うん、ある。かなりあるねぇ。
本丸は **`Expr.ty` だけ直っているように見えて、`ExprKind` 側にぶら下がる型付きメタ情報が置換・投影・検査から漏れる** 系だよ〜。

ソース監査ベースで、型がちゃんと入ってない系として刺さりそうな箇所をリスト化するとこう。

## かなり確度高いもの

### 1. `Lambda` の effect 注釈が置換されない

`Lambda { param_effect_annotation, param_function_allowed_effects, ... }` が、`substitute_expr`、principal rewrite、legacy emit、local refresh/project の各所でほぼそのままコピーされている。つまり、本体や `Expr.ty` は具体化されても、lambda 引数周りの effect 型だけ古い型変数・`Unknown`・`Any` のまま残る経路がある。しかも `collect_expr_type_vars` はこの2フィールドを見ていないから、最後の residual polymorphic check もすり抜ける。

### 2. `HandleEffect` の residual 型が置換・投影から漏れる

`Handle { handler, ... }` の `handler` は、`substitute_expr` や `project_expr_runtime_types` で基本的にそのまま通っている。さらに `project_handle_body_runtime_types` は `handler.residual_before` を使って thunk effect を作るから、ここに古い effect 型が残ると、単なるメタ情報ではなく実際の thunk 型へ注入される。これはけっこう危ない。

### 3. `ApplyEvidence` / `If` / `Match` / `Handle` evidence が principal/project 後も古いまま残りうる

`substitute_expr` では evidence を置換している箇所がある一方で、principal rewrite と local project 側では `evidence` をそのまま保持する箇所が多い。`collect_expr_type_vars` も evidence を見ていない。だから、式本体の型が concrete でも、evidence 側に型変数や `Unknown` が残る可能性がある。

### 4. `AddId.allowed` が detector から漏れている

`AddId { allowed, ... }` は effect 型を持つのに、rewrite/refresh 側でコピーされる経路がある。`collect_expr_type_vars` も `AddId.allowed` を見ない。つまり `allowed` に残った effect 変数は `ensure_monomorphic_bindings` で拾えない。

### 5. 最後の `ensure_monomorphic_bindings` が見ている型フィールドが足りない

`ensure_monomorphic_bindings` は `collect_expr_type_vars` と scheme/requirements を使って残留型変数を検出する。でもその walker が、evidence、lambda effect 注釈、handler residual、`AddId.allowed` を見ない。なので「残留型変数なし」と判定しても、実際には型付きメタ情報に残っている可能性がある。

### 6. `check_runtime_invariants` が monomorphized output の型完全性を見切れていない

invariant checker は thunk node の整合性、`bind_here`、handler body などの構造チェックはしている。でも evidence、lambda 注釈、handler residual、`AddId.allowed` の residual 型は見ていない。さらに strict な `check_strict_runtime_value_types` は別関数で、monomorphize pipeline の通常チェックには入っていない。

### 7. グローバル `Var` の型更新が弱い

principal rewrite の `Var` は local なら `local_value_type` で更新され、既に emit された specialization なら `known_binding_runtime_type` で更新される。でも `known_binding_runtime_type` は `emitted_by_path` だけを見る。既存の monomorphic binding の型は `monomorphic_binding_type` で取れるのに、一般の `Var` 更新では使われていない。結果、既存グローバル参照の `Expr.ty` が古いまま残る経路がある。

### 8. pattern の nested bind 型更新が不完全

`local_refresh` の pattern refresh は、値全体の型から pattern の外側を直すけど、variant/list/or の中の bind まで十分に item/payload 型を伝播しない経路がある。さらに demand checker の `push_pattern_bindings` でも list pattern の prefix/spread/suffix には expected を渡さず `None` で再帰している。list/variant destructuring のローカル変数型が `Unknown` っぽく残る候補だねぇ。

### 9. `project_expr_runtime_type_from_kind` が stale fallback を残しやすい

`Apply` は callee から戻り型を取れないと fallback の古い `ty` を使う。`Match` は最初の arm body 型をそのまま全体型にする。`Lambda` は body 側が `Unknown` を含むと既存 return 型を残すロジックがある。これらは「直せなかったら失敗」ではなく「古い型を残す」方向なので、型未充填バグの温床になる。

### 10. `substitute_binding` が `type_params` を消さない

`substitute_binding` は scheme/body を置換するけど、`type_params` は元のまま残す。呼び出し側で `binding.type_params.clear()` している箇所もあるけど、関数単体としては危ない。具体化済み body に古い type params が残る形になる。

## legacy demand path 側で特に怪しいもの

### 11. associated type closer が実質 no-op

`close_known_associated_type_signature_with_semantics` は名前からして associated type を閉じる役っぽいのに、実装は `signature` をそのまま返している。check/collect/emit で何度も呼ばれているから、「ここで閉じる想定だった型」が閉じていない可能性がある。

### 12. effect hole が `Empty` に潰される

`close_default_effect_holes` は `DemandEffect::Hole(_)` を `Empty` にする。`DemandUnifier` の effect row 処理でも余った effect hole が `Empty` に束縛される。これは「effect が推論できなかった」を「pure」として閉じる挙動なので、型未充填が見かけ上 closed になる。

### 13. `check_demand` が失敗を expected で握りつぶす経路がある

`check_demand` は consumed effect mismatch の特定ケースや recursive self-reference の特定ケースで、`checker.check_expr` の失敗を `expected.clone()` に置き換える。closed expected が来ていると、実際の body 側の未解決型を見ずに solved として進める可能性がある。

### 14. non-function call / non-record select がエラーではなく `expr.ty` fallback になる

normal apply で callee が関数型に見えないと、`signature_from_type(&expr.ty)` へ落ちる。select も base が record に見えないと expected か `expr.ty` fallback になる。`expr.ty` が `Unknown`/`Any`/`Var` なら demand hole へ変換されるから、型が入ってない状態を問題として止めずに推論穴として流す。

### 15. missing demand の expected が `runtime_any_type()` になる

emit/rewrite で見つかった missing demand を再投入するとき、generic binding / role impl では expected に `runtime_any_type()` を使っている。ここで expected の具体性がかなり失われる。後続で閉じる材料が足りなくなる候補だねぇ。

### 16. closed demand が open demand を覆って捨てる

`DemandQueue` は、既存の closed signature が open signature を cover すると open demand を skip する。closed が本当に concrete なら良いけど、effect hole を `Empty` にしたり `Never` にしたりして作った closed だと、後から来た情報を消してしまう。

### 17. emit が top-level `body.ty` を solved type で強制上書きする

legacy `emit_inner` は body rewrite の後に `body.ty = solved_ty` として、scheme もその top-level 型から作る。これは外側だけ整って見えるけど、子ノードや evidence/handler/lambda annotation に stale 型が残っていても隠れる。

### 18. `DemandEngine` が demand check error を捨てて続行する

engine は demand check に失敗しても debug 出力だけで `continue` する。失敗した specialization が単に欠落し、その後の rewrite/emit が残りの情報で進む。型が埋まらないなら落とす、という設計ではない。

## principal path 側で怪しいもの

### 19. principal elaboration の strict failure が環境変数頼み

default path は principal-elaboration 系だけど、strict に incomplete plan を失敗させるのは `YULANG_PRINCIPAL_ELABORATE_STRICT` 側の分岐になっている。つまり通常実行では「完全に型が入らなかった plan」も pipeline が進む余地がある。

### 20. principal plan inference が precise runtime type に強く依存している

principal plan の arg bounds は `runtime_type_precise` を通った型だけ使う。arg 側の `Expr.ty` が `Unknown` や fallback だと plan の材料が減る。型未充填が先にあると、specialization 推論も弱くなる循環がある。

### 21. scheme refresh が最終 `body.ty` 依存

principal emit/effect context specialization では rewrite/project 後に `binding.scheme.body = runtime_core_type(&binding.body.ty)` で scheme を作る。final `body.ty` が stale fallback なら scheme も stale になる。

## 仕様かもしれないけど危ないもの

### 22. `RuntimeType::Unknown` が polymorphic residual として扱われない

`hir_type_has_vars(RuntimeType::Unknown) -> false` なので、`Unknown` は「型変数が残っている」とは見なされない。`Unknown` を runtime fallback として許す設計なら分かるけど、monomorphized 後に「型がちゃんと入ってない」を潰したいなら detector として弱い。

### 23. specialized scheme refresh が thunk effect を落とす可能性

`refresh_specialized_scheme_from_body` は `core_value_type(&binding.body.ty)` を scheme body に入れる。`core_value_type` は thunk の value 側を返す設計っぽいので、thunk effect は scheme に残らない。意図的かもしれないけど、effectful thunk-valued binding の型表示・後段推論では注意が必要だねぇ。

## 優先修正順

私ならまずこの順で潰す。

1. **typed metadata の完全 visitor を作る**
   `Expr.ty` だけでなく、lambda 注釈、apply/if/match/handle evidence、`TypeInstantiation`、`HandleEffect`、`AddId.allowed`、pattern、resume、coerce、thunk payload を全部走査・置換・投影・検査対象にする。

2. **`ensure_monomorphic_bindings` を強化する**
   residual 型変数だけでなく、monomorphized 後の value position にある `RuntimeType::Unknown` / `typed_ir::Type::Unknown` / runtime fallback `Any` も拒否する方向がよさそう。

3. **`check_runtime_invariants` に strict 型検査を統合する**
   今の strict checker は thunk value と coerce だけ寄り。evidence/handler/lambda annotation/AddId も見る。

4. **global `Var` 型 refresh を入れる**
   local と emitted specialization だけでなく、closed monomorphic binding の scheme/body type から `Var.ty` を更新する。

5. **pattern refresh を再帰的に直す**
   特に `Variant` payload、`List` item/spread/suffix、`Or` の child bind 型。checker 側も list item expected を渡す。

6. **effect hole を勝手に `Empty` にしない**
   少なくとも monomorphized output では unresolved effect hole をエラーにする。pure と判明したときだけ `Empty`。

7. **`close_known_associated_type_signature_with_semantics` を実装するか、no-op として呼び名を変える**
   今の名前だと、読んだ側が「閉じている」と誤解しやすい。

8. **fallback-to-old-`expr.ty` を monomorphized 後は失敗扱いにする**
   non-function apply、non-record select、apply result fallback、match first-arm fallback あたり。ここを許すと「型が入ってない」が静かに生き残る。

結論としては、単発の推論ミスというより **型情報の所有場所が多すぎて、visitor 群の網羅性が崩れている** って感じだねぇ。`Expr.ty` 中心の pass と、`ExprKind` 内部の型付き証拠・handler・effect 注釈がズレている。ここを一括 visitor 化しないと、似たバグがまた出ると思うよ〜
