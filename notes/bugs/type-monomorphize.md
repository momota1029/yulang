## 進捗メモ（2026-05-17）

**Detector 強化（#5 の一部）— DONE**

- `collect_expr_type_vars` を以下のフィールドにも降ろした：
  - `AddId.allowed`（runtime が consume するエフェクト row 型）
  - `HandleEffect.residual_before` / `residual_after`（同じく runtime が consume）
- 既存テスト全 0 failed で着地。`Lambda` の `param_effect_annotation` /
  `param_function_allowed_effects` は値が `Name` / `Path` だけで `Type` を
  持たないので detector 対象外（メモ #1 の前提誤り）。

**Apply / If / Match / Handle の evidence（#3）— 保留**

- 同じ detector で evidence も拾うようにすると、`my $xs = [2, 3, 4]`
  みたいな簡単な mutable list 例の `#xs` binding で
  `ResidualPolymorphicBinding { vars: [TypeVar("t11448")] }` が立つ。
  field probe で原因絞ると、`Apply.evidence` の `callee` /
  `arg` / `result` TypeBounds 全てに t11448 が残ったまま。
- `substitute_apply_evidence` 自体は callee/arg/result の bounds を
  ちゃんと `substitute_bounds` 経由で書き換えている。問題はその上流：
  `#xs` の binding scheme には type_params がそもそも無いので、
  monomorphize substitute pass が空の substitutions で呼び出される。
  ボディの Apply の evidence は inference 段階の中間変数（t11448）を
  抱えたまま、ここで触られない。
- 真っ当に直すなら「scheme の quantified に無い inference vars でも、
  body 全体を見て pinned concrete type に置き換える evidence refresh
  pass」が必要。runtime 側の影響評価が要るので別タスクとして切り出し。
- ヘルパー `collect_apply_evidence_type_vars` /
  `collect_type_bounds_type_vars` / `collect_type_instantiation_type_vars` /
  `collect_join_evidence_type_vars` は `#[allow(dead_code)]` で残してあって、
  evidence refresh が入ったら即 detector を一行で起こせる状態。

**#7 `close_known_associated_type_signature_with_semantics` — DONE**

- 関数名と挙動が乖離していた（実装は `signature` をそのまま返す
  no-op）ので、`pass_through_associated_type_signature` に rename して
  doc comment に TODO（実装するなら #7 / #11 でこの一箇所だけ手を入れる）
  を残した。14 call sites も追従。

**未着手**

- #6 effect hole を `Empty` に潰さない方向
- #11 `pass_through_associated_type_signature` の本実装
- #4 global `Var` 型 refresh
- #5 pattern refresh の再帰修正
- #8 fallback-to-old-`expr.ty` の失敗扱い化
- #12 `DemandEffect::Hole` を `Empty` に束縛しない方向

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
