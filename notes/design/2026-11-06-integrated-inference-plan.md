# 推論側の統合: ひとまとめの定理と工程 (2026-11-06)

署名: Claude (Sonnet 5.5), 2026-11-06。ユーザーの決定(2026-11-06): 最初の「ひとまとめ」は**推論側**(案A)。
実行側(lambda・application・effect を含む preservation/progress)は、その後。
この文書は、定理の statement、構成、工程、役割分担、レビュー観点を決める。**ユーザーの確認後に着手する。**

## 1. ひとまとめの定理 (Main Theorem)

統合した核の式 `Core.Expr` と、統合した型付け判断 `Core.Typing`、統合した推論器 `Core.infer` について、次を証明する。

1. **完全な主型性 (sound & complete):**
   `Typing Γ e τ ⇔ ∃ S ∈ infer e, ∃ 自由 parameter, S の具体化 ≤ τ`
   任意の式 `e`、任意の結果型 `τ` を量化する。成功した推論や solver の解を前提に渡さない。
2. **拒否の完全性:** `infer e = rejected ⇔ ¬∃ τ, Typing Γ e τ`。
3. **未対応が出ない:** 統合した断片に対して、`infer e = unsupported` は起きない
   (`recordFree_ne_unsupported` の一般化)。これが、統合の達成の中心である。
4. **停止:** `infer` は全域関数で、fuel も深さの打ち切りも使わない。
5. **モジュール性:** 公開型は、後続の補完(他ファイルの `impl` の追加など)に依存しない
   (`accepted_export_independent` の統合版)。cache の正しさの根拠になる。

対象外: 実行時の preservation/progress、性能、Rust との接続、一般の禁止点つき graph の到達定理
(後者は「未対応」として返すが、拒否にはしない。10.13.6)。

## 2. 統合する層と、既存の成果

| 層 | 既存の AST・入口 | 既存の主な定理 | 統合で要るもの |
| --- | --- | --- | --- |
| 基本(lambda・app・let・branch・pair・variant) | `Inference.Expr` | `principal_exact`、`recordFree_instances_exact` | 土台。値制限付き let を含む |
| record(presence 付き、先頭が勝つ、spread) | `PresenceDataInference` | `infer_instances_exact`(data 構文のみ) | required-field の体系との統合(`presence-inference-integration.md`) |
| record の意味的同一視 | `Shadow*`、`Semantic*` | checker・cut・商の等号判定 | presence と同じ型モデルに載せる |
| effect(request・boundary・handler) | `RecursiveEffects.Expr` | `generate_models_iff_typing`、`principal_exact` | 単一 operation の handler。複数 arm との統合 |
| 複数 operation の handler | `MultiOperationHandlerTyping`(shape 添字つき) | 実行・独立型付け・checker の一致 | 添字なしの `Core.Expr` への埋め込み |
| case / pattern | `CaseTree`、`CaseDataTerms`、`Scoped*` | 型付け・網羅性・progress | `Core.Expr` への埋め込み。presence・variant 残余との接続 |
| nominal / list / literal | `NominalConstructions`、`LiteralValues` | 構築・保留 cast・index | 保留境界を推論の出力にどう載せるか |
| 再帰 SCC | `RecursiveInference` | `generateSCC_exact`、`closeSCC_exact` | effect・case を含む式での SCC |
| 注釈(公開型・T3) | `AnnotationFinalization`、`AnnotationSnapshots` | 一般化直前の観測 | 決定 34 の「注釈は公開型を決める」との統合 |
| role・method・cast・EOF | `QualifiedInference`、`ModuleRoles`、`MethodResolution`、`Casts`、`EOFNoDefaulting` | qualified の主型性、EOF の検査 | elaboration(辞書・cast の挿入)の出力としての統合 |
| 型の求解 | `JointConstraintInference`、`RegularSchemeInference`、`TypeConstraintInference` | 型と行の同時求解、regular scheme | effect の行・presence を含む入力への拡張 |
| 行の求解 | `RecursiveRows`、`SolvedRecursiveRows`、`Semilinear*`、`Guarded*` | 最小解の決定手続き | 保護・解除・残余を含む一般の式 |

AST が複数ある: `Inference.Expr`、`RecursiveEffects.Expr`、`QualifiedInference.Expr`、`CaseTree.Expr`、`CaseDataTerms.Expr`、
`MultiOperationHandlerTyping.Expr`(shape 添字つき)、`OperationalTyping.Expr`(shape 添字つき)。**統合の最初の仕事は、
これらを一つの `Core.Expr` に埋め込むこと**である。

## 3. 工程

依存の順。M2・M3・M5 は M0・M1 の後に並行できる。

- **M0 統合 AST と埋め込み。**
  `Core.Expr`(上の AST の構成子の和。de Bruijn 添字、解決済みの operation key)を定義する。
  各既存 AST から `Core.Expr` への埋め込み `ι` を定義し、保存定理を示す:
  `Typing_old e τ ⇔ Typing_core (ι e) τ`(`RecursiveEffectsConservativity.generate_preserved` と同じ型の定理)。
  shape 添字つきの AST は、添字を消す写像と、消した式の型付けとの対応を示す。
  受け入れ条件: 各既存 AST について `ι` と保存定理が閉じ、既存の主型性定理が `Core` 上の定理の系として読める。
- **M1 型モデルの統一。**
  presence 付き record、意味的 record 商、正則再帰型、行(符号付き・半線形)を、一つの `Inference.Model` に載せる。
  required-field の体系を presence 付きの体系の特別な場合として、`SourcePrincipalInference` を一般化する。
  受け入れ条件: 旧入口が `unsupported` と返していた式(`recordDefault` など)が、新入口で解ける。
- **M2 effect の式の主型推論。**
  request・boundary・複数 operation の handler を、M1 の型・行の同時求解に載せる。
  受け入れ条件: `Core.Typing` が handler 全体を含み、`infer` が `unsupported` を返さない。
  決定 41(引けない arm)、決定 1(非網羅の payload)、決定 3(operation-local 多相、escape エラー)を含む。
- **M3 再帰 SCC と注釈。**
  SCC(単相の連立、全注釈 binding の多相再帰)と、注釈の公開型(決定 34)、effect 行の検査(一般化直前、決定 24)を統合する。
  受け入れ条件: effect・case を含む式でも、`generateSCC_exact` 相当が成り立つ。
- **M4 role・cast・EOF を出力に載せる。**
  elaboration の出力を `Core.Expr`(辞書引数・cast を挿入した式)として定義し、推論が
  「型付けできる ⇔ 挿入つきの式が元の式と整合する」ことを示す。決定 7・8・16〜25・30〜33 を使う。
- **M5 case・nominal・list・literal の推論。**
  presence 付きの型、variant の残余(`VariantsMerged`)、網羅性(guard を数えない)を使って、case の主型を計算する。
  保留された cast 境界(決定 25)と、list spread の `Fold`(決定 45)を含む。
- **M6 組み立て。**
  Main Theorem を `Core.infer` について組み立て、README の「証明対象」に一行足し、Audit を通す。
  「未対応」が残る断片(一般の禁止点つき graph など)を、定理の仮定ではなく、**型として明示した境界**にする。

## 4. 役割分担

- **私 (Claude):** この文書の statement の保守、各工程の statement の敵対的レビュー、Audit の確認、問いの整理。
- **Sol (codex-flow, `gpt-6.1-sol`):** M0 の埋め込み、M1・M2・M5 の配線(機械的な統合)。別ブランチ・別 worktree で作業する。
- **ChatGPT Pro:** 数学として新しい所(例: 一般の禁止点つき graph、solver の完全性で行き詰まったとき)。回数制なので、温存する。
- **ユーザー:** 仕様の判断。統合で見つかる問いに、1 問ずつ答える。

## 5. レビューの観点 (空虚さを避ける)

- 定理は**任意の式・任意の型**を量化しているか。solver の成功、型付けの導出、fuel を前提に渡していないか。
- `infer` の結果が `unsupported` になる式の集合は、**明示された断片の外**だけか。
- 負の例がある: 拒否される式が、独立な型付けで本当に型付けできない。
- 旧入口の定理が、保存定理の系として読める(既存の定理の主張を弱めていない)。
- Audit: 公理は `propext` / `Quot.sound` / `Classical.choice` のみ。`sorry`・`native_decide` なし。
- README の「示さないこと」の列が、証明した範囲と一致する。

## 6. Sol への制約

- ブランチ `integration/types`(worktree)で作業する。`yulang3` には push しない。
- 小さく commit する。lake build と Audit を通してから commit する。
- 既存の定理の主張を弱めない。テストの期待値を書き換えない。
- 仕様が黙っている所は、自分で決めずに `notes/questions/` に積み、仮の前提と明記して、依存しない部分を先に進める。
- 工程の終わりごとに、追加した定理の名前と主張、閉じていない所を、報告として残す。

## 7. 想定される落とし穴

- AST の間で、de Bruijn 添字と環境の表現が違う。埋め込みで環境の対応を取り違えやすい。
- Lean のビルド時間。モジュールが 300 を超えている。新しい統合の層は、小さなモジュールに分ける。
- 型モデルの universe の水準が、層ごとに違うかもしれない。
- 統合で、層と層の相互作用から、仕様の抜けが新しく見つかる(今までもそうだった)。見つかったら問いにする。
