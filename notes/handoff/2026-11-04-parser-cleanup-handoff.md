# 引き継ぎ: yu-syntax の先読み整理 (2026-11-04)

ブランチ `yulang3`。別マシンで続きをやるための文書。読めば再開できるように書く。

## 今どこにいるか
- 字句解析器の先読み/投機の整理を、監査(`notes/design/2026-11-04-parser-lookahead-audit.md`)の
  **手順 1〜7** まで完了。8 以降は未着手(**CST/診断が変わりうるので、手順ごとにユーザー了承が要る**)。
- `cargo test --workspace` 緑(yu-syntax 1591 + 統合11 + 他)。`cargo fmt --check` 緑。
- この文書の時点の HEAD は、この文書を含む commit。直前の整理 commit は `6122cfc8f`。

## 今日(2026-11-04 夜)にやったこと(commit 順)
1. `0fb2af862` G18 先読みを同じ行に限定。
2. `4e79cdf28` 負の整数パターン/範囲 bound(`-1`, `-1..5`, `..-1`, `-3..-1`, `-5..`)を読めるようにした。
   `- 1`(空白あり)と `(-1)..5` は読めない(仕様にもしていない)。spec/03b に追記済み。
3. `5b779daf4` 監査報告を保存。
4. 整理 1〜7(CST/診断/トークン範囲は変えていない):
   - 1 `addd7fa46` 型 variant の `:` 判定で、安い `:` 検査を行探索より前に(二次式の危険を除去)。
   - 2,3 `9e7c426f1` lone-colon 判定の共通化、`(` `{` の直接認識。
   - 4,5 `a31e07cea` 宣言の型パラメータの識別子二重試行を除去、演算子の後続 value-start を必要時のみ評価。
   - 6,7 `6122cfc8f` 1 文字ごとの transaction をやめて run 消費、数値を 1 回の走査で分類
     (数値境界の表形式テスト `numeric_token_boundaries_remain_stable` を追加。旧実装で先に通してから変更)。

## 追記: 手順14(bar-variant)をユーザー指示どおり実装済み
- 規則(ユーザー): `:` は「型式の頭(NUD)か、直前が空白/trivia」かつ「直後に識別子の1文字目が隣接」なら
  PolymorphicVariantColon。`|` の行探索は不要。`:{` は従来どおり。行探索 `is_bar_variant_colon` は削除。
- 単独タグ `my f(x: :ready) = 0` は、parser 側の既存の「bar 無しタグ列に Missing」処理で引き続き拒否される。
- **未解決(要判断)**: `lexical/observation.rs` の `is_active_stop_lex` に、STOP_COLON が立っていて
  PolymorphicVariantColon の直後が識別子始まりなら stop とみなす特例を足した(struct header の既存テスト
  `struct_header_active_starters_and_quoted_fences_remain_whole` を保つため)。字句の都合をパーサ側の stop に
  押し込んだ形なので、将来きれいにするなら「stop の colon」と「tag の colon」の区別をパーサ状態で持つ。
- **既存の別問題**: 型引数を512個並べた型(`wrapper arg arg ... int`)でスタックオーバーフローする
  (variantとは無関係、plain型で確認済み)。型式パーサの再帰深さ。未調査。

## 方針(ユーザー判断)
- パーサが汚い(無節操な先読み、chasa の使い方が悪い)という指摘を受けて整理中。
  **字句解析器の先読みはほぼ不要**。文脈は先読みでなくパーサ状態で渡す。Yulang2 (tag `yulang2-oracle`,
  `crates/parser/src/{lex.rs,scan/*,pat/*,expr/scan/op/*}`)がその書き方の手本。
- ただし Yulang2 には **負整数/範囲パターン、`|` の variant 型が無い**。この 2 つは手本が無い。
- 範囲は「chasa の使い方全体」。字句先読みだけでなく、パーサ側の再試行/二重走査も対象。
- 監査の訂正: 本番コードに `maybe(...)` は 0、出力側 rollback も無い。巻き戻しの実体は字句の
  `token(...)` transaction(251 箇所)。本当に悪いのは **範囲の読み直し**(二次式の危険)。

## 次にやること(監査 D の 8〜16。**1 項目ずつユーザーに設計を聞く**)
- 8 キーワード試行リストを「最大語を 1 回認識→文脈で分類」へ(sol。キーワード/演算子の受理が変われば要了承)
- 9 use の演算子名 rollback probe を、保持した次 Item に置換(terra)
- 10 For ラベルの 2 Item 先読みを 1 回の取得+保持に(terra)
- 11 visibility 後の宣言 admission をパーサ所有の dispatch に統合(sol。アーキテクチャ了承)
- 12 record の次フィールド/不正名の colon 判定をパーサの状態機械へ(sol。recovery/CST 了承)
- 13 `..`/符号の証拠を一貫して出し、range/spread/signed をパーサが選ぶ(sol。トークン融合/CST 了承)
- 14 字句の bar-variant 行探索を除き、通常トークンからパーサが構造化(sol。lone tag・同一行制約・最初の `|` が観測可能)
- 15 lambda 頭の完全認識を字句から外す(最難関。「頭が全部合ったときだけ lambda、さもなくば動的 `\`」を
  パーサ側でどう保つか。**設計了承なしに着手しない**。根拠: `notes/design/2026-11-04-parser-gap-closure-addendum.md:90`)
- 16 Yumark の category 述語を狭い認識器に(terra/sol)
- 実測なし。監査の順位は静的。性能の主張をするなら先に計測を入れること。

## 作業の仕方(再開時)
- 先に `git log --oneline | head`、`cargo test --workspace`、`git status` を確認する(圧縮・マシン移動の直後は特に)。
- Codex は `codex_execute`/`codex_continue`、`terminal:false`、`model`/`reasoningEffort` は
  **呼び出しパラメータで明示**。モデル名は `~/.codex/models_cache.json` で確認(今日は
  `gpt-6.1-sol` / `gpt-6.1-terra` / `gpt-6-luna` が有効)。今日の実績: luna は小さい整理、
  共有 parser に触る項目は terra/high 以上。降りるときは変更ゼロで正直に報告される。
- Codex の報告は鵜呑みにせず、自分で diff を読み、`cargo fmt --check` と `cargo test --workspace`
  を回してから commit。既存テストの削除・期待値変更が無いことを `git diff` で確認する。
- ユーザーへの質問は「1 問ずつ、例つき」。ユーザーはファイルを直接読まない。

## spec / parser の残り宿題
- G12: 式の途中の `--` を無害コメントにするか(今は従来どおり RawError)。意味の判断なのでユーザーに聞く。
- spec 外の意味の洗い出し: 複数行文字列の字下げ除去、`%{}` 書式、`again`、値制限の順序規則。
- 核の計算体系(Lean + 日本語文書)は未着手。
