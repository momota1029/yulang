# 現状: 構文と型推論の「回復可能性」 (2026-11-07)

状態: **観測の記録。WP-18の承認済み規則による修正と測定結果を末尾に追記。** ユーザーの問い（構文と型推論は、壊れた入力から回復できるか）に、2026-11-07 時点で答えたもの。
署名: Claude (Sonnet 5.5)。

## 構文（`crates/yu-syntax`）

回復はできる。以下はWP-18適用前の観測で、適用後の結果は末尾の測定節に記録する。

**できること**
- どんな入力でも、パーサは木を返す。止まらず、落ちない。
- 壊れた所は、`Missing`（欠け）、`RawError`（読めない語）、`Invalid` の印として木に残る。
  `ParsedFile` から、種類・位置・木の中の経路つきで取り出せる（`StructuralRecovery`、`full_parse.rs`）。
- 例: `case n:` の arm で本体が欠けても（`0 ->` で終わる）、`Missing` になり、その arm の中で収まる。

**適用前の弱点: 閉じていない括弧が、後ろ全体を吸う。**

```text
my a = (1 +
my b = 2
my c = case n:
    0 ->
my d = 4
my e = f(
my g = 5
```

観測（2026-11-07、`syntax_guide_check --tree`）: 先頭の `(` が閉じないと、後ろの `my b = 2`、`my c = ...`、`my d = 4` が、
`a` の括弧の中の項目として読まれる。字下げが基準以下なので、項目の区切りにはなるが、括弧は閉じない。
列 0 の宣言のキーワード（`my`）は、開いている括弧を閉じる合図になっていない。結果、BindingStatement が 1 個しか立たない。

影響: 書きかけの 1 文字が、後ろの解析全部を巻き込む。言語サーバー（補完、hover）で最も痛い種類の壊れ方。

直すなら（案。決めるのはユーザー）: 「列 0（または外側の基準）から始まる宣言のキーワードは、開いている括弧を強制的に閉じる」のような規則。
文法と回復の設計判断で、設計文書（`rules/parser-chasa.md` のとおり、Authoritative な追補）と、ユーザーの承認が要る。
関連: `notes/design/2026-09-07-successor-delimited-boundary-priority-correction.md`（区切りの優先順位の既存の設計）。

## 型推論

方針は決まっているが、今は何も動いていない。

- **方針**（ユーザーの決定、2026-08-16。記憶の `yulang3-hir-error-tolerant-partial-inference`）:
  各段階の出力は全域的で、壊れた入力でも構造を返す。エラーは網羅的に報告する（最初の 1 件で止めない）。
  部分的な型情報を言語サーバーに出す。エラー経路の遅さは許容する。部分推論のための別の近似エンジンは作らず、
  一つの全域的な solver が、壊れても続けて、エラーを集め、できる限りの部分情報を出す。
- **実装**: この木に、型推論の実装は無い（2026-11-04 の白紙化の後）。
- **Lean の核**: 判定は 成功 / 拒否（`.rejected`）/ 未対応（`.unsupported`）。壊れた入力から部分的な型を取り出すことは、核の定理に入っていない。
  診断を返す定理（`diagnostic_iff_unreachable` など）はあるが、handler の到達不能 arm のような限られた範囲。

**これから決める課題**（M1 の後）:
- 「拒否」の中身を、どこまで構造として返すか（失敗した束縛の中の、失敗する前に分かった型）。
- 補完の位置を、番兵の識別子（`yulang__completion__probe`）で表すか、構文木の「補完の穴」の node で表すか。
- 壊れた node の周りの連鎖的なエラーを、どう抑えるか。診断の順序は決定的にするか。
- これを核の側の定理にするか、核の外の層（診断）にするか。

## 測定の基準値 (WP-18 phase 1)

2026-11-07、パーサの挙動を変更する前に測定。コーパスは `syntax-guide/ja/src/` と
`spec/` の正常に解析できる全 `yulang` ブロック、および
`tests/contracts/phase2-parser/` と `web/playground/examples/` の全 `.yu` ファイル。
262 件、31,769 bytes。そのうち正常な 256 件の全 CST の構造指紋を
`crates/yu-syntax/src/tests/recovery_mutation_fingerprints.tsv` に固定した。
Markdown は `syntax_guide_check` と同じ imported prelude、`.yu` は空の環境を使う。

コマンド（worktree root、release、offline）:

```sh
cargo run --offline --release -q -p yu-syntax --example recovery_mutation -- crates/yu-syntax/src/tests/recovery_mutation_fingerprints.tsv > recovery-mutation-baseline.txt
```

挿入位置は EOF を含む全 UTF-8 文字境界で、各位置に `(` / `[` / `{` をそれぞれ挿入する。
削除はソース内の全 `)` / `]` / `}`、切断は各行の両端を除く全 UTF-8 文字境界。
文字列・コメント内も除外しない。各変異は常に元の入力に一つだけ適用する。
編集位置より後に始まるトップレベルの文を、変位後の位置、全ノードの種類、全トークンの
テキスト（trivia を含む）で照合する。平均は後続文のある変異だけを分母とする。
切断で削除された後続文は失われたものとして数える。

| 変異 | 全件 | 後続文あり | 平均保存率 | 保存文数/後続文数 | 過半数喪失 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 閉じ区切り一つ削除 | 441 | 228 | 34.429825% | 152/438 | 148 |
| 開き区切り一つ挿入 | 83,583 | 35,982 | 38.230597% | 29,033/72,336 | 22,193 |
| 行の途中で切断 | 25,689 | 11,107 | 0.000000% | 0/22,420 | 11,107 |

実測本体は 6.293 秒（初回ビルド時間を含まない、一回の全数実行）。
最悪例は、閉じ区切り削除で `spec/03-expressions.md:27` の byte 11（0/7）、
開き区切り挿入で `web/playground/examples/yulang2-ordinary-islands.yu` の byte 0（0/10）。
バイナリは各変異の最悪 10 件を、同率なら後続文数の多い順、ファイル名、byte 位置の順に出力する。
指紋生成の引数は基準値取得専用で、phase 2 の実行では指定しない。

### 適用後 (WP-18 phase 2)

同じ262件・同じ全数変異で測定。正常な256件のCST指紋はphase 1と一致する。
コマンド（指紋生成の引数は付けない）:

```sh
cargo run --offline --release -q -p yu-syntax --example recovery_mutation > recovery-mutation-after.txt
```

| 変異 | 全件 | 後続文あり | 平均保存率 | 保存文数/後続文数 | 過半数喪失 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 閉じ区切り一つ削除 | 441 | 228 | 64.473684% | 274/438 | 78 |
| 開き区切り一つ挿入 | 83,583 | 35,982 | 61.264938% | 45,701/72,336 | 13,632 |
| 行の途中で切断 | 25,689 | 11,107 | 0.000000% | 0/22,420 | 11,107 |

実測本体は7.530秒（release、一回の全数実行、ビルド時間を含まない）。
閉じ区切り削除は30.043859ポイント、開き区切り挿入は23.034341ポイント改善し、
変異種別ごとの平均保存率・保存文数・過半数喪失件数のいずれにも悪化はない。
元の再現例は、トップレベルに`a`、`b`、`c`、`d`、`e`、`g`の6個のbindingを残す。
対応のない区切りを既存の`Missing`で閉じ、対応のある区切りは早く閉じない。

残る最悪例:

- 閉じ区切り削除: `spec/03-expressions.md:27`のbyte 11で0/7、
  `syntax-guide/ja/src/whitespace.md:71`のbyte 11でも0/7。
  後続行がrecordやblockの式で、宣言キーワードから始まらないため、WP-18の境界を作らない。
- 開き区切り挿入: `web/playground/examples/yulang2-ordinary-islands.yu`のbyte 1で0/10。
  先頭の`//`コメントを壊す挿入で、通常の区切りownerに入らない回復も残る。
- 切断: 同ファイルのbyte 1で0/10。後続のソース自体を削除する測定なので、保存率は0%のまま。

規則は拡張していない。字下げだけの閉じ、推論の回復、補完用probeは対象外。
事前走査はソースを前に進め、各開き区切りを一度だけpush/popする。
種類ごとの最終openerへのリンクにより、対応するopenerがないcloserも定数時間で処理する。
リテラルとコメントには既存の`lexical/opaque_region.rs`、docとfenceの判定には既存のYumark judgeを使う。
行の字下げも同じ走査で記録するため、事前走査の時間とメモリーはソース長に比例する。
開始行の検索は文の入口で一度だけ行い、トークンごとのソース再走査はしない。

全出力（各変異の最悪10件を含む）は、
[基準値](2026-11-07-wp18-mutation-baseline.txt)と
[適用後](2026-11-07-wp18-mutation-after.txt)に保存した。

### 検証結果 (WP-18)

- `RUST_TEST_THREADS=4 cargo test -p yu-syntax --offline`: exit 0。
  unit 1,647 passed・1 ignored、integration 11 passed、doc test 0。unit実行34.91秒。
  既存テストと既存の期待値は変更していない。
- `cargo test --offline -p yu-syntax valid_corpus_cst_matches_phase_1_fingerprints`:
  phase 1で1 passed。適用後も同じテストがfocused runと上記全体で通り、正常256件の指紋が一致した。
- `RUST_TEST_THREADS=4 cargo test --offline -p yu-syntax recovery_mutation_tests`:
  13 passed、exit 0。6つの指定fixture、対応付けとopaque領域、keywordと字下げ、
  宣言・型・pattern・catchの共有owner、文の開始行とblock基準の差、matchedな外側の括弧を検証した。
- `RUST_TEST_THREADS=4 cargo test --offline -p yu-syntax tests::yumark_cell::isolated_cell_`:
  2 passed、exit 0。全体検証で見つかったsynthetic座標のpanicは、事前走査のない入口で
  座標計算を行わないように修正した。期待値の変更はない。
- `CARGO_NET_OFFLINE=true cargo fmt --check`: exit 0。
- `cargo run --offline -q -p yu-syntax --example syntax_guide_check -- syntax-guide/ja/src/ --quiet`:
  exit 0。114 blocks、ok 110、recovery 0、unexpected-ok 0、placeholder 4。

未検証: ignoredの1テスト、workspace全体のcheck/test、独立したparser throughputの比較測定。
事前走査の線形性は、ソースの前進、種類ごとのstackリンク、各openerのpush/pop回数で静的に点検した。
測定は変異harnessの実行時間で、parser throughputの統計比較を主張するものではない。

### 測定の注意 (Claude, 2026-11-07, WP-18 の取り込み時)

- 「行の途中で打ち切る」の行は、**常に 0%** になる。打ち切ると、変異点より後ろの文が元から存在しないため、「後ろの文の残り」は定義上 0 になる。この変異で意味のある指標は、打ち切り前の文が壊れないことと、パーサが落ちないこと。指標の定義は WP-18 を書いた私の側の誤りで、実装は指定どおり。次に測定を触るときに直す。
- 残る最悪の例は、宣言のキーワードで始まらない後続行（式だけの行）。規則は宣言のキーワードでだけ閉じるので、式だけの文の列は救えない。コーパスの ```yulang ブロックの多くが式だけの行なので、この数字は実際の `.yu` ファイルより悪く出る可能性がある。
- 実装は、括弧を扱う各所に `with_delimiter` を包む配管（31 ファイル）。保守の負担は増えた。
