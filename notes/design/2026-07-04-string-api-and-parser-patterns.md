# 文字列 API v1 と parser pattern

決定日: 2026-07-04
状態: **決定済み（Part A は着手可。Part B は Stage P1 / P2 実装済み）**
署名: Claude Fable 5

背景: ファイルを文字列として扱える（`file::text` が `ref '[file] str` を返す）
割に文字列 API が貧弱、という指摘（ChatGPT 経由・ユーザ承認）。方向は二段:
基礎 API の充実（Part A）と、`rule { }` / `~"..."` を pattern として使い
レコードを返すところを変数で受ける（Part B、ユーザ発案）。

2026-07-04 調査で確定した現状:

- std 文字列 API は `lib/std/text/str.yu` にあり、`find` / `contains` /
  `starts_with` / `ends_with` 相当は **private helper として存在する**が
  public でない（`lib/std/text/str.yu:88-108`）。`split` / `join` / `trim`
  / 大文字小文字 / 書記素 iterator / 数値 parse は無い。
- parser DSL は構文・lowering・runtime（`run_str` / `run_prefix_str`、
  `lib/std/text/parse.yu:63-107`）まで実装済み。pattern 位置の構文も
  既に読める（`crates/parser/src/pat/parse.rs:75-90`）が、case arm の
  専用 lowering は token / word capture の if-chain 展開に限定されている
  （`crates/infer/src/lowering/control.rs:510-596`）。

## Part A: 文字列 API v1

### 決定 S1: v1 は既存プリミティブ上の pure Yulang で書ける範囲だけ

新しい intrinsic（compiler / VM 変更）を要するものは v1 に入れない。

v1 で追加する public API（`lib/std/text/str.yu`）:

- `find: str -> str -> option range`（最初の出現。既存 private helper を
  public 化・型を整える。option/result の既存流儀に合わせる）
- `contains` / `starts_with` / `ends_with: str -> str -> bool`
- `split: str -> str -> list str`（separator は literal 文字列、regex ではない）
- `split_once: str -> str -> option (str, str)`
- `join: list str -> str -> str`（`xs.join ", "` の method 綴りも）
- `trim` / `trim_start` / `trim_end: str -> str`（`char.is_whitespace` 基準。
  空白は単一 codepoint なので書記素境界と衝突しない）
- `repeat: str -> int -> str`
- `to_int: str -> option int`（10 進・符号付き・全消費）

命名・受け取り順は既存 `replace` 系（`lib/std/text/str.yu:110-129`）の
流儀に合わせる。method 追加は既存の `with:` companion に倣う。

### 決定 S2: v1 に入れないもの（新プリミティブか設計が要る）

- 大文字小文字変換・casefold（Unicode テーブルが要る → host/intrinsic 設計後）
- 書記素クラスタ iterator / boundary / normalize（「1文字=書記素クラスタ」
  方針の本丸だが intrinsic が要る）
- `to_float`（丸め・指数表記の仕様決めから）

これらは v2 として別 TODO に残す。v1 の API は将来 v2 が入っても
綴りが変わらないものだけにする。

### 決定 S3: prelude は動かさない

新 API は `str` module（と method）にのみ足す。prelude への昇格は
ユーザの好みの領域なので、まとめて別途判断する。

2026-07-04 追補: `ref '['e] str` の変異 method 族（replace_once / replace /
replace_all / splice / trim 系、いずれも `r.update` への一行糖衣）を追加
（commit 1ed3b61a）。`(&doc.lines.each.replace_once "todo:" "done:").list` が動く。

## Part B: parser pattern（`rule` / `~"..."` を pattern に）

### 決定 P1: 意味論

`case s:`（scrutinee は `str`）の arm に parser literal
（`~"..."` または `rule { ... }`）を置けるようにする。

- **全消費が既定**: arm のパーサが scrutinee 全体を消費して成功したら
  その arm に入り、capture record のフィールドが pattern 束縛として
  スコープに入る。失敗（不一致・部分消費）なら次の arm へ。
- record capture（`rule { id = word }` → `{ id: str }`）は、arm 内で
  そのまま変数束縛になる（ユーザの言う「レコードを返すところを変数で
  受け取れる」）。ネストした record pattern の綴りと合成できる。
- scrutinee は一度だけ評価する。arm は上から順に試行する。
- parser 実行は `run_str` 相当で parse effect を内側で handle するので、
  case 式に新しい effect row は漏れない（parser 本体が別の effect を
  持つ場合は通常の row 伝播に従う）。

### 決定 P2: 実装は desugar 一本、IR / VM は変えない

既存の token / word if-chain 展開（`control.rs:510-596`）を、
「arm ごとに `run_str`（または内部等価物）を呼び、`result` を case して
成功なら record pattern 束縛、失敗なら次 arm」への一般化 desugar に
置き換える。`Pat::Parser` のような IR 変種は足さない
（`crates/poly/src/expr.rs:594-613` の pattern IR は不変）。
runtime（evidence-vm）変更なし。

### 決定 P3: v1 の範囲は literal 形だけ

pattern 位置に置けるのは `~"..."` と `rule { ... }` の literal だけ。
変数に入れた第一級 parser 値の参照（`case s: my_rule -> ...`）は
call pattern と構文が衝突するため Stage P2（ユーザ確認）へ送る。
lazy quantifier（`*?` / `+?`）の未対応 diagnostic は現状のまま。

### 決定 P5（2026-07-04、ユーザ綴り確定）: rest とパーサ参照

rest はユーザ確定綴り `..` とする。`rule { name = .. }` は残り入力を
`str` として束縛し、`rule { .. }` は残り入力を捨てる。`~"..."` 内では
interpolation 経由の `~"{..}"` / `~"{r = ..}"` だけが rest で、裸 `..`
は literal text のまま扱う。`..` は rule branch の末尾のみ許可し、
後続 item がある場合は診断にする。実装は `std::text::parse::rest()`
（pure Yulang、`snapshot` + `advance`）への lowering で、IR / VM は変えない
（2026-07-04 実装済み、commit 61cd3f88）。

変数 parser 参照には新構文は要らない。`rule { x = my_rule }` の裸参照と
`~"{x = my_rule}"` の interpolation capture は既存構文で動き、
fixture で固定済み。

guard は parser pattern と普通に組み合わせる。capture への dot method
（例: `id.starts_with "A"`）は、capture 束縛を synthetic selection
（`parsed.value.id`）で作っていたため method 解決前に record field fallback と
衝突していた。capture を parser result の record destructure に変えて根治した
（commit 61cd3f88）。

### 決定 P4: 網羅性との関係

parser pattern は開いた失敗可能 pattern なので、将来の exhaustiveness
検査（notes/todo/case-exhaustiveness.md）では guard 付き arm と同格に
「網羅に数えない」扱いとする。これを同 TODO に一文で追記しておく。

## Stage 分割

- **Stage A（着手可）**: Part A の v1 API + テスト（各関数の正常系・
  空文字列・separator 不在・複数出現。fixture は `stable-api` 相当の
  流儀で）。
- **Stage P1（実装済み）**: Part B の desugar 一般化 + fixture
  （`~"..."` 数本の case、record capture 束縛、fallthrough、
  ネスト record、全消費失敗で次 arm）。
  （2026-07-04 実装済み、commit 39bc3543。既存 token/word if-chain は
  一般化 desugar に統合。付随して rule alternation の choice 未起動バグを修正）
- **Stage P2（実装済み）**: prefix / rest 束縛の綴り、変数 parser 参照、
  guard との組み合わせ。
  （2026-07-04 実装済み、commit 61cd3f88。lazy capture / interpolation /
  裸参照 / guard / rest の fixture 固定込み）

## Do not

- 文字列 v1 のために新しい intrinsic を足さない。
- parser pattern のために IR / VM の pattern 表現を変えない。
- 「1文字 = 書記素クラスタ」方針に反する「codepoint 数え」の公開 API を
  足さない（`_raw` 系の内部流儀は現状のまま）。
- prelude の顔ぶれを勝手に変えない。
