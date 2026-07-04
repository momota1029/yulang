# file line editing ergonomics regressions

日付: 2026-07-04。発見: Codex（native host で `/tmp` 実ファイルを使った
`file::text` / `lines` 実験中）。
状態: **fixed**。file resource の意味論そのものではなく、行単位編集の書き味と
method / runtime availability の詰まりとして見つかったもの。

## 背景訂正

ユーザの言う `each` は foreach ではなく `std::control::nondet::each` のこと。
目標 idiom は、`file::text` で得た unscoped ref から `$doc.lines.each` で 1 行を
非決定に取り出し、`std::control::nondet::guard` 相当で絞り、当たった分岐が
行を書き換える形である。

ambient buffer は nondet 分岐間で順に共有・蓄積され、`file::text` の extent 終端で
backing file へ commit されることを期待する。これは「副作用目的の foreach を
`each` という名前で追加するか」という話ではない。

確認コマンド:

```bash
YULANG_CACHE_DIR=/tmp/yulang-cache RUSTC_WRAPPER= \
  cargo run -q -p yulang -- --std-root lib run /tmp/<case>.yu
```

## 1. `for` 内の動的 `line_range` が native runtime で落ちる

### 観測した挙動

`for i in 0..line_count` の中で `std::text::str::line_range $doc i` を呼ぶと、
型検査後の runtime で落ちる:

```text
runtime error [yulang.unsupported-runtime-feature]: unsupported primitive in runtime: StringLineRange
  hint: this primitive is not available in the selected runtime
```

失敗時、backing file は更新されない。

### 期待

`line_count` で得た範囲を走査し、各 `i` の `line_range` で該当行を読み書きできる。
少なくとも `StringLineRange` は native run 経路で使えるか、未対応なら
compile/check 段で分かる診断になる。

### 再現

事前入力:

```text
keep
todo: one
skip
todo: two
```

```yu
use std::control::var::*

my path = "/tmp/t3-for.txt"

(\&doc ->
    my count = std::text::str::line_count $doc
    for i in 0..count:
        my r = std::text::str::line_range $doc i
        my line = std::text::str::index_range $doc r
        if line.starts_with "todo:":
            &doc[r] = line.replace_once "todo:" "done:"
    ("after-for", $doc).say
) (std::io::file::text path)
```

## 2. `ref_lines` / `line_view` の行単位 ref 更新が method 解決で通らない

### 観測した挙動

`std::text::str::line_view &doc` から `lines.index 1` で行 ref を取り、
`update` しようとすると method 解決で落ちる:

```text
compile error [yulang.unresolved-method]: no role implementation satisfies this method call
  detail: unresolved typeclass method ... for receiver std::text::str::ref_lines(std::io::file::file) -> int -> ...
```

`&doc.lines[1] = ...` の自然形でも同系の unresolved method になる。

### 期待

`lib/std/text/str.yu` には `impl (ref_lines 'e): Index int` があり、
`ref_lines` の `index` は `ref 'e str` を返す。したがって、行 ref への更新は
元の whole-file ref へ splice として伝播するはず。

### 再現

事前入力:

```text
keep
todo: one
skip
todo: two
```

```yu
use std::control::var::*
use std::text::str::*

my path = "/tmp/t3-line-view-fail.txt"

(\&doc ->
    my lines = std::text::str::line_view &doc
    (lines.index 1).update: \line ->
        line.replace_once "todo:" "done:"
) (std::io::file::text path)
```

## 3. `[1, 2].each` の method 形が型候補衝突する

### 観測した挙動

`Fold` role の `container.each` は `std::control::nondet::each container` へ委譲される。
ただし method 形で呼ぶと、`.list` と receiver item 型が衝突する:

```text
conflicting type candidates for slot 3: {list: 'open1} vs int
```

関数形の `each [1, 2]` は動く。

### 期待

`Fold` role に `container.each` があるなら、少なくとも
`(each [1, 2]).list` と同じ意味で `([1, 2].each).list` が動く。

なお、ここで扱う `each` は `std::control::nondet::each` であり、foreach ではない。

### 再現

```yu
use std::control::nondet::*

([1, 2].each).list.say
```

動く関数形:

```yu
use std::control::nondet::*

(each [1, 2]).list.say
```

## 回避形

- 単一の既知行なら `my r = std::text::str::line_range $doc 1; &doc[r] = "BETA\n"` は動く。
- 条件付き全行変換は `&doc = (($doc.split "\n").map rewrite).join "\n"` が動く（`rewrite(line: str): str` の注釈つき）。
- 読み取りだけなら `for line in $doc.lines:` で走査し、別 buffer を組み立てて最後に `&doc = $out` する形が動く。
