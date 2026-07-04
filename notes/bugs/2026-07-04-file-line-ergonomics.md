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

## 2026-07-04 chain diagnosis

本来の書き味である `&doc.lines.each` 系の one-liner chain を、helper extraction なしで
直接試した。過去の lambda / helper 形だけの失敗とは別に、chain そのものでは
次の 4 系統の原因が分かれた。

### D3 fixed: effect row が naked effect へ崩れていた

修正: 2976bb07, 56df359d。

`ref '[file] str` のような effect row を invariant な型コンストラクタ引数へ
lower すると、内部 scheme で `ref(file, str)` のような naked effect として
保存される経路があった。さらに、payload なし effect marker が row tail へ流れるときも
`[file]` ではなく裸の `file` として流れていた。

`std_file_text_public_signature` は spec/2026-07-02-io-resource-api.md §1 の綴りに合わせ、
`ref '[std::io::file::file] str` を pin する。古い golden は naked bug 形を
固定していたものだった。

### D4 fixed: parse diagnostics のある run が無言成功していた

修正: 3e1d1e08。

`&(expr)` は現状では `InvalidToken` として lex されるが、module body lowering が
それを捨てていたため、`run` が root なしで exit 0 になる経路があった。
`run` は parse diagnostics を持つ source を診断つき exit 1 で拒否するようになった。

`&(...)` は分割代入構文として予約済み。ref tuple `&(a, b)` / ref record
`&{ a: b }` を想定した設計で、未実装。実装時期は未定。

### D1 / D2 fixed: record fallback が typeclass fallback と同じ batch に混ざっていた

`(&doc.lines.each).update \line -> ...` と
`($doc.lines.each).replace_once "todo:" "done:"` は、selection probe の hop 追跡ではなく
fallback の時系列が原因だった。

trace 上、`replace_once` receiver は fallback 時点で `lowers=[Var(20839)]`。
fallback 後に `Var(20839)` へ `str` lower が入り、replay で receiver 側にも
`str` lower が到達した。つまり var-var 伝播自体は効いていたが、record fallback が
具体 lower の到着前に確定していた。

根因は final fallback の batch 判定。quantified typeclass method fallback は batch 可能だが、
同じ batch に record field fallback も混ぜていたため、`.each` の typeclass fallback と
後続 `.update` / `.replace_once` の record fallback が同じ drain で確定していた。
record fallback は receiver shape constraint を追加するため、structured method fallback の
instantiation が receiver bounds を更新した後の別 pass まで待たせる必要がある。

修正後、record fallback は method / typeclass fallback batch に混ぜない。
`($doc.lines.each).replace_once ...` は native run まで通る。
`(&doc.lines.each).update ...` は method 解決を抜け、既知の downstream
specialize2 conflict `[std::io::file::file] vs []` まで進む。

### New finding: check 後の run が specialize2 で落ちる

D3 修正後、`(&doc.lines).index 0` と `.get()` chain は `check` を通る。
ただし `run` は specialize2 で次の別 conflict に当たる:

```text
conflicting type candidates for slot 11: [std::io::file::file] vs []
```

これは D3 の `file vs [file]` とは別の downstream row conflict として調査が必要。

## 回避形

- 単一の既知行なら `my r = std::text::str::line_range $doc 1; &doc[r] = "BETA\n"` は動く。
- 条件付き全行変換は `&doc = (($doc.split "\n").map rewrite).join "\n"` が動く（`rewrite(line: str): str` の注釈つき）。
- 読み取りだけなら `for line in $doc.lines:` で走査し、別 buffer を組み立てて最後に `&doc = $out` する形が動く。
