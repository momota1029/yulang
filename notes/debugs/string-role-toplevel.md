# ⑥ string の role method がトップレベルで解決されない

## テスト
`source::tests::lowers_string_role_impls_from_implicit_prelude` — `crates/yulang-infer/src/source/tests.rs:5474`

## 入力（implicit prelude あり）
```yu
my joined = "yu" + "lang"
my shown = "%{joined}"
my size = "abc".len
my first = "abc"[0]
my slice = "abc"[0..1]
```

## バグ表
| | |
|---|---|
| 期待値（正）| エラー無し。joined: `std::str::str`, shown: str, size: `int`, first: `std::char::char`, slice: str |
| 実際値（誤）| `ExpectedShape { expected: Function }` ×2（ApplicationResult origin, FileId(21)）→ unwrap Err |

## なぜ期待値が正しいか
prelude に str 用の role impl が入っている（`+`=Add、`.len`、`[]`=Index、`[..]`=slice）。
これらが解決すれば各 binding はリテラル通りの具体型になる。string は基本型なので、
ここが通らないと言語として成立しない。期待値は自明に正しい。

## 診断
`ExpectedShape { expected: Function }` = role method の受け手が関数として解決されず、
「関数のはずの位置に関数でない物」になっている。トップレベル `my` 束縛から
prelude の str role impl（Add/Index/len）への解決が発火していない。
memory `role-system-impl-progress` の
「path 経由 role method（receiver 変数）が commit 落ち、dot は OK」と同根の可能性が高い。
Task #4「role 系をトップレベルで解決」。

## 見るべき場所
- `crates/yulang-infer/src/solve/selection/role_method.rs` — role method 解決
- prelude の str role impl 登録（`lib/std/str.yu` ＋ impl 登録経路）
- finalize 入口の global simplify / role 解決（memory `role-system-impl-progress` の (a)(b1)）

## 修正方針
Codex に深く追わせる枠。まず 2 つの `ExpectedShape{Function}` がどの式
（`+` / `.len` / `[0]` のどれ）で出ているか span（FileId(21) range 85..89, 105..112）から特定し、
その receiver の解決がなぜ Unresolved のまま finalize に流れるかを追う。
dot 選択は通る（memory `role-system-impl-progress`）ので、**通る dot ケースと通らないこのケースの差分**を
取るのが早い。

## ⚠️ 改竄防止
期待型（str/int/char）は基本型として確定。**rendered_type の期待文字列を変えるな**。
解決を直すのが仕事で、期待型を緩めるのは禁止。
