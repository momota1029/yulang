# dots cycle 295: 選択済みの role 一宣言だけを既存の表へ手渡す

## 再開と範囲

2026-11-20 10:30:00 UTC 開始。統合 pin
`ea6a9b81a48d8965f2d6f628b81ad92757cf6b5b` で standing orders → inbox
の順に読み直した（ACTIVE、I-51〜53）。同じ tree を持つローカル祖先も確認。
Yulang2 の固定監査メモは再読したが、本周の解析接続をその実走で確認したとは扱わない。
前周の公開 `95cd9ea8540f8e37d03d376a79e999254b2b80f6` の完了心拍と報告、
同一作業 tree、および別 writer の稼働を示す状態がないことを確認。
`work/dots-main` のみ、以前の head と tree を照合した非強制更新。

## 結果

1. **回復診断 receipt と、許可した一宣言の選択を分離した。**
   C294 の診断 receipt は同一 wire 内の他の選択にも検査できる。
   その性質を保ちつつ、C295 の手渡しは元 wire、snapshot brand、正確な混合 child
   path、scope、回復 policy が一致した場合にのみ既存の role 射影へ進む。
   渡す入力はその射影結果の 1 件だけ。成功する表に実 role 行はちょうど 1 行で、
   別 ID の読み出しは既存 fallback。path や spelling から勝手に数値 ID を割り振らない。
2. **保存済み Rust CST を現行の Lean exporter に接続。**
   role `a` は `[0]`、範囲 `0..49`。head `[0,2]` は `5..9`、
   method `[0,4,2,0]` は `15..49`。外部入力の構造回復 `49..58` は選択枝の外。
   呼出側が与えた `a → 7` で arity 1 の行が一つでき、関連型出力はない。
   この名前表を外すと出力表はできない。同じ入力でも全体 policy や異なる位置は不可。
   JSON の外側の空白だけを変えても wire が同じなら同じ選択として扱うが、元 token
   を含む wire 自身の変更、brand 不一致、診断未取得は拒む。
3. **合成の二宣言で既存の `assocOf` を Lean 上で実行。**
   どちらも同じ `Index` の spelling を持ち、旧診断 gate だけなら各々を選べる。
   `[0]` の `type value = 'key`（`[0,6,1,0]`, bytes `36..53`）と、
   `[2]` の `type value = char`（`[2,6,1,0]`, bytes `119..136`）を別の手渡しにした。
   同じ既存 goal で省略実装に対して前者は `int`、後者は `char`。`[0]` の手渡しを
   `[2]` へ転用すると失敗する。明示実装の値は既存規則の通り優先し、その値を
   role の既定値由来とは数えない。必須スロット `some none` と未宣言 `none` も区別。
   これら二宣言は **手で作った CST**。Rust に同名二宣言の入力が通るとは主張しない。
4. **名前照合を使う範囲だけ、有限 trace にした。**
   `Index → 2`、`(2,value) → 0`、必要なときだけ `char → 3` を記録する。
   無関係な名前表の変更は問題なく、実際に使う role/name/constructor key の変更や
   順序の異なる trace は拒む。変更した名前環境でも新しい真の診断や承認を合成しない。
   選択済み wrapped 断片から既存の symbolic role までは必ず到達する。
   その後の名前不明、未束縛 binder、重複 binder・出力 ID の拒否は別。

## 主な定理と受け入れ範囲

全 95 定理の型（前提、量化子、定理名、ファイル）は
[完全な型一覧](../verification/cycle295/theorem-index.md)。
本周は既存の規則を適用する連携確認で、M1 の一般健全性・完全性・主型性の主張ではない。

- `select_exact`, `compile_exact`, `compile_single_row`,
  `no_other_role_data`（手渡しの健全性・完全性）:
  任意の有限 wire と受け取った証跡に対し、成功は seal の exact address と policy、
  scope、元 wire、および既存の単一 payload 変換に対応する。旧変換が成功した表は
  名前表の role ID と元 head の arity を持つ 1 行のみ。
- `selected_head_from_original`, `selected_member_is_exact_original`,
  `selected_member_contained`, `text_exports_one_original_role`,
  `text_read_has_raw_type`（出所の健全性）:
  成功した選択・表読み出しは、与えた JSON 内の元 `RoleDeclaration` /
  `TypeExpression` / `TypeDeclaration` の位置への証拠を保つ。
  直接 body member の suffix は body / statement / leaf の 3 混合 ordinal。
  位置の UTF-8 byte 範囲は選択 role の内側で、型の数値 ID ではない。
- `exact_for_entry`, `selected_type_contributes`, `text_has_every_selected_type`
  （関連型の出所の健全性・完全性）:
  当該単一入力の旧 lowering が成功した場合に限り、任意の表の関連型読み出しは
  選択 role の元の型宣言と一致し、逆に各 direct type member は読み出しを持つ。
  必須スロットは値なしの読み出しとして残る。名前表で解けなければ成功を主張しない。
- `old_read_omitted_exact`, `selected_explicit_preserved`（既存 reader との接続）:
  旧 `WellFormed`・`resolve = .resolved`・一意 candidate・実装 membership を仮定。
  その実装が出力を省略した場合のみ、元の選択 role の既定値の positional substitution
  が説明となる。明示実装では従来通り implementation substitution。
- `captures_eq_agree`, `captured_naming_same_result`（有限 lookup の補助）:
  任意の二つの lookup 環境に対し、順序付き trace が一致することと、選択された
  symbolic role が使用する名前の局所一致は同値。一致した reference map と
  current map は同じ lowering 結果を返すが、どちらの真正性も認証しない。
- `selected_goes_symbolic`, `never_unsupported_symbolic`,
  `naming_mismatch_exact`, `old_export_rejection_exact`（境界の補助）:
  exact wrapped selection が成功した範囲では symbolic 段で失われない。
  JSON 失敗、schema/depth、選択・回復拒否、lookup trace 不一致、旧 exporter 拒否を
  混同しない。旧 exporter 拒否を常に「名前不明」とは呼ばない。

## 検証

- Lean 4.35.0、`--trust=0 -j 1 -M 3200 -DwarningAsError=true`。
  今回の追加 OLean を除いた影キャッシュから 32 モジュールを再構築。
  今回の 11 standalone 監査の全 95 定理、既存 293/294 の 20 standalone 監査を確認。
  I-51 の[個別 Lake 監査](../verification/cycle295/standalone-lake.txt)と、
  I-53 の [barrel 確認](../verification/cycle295/barrel-dependencies.txt)も実施。
  [入力ソース一覧と SHA-256](../verification/cycle295/source-sha256.txt)。
  公理は `propext`・`Classical.choice`・`Quot.sound` の範囲内。
  [再現手順](../verification/cycle295/README.md) /
  [独立検査ログ](../verification/cycle295/focused-replay.txt)。
  同時起動した初回の検証は exit 137 で中断したため、1 スレッド・直列で再実行し完了。
  [初回ログ](../verification/cycle295/first-isolated-attempt.txt) と分けている。
- 統合 pin の Rust ファイル 3 本を [byte 照合](../verification/cycle295/github-rust-sources.txt)。
  Rust テストから保存値を再抽出して JSON を比較し、[独立な原始走査](../verification/cycle295/independent-archived-source.txt)
  でも役割と method の byte 範囲を確認。保存 JSON の handoff、
  合成旧 reader、入力拒否、12 の名前・構文段階コントロールの出力を再実行して照合。
- `tools/verify-lean.sh . <base> --no-build` は 294 base と統合 base の両方で exit 0。
  [静的検査全文](../verification/cycle295/static-diff.txt)。
  全体 Lake ビルド・全体監査は standing orders に従い未実行。既存 Lean 本体、
  Rust、spec、lake 設定、inbox は変更なし。

## まだ検証していないこと

この環境に Rust toolchain はなく、Rust を新規実行していない。現在の Rust
パーサが関連型 fixture から実際に生成する CST、完全な診断の実行時収集、
新鮮な snapshot の認証、本番での名前表の導出、一般型推論・カーネルの停止性は未検証。
CLI の lookup 数値は外部入力であり実 Rust 環境ではない。仕様の選択を変える必要はなく、
質問ノートは追加していない。使用枠は不明。

次の候補: (1) Rust が利用可能なら同じ retained parse の実 CST と fallible diagnostics を
関連型付きケースで記録する、(2) 独立な名前解決元から実 lookup trace を照合する、
(3) 既存の一般 solver/宣言側へ進むときは、旧 reader の一意実装仮定を別に検証し、
この選択的射影を一般停止性や型推論の証明に取り違えない。

- 最終報告書の時刻: 2026-11-20T11:20:04Z、経過 50.07 分。前周からの変更 80 ファイル
  （この報告と完了心拍を含む）。完了書き込み後に再読出しで照合する。
