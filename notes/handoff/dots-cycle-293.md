# dots-main cycle 293: 保存された Rust CST から未解決 role を読む

## 結果

**現行 Rust テストが保持する実 Rowan CST の golden を、タグ付き JSON に変換し、
Lean の実行可能な抽出器で再生した。** 出力は未解決 role `a`、binder `'x`、
直接の非型 binding の path `[0,4,2,0]`。数値 role ID、型名の解決、scope の
推定はこの抽出器にない。実 Rust パーサは今回新たに動かしておらず、
Rust serializer の組込みもない。変更は補助 Lean、検証、設計のみ。

## 1. Rust 実装と保存済み golden の対応（検証の根拠）

- fresh `integration/m1-final` pin `396ffa8a4a7984a19431e299b434f4d65bceb664` と
  同一 tree の Rust ソースを照合した。現 `role_decl.rs` は普通の type expression
  と indented statement owner を呼び、`TypeDeclaration` は一般宣言ノードのまま。
  [静的ソース追跡](../verification/cycle293/rust-static-trace.txt)。
- 現行 `role_method_signature_where_keeps_its_pre_wp17_recovery_cst`
  （`crates/yu-syntax/src/tests/declaration/act_decl/operation_where.rs`）は
  `syntax_guide_check --tree` で記録した exact Rowan 出力を検査する。
  この出力によって、**実 `TypeApplyArgument` の直下には
  `TypeExpression` がもう一段あり、その中に sigil token がある**と確認した。
  途中の文書由来の浅いモデルは、そのままでは実 golden を読まない。
  旧断片を名前付き対照に残し、最終 CLI は deep wrapper の厳密版を使う。
  元の CST のノード、bytes、ordinal、枝は書き換えない。
- [golden 変換器](../verification/cycle293/rowan-debug-to-wire.py) は指定 source の
  UTF-8 範囲からトークンを採り、Debug の綴りと子範囲の完全分割を検査する。
  Debug 形式はバージョン固定の検証用であり、stable な production API ではない。
  [golden から再生成した wire](../verification/cycle293/recorded-rust-cst.json)
  に対する Lean CLI の実出力を照合。統合枝から exact Rust テストを
  [別経路で取得し再生成](../verification/cycle293/github-golden-readback.txt) しても
  wire・隔離実行結果が同じだった。取得した path の [UTF-8 範囲を実測](../verification/cycle293/golden-extents.txt)
  しても、role 0..49・binding 15..49 が記録と一致した。元の golden には role の後の root に recovery が
  あるが選択 role の抽出が通るため、成功を「ファイルが診断なし」とは読まない。
  この golden には関連型の宣言がない。関連型三形の対照は別の文書例を実 wrapper
  に合わせて再構成した入力である。

## 2. 生の構造から直接子と role shell を作る（健全性／完全性）

- `CstTree293.indexed_exact/significant_exact` は任意の生 child 列と index に
  ついて、元 mixed list の該当位置と、trivia 除外後の所属の関係が iff。
  `CstTrivia293.visible_filter` は payload 投影では真に trivia だけを除くことを
  証明した。node-only `SourceNode::children()` の ordinal は使わない。
  実 Rust の診断 walker は `children_with_tokens()` を列挙する。
  `StructuralRecovery::path()` は kind path で、数値の
  `SyntaxDiagnosticIdentity::occurrence_path()` や `direct_root_ordinal()` と別。
- `CstRustHead293.argument_exact_rust/head_exact_rust` は任意の tree に対し、
  一つの単純な identifier primary と、順序を保った **全** wrapped bare sigil
  argument があるとき・そのときだけ受理する。一般の TypeExpression、
  qualified path、型構造の引数、可視化できない形を飛ばさない。
- `CstTypeRules293.rhs_exact/type_exact` は、普通の type node の意味ある直接
  子が `type`＋名前だけなら required、または実 `Equals` と
  `TypeExpression` が続き、その直中が単一 identifier/sigil の場合だけ
  default の未解決 RHS になる、という判断と実行の iff。
  `shape_never_fakes_required_after_equals` は実 Equals の後で欠けた RHS
  が required として現れないことを示す。identifier が本当に nullary
  constructor を指すかは別の解決段階で検査すべき内容。
- `CstBody293.statement_exact/members_exact` は各直接 `Statement` の
  意味ある子が一件で、上記 TypeDeclaration または marked recovery の
  ない普通の BindingStatement のときだけ記録する、という関係との iff。
  nested の TypeDeclaration は promote しない。
  `CstRecovery293.clean_tree_exact/clean_list_exact` は任意の subtree／子列で
  Missing・Invalid・Error のマークがどの子孫にも無いことと clean Bool の iff。
  実転送側は資源制限 `NestingTooDeep` と `Unknown` を回復マークとして送る。
- `CstRustRole293.extract_exact/extract_origin` は任意の供給 role、scope、
  absolute path、結果について、実 colon＋indented body、optional な一つの
  visibility、実 wrapper の head、全直接子の対応と実行成功が iff。
  任意の結果 member のアドレスは**同じ supplied raw 全木**の当該直接 node
  へ戻る。 `CstCoverage293.direct_complete` と
  `CstRustFixture293.wrapper_paths_unique` により、元 direct list の対象を
  一件ずつ対応させ、全 mixed child path が相異なる。binding に含まれる名前を
  role の出力名として解決しない。
- `CstRustSnapshot293.export_exact/declaration_member_roundtrip` は独立の
  snapshot brand の一致を必要とする。外部が別の木に同じ brand を再利用すれば
  自動では見分けられない閉じた対照を明示。root と revision/brand の実装側の
  所有と鮮度は別の義務。重複する未解決綴りは二つのパスで保存し、実 ID が
  衝突するなら次段の既存検査で拒否される。

## 3. Wire、実行、幅、添付（健全性／完全性／補助）

- `CstWireTags293` は現 Rust enum と **297 個**の label が順序も含め一致
  （[独立スクリプト](../verification/cycle293/check-rust-tags.py)）。
  未知 label は失敗し、既知の不使用 kind は位置を削除せず Other に
  compact。 `CstWire293.decode_exact/transfer_preserves_text` と
  `CstWirePaths293.transfer_path` は任意の wire の成功について、node/token,
  配列の順序, token の text, 同じ path の元データの存在が保たれることを
  双方向に確かめた。compact 値だけから全 Rust label を逆算するものではない。
- `CstJson293.read_exact` は任意の JSON 値に対して、厳密な三要素タグ配列
  スキーマの符号化と指定 depth 以下であることに成功が iff。
  depth 制限は wire の資源制限であって、言語の深さ制限ではない。
  `CstRustEntry293.value_exact/text_exact` は JSON 読込、タグ移送、
  同じ snapshot の role 選択を各段で明示する。外部 scope/brand、
  選択 path は入力であり、数値 role ID を求める引数は無い。
- `CstRustOrigin293.text_member_origin` は任意の成功 CLI 入力・任意の
  送出メンバーについて、同じ exact wire child、同じ brand、分類、
  UTF-8 extent と root の byte bound の証人を取り出す。これは**供給した**
  wire の証明であり、Rust から来たことを証明しない。
  実際に同じ source text を持つ二つの受理 wire に異なるノードラベルを
  供給すると、一方だけに関連型が現れる閉じた対照
  `CstExternalContract293.no_text_only_equality_certificate` を示した。
  Rust 側が全ラベルと mixed 子を忠実に渡す必要がある。
- `CstSpan293.locate_tree/locate_bounds` は任意の raw path の tree と範囲の
  projection、幅、包含を保証。文書の role を再構成すると full role
  0..75、body 31..75、required 36..46、binding 51..75 が一致。
  日本語文字の UTF-8 幅や trivia 追加で path と byte span が変わる対照も確認。
- 最終 CLI を **15ケース**実行した。[出力](../verification/cycle293/json-cli.txt)。
  通常・named RHS・binder RHS・UTF-8 名・同じ未解決綴りの二 occurrence・
  trivia 後の移動・実 golden を確認し、unknown label、marked recovery、
  wrong path、余分な要素、壊れた JSON、depth 超過、実 wrapper 欠落を区別した。
  加えて [独立の42形](../verification/cycle293/cst-matrix.txt) を一回の Lean 呼び出しで
  検査し、可視性や trivia、required/default、欠けた Equals・RHS で
  成否と直接子 path が一致した。これらは合成対照で Rust parser acceptance ではない。
- 推論接続の別試験 `CstRustFixture293.wrapped_roles_actual_consumer`：
  実 wrapper の test root を抽出し、**別途**既存の名前環境を与えた場合だけ
  旧 `Index str int` の省略実装に付く。同一の既存 `Roles.assocOf` が
  `'key` に対応する `int` を返す。実 Rust solver、一般の完了、古い raw
  journal の新しい経路、主型性、K2 全体は主張しない。

## Yulang2 と言語上の判断

`work/dots-audit` の `runtime-cycle-3-parent-fixed.md` を既存実機資料と
して照合（`Produce` の required と impl 側の explicit 出力）。
Yulang2 の Rust/CST 互換規則を追加したわけではなく、新規の実機実行も無い。
規範の provenance は現行 spec 6.1 と既存の型表／resolver。言語の解釈を
新たに決める必要はなく、質問ノートなし。

## 検証

- Lean 4.35.0 の `lake env lean --trust=0 -M 3200 -DwarningAsError=true`。
  **35 modules** の focused、**9 standalone audit**、監査対象 **107 宣言**、
  実行可能 guard 8 件。監査に現れたのは `Classical.choice`、`Quot.sound`、
  `propext` のみ。I-51 に従い監査から他の audit は import せず、
  I-53 に従い新規モジュールの import だけを barrel の末尾に追記。
  [全文](../verification/cycle293/focused.txt)。
- 前周 OLean だけを使った隔離依存グラフで 35/35 再構築、9 監査も単独成功。
  focused と独立の追加 OLean は全件 SHA-256 一致。
  [隔離](../verification/cycle293/isolated.txt)、
  [hash](../verification/cycle293/olean-sha256.txt)。同じ独立 cache だけで
  [goldenを実行](../verification/cycle293/isolated-golden.txt) して出力も一致。
  `lean --deps` で [追記35件のみを全解決](../verification/cycle293/barrel-dependencies.txt)。
- 旧 68 件の focused な単独監査（Cycle292 の 13 監査を含む）を再実行。
  [旧回帰](../verification/cycle293/existing.txt)。
  両正確基準に `verify-lean.sh --no-build` を実行、全体 build は実施していない。
  [静的検査全文](../verification/cycle293/static.txt)。
- [interface 表示](../verification/cycle293/interface.txt)、
  [CST CLI の再現](../design/2026-11-20-cycle293-cst-producer.md)。
  旧 raw Step、Rust、spec、lakefile、既存 Lean の本文は変更なし（barrel 追記のみ）。
  Cargo/Rustc 不在、
  他の認証済み作業コンピュータ無し。この周は実 Rust の起動・CI・既存テストの
  再実行なし。使用量の枠は不明。前周完了と同一 tree、統合枝の ancestor、
  namespace の単独 writer を先に確認。復旧なし。

## 次の一手

1. Rust toolchain のある場所で現行の exact golden テストを実行し、次に
   **関連型を直接含む** role （required、scalar default、binder default）を
   `syntax_guide_check --tree` で capture。同じ pointer-owned parse result
   から直接列挙してこの CLI と照合する。production には Debug 変換器ではなく
   `children_with_tokens()` の構造と token bytes を直接渡す。
2. 独立の Rust semantic name resolver がある場合だけ、scope、role、出力名、
   RHS 名を finite table の attachment として証明する。CST shape が正しい
   ことと、意味論の選択・停止性は別の主張。

- 最終報告書の時刻: 2026-11-20T09:22:44Z、経過 50.03 分。前周からの変更 85 ファイル
  （この報告と完了心拍を含む）。完了書き込み後に再読出しで照合する。
