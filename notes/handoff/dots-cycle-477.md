# dots cycle 477: 元の typed field から有限深さまで、同じ入力で K2 を照合

道具: モデル名不明、Lean 4.35.0、GitHub; 委譲: モデル名不明、1 回、task `/root/yulang302_resume`（追加委譲・Codex thread なし）

**G04 は部分完了、未完 20 / 24。** 検査済み GD と単一の元の可視 head を前提に、入力の型付け・捕捉と同じ既存 raw の上で、複数の深さの実 field を調べる局所判断を積み上げた。既存の State・Fits・checker・spec、raw の名前・行を変えていない。既存 checker の入口には新分岐を接続していない。

## 進んだこと

- **経路の正確な再生。** `NamedPathTrace477` の有限列は、各 step について元 AST の相対 pose、実 query の選択、同じ captured trace にある raw/author の mark、既存 raw の実 operand と観測点を結び付ける。任意のこの判断を `finite_named_path_receipt_replays_exactly477` が同じ wire で再生する。最初の field は C476 の独立に固定された `FieldOrigin`。最後の action が field のときだけ報告し、元 occurrence・宣言・ordinal・連結した元 pose・field label を保持する。
- **両符号と実 edge。** 任意の検査された named 経路では、元引数から終点まで実 edge があり、全 proper prefix は実観測の商で安全。終点の true は正長の帰還があり、全ての同じ `FitsFull` で実際に選んだ末端 operand の型に戻ることを示す。false は checked class へ帰還する経路がない証拠で、探索失敗ではない（`a_positive_deep_field_cycle_returns_to_the_actual_last_operand477`、`deep_negative_field_excludes_every_return_to_its_checked_type477`）。実 operand は最後の選択から計算し、単に型が等しい別位置で代えない。
- **ordinal と有限 witness。** 成功した C332 located capture の compiled path は一意。指定済みの元 field と各相対 step を変えず、探索から exact mark ordinal を補える。今まで通った任意の wire を `exact_field_report_and_entire_trace_replay_without_any_supplied_ordinals477` が同じ ordinal と報告で復元する。別の元 field を決める機能ではない。`ScopedNamedRoute477` では、実入力上の独立な route・点ごとの閉じた観測の適用条件と型商の符号から、任意の有限深さの checkpoint witness を構成する。その逆も `scoped_named_route_iff_exact_finite_checkpoint_replay477` で示した。固定された元 field と最初の二点の guards から両符号の正確な報告まで構成する定理は `scoped_original_field_with_independent_path_has_finite_report_for_either_sign477`。
- **named と inline の混在。** `MixedLiteralTrail477` は同じ既存の named cell と旧行内の literal pose を一つの構造経路で読み分ける。named 側だけ actual trace の ordinal を求め、inline 側は exact old equation ordinal と行内位置を維持する。独立な最初の source receipt（named または inline）、実 capture trace、与えられた有限 mixed checkpoint trail から、同じ最初の根拠・終点を持つ報告を再生する。全ての混在 cone を upstream から生成した、とはしていない。
- **実入力での対照。** 出力なしで `FitsFull` に実モデルがある元 field 30→40 について、二つの安全な prefix と元 pose を再生し、正しい terminal の K2 を確認した。ordinal を渡さずに `[1,2]` を復元し、別 label・元 pose・旧物理点の代用は通らない。別の出力なしの fitting fixture では named→inline→named の実経路で、行内にある安全な点の false と、深い named 終点の true を区別し、違う pose と中間の飛ばしを拒む。これらは局所 reader の試験で言語全体の受理・拒否ではない。

## 残りと次の焦点

- I-92 の **同じ compiler 相で型付けされた入力 event が、元 occurrence・実 decl/ordinal・head arg・original/normalized pose と、それに対応する既存 raw/author の位置を発行する部分**は未証明。今回の reader は渡された元 source receipt と existing table を検査する側。C332 の旧 projected source view や mark の一致から発行・選択を逆算していない。未完の別出力で source を代用しない。
- 現行 `yulang3@1acc24c888eb30dbc21b90c0d0c0a25963ad77d5` は C476 の同期のみ。spec §6.3 `a3d903781fef0691b773f886ba8976a6b4ac871d` の I-93 最小グラフはそのまま。現行 Rust のパーサ位置は元構文を表すが、同相の型付き入力 receipt ではない。現バージョンでこの発行を確認できる型検査系は見つけていない。旧 Yulang2 の例を読み替えず、実行もしていない。
- 次の候補は `MixedLiteralTrail477` の独立 cone witness を入口まで構成し、実際の typed source event を使えるなら最初の選択と全 ordinal を結ぶこと。I-89 に従い候補走査 G05/G10、残余 join G08、開いた tail G06/G07、一般 mode 等 G20/G21 は別で未着手。新規の意味論の質問は積んでいない。
- **I-95 を今回の +20 で受領。** G04 の期限は cycle 479 の報告まで。それまでに三条件が揃わなければ、残りを量化子と前提のある一つの `G04Producer : Prop` として明記し、証明も公理化もせず、次の行で名前つきの前提にする。G04 の数は閉じない。C480 は短縮の設計ノートから始め、既存コードや Audit は削除しない。今回その命題を書いた、とはしていない。

## 対象検証と引継ぎ

- Lean 4.35.0 の独立対象検証で標準範囲内の結果 82 件、ガード 11 組（既存の fixture の再生も含む）。新規 production 21、独立 Audit 24、既存集約は import 21 行だけ追記。I-94 の公式・単語境界の追加行検査に違反 0。集約を含む Lean 46 パス、設計・引継ぎ・heartbeat を含む全 49 パス。既存本体は変更なし。今回の Lean tree `ac88b2ecc8e95250455ce95914b53c9342f5a7d7`。
- 権威 `35d7ba8bc2bedb33b6043a89b35bc1bcdde86d90` が work の祖先と確認。実開始 `2026-11-28T00:32:39.160Z`。+10 `e96d90aa930736f228137c86869302ba52a2d8ec`、+20 `5b361f1f67be04a6f4cfbe5891ed4d3d07e9aa33`、+30 `c55d2bd293053bedccb341060dfe4a130b05006c` で Lean 凍結、+40 `cbf0e236c4da9e9d2bd9f7fa1d45b6de8482b1c7` は heartbeat のみ。I-95 を含む exact owner inbox を +20 で取り込み、入手時のずれでは止めず再照合。全体の verify-lean.sh と Lake build は dot では未実行。作業者を解放し、次回は最新 inbox を最初に読む。具体的なモデル名・使用量は不明。
