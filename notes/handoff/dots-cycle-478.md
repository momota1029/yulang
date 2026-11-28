# dots cycle 478: 同じ相の入力に必要な元座標と、実 compiler が発行する番地の切り分け

道具: モデル名不明、Lean 4.35.0、GitHub; 委譲: モデル名不明、1 回、task `/root/yulang302_resume`（追加委譲・Codex thread なし）

**G04 は未完、残り 20 / 24。** C477 の有限深さの named/inline 経路を維持した上で、今の一候補・検査済み GD の範囲では、head 引数、順序つきの既存 raw/author ordinal の対、元 AST の全 pose 一つを、同相の元入力と照合して再生できる形にした。raw・source table と観測用 checkpoint は別入力。これが実 compiler により発行済み、とはしていない。新たな raw 名・式、既存 State/Fits・規則・checker・spec の変更はなし。

## 今回そろった局所結果

- **座標からの exact replay。** `recoverOldStamps478` は書き込みや名前の割当てなしで、各 raw ordinal と authored ordinal が同じ旧式を読む場合だけ、その式と元の ordered pairs を復元する。`readSingletonInputBeforeCapture478` は旧 `BeforeCapture` の独立な結果をそのまま再生し、単一候補では可視 ordinal=0 と宣言の frame を実 table から復元する。各証拠を再生する iff あり。actual fitting 例では同じ文字列の二つの旧 row の組 (2,1) と (3,3) がそれぞれ実 C332 trace の別々の mark として残り、別式・範囲外 ordinal は通らない。
- **元 pose は最終出力に残る一つの実データ。** `parseOriginalActionPath478` は既存 `Origin` に従い、元 pose 一つから最初の field、全構造 action と相対 segment を復元する。独立に同じ元 pose を持つ解釈は同じ action と分割。正規化で消える同一 join は、実に異なる元位置を一つの compiled path に落とす。実 fitting 例では同じ ordinal 1 に左・右の二つの元 pose が正しく残り、どちらが要求されたかを compiled 側だけから復元できない。沈んだ重複 field や残余の異なる join を、新たに訪問可とはしていない。
- **最小座標の検査と健全性。** `replayEventFootprint478` は上記の座標で正確な旧 report を再生し、その逆に成功から同じ元 occurrence・実 registry ordinal・head 引数・元 pose、全 checkpoint と旧混在経路を得る。余分・不足・並べ替えで checkpoint をすり替えない。判定は同じ raw 型商、全 proper prefix は安全、全ての同じ `FitsFull` で元入力の型付けを保存する (`referenced_event_can_be_checked_against_one_original_fitting_state478`)。出力なしの実 fitting 例で field 30→40→50 の named/inline/named 経路と終点 true、違う元 pose、引数、物理/author 座標の不一致を確認。負側は旧 checker の checked quotient safety をそのまま使い、`none` を K2=false と扱わない。
- **実 producer と現在相は別。** 実 C332 compiler receipt の新しい ordinary 行の例は ordinal 3 / target 16。実 after snapshot では読めるが、同じ ordinal は before ではどの authored table を渡してもない。after でも、対応 authored index を別途突き合わせる必要がある (`actual_old_compiler_job_is_a_post_input_ordinal_not_a_same_phase_read478`)。Native360 の実 output receipt は元 demand に実 output ordinal を要求し、同じ出力なし要求からは発行されない。別の完了済み出力が入力を支える場合でも、旧 board の exact release/実 address/版の根拠が別に必要。旧 `attach` は既存式の一致にすぎず、同じ raw を source または未完 output と指定したデータがどちらも attach できる。したがって `attach`、既存の raw 値、compiled trace のどれも、実 input event の発行証明ではない。

## 残り

- 必要なのは **実際の source 型付け／捕捉 event が、その要求の選択済み元 pose と今の同じ相の raw/author 座標を発行したことをつなぐ証明**。現在の yulang3 `9733cdf302ec06e7337cd646ce0052a00e184fe0` は C477 と I-95 の同期で、spec §6.3 は `a3d903781fef0691b773f886ba8976a6b4ac871d` のまま。型付き発行箇所は現行の parser-only Rust 経路では確認できなかった。過去の Lean の出力完了・capture 生成の別相をここへ移さない。
- I-95 は **C479 の報告まで**。揃わなければ残りを量化子つきの一つの `G04Producer : Prop` として書き、証明したり公理化したりせず、次の行には名前つき前提と未完件数を正直に残す。その次の C480 は統合入口と Audit の短縮設計から始め、別承認なしに削除しない。この周にその名前つき命題は追加していない。候補走査 G05/G10、残余 join G08、tail G06/G07、一般 mode 等 G20/G21 は別。新たな意味論の質問なし。

## 対象検証と引継ぎ

- Lean 4.35.0 の独立対象検証（--trust=0 -DwarningAsError=true）で標準範囲内の結果 62 件、ガード 10 組（既存の fixture の再生も含む）。新規 production 18、独立 Audit 24、既存集約は import 18 行だけ追記。I-94 の公式・単語境界の追加行検査に違反 0。集約を含む Lean 43 パス、設計・引継ぎ・heartbeat を含む全 46 パス。既存本体は変更なし。今回の Lean tree `fa6a703c3f51ba331df12725e0eab6dca1a4c84d`。
- 権威 `579f3019320e7206b0cbac90d45256ff14636eee` が work の祖先と確認。実開始 `2026-11-28T01:26:21.105Z`。+10 `a68f6a6086908537dc2f5a514fa29687295dcc7e`、+20 `c0d8530d9d5557b5d1904864d0127194da20af06`、+30 `8e4aad2fb20c4c7cfe1b31ac9f4106c41dd0a0bb` で Lean 凍結、+40 `083e5624731ed10757ca7aceb9242990ea10a14e` は heartbeat のみ。+10 で C477 の完全な採用を確認。I-95 の inbox は変更なし。全体の verify-lean.sh と Lake build は dot では未実行。作業者を解放し、次回は最新 inbox を最初に読む。具体的なモデル名・使用量は不明。
