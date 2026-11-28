# dots cycle 479: G04 未完、名前つきの前提を残す

道具: モデル名不明、Lean 4.35.0、GitHub; 委譲: モデル名不明、1 回、task `/root/yulang302_resume`（追加委譲・Codex thread なし）

**G04 は未完、残り 20 / 24。** I-95 の期限に従い、未証明の残りを `G04Producer : Prop` として `lean/Yulang/GeneralDeclarativeI65I74G04Producer479.lean` に一本化した。前提自体を証明したり公理として追加したりはしていない。現行の compiler がこのデータを発行することは確認できていない。以後 G04 に依存する箇所では `(producer : G04Producer)` と明示する。

## 命題の入出力と検証したこと

- **独立な入力。** 任意の元 `FullProblem`、単一可視宣言の検査済み GD、実際の入力引数について、旧入力に支えられた型付け `Read`、元の構文にある選択済み action、同じ既存 raw 上の物理座標・正則型商での訪問を要求する。既存 report が成功したことは前提にしない。すべての proper prefix が安全、正負は終点自身の等価類で判定する。
- **未証明の結論。** 一つの入力相発行操作が、その元入力を参照する全ての対象イベントに、有限の証拠を返す。同じ要求、raw snapshot、元宣言 ordinal・引数、元／compiled の両 path、物理的な全経路と同じ報告を照合する。source 枝は旧 raw/author の対を順序つきで検査し、その同じ順序の行で独立な型付けが成立する。既に元の選択順が保存されていれば同じ順序・座標をそのまま使い、空列で代用しない。release 枝は別途保持済みの同一 owner / raw ordinal / equation / Write / origin ordinal の対応と実 release の両方を要求する。同じ target や別の released Write では足りず、release を authored に読み替えない。この対応台帳を新たに発行する証明を置いたわけでもない。
- **実装との境界。** 上の命題は論理上の発行操作の型と照合条件を明示するもの。実際に閉じるには、情報を落とす前の compiler 相がその操作を実装することを示す必要がある。添付表・旧 checker・後から同じ report を選ぶ関数だけでは、元の event が発行したことにならない。C332 の実 fixture では raw・author の異なる選択が同じ元 State にあり、実の後段 receipt が丸ごと同じになるので、そこから両方の正確な選択を復元できない。現行 yulang3 `677db044de983430464675419eeb4cf206631bb8` は C478 の同期。roles/spec と parser-only の Rust 側にこの型付き発行を追加する変更はない。
- **成立した補題。** 独立な経路を finite data に再生し、その成功を同じ経路へ反映。任意の適用入力で source route を独立に選んだなら、issuer を仮定せず幾何と正負の証拠までは具体化できる。名前つき前提から発行結果を取る場合は、全ての同じ `FitsFull` で元の型付けを保ち、正確な prefix と終点を得る。これは前提を消す証明ではない。
- **実例。** 出力なしで `4={30:{40:{}}}` の元 State に `FitsFull` があり、独立な型付き入力と有効な prior source が存在し、field 30 の inline 終点で安全（false）。別の出力なし fitting fixture で field 30→40→50 の既存経路と終点の K2=true を読み、author ordinal、元 pose、宣言 ordinal、最初の物理位置を差し替えると失敗することをガード検証した。 `none` は安全の証拠としない。

## 残りと範囲

この範囲で G04 を閉じるために残るのは、実 compiler の入力相が元の発行履歴を供給する証明。release 側の対応は別に保持済みである場合に限る。既存 State / Fits、checker、raw 行・名、spec は変更せず、C479 の証拠用モジュールを追記した。候補走査や曖昧性前の優先は G05/G10、残余 join は G08、tail は G06/G07、一般 mode は G20/G21。別の意味論の判断は求めていない。I-95 に従い、C480 の最初は累積入口・狭い分岐・Audit の短縮設計ノートを一つ書く。削除は別の承認まで行わない。

## 対象検証と引継ぎ

- Lean 4.35.0 の独立対象検証（--trust=0 -DwarningAsError=true）で標準範囲内の結果 30 件、ガード 3 組（既存の fixture の再生も含む）。新規 production 11、独立 Audit 14、既存集約は import 11 行だけ追記。I-94 の公式・単語境界の追加行検査に違反 0。集約を含む Lean 26 パス、設計・引継ぎ・heartbeat を含む全 29 パス。既存本体は変更なし。今回の Lean tree `a24cabe42861ba7813214b35d5a6fcd419ba7578`。
- 権威 `08e3aaa66bdab9d4adbf9b65ce6e868c9a74df08` が work の祖先と確認。実開始 `2026-11-28T02:28:20.000Z`。+10 `b821eb7192ca84b464df934bd6d26bcef3b7206f`、+20 `c50d9e9e07afbb7ac875de66bee943860a7f879f`、+30 `b820a889c4543cec0e23fadcbff646db95046ebb` で Lean 凍結、+40 `f88ceadbb4bf2f05a6663dfcbe78c7cfd8dbd4ee` は heartbeat のみ。開幕から C478 の完全な採用を確認。I-95 の inbox は変更なし。追加 import の組合せも対象検証済み。全体の verify-lean.sh と Lake build、および Yulang2 実機は dot では未実行。作業者を解放し、次回は最新 inbox を最初に読む。具体的なモデル名・使用量は不明。
