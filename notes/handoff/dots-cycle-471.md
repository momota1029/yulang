# dots-main handoff: Cycle 471

道具: モデル不明、Lean 4.35.0; 委譲: モデル不明、1回、task /root/yulang302_resume（追加委譲なし、Codex thread なし）

- scheduled: 2026-11-27 18:30 UTC; actual start: 18:26:20.888 UTC; normal completion gate: 19:16:20.888 UTC; hard cap: 19:21:20.888 UTC。
- Authority: `integration/m1-final` `48666cd6595efc477ab41204ca7023b8b49f82a2`。C470 の handoff・heartbeat・設計を取り込み済み。I-93 `0e8f12dc7e6438ee8aa512feaa1e30c39773bfa9` のまま。C471 の Lean は作業枝の `d0f1bd50791f1fe478154c3885edf7d8ef445e5a` で確定、Lean tree `f2b093c753665439f70016554ea287a70c159e92`。統合枝へは書いていない。
- 設計: [C471 I-93 同相 source fold](../design/dots-cycle-471-i93-source-fold.md)。

## 確認したこと

既存の C464 の単一候補・GD 検査済み・出力なしの入力を、元 occurrence `[71,2]`、宣言 218（role 19、元宣言 ordinal 0）、head 引数 0、元 `payload` 経路に固定した。raw を書き換えず、元の `4={30:{40:var 5}}` と `5={40:var 5}` を使う。別途根拠のある source 入力だけを読み、実際の旧 C332 の根付き読取りで binder 3 から既存の 5 を読む。同じ元 `FitsFull` のもとでも、外側 4 は循環へ到達するだけで安全、観察された field30 の inline は 5 と等しい型なので同じ商の循環上で K2。5 を元の報告位置に置き換えていない。元の raw には名前も行も足していない。

型観測を構成子と全ての順序付き子から検査し、到達部分の閉性と最小分割を有限データで照合する。完全な観測グラフでは、同じ型へ戻る非空経路の有無を両方向で証明した。負例は「証拠が見つからない」ではなく、検査済みの最小観測グラフ上で循環がない結果。未解決の子が実際に到達範囲にあれば未確定。無関係な未解決ノードは妨げない。nominal は明示引数だけを扱い、body は開かない。現在の分割検査は有限関係を列挙するので、性能は未評価。

元経路・元宣言・代表位置の差替え、未完出力だけの source、必要な子がない表、同名の競合定義、過細分割と誤合流を対照にした。公開 source の安全判定は外側引数で確認した。一般の選択 field について安全を生成する入口とはまだ異なる。

## 検証と範囲

- 既存 Lean ファイルは不変（集約ファイル末尾の 7 import 追記のみ）。新規 production 7、standalone audit 7。公式 Lean `--trust=0 -DwarningAsError=true` で絞った依存と各対象を再生し、39 の axiom 照会は標準のみ、7 組の実行対照が期待どおり。追加 import も照合。全 Lake / Rust / 旧 Yulang2 は再実行していない。
- 旧 Yulang2 は既存 `work/dots-audit` の比較表 `0d75bdb801151589d5aeef453fd6b7dfa414baec` を参照した。X8/X9 は構造型 μ を出していない、X10 は空の record-head impl dump まででループ・結果未確認、X11 は parser で失敗。いずれも I-93 の K2 検査済みとは数えない。
- **G04 は未完了、残り 20/24 行。** 公開の実入力接続は同相・単一候補・GD 前提で、実入力の source provenance は別途与える。現行 compiler がその証拠と任意深さの元訪問を生成するところ、実入力の一般 alias/正規形と安全 field への完全性、既存 checker への接続は未証明。非対応は言語の拒否としない。GD、G05/G10、G08、G06/G07、G20/G21 の範囲は広げていない。
- 次は K2 の正負を前提にしない同相の元 field 証拠と、現行 compiler の input event が供給できる根拠を分けて接続し、同じ場所で安全／循環を再生する。次回は最新 inbox を再確認する。
