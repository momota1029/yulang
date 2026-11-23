# cycle 375 handoff — I-65 step 1: actual typed install versus release permission

- UTC 2026-11-23T18:33:12.294Z 開始。integration/m1-final `bc7242cb76edefbe5a6ca7849393408b3c48a895` の常設指示、inbox、roles/inference spec と前周完了 `42520193511186726e3ef5ffddad0fae16a3ed73` を照合。最新は I-65、STOP なし。書き込みは work/dots-main の expected-head / non-force のみ。
- [設計固定版](https://github.com/momota1029/yulang/blob/87caf43eb7df95d318945305f030a86430127812/notes/design/dots-cycle-375-retained-release-cut.md)。

## 今回のソース上の導出

1. C360 の原ソースからの typed produce/compile と実際の `install` が成功した直後は、固定 target にまさにその書き込みがあり、作者の版は active、active position は一意。従ってその正確な行の release が通ることと、**出現・版、元宣言位置、出力位置、元等式位置、固定 target を含む全アドレスが独立許可表にあること**は同値。行の値や target だけの一致では別アドレスを通さない。もとの成功 install と現在の独立許可は別条件。
2. 異なる target だけへの有限回の C360 append は、対象の実際の lookup と active リストを保持する。同じ target への2回目の成功 install は freshness に反する。版更新・削除・許可撤回はこの結論の対象外。
3. 現在の fitting model で release から真のコードの解釈を読み、同じ assignment に対して C372 の保持された普通等式の意味を得られる。C360 の既存実例の `Sequence.final` は、継続の普通状態と、release を確認したままの board を実際に組み合わせる。普通の保持から型つき許可や選定を推測しない。
4. 残るのは、正しい元出現を**実際に選んだこと**、初期 allocation/capture、独立許可の由来、早期 native/candidate K2 と再帰の選定。今回の導出は任意の solver 成功からの証人生成でも言語規則追加でもない。仕様質問・fixture なし。

## 検証と残り

- 2026-11-23T19:12:49.117Z UTC の検証ゲートまで承認済み実行環境は offline。既存 Lean ソースを固定して上記を導出したが、今回は Lean / Lake / Rust を実行していない。C371/C372 の私的な保持草稿の入力と依存範囲を集めて再生準備し、未検証の追加は公開していない。
- design、canonical heartbeat、handoff の 3 ファイルのみ。固定コミットでバイト／独立 Git blob SHA を照合。C374 の Lean tree `d4b484dd4db34001f1a65a439422ba996480d467` と凍結二つの blob ID を Git tree メタデータで確認した。
- I-65 **1 未完、2・3 未着手**。S1/S2 未閉鎖、C 後回し。停止性・旧 Local・C334 の読み替えは対象外。開始から報告まで約 39 分、利用量枠不明。
