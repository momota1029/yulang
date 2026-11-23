# cycle 373 handoff — I-65 step 1: stable source selection and retained event identity

## 起点と指示

- 開始 UTC 2026-11-23T16:31:39.967Z。最新 `integration/m1-final`: `c8143d63f5ea70cc5f7bb51fe09ec1da0741cb01`。standing orders / inbox / role・inference spec を照合、I-65 の 1 が対象・STOP なし。前周の完了 `f480139d97165bb3330a32a4e7c837d9e7211816` を読み返した。公開は `work/dots-main` だけ、expected-head / non-force。
- 成果の途中固定版: [C373 source note](https://github.com/momota1029/yulang/blob/f1cb853260b6a33ea51afe4ebaaf8823070a0829/notes/design/dots-cycle-373-visible-frontier-cut.md)（blob `c69f835b9eeb0841321be8f120aff786fe4855ea`）。

## 今回のソース上の導出（Lean の新規実行ではない）

1. 全可視宣言を覆う二つの C367 `CandidateTape` が**同じ現在状態・同じ出現の要求**に対して `TapedMatch` を持つなら、台帳が同一物理スロットで整合する限り、二つが選ぶ宣言は同じ。一方の `actual_matched_row` が返す実記録の頭を、他方の選定済みテープが別宣言の rigid rival として排除するため。
2. C367 の排除で意味モデルを使う箇所は「同じ物理スロットの二つの原記録は同じ端点」だけ。これは C368 の `SlotCoherent` の定義そのもの。actual route と `SinglePhysical` を使ってスロットを同定し、台帳整合性で元の端点を同定する。残る通常の枝と join の枝は既存の宣言モード／構文で矛盾する。状態を満たす普通のモデルがなくても、この限定された同一性にはモデルは不要。逆に、`Fits` のある場合は同一スロットを同じ関数で解釈するため、この整合性が従う。異なる物理スロットを論理名の等しさで同一視しない。
3. 一つのテープ内では `Stores` に沿って実際の可視位置を辿れる。singleton `live` は、宣言値が同じ場合も含め、二つの照合位置を許さない。この位置はあくまでその可視リストの位置で、物理書き込み位置ではない。C372 の保持イベントは、そのイベント側の**同じ状態・出現で実記録された頭**に対して `BodyLayout` を合わせる。宣言の一致だけで別の観測の捕捉・割当て・順序付き子・型つき release を代用しない。
4. 実際の完全な選定に必要な早期 native/candidate K2・優先順位や、実際の源からイベントを得る義務は残る。`TapedMatch` または body 成功そのものを最終選定とは呼ばない。言語の受理範囲、定理形、fixture は変更なし。意味論の質問なし。

## 検証と残り

- 2026-11-23T17:12:53.032Z UTC まで承認済み実行環境が offline。GitHub 上の固定 Lean ソースに沿って上記を導出したが、Lean / Lake / Rust は実行していない。C370〜C372 の未検証草稿は公開せず、新しい Lean 草稿も積まなかった。
- 公開差分は design note・canonical heartbeat・本 handoff の 3 ファイルのみ。固定コミットでバイトと独立 Git blob SHA を照合。Lean tree `5f2ecd6eaa09d81f6cdcf36d68c6b37747fdf3ec` 不変。凍結 2 ファイルは Git tree の ID のみ確認。
- I-65 **1 未完、2 と 3 未着手**。S1/S2 未閉鎖、C 後回し。次の実行可能な機会には C370 の独立 rank、C371/C372 の普通 body / allocation / retained event の順に実検証し、早期 native inspection と、どの実出現の保持イベントを使うかの独立した証拠を詰める。旧 Local・C334 の読み替え・停止性は対象外。開始から報告時点まで約 41 分。利用量枠不明。
