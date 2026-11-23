# cycle 378 handoff — I-65 step 1: ordinary entry versus native dispatch

- 開始 UTC 2026-11-23T21:34:08.353Z。integration/m1-final `311024674c0af6cbeed84c86640f34d654205f6c` の standing、inbox、roles/inference spec を再確認。I-65、STOP なし。前周完了 `67435181b84910d54c5656e2828a34d519662e6d` を照合。expected-head/non-force の work/dots-main のみ。
- [成果の固定設計](https://github.com/momota1029/yulang/blob/1fede47fffdaa4d677627ef3b5f47bdbeabb64ae/notes/design/dots-cycle-378-ordinary-crossing-root.md)。

## 普通入口と native dispatch の区別（Lean で検証した部分を含む）

1. C321 の `Visit` を場合分けすると、どの普通 view・どの名前でも、「どこかへの訪問が存在する」ことは元の式が `Inspects` であることと同値。順方向は各 `Visit` の外側構文、逆方向は `Visit.here`。この最初の**普通**位置には支持付きの内部頭を要さない。より深く進むときは、各構文に対応する支持付き shape の証拠を要する。
2. 既に独立に native 側の実際の入口を証明した名前つき `.ordinary (.var n)` の範囲なら、検査する元の子パターンはその位置を最初の普通の訪問として与える。K2 はそこで未完出力も含む既存の全普通グラフに対して調べる。候補展開の入口がない場合に、これで新しい入口を作らない。根の K2 は候補の中を新しく訪れることとは別。
3. C369 の私的 `NativeOrdinaryInspection` の `visited` 欄は、同じ式が検査形なら、単に `.here` で埋まる。従って、この欄だけでは**native が実際にそのポートへ入ったこと**を認証しない。実際に訪れた native の親、同じ要求出現と候補、継承 mode、許可された正確な子位置/向きによる入口が別途必要。片側ポート計算、上端だけの物理許可、同じモデル値を入口へ読み替えない。現行言語に新しい拒否や優先順位は足していない。

## 検証と残り

- 22:03 UTC 頃に承認済みの実行環境が復旧。保持していた公式 Lean 4.35.0 で `lean --trust=0 -DwarningAsError=true -o …`、独立 Audit 2本も同条件で直接実行し exit 0。標準公理のみ（`propext`、`Classical.choice`、`Quot.sound` の部分集合）。全体 Lake、Rust は未実行。
  - [A](https://github.com/momota1029/yulang/commit/b160b0171273ee15b82505508bb78b1d8463901d): 独立した `NativePrefixCore377` と `OrdinaryCrossingRoot378`。固定依存を再構築し、5定理を監査。一方の元端点、実際の候補構文、同じ mode 表にある引数番号から、後で生成される value / row 比較の正確な仕事番号・向きが一致する。unused value はポートなし。C321 の普通訪問存在の同値も Lean で検証。
  - [B](https://github.com/momota1029/yulang/commit/56e61fed8beb928aaecee7ec89199628773bb1e9): `NativePrefix369` の正確な物理 adapter。さらに既存ソース56ファイルを不変の Git blob から再構築。最初は依存 match の `some` の等式で失敗し、証明項だけ修正後、対象と独立監査ともに exit 0。8宣言。 `original_from_installed_and_retained_author` は、実際の typed install、別 target の後続書込み、独立の完全アドレス許可、現在台帳の正確な元記録と論理 route があれば、実作者・slot のまま `NativeOrder362.node` による片側の元端点を得る。対象の物理足場は作ったが、その port に本当に候補が入ったことまでは新しく仮定・証明しない。
- 新規 Lean 3、独立 audit 2、barrel 末尾 import 3、設計・心拍・報告。固定コミットで全9変更パスと exact bytes／独立 Git blob SHA、凍結2ファイルの Git tree IDのみを照合。
- I-65 **1 未完、2・3 未着手**。実際の早期 native の入口と、許可された位置の K2 / 優先順位を独立に結び、C376 の同一出現の準備/保持/許可に接続する作業が残る。S1/S2 未閉鎖、C 後回し。fixture・仕様・定理文変更なし。仕様質問なし。旧 Local/C334 の読み替え・停止性は対象外。開始から約 36 分、利用枠不明。
