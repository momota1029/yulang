この周に閉じた C の行: **なし**。C14 は未完。元のレコード端点からの射影と、元の関連型出力先の保持を、同じ適合モデルで証明した。

## 証明・公開した範囲

- `read_retained_Pick_write_sound423`: 実際の元 record 端点、元 B6 の関連型右辺、ordinary State に既存の固定行を、証人の位置から照合する。元出現・宣言順・出力順・target を変えず、任意の適合モデルで実射影と target が同値となる。共通名、異なる変数間の両向き制約、既存行の位置を順にたどる有限パス、required のみを束縛する既存行の四つを検証した。出力の証拠は、ここでは候補選択の判定と分離している。
- `prepared_write_preserves_full_projected_capture_and_actual_value423`: required / optional を別々に元 field の区間へ、mask を元の残余区間へ結び、同じ required 射影を実 B6 出力に渡す。両 channel が非同値でも実 target に結べる例（出現 `[61,423]`、宣言 1・出力 0・target 12、旧中心 record 行なし）を、元の B6 atlas と同じ適合モデルで検証した。証人の行やパスを変えても同じ出力であることも証明した。
- 途中の I-75 に従い、低依存の `source_endpoints_have_projected_meaning423` と実準備入口の `checked_preparation_supplies_I75_head_and_actual_target423` を追加した。中心に新しい行・名前を作らず、spec 6.5 が要求する端点射影・mask の証拠を、元出力保持とは独立に得る。
- 既存 Heads367 の隔離試作では対応する source と意味の構成子を足し、実読取りから作った新 head に対する局所 soundness を strict Lean で確かめた。**試作は正本には未反映**。C422 の旧 head 全枝を対象とした否定を新構成子にまで広げないこと、由来を持つ端点射影を旧 `NamedMixedReceipt401` の単なる名前や中心に読み替えないことを、[移行ノート](../design/dots-cycle-423-projected-retention.md) に記録した。

## 境界と検証

- 健全性の局所補助と準備入口のみ。今回の公開コードは固定 I-65 の文・正本の旧 head・R13 の checker を変えない。C14 の正本の source/head 移行、R14 と同じ元 receipt に対する公開 check 分岐、dictionary/check sound は未完。既存の不対応は仕様上の拒否とは数えない。spec の W/Hold を含む例全体が新入口を通ったとは主張しない。C15 には着手しない。
- Lean 4.35.0 `--trust=0 -DwarningAsError=true`。固定コミット `7e882f6e1ca10e57dbc9a120941a5e1f82621ed9`、Lean tree `6c9271038132d871565a7f85fbda7bcfcb33b233` の exact-byte replay を C423 単独、C422＋C423、C409–C423 の範囲で通過。旧入口の 42 例と公開 R13 の 13 通りも照合。新規の独立監査は45件、公理は標準のみ。[検証ノート](../design/dots-cycle-423-c14-verification.md)。Yulang2 実機・Rust/full build・停止性・NoFalseRejection は未検証。
- 最終照合時: `integration/m1-final` は `b2fe5a3d9324aa1ef2964c95f7445884ee4dd66e`、`integration/types` は `1b9361bb6dfca0642ee7d7e149e2e224bff535c0`、I-75 Inbox `42ed184178357af37ba86de355218d720cb36746`。統合先では C422 の Lean tree 一致、C423 の成果は work/dots-main の固定 pin。50分経過後に通常の最終確認を開始し、この heartbeat で書込み作業を解放する。

**C の残り: 9 行（C14–C22）。**
