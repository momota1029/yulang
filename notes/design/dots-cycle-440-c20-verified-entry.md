# C440 — C20 の scoped 公開入口

`GeneralDeclarativeI65.I72.NestedInvariant440` に独立規則 `nestedLocal`、`R20`、データだけの `Wire`、`check` と `check_sound` を追加。既存の宣言判断、元の `I72.DictionaryEvidence.node`、Handoff の報告形式、および以前の witness すべての Bool（定義的等式）は変更しない。

- 元の同一 request の actual 原点二つと raw 行二つから `Outer(Inner 'a)` を照合。候補宣言は可視集合の全体が一つである場合だけ。外側 stored invariant、内側は著者 metadata 由来の invariant / covariant / contravariant のどれか。内側の interval の端点と実際の中心名を一つに潰さない。葉で where・出力が空の実際の source trace と同じ辞書を、同じ元の状態の任意の適合モデルで得る。
- `CandidateTape` の元の ordinal、`ModeWindow` と `DeepRead`、`Local.evidence` を直接使用。外側 raw の alias-class 全てを走査し、安全を必要とする実際の root と内側 site を区別する。raw root K2 は旧ルートでそのまま受理される。認識できない中間 raw 行の構成を言語の拒否にしない。
- 実入口の standalone 正例三つ（list の内側に invariant list / covariant box / contravariant 宣言）。端点は厳密に異なり、同じ中心名が二つの適合モデルでそれぞれ別の型を表しても同じ根・辞書・端点・中央の拘束を持つ。不正な mode、明示 atom なし、元の issuer なし、間違った raw 行・結果、実際の競合候補、外側 raw alias の別 site、実際の内側循環をテスト済み。原点の interval は片側の外側頭の二つの endpoint に共通。既存の comparator に深さ制限はないがこの checker の追加分は構造深さ 2 の範囲。
- I-74 の三条件をこの scoped row で満たす。文字どおりの X14 の float ソース変換、X17 の関数ソース簡約、全入力・入れ子全深さの決定・入出力の任意混合は未主張。X19 の既存検証と区別。

今回追加した 4 production source と独立 Audit 5 ファイルを公式 Lean 4.35.0 `--trust=0 -DwarningAsError=true` で個別検証、31 axiom 行は標準のみ。全体/Rust 検証は未実施。
