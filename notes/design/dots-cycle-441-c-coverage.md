# C441 後の C の進捗

元の [C423 一覧](dots-cycle-423-c-coverage.md) の番号・意味はそのまま。

| 行 | 状態 |
| --- | --- |
| C01–C20 | 開始時正本 `integration/m1-final@2e47eb95797eda5d68d1b62ac1664fe07cb1d2c5`、Lean `5d57993d91ace99c523aaca4b6d8804d4b1498aa`。C440 exact 採用。 |
| C21 | **`work/dots-main` 側で scoped 完了。** 明示的に別 binder を持つ `ref _ 'a` の row/value の順序・kind・source-derived variance、元の実捕捉と辞書を [R21](dots-cycle-441-c21-verified-entry.md) で確認。3 条件 `dictionary_sound_R21`、plain-data `check`、固定外形 `check_sound`。科学 pin `658106bae52323f830bec55a8ee3349b2815774e`、Lean `f9471c73c28ed615317a4de8ff847af8b093e97d`。文字どおりの `ref _ int` は [既存 named carrier 内の未対応](dots-cycle-441-c21-literal-boundary.md)、B3 の rank-2 は別。 |
| C22 | 元の一覧どおり未着手。 |

**C の残り: scoped 一覧の 1 行（C22）。** Literal・rank-2・一般 completeness や solver witness 生成を閉じたとは数えない。元の literal の言語仕様を変えていない。

最終照合時の正本 `integration/m1-final@2e47eb95797eda5d68d1b62ac1664fe07cb1d2c5`（Lean `5d57993d91ace99c523aaca4b6d8804d4b1498aa`）に C441 の exact 13 blobs はまだ揃っていない。C21 の scoped 完了は `work/dots-main` 上。正式取込・監督役の全体検証は別。
