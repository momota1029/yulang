# C440 後の C の進捗

元の [C423 一覧](dots-cycle-423-c-coverage.md) の番号と意味は維持する。

| 行 | 状態 |
| --- | --- |
| C01–C19 | 開始時の正本 `integration/m1-final@1d2084ac7278aa7b9eb29eea86caaf740a7bc567` の Lean `3fa551ff461d24ab106f9dca1f55cdefd742b49e`。C439 の exact source 採用済み。 |
| C20 | **`work/dots-main` の scoped 完了。** 元の入れ子 nominal 候補と declared variance、外側 inherited invariant の [実辞書／検査／健全性](dots-cycle-440-c20-verified-entry.md)。`dictionary_sound_R20`、plain-data `check`、固定外形 `check_sound`。科学 pin `edaebd19d22cd90ee6b7ae7cfce675ae4b2eb578`、Lean `5d57993d91ace99c523aaca4b6d8804d4b1498aa`。 |
| C21–C22 | 元の一覧どおり未着手。 |

**C の残り: 2 行（C21・C22）。** 今周の追加は C20 一行だけ。比較 backend の任意深さ証明、元の literal X14/X17 のフロントエンド未検証と scoped checker の範囲を区別する。完全性、証人生成、停止性はこの数や完了条件に含めない。

最終照合時の正本 `integration/m1-final@1d2084ac7278aa7b9eb29eea86caaf740a7bc567`（Lean `3fa551ff461d24ab106f9dca1f55cdefd742b49e`）に C440 の exact 15 blobs はまだ揃っていない。C20 の scoped 完了は `work/dots-main` 上。正式取込・監督役の全体検証は別。
