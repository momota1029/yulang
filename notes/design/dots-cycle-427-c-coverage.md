# I-74 C coverage after C427

**この周に閉じた C の行: なし。**

[C426 の一覧](dots-cycle-426-c-coverage.md)を継承。C15 のみ、元構文による構造引数・元の子順・全可視候補と raw K2・同じ適合モデル内の正の辞書までを独立検証。

未閉鎖の理由: C426 の exact canonical R14 が integration にまだ無いため、R15 の独立局所規則と `DictionarySound`、公開 `check` の追加データ分岐、同じ形の `check_sound` の三点はまだ接続していない。狭い実行可能 reader / 辞書の補題は公開 check の範囲追加ではない。

健全性定理の固定形・旧分岐・語義は変更なし。**C の残り: 8 行（C15–C22）。**
