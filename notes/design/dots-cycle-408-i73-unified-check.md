# C408: 同じ Problem の検査器

I-65(1) exact integration `bcc13d217bd7d9dd65be080caa01fbb8cec201e1` の `dictionary_sound_R0` を確認。2 は `check : Problem → Result → Witness → Bool`。同じ State/root を C350 raw K2 経路と C403 の実 nullary leaf 経路で共有する。報告の木、結果、実書込みの順を比較する。出力のない二経路は実書込み列が空であることを検査。未対応 wrapper は false、言語の拒否ではない。データ witness に Classifies/モデルの証明を持たせない。次に (3) は同じ導出の replay と任意の fitting model での固定の意味を結ぶ。