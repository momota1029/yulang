# C415 / I-74 C07 / X4 後半の検証

| I-74 の条件 | 実装・検証 |
|---|---|
| (a) 元の独立判断 | R7 は R6 に、有限二フィールドの閉じた実入力と実残部から、別の宣言済み role の where 子を確かめる局所の選択だけを足す。根・子で可視候補全体がそれぞれ一つ、実宣言の ordinal と role 表を読む。`dictionary_sound_R7` を固定の `DictionaryEvidence` について同じ State、すべての Fits モデルで証明。 |
| (b) 実行可能な有限データ | `ClosedWire` は元の行の添字、実宣言の添字、raw K2 の証明書の有限データのみ。選択済みという主張や残部の内容を証人から受け取らない。元行の `x:int,y:str` と別の実残部行を読み、`x` だけを引いた残部の位置を一意の split から再構成する。 |
| (c) 同じ健全性 | `ClosedResidual415.check_sound` は同じ入力の元の正確な親＋子の木と辞書を証明。子は宣言通りの `[親の出現,0]`、元 binder を残部 point に捕捉、空書込み。旧分岐は定義的に unchanged。 |
| 元入力に基づくこと | `closed_source_subtraction_exact415` は元の normalized field 列から prefix x だけを除く。`split_is_semantically_derived_from_closed_source415` は split がなくても元の閉じた行と残部行からモデル上の分解を導き、実行版では別途 retained split を照合して実際の名前を固定する。候補・元 clause の序数や残部の名は別証人で入れ替え不可。同じ型の別名を選ばない。 |
| 対照と限界 | 並べ替えた元行・宣言で正確な添字を使い正例。二重の同形の残部アドレス、偽残部行、元 split なし、偽 declaration ordinal、子省略、role の fallback のみ、親／子の raw K2 はこの正分岐で false。従来の親 raw K2 拒否はそのまま true。別 role の子が同じ残部で実際に選択する断片。同じ role への再帰・複数候補・任意の tail・Rust／パーサ／停止性／一般完全性は対象外。 |

固定コード `7594718fae005a652354ccd40d1e64d94306358e`（Lean tree `5dc336814391429d07ea6cf7bf486d16a3a11542`）。仕様 [6.3 の X4 後半](https://github.com/momota1029/yulang/blob/5f52a59fdb675938fcd0f3120293d5527aa9bcc4/spec/06-roles.md#L106-L109)。型として確認した tail は `{y:str}`、`emptyRecord` の意味を「x が絶対に存在しない」と強めない。

固定コミットから C415 11 モジュール／監査 6、C414+C415 22／13、C408 基準の C409–C415 58／41 を正確な Git 実バイトに戻して strict Lean 4.35.0 replay（すべて exit 0）。最新公開入口を使うローカル結合テストは実例 10 正例 true、誤報告・未対応など 4 対照 false。C415 の 36 宣言の依存は標準公理のみ。
