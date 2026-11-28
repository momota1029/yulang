# C482: 元の入力位置と型商観測をつなぐ検証

I-97。C481 の平坦互換は変更・削除しない。integration への採用前なので段階 2 は開始しない。

1. 旧 `Read`、`Closed`、`Spine` を独立な判断にする。同じ旧 raw ordinal と別途根拠のある source ordinal を含む有限 card を検査する。元 capture の順と式を返し、`Attached` のもと全カードの成功を反映し、任意の独立な Read から有限カードを復元する。これは入力の型付けの検証であり、元の binder や join を K2 で調査できることは意味しない。
2. 元の prechecked singleton head、指定された元 occurrence と経路、同一 raw での選択済み各物理座標、読み取った source 側の旧行を結ぶ。名前のある子だけ exact raw/author 対と既存 alias を検査し、inline の子は元の式を比較する。型商の終点と安全な途中点、要求の全実引数の安全を同じグラフで検査する。独立な先行 source 根拠を仮定して、同じ全 `FitsFull` で元式とその型付き子が合うことを示す。
3. 既記録の旧序列・source/release 所属と、検査に使う card の存在を分離する。カードが同じ型を再現しても失われた順を逆算しない。完了出力は先行した exact release の address・version・grant と実元行が結びつく場合だけ。境界が残れば G04 を閉じず、新しいグローバル tag を付けない。G05 以降には進まない。
