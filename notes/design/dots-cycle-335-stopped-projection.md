# C335: 実際の成功停止から通常状態を取り出す

まず既存の実 C276 Display (list int) 実行に結ぶ。raw の slot は既存の source/rowSource に読み下し、実中心は現行 Site による。scalar の記録と point 型引数を持つ opaque nominal はそのまま普通の等式にする。行パラメータ・非点 nominal や投影不能 head は黙って消さず、この断片の射影は失敗する。raw source の初期射影で裏づけられた行だけを source とし、停止時に普通に真であるだけの行に由来を与えない。

目標: 同じ任意の assignment に対する raw/通常 Models の同値（上の断片）、出現を保持した固定子順と確定 target の取り出し、raw の実成功から witnessed 診断木と辞書への戻し。停止済み範囲のみ、時間・停止性の主張なし。
