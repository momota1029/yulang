# Cycle 282 — compiled 共通モデルを使う actual successor interface
旧 kernel の非 install 一歩を (actual かつ plan 数不変) として厳密にそのまま使う。install の分岐だけを compiled 共通モデル＋live fixed 表へ置き換える。到達前提込みの relational driver を定義し、任意の実到達点から全一歩・有限 path が行き来することを示す。従ってこの無制限 driver は旧反例の非停止性も持つ。cycle 281 の chart/phase を別に交差して得る guarded driver では Acc と旧守備範囲が保たれる。元の raw snapshot を補助データに使うため、有限記憶の独立 executor とは呼ばない。
