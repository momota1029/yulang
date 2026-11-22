# C348 早期検証点

承認済みの支持付き入力・候補選定を旧 `Local` と同一視せずに受け取る、隔離した transaction の検証用境界。実 frame・物理 refinement・以前の choice の保護・全 pre-model の footprint 付き拡張をそれぞれ別に検査する。そこからモデル双方向、実 canonical child 順・物理位置、書込み Cell の由来、出力を追加しない子を生成した場合の literal 要求列全体の不変性を得る。native 接続や停止性は主張しない。
