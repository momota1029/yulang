# Cycle 281 — 実 replay から有限なローカル chart を作る
現 packet の cross/self-check に、旧 source 上に残る版付き書き先の二方向 atom を加える。旧 raw Models に相対化した場合、各 atom は旧 source 上で読み取れ、全体の連言は旧 source への射影と厳密に同じ。従って「旧射影からモデルが失われる」ことと「このリストの中で新しく含意される atom がある」ことが同値。各 packet ごとの有限リストであり、任意の旧 family を通じて固定した有限 basis または一般 termination rank だとは主張しない。次は保持式を source/owner basis に展開し、同じ有限 chart を再設置全体に適用できるかを示す。
