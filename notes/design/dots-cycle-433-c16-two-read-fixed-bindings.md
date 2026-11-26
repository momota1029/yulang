# C433: 二子の実 read packet は元の同じ固定出力に着く

前提は、二子の独立データ読取器が返した packet。元の 0/1 の occurrence、元の「item」「seen」の名前と出力 ordinal 0、同じ正確な物理 target を、適合モデルを見る前に合わせる。実 read が使う限定 R15 child reader の `noOtherLiteral` から、同じ target の保持済み RHS 自体が一致する。意味上の等しさから address を同一視しない。正例の実 packet から両方の座標を取り出し、具体的な適合モデルに辞書の意味も確認。

これは独立 supplemental reader の境界を明示する補題。公開 R16 の singleton 分岐、旧経路、宣言仕様、カバレッジを広げない。一般の場合の生の式の同一性は主張しない。
