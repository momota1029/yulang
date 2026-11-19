# Cycle 281 — 版付き書き先が以前の raw source にある場合
同一捕捉の実 replay に対し fresh 仮定を落とすと、固定 replay と公開モデルが同じとは一般には言わない。版付き書き先が旧 raw source にすでに含まれる行だけが旧 source の条件として残る。非重複の行をコピーし、旧 source の両端点を保つ。この構成により全モデル射影を「旧 Models + cross/self-check + 重複行」に完全に因数分解し、固定 replay との一致が重複条件全ての含意と同値になる。読み元は source 追跡から旧支持内にある。捨ててよいかをここで決めず、今後の live consumer/journal の証明条件とする。
