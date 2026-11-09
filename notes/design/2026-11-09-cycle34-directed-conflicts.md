# Cycle34: directed scalar conflict certificates

部分目標: 任意の n と State n について、独立 Derived の相異なる scalar の
下界・上界が同じ slot に到達することと有限チェックの成功を同値にし、
成功が全普通制約モデルの不存在を含意することを証明する。
検出しなかったことは充足可能性を意味しない。構造型や直接base間の矛盾などは対象外。
これは独立な拒否理由の証明であり、言語の最終分類ではない。

接続: 任意の有限 State n リストから check=true の状態だけを除く prune を定義。
任意の割当 a について、prune 後の状態に a が属する iff 元のリストの状態に a が属する。
これを実 directed self-output infer に適用し、全 Stable 表についての既存のモデル iff を保つ。
prune 後が空なら任意 Stable 表の出力モデルは存在しない。ただし言語 rejected の判定ではない。
一般 B4 の5橋は未完。source receiver/annotation生成やdriver収束を仮定で隠さない。
