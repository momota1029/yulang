# Cycle41: structural closure and diagnostic canonicality

## 部分目標
有限の構造分解・推移閉包の所属固定点を、実 materializer と順序付き診断treeの再正規化不変性へ接続する。必要なら自己出力候補探索の実行版に接続する。

## データと独立判断
Atom (Fin n) の任意有限seed。独立判断は CommonRoleStructuralCarrierCoverage.Derives のseed・分解・推移。外部carrier仮定は置かない。実行版は既存FiniteStructuralClosure.normalize。

## 目標の型
全n、seed列、入力モデル（必要な場合）、全source/候補表について、normalize seed と normalize (normalize seed) が返す materialization・候補・順序付きtreeが等しい。自己出力探索を接続する場合は、その新しいStable述語を明示する。解の存在や旧Stableとの同値は主張しない。

意味論の変更はしない。完全性の範囲は支持規則系のみ。一般B4、source lowering、状態依存receiverとrole feedback停止は別の橋。
