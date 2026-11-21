# C308: 観測表・据え付け前の証明・再帰辞書の境界

対象は C238 の checked source（root の関連出力 (0,4)、生成される実 child は一つ）。
observer で表現するものを、現 report、公開射影、履歴を含む現在の局所証明、
子を含む再帰証明に分けておく。これらは同じ判定ではない。

## 検証済みの分離

- C308 の二つの到達点（再観測→据え付け→refresh と、従来の据え付け先行末尾）で、
  root の report の source ID、変数 capture、anchors、checked bounds の
  正規化・順序を一致させられる。表には現在の候補と同じ ordered child が載る。
  公開値と全 row へのモデル射影も全境界割り当てについて一致する。
- 一方、現在の root packet を全履歴と同時に実現できるかが異なる。
  先行再観測では点区間を最初から据え付けるため、同じ capture を持つ現在の
  frame へ移し直せる。従来の履歴 packet では optional 側の端点が既に固定され、
  現在の point capture と両立しない。局所証明を判定するコードがこの二状態を
  区別しないなら、そのコードから正しい判定を復元できない。
- 局所証明が作れる側でも、実 child は刷新前に pending、刷新後に nominal
  head の要求と structural variant の不一致で rejected。枝を消さずに再帰すると
  tree は `selected rootKey [rejected]`、最終分類は rejected。完全な Evidence はない。
- 据え付け直前の候補については exact current frame・生存の一意性・保留の解除・
  派生 class output・実据え付けの cert を分けて構成した。据え付け後の同じ候補は
  全完全モデルに対して `Committed` なので再据え付けは行えない。

## 次に試す断片

1. 先行再観測側の最後の source を、支持 ID × 已知/未知 × current/retained
   input slice で列挙する。今回の strict refresh/equate の iff を入口にし、
   残る新知識が本当に親下側 aggregate だけかを証人モデルで調べる。
   一方、任意の有効な refresh は協議された raw 証明を運ぶので、
   具体 shell の候補数をそのまま状態数には使わない。
2. 履歴互換性は export された判定から独立した証明責務にする。
   一つの frame と同じ名前を再利用しても、保持 packet の input slice、
   出力・class slice、現 packet の全 Holds に共通証人があるかを取り違えない。
   固定の source で次に検証する型は
   `∃ m, Models state m ∧ Holds currentPlan m ∧ ClassEffects state.core root currentPlan m`。
   current readback だけでこの存在を真にしてはならない。
3. 再帰 EvidenceNode の正例は child が実選択される別の checked fixture で行う。
   C238 の child を成功扱いに変更せず、選択された全 child の同じモデルでの
   順序付き証明を別に与える。空前提や failure 枝を削ることで正例としない。

このノートは意味論の決定・変更ではない。一般 compiler の完全性、
無条件の終了、Rust 実行結果は含まない。
