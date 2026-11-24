# Cycle 397: 型付き source 経路を消す前に、同じ選択のデータを保持する

正本 2259f3681e811f9362032150368090328f566371、I-69 inbox 5e202637769e290325b60e4425812e784428f3d7。対象は固定 [S13bbba](https://github.com/momota1029/yulang/blob/82ab0a52620a60875265f3ea4d1ac88e82695980/notes/design/dots-cycle-380-i65-step1-skeleton.md#L325) のみ。分割・固定文・受理規則の変更なし。以下は検証済み既存ソースに基づく設計。クラウドが取得できず、新規 Lean は未検証・未公開。

## 足りない事実 (a) と保持する場所

**実選択が持つ同じ型付き head 経路と、同じ finite where 子の元 Body から、元 output の literal RHS を出すこと。** 生の宣言 ordinal だけではこの対応を戻せない。現在の [C367 DeepHead](https://github.com/momota1029/yulang/blob/82ab0a52620a60875265f3ea4d1ac88e82695980/lean/Yulang/GeneralDeclarativeI65Heads367.lean#L15) は Prop で、[authored_node](https://github.com/momota1029/yulang/blob/82ab0a52620a60875265f3ea4d1ac88e82695980/lean/Yulang/GeneralDeclarativeI65Body367.lean#L67) は shallow projection で DeepRead を落とす。選択を消去した後で同じ型付き経路の存在だけを取り直すのではなく、元 source 候補を得たときにその経路をデータで固定する。

1. actual native window/read が既存 source rule から作られたとき、元 head の引数順に、ModeWindow と DeepRead の選ばれた葉列を Type のデータで保持。ordinary の head fact を native に変えず、unused slot から capture を発生させない。old C367 DeepHead/All₂ はこの**同じ値から**射影するだけ。独立の head 読み取りを二回行って「同じ」と仮定しない。
2. 各候補 tape cell は、この構造を保持してから旧 Assessment/CandidateTape に射影する。live list と順序は射影で不変。旧 TapedMatch の clearRoot・waits・singleton live は変えない。同じ tape の元位置から unique live *data cell* を取る。decl.id で候補を探し直さない。joined 等の未移植 cell を取り替えたり .none を拒否にしない。次に [C395 の unfilterOrdinal395](https://github.com/momota1029/yulang/blob/82ab0a52620a60875265f3ea4d1ac88e82695980/lean/Yulang/GeneralDeclarativeI65SelectedHeadBindings395.lean) で同じセルの元 registry ordinal へ戻る。
3. その cell の元引数 i・葉 j をデータから読む。C366 deep_reads_retain_all_sources が同じ捕捉の真の ValueBind/RowBind を与える。C395 の prepared value に渡すのは、この葉の kind と original seed の同一性。invariant で使う型付き上下端は元 head の番号をそのまま流さず、独立準備が実名に書いた端点を読む。value 原子を row 証拠にしない。既存 C367 を全 Classifies に採用したり、新しい物理 origin/release を宣言側の状態に入れない。

## 実子への接続

親の where 原位置から子の元 selected subtree を index で読む。子の元出力 Body は [C396 の source lookup](https://github.com/momota1029/yulang/blob/82ab0a52620a60875265f3ea4d1ac88e82695980/notes/design/dots-cycle-396-selected-child-body-origin.md) の actual declaration/declared role から得る。次はその**同じ子ノードが生成した** head 経路・prepared frame に対し、元 output Fin 位置の source RHS を計算する。別の prepared frame や完了済み receipt を受け取って一致を仮定しない。既存 C394 の value evaluator は実入力で計算するが、child 由来の where point に対して旧 C366 の raw atom を書き足したことにはならない。where point の型種は actual child typed output の出所と元 target を一緒に持たせる。元 proof の別の子に渡らないよう有限 selected tree の厳密な下位ノードでのみ読む（solver の停止性とは別）。

任意 mixed compound を既存 .declared の ordered vector にする実 source writer、全 Classifies からの同じ exact 証拠、where/default/row の型種生成は残る。別の wire/flatten、旧 Local/C334、fixture、S13bbbb、停止性は扱わない。意味仕様に新しい決定は見つかっていない。
