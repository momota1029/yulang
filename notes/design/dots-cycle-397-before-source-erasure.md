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

## 消去前の where datum と I-67 の読み口

選択ノードを作るとき、独立の positive source step と同じ request/key/ordered children に local datum を置く。そこで **同じ**子 forest を再帰保存し、[C383 SelectedSourceProof](https://github.com/momota1029/yulang/blob/82ab0a52620a60875265f3ea4d1ac88e82695980/lean/Yulang/GeneralDeclarativeI65FiniteCompletion383.lean) へは datum だけを消去する。親の OutputBinder が指定する clause ordinal でこのデータ付き forest を読むと、同じ子の datum と dictionary が返る。元 child output Fin に対し、選択ノードに属する既存 C395 の準備済み入力で direct value RHS の評価を実行する。親子 q/d の一致だけで別の prepared frame を組み合わせない。既成の child receipt を入力にしない。成功した scoped value 結果は元 lexical point の source 種別を裏づけるが、raw ValueBind の四つの atom が存在するとは言わない。draft の child 実行部は既存 C395 prepared value 読み取りに限り、head の保持形から prepared scanner への全接続は未実装。

C367 ModeWindow は旧代表経路の source-side 調査に使えるが物理 origin を含む。これを I-67 の宣言側 authority として流さない。DeepRead の ordered binding 自体には mode table と logical bounds が入っており、I-67 下では元 endpoints の承認は別に実 source から得る。[C383 SourceEquationRead](https://github.com/momota1029/yulang/blob/82ab0a52620a60875265f3ea4d1ac88e82695980/lean/Yulang/GeneralDeclarativeI65CompletionRead383.lean) と [C384 ExactSupportForest](https://github.com/momota1029/yulang/blob/82ab0a52620a60875265f3ea4d1ac88e82695980/lean/Yulang/GeneralDeclarativeI65ExactDependencies384.lean) の同じ State の exact emitted source cell がその入口。後者の現 typed cell は tagged unary に限り、全ての native endpoint pair、あるいは `chosen` の実 datum まで自動化したわけではない。C383 の unfiltered K2 優先は変えない。これは C367 の旧物理表を採用するための設計ではなく、より純粋な source producer でも同じデータ消去を避ける方法。

## 実 selected cell → prepared read の draft で決めた境界

未検証 draft では、exact live data cell をただ一度選び、その宣言を C350 context の宣言欄に **構成時に** 入れる。元 ordinal は unfilter 検証で得る。別々に作った AuthoredCandidate と frame が同じだという仮定は置かない。prepared frame はその context の actual preparation/placed/initial を使う。旧 head の trace data で元 i/j の value kind を読み、元 seed と actual spans の先頭が一致することを照合した場合だけ、実 prepared port の新しい二端点を使う。C395 の生成原子から必要な結論を得るために、同じ current State への normal atom 包含のみを使い、全 State Extends は要求しない。

この draft の child 実行関数は、データつき finite forest から元 child を取り、その child の exact-cell prepared frame を使う C394 evaluator を呼ぶ。子の actual output を先に受け取って照合するのではない。現時点の binder 読みはその child の explicit body に出る head 由来の value のみで、where/default/row の入力を捏造しない。成功結果の元 target を親 lexical point とつなぐ。実 source のすべてに対する準備入力（特に全 spans と K2/保留を含む正しさ）や、さらに親の where 型付き環境にその出力を使う版は未実装。上の前節の「head 保持形→prepared scanner」はこの scope で draft したが、Lean の検証はまだ行えていない。

再現時は C395 の exact PreparedSourceBindings395、SelectedHeadBindings395、SelectedWhereBindings395 と I-67 C383/C384 の元 import に対して、公式 Lean 4.35.0 で (1) tape の projection と位置、(2) actual prepared value ticket、(3) actual where child evaluator と same target を別々に厳格チェックする。新しい Lean は未検証なので branch には置かない。
