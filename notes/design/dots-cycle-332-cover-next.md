# C332 残った宣言的な source→ReadBack の切り分け

対象は I-56 (4) の一群。既に独立な候補選定が成功した場合を含め、任意の安定した source judgement が具体的な読み取りと同じ固定出力を持つ、と言いたい。有限 read の成功を新しい受理条件にするわけではない。

## 得られた側

- `GeneralDeclarativeNestedHeadList332.capture_sound` は、一定の支持 snapshot と実 `translate (normalize pat)` の読み取りで、古い割当を保つ head の有限列を返す。後の ordinary row は元の支持に加えない。
- `GeneralDeclarativeNestedReplay332.replay_frame` は、そこから同じ固定 target の `Frame` を再構成する。`current_after_replay` は現在の候補ガード、同名 receipt、計算した順序付き実子と提案の一致を別々に使う。すべての現在モデルに意味を運ぶ。
- `GeneralDeclarativeNFComplete324.ReadBack` は head、capture 区間、名前の整合、各 where 読取りを要求する。その出力安定性は `produces` で別に用いる。`Frame` の存在や `Receipt` を stable judgement の定義に足せば循環する。現行の source/通常伝播を入力にする形を保つ。

## 詰めたい側

1. **候補に使ってよい spelling の存在。** 今の `ofRows` は supplied rows の最初の一致を読む。先頭の RHS が alias や不透明表現で、後続の supported RHS からは必要 field が現れる場合を作り、first hit の失敗を候補否定としない。候補選定を参照して行を選んでよいのでなく、元の実 source rule が使った行／alias と出力完了の由来を確認する。証拠列挙が必要ならその用途だけにする。
2. **必要な通常式の存在。** 選ばれた中心、where の compound、associated output の固定 target のうち、どの通常式が実伝播から得られるかを分ける。モデル同値だけから支持を移さない。実 tuple の順序をリストとして照合し、名前の一意性は要求しない。
3. **未知は未知のまま。** 有限 index の不足は、未完了出力の保留、広い端点、真の下端の欠落を区別する。I-59 の根 K2 検査は別の通常グラフから来る。このノートは新しい優先順位の問いではない。
