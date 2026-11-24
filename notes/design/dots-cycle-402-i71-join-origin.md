# C402: 既存の宣言 join 選択から実 pre-output frame を読む

I-71 を維持する。S13bbba に不足しているのは、元の選択ルールが、本体出力の前に確定した frame を、同じ出現の子列とともに供給すること。C401 は frame を受け取る側。今回は正本に既にある C357 `JoinedLocal` / C381 `ActualWrittenJoin381` の native unary covariant join だけを使い、供給する側からつなぐ。旧 C334 / Local に翻訳しない。

- 元 `JoinedLocal.head` の二つの捕捉は独立に選ばれた同じ merged payload。可視行一個の元位置を unfilter して original registry ordinal を得る。辞書 key やモデルだけでは出現を復元しない。
- 既存の選択 event が持つ C350 `execute` から、その同じ Context の `preparation` の成功を反転する。同じ ports / capture / ordered literal where を保持し、同じ有限選択導出を新しい B6 木の pre-output frame に結ぶ。既存 C357 branch の部分結果であり、C350 の古い fixed 出力成功を、新しい `Classifies` の採否条件にはしない。
- C357 の `Receipt` は現在状態に同名で含意することだけで `Extends` の literal inclusion ではない。pre-output frame の本体はこの差を使わない。固定出力 retention（S13bbbb）を証明したことにはしない。
- その同じ元イベントに B6 の注釈が実入力としてあれば、C401 の型つき右辺と原固定先を使う。旧 C386 `.declared` ベクタを復元しない。固定文、S13 の行数、言語意味、fixture は変えない。
