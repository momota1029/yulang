# Cycle192 主張と残る境界

すべて actual WF / V6 の境界。旧ソースと意味論は変更しない。
厳密な量化子・前提・公理出力は Audit/Cycle192PublicTypes.lean と検証ログに保存。

- CommittedEvidence192.trace_evidence（健全性補助）: 任意の registry/state/plan/support、実 Installable と Committed、および ordinary な実 Step 列を仮定する。任意の終状態の model が全子の Evidence を持つなら、同じ model で親の Evidence が成り立つ。committed_instance190を再利用し、新原理とは数えない。
- generated_child（補助）: 任意の Committed packet、生成済み親と packet の子の membership から、同じ状態で子 Generated。余分な Step を作らない。
- ReusableForest192.Build（定義）: 有限の任意深さ・幅の木。新規 install は Installable/Generated/novel を持つ。reuse は Installable/Generated/Committed を持つ。どちらも正確な順序の子・兄弟 certificate を持つ。Evidence はフィールドに入れない。
- ordinary_trace/execution（補助）: 任意の Build から実 WF Step 列。reuse の局所動作は恒等、子と兄弟の実動作だけを合成する。
- evidence（健全性）: 任意の Build と任意の終状態 model に対し、全需要と payload の順序付き Evidence。全節点を同一の最終 model で評価する。
- inhabited/nonempty_inhabited（健全性の非空性）: 任意の Build は初期 model 存在を終状態に保存する。非空 Build は最初の実 enablement が common model を持つので、初期存在を別仮定せず終状態存在を導く。
- tree_sound/source_tree_sound（健全性）: singleton Build は実実行・非空終モデル・全終モデルの Evidence。さらに実 WF Initial なら終状態 Reachable と同じ model の初期への逆保存。Build の存在そのものは仮定。
- ForestProducer192.of_installed（補助）: 任意の cycle191 Build を同じ初期/終状態・需要・payload の新 Build に埋め込む。
- first_enabled（補助）: 任意の非空新 Build は先頭需要に対応する実 Installable packet を持つ。
- leaf（部分的構成）: 任意の Installable/generated/子空 packet に対し、新 Build と、恒等または1実Stepの終状態が存在する。novelty/Stable は仮定しない。Committedかどうかの古典的場合分けで証明。
- stable_no_installed（制限）: 任意の実 Stable 状態から非空の旧 all-novel Build は存在しない。
- selected_initial_leaf（部分的構成・健全性）: 任意の Checked registry、実 WF Initial、V6 selected、当該keyの可視宣言すべてがwhere無し、root出力無しという前提から、子空と、0または1Stepで到達する新Build・Reachable・非空モデル・全終モデルのEvidence。189のenablementを接続する統合結果。
- selected_variable_leaf（部分的構成・健全性）: 任意のChecked/Initial/selectedに加え、当該keyの可視宣言が有限変数head（繰返し可）、where無し、全root出力を宣言が覆い、各RHS翻訳がCompleteなら同じ結論。190のproducerを接続。名前付き出力を許すが任意構文の完全性ではない。
- ReusableRegression192: 既存のinhabited stable scalar sourceに新Buildがあり、どの終状態にも旧Buildがない。実 novel repeated-variable sourceの旧certificateも埋め込める。両方とも葉のfixtureで、非空where例ではない。
- ForestBoundary192.no_build/not_universal_selected_build（制限）: 既存のWF多tag-materialization反例では任意payload/終状態に新Buildがない。したがって一般のChecked/reachable/stable/selectedから新Buildを得る主張は偽。この部分は既知no_installの帰結であり、新しい言語反例でもEvidenceNode自体の否定でもない。

一般 EvidenceNode の新規解決フィールドは0。終状態Stableは葉producerの結論ではない。
次は Display(List Int) → Display(Int) の親を実WF Installableへ移す具体的橋。
一般化を狙う前に、既存のmulti-tag materialization不一致の修正が必要。
