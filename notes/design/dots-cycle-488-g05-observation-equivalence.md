# C488 / I-100: 観測記録の同値と要求引数なし

- C487 の対象は全可視候補の元順・元 ordinal・分類の全一致。独立な観測記録の正確さは同じ元位置のキーの所属で定まる。新しいタグも順序と分類は完全一致で、観測列だけ両方向の有限所属検査を行う。witness の根・path は生成器の正準 tape を既存の reader で再検証する。report に自分の実訪問範囲を決めさせない。
- 正の本数では、全実候補の arity は元引数 0 の独立な始点から従う。ゼロ本のときは旧 root checker を用い、全可視 ordinal に空の訪問列を割り当てる。これだけで候補を適合・不一致としない。分類は既存の独立な局所 protocol に任せる。読み取り不能は `none`。
- 任意の同じ State・正確な prior/局所 protocol と観測 report について、上の検査成功の独立な正確さと同じ FitsFull での証拠を示す。逆方向では独立 report が正確なら、正準の元 tape にその候補の有限局所証拠を付け、観測表現の順序や重複を仮定しない。G05Goal 自体・G04・辞書選択は変更しない。

## 証明の分解

`G05Goal` の既存 report / witness の型を変えない。局所判定が single-valued なら二つの正確 report は訪問表記以外で一致する。一方、同じ判定の別の token codec に対しては、同じ wire が通るとは言わず、同じ正確 report に対する有限 witness の存在を保つと示す。

`checkFlatWithDemandScopedG05Tag488` は座標の空／非空で分岐する。空では定義上 visited K2 が無く、既存 reader で元可視候補ごとの空の path を照合する。各候補の局所判定用 token は省けない。非空では最初の実引数の独立開始位置から各候補の arity が従い、出力側は正準観測列と相互包含を満たす。報告候補の順序を入れ替えたり、canonical witness 内で path を入れ替えたりする変更は受けない。

exact scope と独立 local protocol の下で新タグの成功は独立正確報告と全 FitsFull の証拠を含む。その逆は観測リストの並びや別途の arity 仮定なしで有限 witness を与える。仮定の外側に一般的な matcher・prior の発行・辞書・最終曖昧性判定はない。定義された名前つき目標と今回の部品は区別する。

I-100 の旧入口は権威 `dc51fb0613f5df358f1ff4cc86a39dff22981a8b`、Lean tree `9731ca088dbe50869458d94cd80f135be9771c16` と C487 の逆参照明細が一致。変更前の同じ 18 件すべてに production の直接依存と個別 Audit の import があり、消せる入口なし。
