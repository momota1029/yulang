# C489 G05: 実訪問の K2 を局所照合に先行させる

I-100 の G05Goal の「実訪問 K2 を任意の元候補で保持し、選択より先に扱う」の検証を補う。G05Goal・G04Entry の定義と既存 checker は変えない。G05Goal 自体の証明を宣言しない。

独立側: 元可視列の各 index i に同じ元登録 ordinal と宣言があり、bit が真であることと IndependentScopedReturn487 が同値であること。全可視列と同じ長さの signed list についてこの命題を置く。元 index ごとに一致するので signed list は一意であり、その正の部分列が順番ごとに決まる。局所規則の一価性は不要。

実行側: 既存の元 root guard、computed palette と source permission、全有限の候補 tape の replay を使う。成功して本当の K2 の列があれば、局所照合を呼ばず K2 を返す補助入口を別に置く。未検証と真の all-safe を分け、後者でも辞書選択を自分では行わない。C488 の full report は今までと同じ条件で検査する。独立な入力付きで実行結果と full report の K2 リストが同順で一致することを示す。

元 prior を型付けから導かない。元の registry を越えた順位や診断位置の選択を決めず、単なる可能 site の循環は陽性にしない。データ上の拒否と witness が読めないことを区別する。

## 有限の独立照合
自動 preflight に加え、元 root と全候補の signed tape だけを別の呼び出し元から受け取る入口を分ける。局所 token、分類、電子化した報告は持たない。checker は元候補・引数・prefix の実際の必要列を自分で計算し照合する。完全な tape と合法な座標の場合だけ独立 ordered signs が得られ、任意の成功 wire について同じ結果を与える。成功する自動 preflight には同じ出力を再生できる有限 tape がある。空・欠損・候補 swap の壊れた証拠は all-safe とみなさない。
