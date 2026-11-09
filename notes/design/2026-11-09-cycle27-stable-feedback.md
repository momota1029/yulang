# Cycle27: 自分の出力で再検証する有限共有証拠

データは Paterson 検査済 registry、有限 source root、route ごとの関連型 request annotation、ordinary seed。
表の全項を静的 choiceSpace で正準化し、その項の全 annotation を実 associated batch で seed に加える。
旧観測状態を入力にせず、その結果状態で独立 Valid を検査する。さらに各 annotation に実関連型出力が存在することを検査し、未解決を黙って無視した完全証拠を除外する。

独立 Stable(table) は、正準出力で Valid(table) かつ全関連型 request の Computed 出力が存在。
実行版は choiceSpace の有限部分列を全列挙して Stable の Boolean 検査で絞る。
任意 table の membership 正準化は出力を厳密に保つ。これにより任意 Stable table は探索に正準代表を持つ。
任意 assignment の出力モデル族 iff seed のモデルかつ Stable table が存在して全選択関連型等式を満たす。
AssocWellFormed を明示して独立宣言導出にも接続する。

これは reference 診断の self-consistent な完全証拠。探索結果の存在、一意性、言語の候補選択、source lowering、状態依存 receiver の生成、反復 driver の停止は主張しない。
未解決 request がある場合の除外は言語拒否ではなく、この強い証拠形式の不成立。
