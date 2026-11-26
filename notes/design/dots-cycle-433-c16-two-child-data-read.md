# C433: 二子の独立したデータ読取器（公開 R16 には未接続）

`readTwoNamedWrap433` は元の宣言・二つの異なる role・元の名付き式・元の input `a` と共有 target を同じ State で読み、本物の旧 child reader を両方の実 request で検査。選択済み trace や計算済み辞書を証人として受け取らない。試験では正しい二子を読めること、元の子証人の取り違え、二子目の別 fixed row、receipt 順の反転を退けることを確認する。

`read_pair_has_exact_source_trace_and_order433` は、成功した packet の元の二つの選択・元の clause 序数・親に続く実 receipt 列を保存。任意の同じ適合モデルに `read_pair_same_model_dictionary433` を与える。これは独立 module であり公開 R16 の分岐と計上結果は変えない。出力専用変数を匿名入力にせず、solver の順序や収束を証明するものでもない。
