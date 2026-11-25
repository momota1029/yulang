# C409: 仕様例 X12 の名前付き再帰型を開かない

[一覧 C01](dots-cycle-409-c-coverage.md)。spec/06-roles.md の K2 は名前付き型の本体ではなく、実際の要求根と本来検査する構造上の位置だけを拒否する。 X12 の `enum tree` に対する `impl Show tree` は型引数 0 の constructor 名をそのまま照合する。同じ元要求・全可視リストの singleton・実 role 行・実宣言範囲を使い、要求の端点を指す元 nominal 名前を確認する。構造の alias/Missing に名前を捏造せず、現在の普通グラフに raw K2 があれば選択しない。

型付き declaration coverage には C357 の実 mode/chkDecl と空 where の declaration readiness を用いる。C349 の ordinary coverage をそのまま要求すると、同じ実表の X12 で C357 の真正な declared constructor を弾くことを切り分けた。C349 の後続の出力無し分岐は変更しない。B6 や実構造 read の意味を再設計しない。

`namedLocal409` は独立宣言的な追加規則。 `R1` はその局所選択だけを `R0` に足す。旧 `other` と根 K2 はそのまま。実際に検査する引数のない bare name は旧 native unary site にもならず、唯一候補ゆえ既存 ambiguity と衝突しない。`dictionary_sound_R1` は任意の有限混合導出・同じ fitting model に固定 C402 `DictionaryEvidence` を返す。`liftTrace` は旧元出現・診断・実出力順を保存し、`check_sound` の全称と報告の意味は同じ。Witness は元 origin の ordinal と普通グラフの有限 rank、分類やモデル・望む Yulang 出力の証明を持たない。`previous` は Checker408 を結果も変えずそのまま実行。

統合監査だけで再帰を持つ tree body を具体化した。role 7、impl 88、元要求 27、origin の nominal 名 90、出力なし。宣言 body は同じ名に本当に再帰する。実入口で選択を受理し、一つの明示的 fitting model と辞書を証明。旧入口、誤った名前、ordinal、辞書、混入した raw 構造循環は false。これは純粋 B4 の resolved 入力で、ユーザー向け parser・Rust・B6 を実行したテストではない。直接の元 name 読みを二端点で共有できる一引数・空 where/出力の X12 が対象。すべての名前付き recursive type、非点／別 origin、複数候補、where や退避された他行の完全性を主張しない。有限グラフ rank が見つからない場合の false は言語上のエラーではない。
