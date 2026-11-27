# C457: 同じ Ready 元宣言から混在 field K2 へ

単一の可視候補・親 point・元 where 一つ・名前付き出力指定なしを維持する。局所 Ready に含む author/role/constructor、字句範囲、正規化後の個数と実 構造減少を保存。旧宣言を受理したとはしない。旧 ConservativeSmaller が成立しない元 where だけの診断分岐であり、where を生成・実行したり impl を選択したりしない。report の元 clause ID/ordinal は認証用で、診断位置は実到達 field。表示方針は決めない。

閉じた record の経路に加え、C456 の variant/pair/実 declared unary covariant nominal self-point を使う実混在経路を同じ FullProblem 上で検証した。新しい正規入口 `RoutedReadyMixed457.check_full_ready_mixed457` は少なくとも一つの非 record hop を要求し、前の `RoutedReadyRecord457.check_full457` は旧版通りの Bool と純 field 側への完全な委譲を保持する。全 witness に対し報告された終点の raw K2 は必要。where 型、scope、route、元宣言番号・位置をすり替えない。open tail 等を含む G04 全域は未完。
