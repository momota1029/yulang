# C400 I-70: guarded where 子の中心名は、既に発行した Port から読む

ここでは既存ソースの exact 読合せと証明経路を記す。新規 Lean はこの中間点ではまだ機械検証していない。混在 literal wire・選択条件・固定定理は変更しない。

## 実際の正の経路

1. [C350 `preparation` / `placed`](https://github.com/momota1029/yulang/blob/39eb39011dbd5032f9d5e5b8b07700a26f47bcd2/lean/Yulang/GeneralDeclarativeWitnessCompiler350.lean) は、出力本体の `fixedBatch` や子の解決より前に、元の where 節順で `Port` を作る。各 `Port.input` は [C327 `make`](https://github.com/momota1029/yulang/blob/39eb39011dbd5032f9d5e5b8b07700a26f47bcd2/lean/Yulang/GeneralDeclarativeClauseBatch327.lean) の `SparseWhere325.atPosition (seed …) (plan …)`。複合位置には保持した三つ組を使い、中心はその原本の `.center` を読む。ここでは `execute` の成功も、候補照合用にその中心行が観測できることも前提にしない。
2. [C327 `read_order` / `located`](https://github.com/momota1029/yulang/blob/39eb39011dbd5032f9d5e5b8b07700a26f47bcd2/lean/Yulang/GeneralDeclarativeClausePlacement327.lean) は、実際の preparation の節順と検査済み元 clause ID の重複なしから同じ `portAt` を得る。ここで必要なのは照合した port 本体だけで、導かれた `Input` の行の証明を選定条件に戻さない。古い `getD` の 0 に落ちない。
3. [C393 `clauses` / `whereFor`](https://github.com/momota1029/yulang/blob/39eb39011dbd5032f9d5e5b8b07700a26f47bcd2/lean/Yulang/GeneralDeclarativeI65OriginalBodyEvent393.lean) の元 clause ordinal を保存し、[C322 `exact_at`](https://github.com/momota1029/yulang/blob/39eb39011dbd5032f9d5e5b8b07700a26f47bcd2/lean/Yulang/GeneralDeclarativeSourceEmission322.lean) を元の argument ordinal へ適用する。正規化後の **bare binder** は親の実 lexical slot、複合の場合は 2 で保持した実 port。どちらも実の `Capture.center` を名前として読む。役割や出力順は変わらない。
4. [C399 `addressed_child_event_at399`](https://github.com/momota1029/yulang/blob/39eb39011dbd5032f9d5e5b8b07700a26f47bcd2/lean/Yulang/GeneralDeclarativeI65B6SelectedChild399.lean) を同じ clause ordinal に当て、その有限 where ledger から実の guarded event／辞書子を取り出す。出力のない節も位置をつめない。ここで同じ event と同じ demand が保証されるため、元位置への名前の読みを [C399 の B6 source を読む関係](https://github.com/momota1029/yulang/blob/39eb39011dbd5032f9d5e5b8b07700a26f47bcd2/lean/Yulang/GeneralDeclarativeI65B6ExactProjections399.lean) に渡せる。B6 が型・行の適合を供給することは別の義務。

## 名前と観測を混同しない

- `FreshWhere325.seed` は full state の `stateNames` を見る。そのため、選定の観測用に行を隠した状態で **再 allocation** すれば元の内部名が保たれるとは言えない。原本の port／名前を保持し、観測のための制限は行の読みだけに使う。
- [role §6.5 382–410](https://github.com/momota1029/yulang/blob/39eb39011dbd5032f9d5e5b8b07700a26f47bcd2/spec/06-roles.md#L382-L410) は、名前を保持したまま中心の構造行を要求せず端点で選べる場合を指定する。繰り返す binder の実中心同士は選定後に等式を入れる。等式から字面の名前を別の名前に置き換えない。
- 任意の入れ子の native head leaf が保持すべき中心名を `DeepRead` から作る案は採らない。C399 は lower/upper を全部保持して中心名だけを変えられることを機械検証済み。上の正の経路は、元から確定した ordinal、recorded port、同じ有限子がある場合に限る。任意の `Classifies` がこのデータを生成する主張・混在 `.declared` の対応は残る。
