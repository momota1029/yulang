# C401: S13bbba に残る独立な source 入力

I-71 の [指示](https://github.com/momota1029/yulang/blob/793febb8a7f2069c7315a1a37954209395461c03/notes/plan/dots-inbox.md) に沿い、B6 が渡した型つき RHS を直接持つ。S13bbba を分割せず、[固定した最上段](https://github.com/momota1029/yulang/blob/6601c59528413726906e88eb509f004a396b6db0/notes/design/dots-cycle-365-i65-fixed-statements.md) と C380 の文を変えない。

## 今回、前提から出せるようになったこと

[厳密検証済み source](https://github.com/momota1029/yulang/blob/4a1eff9dab3e95012e3731f74f38ce60e5d4f204/lean/Yulang/GeneralDeclarativeI65CertifiedWhereInputs401.lean) の `original_guarded_tree_produces_mixed_source_values401` は、同一の有限 `GuardedFrameTree400`、検査済み原宣言、根の role signature、元の出現・宣言番号・出力番号・本体に対する B6 注釈から、全節点の原本・実名・同じモデルの値を構成する。子の arity と関連出力の宣言は、元 where 節の `Clause.Signature` から導く。入力枠の explicit は `Declaration.Scoped` と実 lexical scope、既定値は元 role の位置つき signature を使う。単に名前を代入するために、中心行の観測や同じ種類の二度目の推論は要らない。native 端点の構造の正しさと、固定先が State に保持されていることは、別の事実であり、ここからは導かない。

全 primitive を ordinary 扱いに戻したのではない。実 `Use.mode` が .primitive のときだけ scalar、pair、emptyRecord、exactEmpty を結び、既存の `primitiveValue` を使う。pair の両子、record/variant/join の中、nominal の値側の子で有限の混在を表せる。点／不変区間と value/row で型の index を分ける（複合 row 式や全 B6 source syntax が入った主張ではない）。旧型付き C398 plan の読み位置・実値は保つ。旧 C386 平坦ベクタの互換は要件ではない。

## 足りない事実と出どころ

**一文:** 任意の `Classifies s q (.selected d)` に結びついた同じ `GeneralLocalMeaning` の元イベントが、実際の独立な候補判定を保った pre-output frame と、その元本体を指す B6 注釈を与えることが、まだ証明されていない。

- **B4 の原規則から:** C386 の [`ReplayJudgment`](https://github.com/momota1029/yulang/blob/6601c59528413726906e88eb509f004a396b6db0/lean/Yulang/GeneralDeclarativeI65LiteralReplay386.lean) は `localRule` と旧 `eventAt` の抽象インターフェースで、`AddressedDictionaryEvents` の住所自体は実 head の選択証明を補わない。`TapedMatch` は実の可視行、唯一の positive、pending なしと raw root K2 なしを読むが、deep candidate-local K2 や全 native の early visit の独立な判定を与えない。C384 の same-state finite completion は補助 producer を木として持つ。そこへ original frame を同じ選択節点の時点で保持して、where の順と別の入力 support を区別する必要がある。仮の selected キー、後の `Fits`、反復選択、同じ数値の target では差し替えない。
- **B6 の入力として:** 現 `State365` は `current`・`modes`・`origins`・`routes` のみで、B6 の種類つき RHS はまだ保持しない。`B6OccurrenceAtlas401` は I-70/71 の引渡し口。元の正規化済み role Pattern を索引にし、元 body は残す。正本 [Main.current_core_principal](https://github.com/momota1029/yulang/blob/793febb8a7f2069c7315a1a37954209395461c03/lean/Main.lean#L116) も統合 B6 の定理ではないと明記する。正しい B6 の注釈生成の証明は B6 側の別責務。B4 側はその注釈を State または Request の実入力に置いて読む。全モデル同一の元注釈を `Fits` や solver の release から作らない。
- **I-71 の内部変更:** 新しい受取りの同じ元イベントを `GeneralLocalMeaning` と `ExactSourceRhs` が共有するよう、具体的な ledger の payload を typed tree にする。住所・ordinal・同じ actual guard の構造は保ち、既存の C386 event の `.declared` 値から混在木を復元する橋を要求しない。固定した主定理に追加の soundness 仮定を足さない。新しい採否・優先順位・fixture・物理規則を導入しない。

この周で S13bbba・S13bbbb の状態は変えない。上は次に接続すべき実入力を明記したもので、新しい S 行ではない。仕様上の未決事項への新しい質問はない。
