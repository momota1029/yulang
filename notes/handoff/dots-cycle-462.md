この周に閉じた G の行: **なし。G04 は部分進捗、残り19行。**

# C462 引継ぎ

- 実開始 2026-11-27T09:30:08.764Z、通常終了下限 2026-11-27T10:20:08.764Z。終了と writer 解放は同 commit の heartbeat。使用量の枠は不明。
- I-87 の G04 のみ。開始時の権威 `integration/m1-final@d7cc17c307b1addb359c6ba3519169b653249df2` / Lean `bb03498abfa398bfb2152fdc636f19216a6a024d` は C461 の exact な統合。今回の [固定済み成果](https://github.com/momota1029/yulang/commit/a04cf3bf9cf12e939b2deb0faee59a070042289f) / Lean `067944a8e790e8590393e07a2ea1b8715fad22bf` は *work/dots-main* 側。設計: [既設三分岐と単一 reader](../design/dots-cycle-462-i87-one-installed-field-reader.md)、[有限の正負 capture 証人](../design/dots-cycle-462-i87-captured-normal-form.md)、[元部分木の度量](../design/dots-cycle-462-i87-retained-author-profile.md)。

## 既設の結果と同じ Bool

- `existing_canonical_bool_is_factored_on_every_original_input`: 任意の FullProblem・元 report・元 witness で、既設 C459 最上位 checker と分解版の Bool が同じ。plain C458・binary projected C459・homogeneous C459 の **実在する三 field 分岐**に対して、実 author ticket の tag/key、同じ raw wire、元 where 位置、terminal field と旧 true stamp を一つの構造 reader に渡す。さらに古い枝の Bool は既設 C458 の入口へそのまま委譲し、報告と証人の tag 不一致は false のまま。既設 checker ファイルは変更せず、比較用の分解版はインストールしない。
- `exact_installed_scope_iff_finite_witness`: 各実 author 分岐について、独立の実元適格性と同じ state の構造経路・実 terminal K2・元 report・旧 true stamp から有限データを具体化、逆方向にも反映。全 FitsFull でも同じ元位置・選択された構造経路・同じ stamp の evidence を保つ。旧成功の任意の実経路は、既存の author coverage と raw 訪問から構造範囲を導く。実 source の protocol tag は、同じ problem では key を変えても互いに交差しない。経路や report が全体で一意とは言わない。
- 実 three-provider fixture は旧最上位と比較版それぞれで三分岐の正例（同じモデルが実 Fit）、tag 取り違え、別 provider の投影、issuer・元 where ID・訪問 arm・terminal 無しを区別。既設三 author の元 address と個別の捕捉安定性を分解しても、正・負とも同じ Option と report/stamp。

## 元 source の安定性

- `actual_shell_readiness_failure_iff_finite_bad_capture`: 実有限 source shell がある場合、実元の `DeclarationReady` 不成立 iff 元 head と元 where の有限 capture table 一例が代入後の Smaller を壊す。任意の capture を元の変数 support に制限して両代入が不変。個々の代入木の一様なサイズ上限や、任意の Ready の決定手続ではない。実 late capture の `'a := int` は有限欄と静的縮小を通るが、捕捉後の縮小を壊す。
- `same_captured_normal_args` と `finite_projected_stability_check_exact`: 元 AST の各構成子で一つの構造再帰を行い、証明用投影はすべての capture で元の normalize を保つ。既存 hide で隠れる field と投影後の文字通り同一の arms だけを扱い、異なる arms の新しい意味は決めない。両側が既存の閉じた WrittenArgs へ投影し元 Smaller も成立する場合、元のすべての捕捉に対する StableSmaller がつく。実 where 内の隠れる field を追加した正例は同じ model/graph/原位置で、支持 reader は同じ (report,true) を返す。旧三 author の有限 key はすべてこの元 where を読めないことを別に証明。既設 top に新しい受理分岐を設けてはいない。
- `nonempty_actual_subtree_is_stable_under_every_capture`: 確認した元 app 引数・record payload・variant payload の非空な元 AST path の下に **同じ実 where 型**がある場合、どの capture でもすべての出現数を保ち、選んだ深さだけサイズ余裕がある。兄弟の形を仮定しない。尾・join・raw graph はこの証明で辿らない。実 Ready の対照には右の残余 join を無視し左の部分型を使う例があり、閉形式の十分条件がすべての key で偽でも元の安定性が成立。これは新しい field 診断ではない。二つの正の安定性証人を一つの元 source protocol にまとめ、同じ元に対する有限の負証人と両立しないことを示した。
- `stamped_source_iff_exact_finite_structural_read` は任意の反映済み author protocol について、同じ report と **実 used stamp** の独立構造判断 ↔ 同じ構造 reader の有限証人。実元 address・raw 位置や分散の仮定を変えず、全 FitsFull で証拠を保つ。正の author protocol があること自体から、任意の raw 訪問や診断は導かない。

## 残りと検証

- 一般の G04 には、実際に訪問する inline/bound の元と既存 raw 位置を上流で揃える証拠、全ての該当する実宣言に十分な有限の安定性証人、実 canonical 意味との合成が残る。残余 join の不支持を Yulang の拒否にしない。次の候補: 元 AST の exact opaque capture weight を用いた構造的度量、実元安定性の判定範囲、既存 canonical の同一位置受理と証明支援の境界。open tail は G06/G07、非 point・一般 mode/kind/多引数は G20/G21。G05、全体 NFR、parser、solver、raw graph 変更は未着手。I-84 の表示位置に新判断なし。質問ノートの追加なし。
- Lean 4.35.0 `--trust=0 -DwarningAsError=true` で公開 exact Git bytes に対する focused production 15、独立 Audit 19、`#print axioms` 61（標準公理のみ、またはなし）、実行 guard 7 群。**Audit の import: Yulang.* 以外 0 件**。旧 production 7832 と旧 Audit 2262 の全 blob は不変、集約は末尾 15 import 追記だけ。変更のある既存ファイルは集約と心拍のみ。公開範囲は計 40 path（この報告を含む、Lean 34追加 + 集約、設計 3、心拍、報告）。全体 Lake/Rust/`verify-lean.sh` はこの worker では未実行。
