# Cycle 272: 有限分岐 readback、保持済み出力式の閉包、実218・252の検証

- 指示: I-52（後継 rebase と元の意味の対応）・I-51 / I-53。書き込みは work/dots-main のみ、expected-head 付き non-force。既存 Lean・spec・計画・凍結ファイルは未変更、barrel は末尾追記のみ。
- 開始: 2026-11-19 11:30:00 UTC。報告作成: 2026-11-19T12:20:05Z（50.08 分）。使用量の枠: 不明。
- cycle271 は正常完了。公開 3382f7eaab33017d4697fcbe082acc070bd1ae1b と完了心拍を照合、ローカル開始 tree は公開 ed47f02db1847fe2c221b7a9788ec6c3fc163853 と一致。同じ repo の別 writer は確認なし。
- integration/m1-final 157c21459328db42119c52326288d8e672036535 の指示・inbox を開始時と最終公開前に再取得。blob 7ae4d68d2ac7df80d1eadbd061dadd2296faf4c4 / 2f6b72446884d0e340537ac4b9aea1bb6c0e047d は同じ、STOP なし。同 tree 70cfa0e4b4a9d9c12e5c9c00f292546d72a83302 のローカル祖先 9c415785a を静的検査基準に使用。
- 途中公開: 5da8cc2b、943e685b、85aa6c61、eb63f150、bb511886、acec4517、60ebb10e、00e7587b、59e961c1。成果物、証跡・報告・心拍を含め前周から 86 ファイル。古い依存キャッシュに未出力の実218関連4モジュールは、内容を変更せず個別に再コンパイル。作業中断なし。

## 成果と境界

1. **元の semantic Edge で有限分岐 tree の高さが真に減る。**
   GeneralRebaseFiniteTree272.height_invariant / GeneralRebaseCanonicalUniqueness272.exact は、full carrier で等価な任意の canonical な有限 tree は高さだけでなく全 tree が同じと証明。対応は scalar、pair、variant、exact-empty、有限の record、任意の有限個の型引数を持つ nominal。GeneralRebaseTreeProjection272.child_of_live は、非正規順序・重複付きの literal record query でも、元の live semantic projection が canonical な実 child に入ることを示す。GeneralRebaseTreeAcyclic272.acyclic は任意の一つの実 full model で有限 tree として読める Origin について、semantic Edge ごとに高さが真に減るため、元の Cyclic を否定する。元の kernel の停止性ではない。
2. **入れ子の実行器と、実218の分岐読み出し。**
   GeneralRebaseTreeInterpreter272.run_sound は、モデルに対する認証済み source table のもと、任意の入れ子 query を「不明」「観測なし」「任意の型を観測できる」「既知の canonical subtree」に分類する。影になった record 位置は単なる観測なしではなく任意の型が観測可能。さらにそこから有効な nominal または structural projection を選ぶ場合も任意、範囲外なら観測なし。GeneralRebaseTreeCoverage272.unknown_exact は不明になるのは起点の証人がない場合に限ると示す。
   GeneralRebaseTreeActual218272 は実 installed journal と既存の実 full model を使い、2引数 nominal root の左右の variant 下から Int と Bool を読み出し、元の V8 RootK2 は負と計算して証明。別の未支持の区間端点は unknown。GeneralRebaseFiniteTreeCompare272.Actual218.current_not_equal は同じ coarse variant tag を持つ実プロジェクション同士も、単一モデルで異なるため元の all-model Equal が不成立と示す。この否定を、別の子の共有入力 guard と同一視しない。
3. **保持済み emitted equations から支持済みの有限形状を導く。**
   GeneralRebaseTreeExprCompile272.compile_sound は、mode ごとの変数型 witness が正しければ、元の式から計算した finite tree が元の意味と等価と示す。scalar、pair、variant、型引数のみの nominal、exact/width-empty、昇順かつ閉じた width tail の record に対応。join、その他形状や不足した変数は棄却する。分岐の synthetic schema から pair/record/variant を含む出力を再現。元の238の optional top-level join も未支持のままであり片側へすり替えない。
   GeneralRebaseTreeSchema272.rounds_sound は、任意の保持済み plan と実 full model で、既存 schema の成立の証拠からだけ source target を増やし、既存 witness は変えない。実 installed 252 では入力2の既知形状だけから実 emitted equation で出力3を復元、そこから三つの nominal 選択で Int に至る。既存 evidence による検査であり、任意のモデルや source semantics は生成しない。
4. **同じ保持済み plan 集合の有限な最小閉包。**
   GeneralRebaseTreeSchemaProgress272.strict は、任意の source table に対し、保持済み plan の1パスで表が変われば「まだ未知の emitted target の出現数」が真に減ることを示す。GeneralRebaseTreeSchemaClosure272.close はその初期数で実行し固定点に達する。GeneralRebaseTreeLeastClosure272.least は、同じ実 full model について同じ種を拡張する認証済み固定点の中で最小と示す。order_independent は任意の二つの journal の plan リストが並べ替えの関係にあり、両者の同じ full model と seed が認証されている場合、閉包値が同じと示す。固定 plan リストの計算であり、一般の Step や閉包の対象外の型式については停止・完全性を主張しない。
5. **全モデル等値の正・負の境界と、実252の自動 seed。**
   GeneralRebaseUniformTree272.equal_sound は、一つの実モデルによる shape 比較が all-model Equal の否定に使えても、正に使うには同じ witness table が全 full models で認証される必要があると区別する。GeneralRebaseOneModelBoundary272.actual_boundary は実初期252の二つの full model で反例を示す。small model では未据え付け出力3と scalar source0 が等しいが、別の full model では出力3が深い nominal で等しくない。
   GeneralRebaseTreeSeedExtract272.seed_uniform は元の checked structural heads、tight な nominal 型位置、双方向の literal scalar 原子を使い、全モデルに対して sound な有限 seed を raw journal から計算。GeneralRebaseTreeSeedExact272.exact_support は、任意の fuel・slot について計算が成功することは、選ばれた checked frame 規則で有限導出があり、その tree 高さが fuel 以下であることと同値と示す。任意の型の denotation の発見とは別。
   GeneralRebaseTreeAuto272.Actual252.automated_equal は、実 installed 252 の seed 自体も自動抽出し、保持済み式から出力3を導き、その二重 projection と元の入力2がすべての full models で同じと計算して証明。GeneralRebaseTreeHybrid272.retains_positive は真に循環する Origin では有限 witness 側はどの fuel でも abstain するため、既存の局所窓が得た正を落とさない。guarded record の正と、局所窓だけでは不明な実252出力の負を確認。

[設計ノート](../design/2026-11-19-cycle272-finite-tree-readback.md)。言語の追加判断を要しなかったため質問ノートなし。各モジュール/宣言と公理出力は [検証一覧](../verification/cycle272/) の各 *-modules.txt・*-declarations.txt・*-audit.txt。

## 検証

- Lean 4.35.0、--trust=0 -DwarningAsError=true -R .。新規 31 モジュールを旧依存キャッシュと区別した新しい隔離出力へ再コンパイル、終了0。[全文](../verification/cycle272/final-fresh-recompile.txt)。
- 9 Audit を独立に実行、291 宣言、標準公理のみ。隔離再コンパイル後の出力もバイト一致。[監査集計](../verification/cycle272/final-audit-recheck.txt)・[14対象の再検証](../verification/cycle272/final-fixture-recheck.txt) は終了0。
- bash tools/verify-lean.sh . 9c415785a --no-build と前周基準 ... a1cc0b224 --no-build は両方終了0。[integration 同一 tree 基準の全文](../verification/cycle272/diff-gate.txt)・[前周基準の全文](../verification/cycle272/prior-cycle-diff-gate.txt)。[凍結とbarrel 一覧](../verification/cycle272/freeze-and-barrel.txt) も照合。全体 lake build、CI、Yulang 実機は実行していない。

## 未完

- 任意の模型を構成する手順、join や行引数・一般の影つき/未正規の emitted record 式に対する witness 生成、raw の有限導出をすべて拾う無燃料の抽出は未証明。
- 新規 install 含む任意の old journal の公開モデル保存・反映と後継 rebase Step の一般の soundness/completeness。
- V8 EvidenceNode と12性質の全面移植、元の kernel の停止性。239/240 の元の kernel の非停止は変わらない。
