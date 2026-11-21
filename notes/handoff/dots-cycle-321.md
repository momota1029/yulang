# dot cycle 321: 入力根拠・実中心・順序付き where の宣言的な健全性

2026-11-21、作業開始 12:33:42 UTC（12:30 定時枠）。開始時に
`integration/m1-final` `2cf72ce2107b1333275df6329f757b265d312fb4` の
standing orders `7ae4d68d2ac7df80d1eadbd061dadd2296faf4c4`、inbox
`f259434f2d1b233c3dde6e6e2b9d804df9349b5a` と
C320 の完了・報告 `622189d0d4bd701abe8804e27c4aff45a8addce3` を再読・照合。
後半にも integration を再読し、I-56 は同じ。設計:
[宣言的な観測・実中心と普通の新変数](../design/2026-11-21-cycle321-declarative-support.md)。
対象は普通の型・行制約、区間、通常等式。solver の帳簿・版・Step は変更しない。

## 証明したこと

1. **入力の展開根拠と、普通の意味を分離。** 任意の状態に対し、
   `Origins321.backed_iff` と `NormalSupport321.restricted_valid` は、展開用の
   等式・型行の原子・区間を、ソースまたは完了した出力から来たという証明で
   射影し、元の状態を満たす全割当てが射影も満たすことを示す。通常等式を
   元のモデルや普通の K2 グラフからは落とさない。型行原子まで追う観測は
   部品として証明し、全 source の分類への接続は残る。`LowerKnown321.Ready` は
   全ての名前なし引数の**下端**を要求し、上端・名前つき出力は代用にしない。
   `unfinished_blocks_second` / `completed_restarts` は 2 番目の実例を検証し、
   `SupportCut321.no_bare_state_readiness` は、全く同じ普通状態と需要でも、
   出力以外に独立の根拠があるかで展開可否が変わり、裸の状態だけの述語では
   区別できないことを示す。 `Settled321.no_self_grounding` は依存先を明示した
   任意の有限の完了**導出**について、外部根拠のない成分が自分から完了を
   作らないことを示す。停止性や、全 source の完了関係との一致ではない。
2. **K2 の達する位置と優先。** `GraphRows321` / `K2Alias321` の断片では、
   alias は同値な論理名を結ぶが構造辺ではない。根や実際に調べた非変数
   pattern の位置で、型引数も含む非空の戻り道を要求する。
   `Inspect321.variable_has_no_visit` と `VisibleFields321.no_hidden_payload`
   は、変数で受ける内部と、隠れた同名 field が観測対象ではないことを示す。
   `Priority321.recursive_over_viable` は、下端の展開根拠がそろっているなら K2 が
   候補選択や曖昧より先であることを示す。正規化グラフの全形・開行・展開同値
   まで含めた充足性や、一般の候補伝播との一致は未証明。普通の自己環があるが
   展開根拠がない重複を `Overlap321.overlap` で別に検証し、今回の断片では
   優先を決めず、[遅延案を先にした質問](../questions/2026-11-21-cycle321-k2-with-unsupported-lower.md)
   に例を残した。新たな拒否・保留規則は追加していない。
3. **実中心を読む規則から普通等式へ。** `Trace321.trace_model` は、任意の
   普通状態で、構成子・位置・alias を辿った出現を一つの捕捉に結べば
   各モデルで正しい読取りになることを示す。 `SourceNames321.actual_source_occurrences`
   は元の source 変数の出現を順序つきで保持し、`Representatives321.chosen_entails`
   は同じ binder・極性の出現が普通に同値なら先頭の実出現を代表に選べることを
   示す。 `NormalizedCompiler321.normalized_batch` は隠れた構造を観測せず、
   元の綴りの compiler 等式を全モデルで導く。
   - **不変 nominal**: `NominalProjection321.nominal_center_consequence`,
     `endpoint_parameters`、`NominalHead321.supported_nominal_head` は、上下端が
     nominal で普通の区間を満たせば、上下で operand の論理名が違っても実中心が
     下端の値に同値となり、展開根拠のある下端の走査だけで実捕捉を作れることを
     示す。上端に独立の展開根拠がなく、中心の直接等式もない非空モデル例で検証。
   - **共変 pair**: `PairCut321.probe_not_enough` は、ソースで同じ変数を 2 回
     使い、下端と上端ではそれぞれ同じ変数の名に読め、対角な中心が実現する
     モデルもあるのに、実中心の成分が異なる別のモデルがあることを示す。
     `PairProjection321.projection_exact` は実中心の等式を読めるなら二成分の
     同値性が繰返し捕捉に必要十分、`CovariantIntervals321.record_pair_bounds` は
     必要な実成分・両端の投影があれば成分の区間を加えてもモデルが変わらない
     ことを示す。対角の反例は「承認済み Classify がそれでも選ぶ」という主張
     ではなく、単に下端・上端だけで健全性を示せないこと。
4. **where の論理名を生成。** `ChildScope321.all_where_names` は実 source の
   チェック済み節の全ての unnamed operand が、不変 nominal 内部も含め
   可視 head 変数しか読まないと示す。 `FreshExact321.exact_forest` は実際の
   source compiler が生成した全 where の論理三端・名前つき出力の普通等式列が、
   順序・重複を含め定義列に文字どおり一致すると示す。 `Fresh321.old_model_projection`,
   `Construct321.compiled_with_fresh_children` は任意の旧モデルを、旧状態の全論理名
   と別途指定した名を保ったまま、その定義列で拡張する。solver の予約や slot では
   ない。実際の安定状態の既存名を同定したわけではなく、親の既存出力 target の
   等式や子の辞書を新しい定義で成り立たせる主張でもない。
5. **一つのモデルで順序つきの辞書を構成。** `HeadCases321.compiles` と
   `HeadCases321.sound` は任意の普通状態・任意のそのモデルについて、上の
   構文導出を供給する独立な断片の `Local` が選んだ完全な診断木から、
   実 compiler の等式列・同一モデルの Evidence を全子へ組み立てる。
   `FixtureClassify321.nonvacuous` は実際の checked `Wrap` / `Container`
   について、両需要の下端を確かめ、実際の endpoint probe・可視候補の一意性・
   非再帰の普通グラフを証明し、名前つき項目を使う 2 節点の辞書と非空モデルを
   構成する。負の選択全般や任意の source の分類との同値までは主張しない。

## 残りの橋

- **宣言的な (4): 1 本。** 承認された一般 source の独立な局所選定から、この
  構文導出を得る source exactness。普通の制約の正規化と許される出所の関係、
  K2 と全可視候補の生存／検査未了の対応、そして共変 actual を含む捕捉と
  完了した既存出力の等式がそろうこと。where の論理名は今回一般に生成できたが、
  既存の安定状態で同じ関係が存在することは残る。候補の生存を、
  「辞書の証拠をこのモデルで持つ」ことで再定義していない。
- **(2): 2 本。** 到達 solver 状態から帳簿を消した普通の状態と別の出所導出への
  射影とその不変性、停止して返した診断木の宣言分類との一致。今回未着手。
  次は一般の source 正規化の出所完全性、covariant の実位置、正則 K2 の
  適正化を優先。停止性・実行系との一致・Rust は主張しない。使用量上限は不明。

## 検証・公開

Lean 4.35.0。52 新モジュールの focused build は依存込み 1,040 jobs、exit 0。
新ソース52本は個別に trust=0、I-51 standalone audit 5本もすべて exit 0。
標準公理のみの scoped gate は 60,766 宣言で PASS。新定数958個から
5,106の型・値の依存を追い、指定された旧状態・帳簿・実行 solver・物理配置が
証明依存に入らないことを照合。I-52 diff-only は exit 0、I-53 import は52件。
具体 where の compile/readback 別検査は、旧名55保持と新しい三端56–58・
出力59の普通等式を確認し exit 0。全出力は [検証](../verification/cycle321/verification.md)。
全体ビルド、Rust、Sat は実行していない。13:19 UTC までに検証済み、50分枠で最終照合。
前周からの差分は 90 ファイルと心拍1パス。

途中の照合済み pin:
開始 `d07cb4c19fc9aab3e734729f0cc2f7fe897beaef`、
早期成果 `b9835b279a77ffaa96e0725d8f758a9ac4792397`、
10分 `dcd30ed00fdc3b0ac3edad61855dc188891f4ceb`、
20分 `7060e6293bf557a3f2e78292931f541c462d51ab`、
30分 `b588968bac302711fc4b80c6e207737133f59f4d`、
40分 `426884800781eb644f4fad95a9e7da3128f39cd6`。
公開先は `work/dots-main` のみ。独立 audit は `lean/Audit/` に配置し、
途中に同じ内容を置いた本周の暫定トップレベル3パスは除去し、404まで照合した。
