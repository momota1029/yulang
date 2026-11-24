# Yulang dots cycle 383 — I-67: 同じ状態での有限の宣言的完了

周の途中で [I-67](https://github.com/momota1029/yulang/blob/d24d654817367e7a565b1ee97c1306931332d19d/notes/plan/dots-inbox.md) を確認し、物理的な作者・版・release の再構成から、**同じ宣言状態での有限 `.selected` による完了**へ変更した。切替前にローカルで調べた索引付き where compiler は公開していない。C381/C382 の物理的権限・記録は検査器（2/3）に留保する。固定の `dictionary_sound` と `check_sound` は不変。

## 今回の検証済みの部品

1. `FiniteCompletion383`: `SelectedSourceProof383` は同じ `s` を保つ相互帰納型。読む出力の producer に対する有限選択証拠と、辞書を構成する literal where 子の証拠を別々に保持する。producer 証拠は辞書の子にはならない。`no_finite_circular_completion383` は、任意の選択規則で同じ閉じた族の producer 又は where 子が不可欠なら、その族には有限完了がないことを示す。別の根拠がある循環、実行順、全体停止性、一様深さ上限は結論しない。
2. `CompletionExact383`: `finite_selected_iff_projected_classifies383` と `finite_completion_iff_projected_selected_exists383`。**独立な正の局所規則が供給されたインターフェース上でのみ**、同じ辞書を返す有限証拠と既存の `Resolves/Summarizes` の `.selected` 投影が同値。逆向きは既にある producer の有限証拠を使い、where の元順序を保持する。結果の辞書から消した producer を捏造しない。一般の `Classifies` でも四種すべての診断でもない。
3. `CompletionRead383`: 直接の source 制約でない読みには、同じ (s) で選択された producer、元要求の出力位置・固定 target、独立な論理的等式生成を全て求める。等式が現グラフにあることだけでは足りない。閉じた循環族だけが候補なら読めない。root K2 は元の普通グラフを読むため、未完了で読めなくても先に拒否する入口となる。
4. `LogicalOrdinaryOutput383`: 既存の独立な ordinary `SourceEquation323` を、実要求の literal output ordinal で言い直して同値を証明。`completed_ordinary_source_reaches_literal_read383` は、実選択と捕捉が**別の宣言的判断ですでに保持**され、実等式と有限 producer 証拠が揃うと読みが成立することを示す。output 名・target の類似から別の宣言を選ばない。typed 全般や選択判断そのものを生成しない。
5. `LogicalNominalOutput383`: 明示された tagged unary covariant 関連型の既存構文に限り、宣言から独立な `Supplies`、要求の元 ordinal、宣言された共変 mode、実 binder の中心を typed 出力の根拠にする。実選択・捕捉と同じ状態での finite producer、現 typed row の保持が揃えば、同じ全適合モデルで固定 target と中心の値を得る。`authoredValues` の観測であって、native endpoint や任意の typed 出力の証明ではない。release・writer version は使わない。
6. `OrdinarySupportGraph383`: 同じ状態で支持された ordinary 行に閉じた観測ビューを作り、既存の下界の `Knows` と、最後の constructor 行だけでなく **各明示的 alias 辺**も有限支持を持つ論理的な経路とが同値だと示した。元の bounds はそのまま、同じモデルを制限して使える。`Bound319` に現れる interval/`tyLe` に未完了出力の alias を上流で移さないか、その由来を検査する実ソース側の橋は未証明。ordinary のこの断片では全引数の ready とこの読みの対応がつき、元のグラフの根 K2 は ready でも優先する。混合・native の ready、候補内 K2、すべての候補の実選択は別。
7. `CompletionRootCycle383`: 実引数の lower に現 ordinary の名付き自己参照行があれば、支持で絞る前のグラフで root K2 が成立。循環族のみの出力で同じ行の支持付き読みが成立しなくても、root K2 が優先することを示した。候補内 K2 や任意のグラフの完全判定は別。

## 実規則に残るところ

`FiniteCompleted383` は実規則をパラメータとする部品で、全可視候補を同じ最終 snapshot で判定する実規則・正確な保留と不一致・必要な訪問の取り落とし防止・一般の実 typed 出力生成は未実装。`Tape367.PendingCandidate` の旧 `complete : Nat → Prop` と `derivesFrom original (.output owner)` を今回の完了へ読み替えるだけでは、具体的な論理 `Request` と ordinal を特定できない。これらは逆輸入せず、実の同一状態の論理出力関係と正の mismatch / 本当の pending を使って、`CandidateTape` の可視リスト全体に相当する判断を作る必要がある。 次の最小の実作業は、普通の支持付き path を **可視候補の実訪問位置**までつなぎ、`Rivals367.RigidCandidateMiss` の実 head/引数 index に、確定した構文上の不一致の証拠を返すこと。既存の `rigid_candidate_excludes_a_source_head` が `Fits` を用いるのは同一モデルでの健全性であり、モデルの存在によって選ぶ規則にはしない。宣言選択の入口と、あとで任意モデルに意味を与える証明を分ける。 可視集合側では `Bundle291.SourceBundle.declarations` は論理宣言のリストであり、呼出し元ファイルや import 順を含まない。`State365.visible_exact` と `Bundle291.actual_registry` は role filter と既に添えた registry の同一性まで。既存 `ModuleVisibility.FileScope.mem_select` / `selected_origin` は読み込んだファイルとアクセスの論理を表すが、旧 `Roles.Impl` 上であり、この `Declaration` の同一出現や新版 registry の供給証明として使わない。実 compiler の成功を必要条件にせず、呼出し側の同じ範囲が各 where 子へ渡ることを別に示す。 native の最初の層では `ActualUnaryDispatch379.unary_dispatch_exact` が既存の unary machine の構文・子の境界を示すが、`released_unary_dispatch_has_literal_child` の release 結合は 2/3 のまま。1 では論理 source の端点と宣言 mode だけで同じ位置を選び、`authoredValues` の tagged view から `NativeSyntax` を自動で復元しない。有限証人の都合で完了集合の一部だけを採用し、その下で一意なら selected とすることはしない。正の読み根拠が増えることと一意選択の保存は別。実規則では `LogicalOutputLink383` が記録する producer の `d` と、同じ要求の有限 subproof の `d` を一致させる。`List Request` だけの generic 骨組みから一致を推論しない。次は、head 読み・実不一致・保留の独立な判断を同じ state の全可視候補に接続し、その実選択だけを有限完了の局所規則へ渡す。一度の読取りの失敗を言語の不一致にしない。

次に必要な判断の分離（spec 6.3 の 2026-11-15「型の頭として覚えてよいのは、根拠のあるものだけ」、2026-11-22 の根 K2、6.5 の同日端点規則）: (i) 元の ordinary グラフで根 K2 を確認し、成立なら候補を訪問しない。 普通下界は `OrdinarySupportGraph383` で祖先の名寄せ経路まで読む形を得た。(ii) 根 K2 がない場合、候補が本当に訪問する非変数位置についてのみ、その経路に必要な支持付きの端点を読む。中心の行に支持がないことは、両端が読める場合の不一致・未解決にはしない。(iii) 同じ最終状態の全可視候補について、読めたために確定した不一致、未解決、実訪問に基づく K2 を区別してから選ぶ。有限の `.selected` 証拠にはこの分類を外から渡すのではなく、この実規則の由来を保持する必要がある。先に complete フラグを付ける実行順・外部表は要求しない。`State365` の既存 `Origin.slot` / `Origin.issuer` / `OriginRoute` は既存の構文観測表現で、今回これらから solver の作者・版や release を復元する解釈は採らない。型付き側で直接の source と論理出力をつなぐには、当該フィールドを物理的な完了の証明にせず、型宣言・出力位置の証拠を別に示す必要がある。このうち明示的な unary covariant tagged 出力は `LogicalNominalOutput383` で切り出した。具体的に `State365.BodyFacts` / `body_facts_sound` は同じ ordinary モデルで固定 target と保持等式を返し、`ModeWindow` / `mode_window_sound` は両端の構文と型付き比較を返すが、後者は前者の特定出力 ordinal を生成したとは述べない。次の typed 接続ではこの二つを、候補の実選択と独立な出力生成を経由せずに同一視しない。

spec 6.3 は安定まで判定を遅らせ、兄弟の更新順によらないと明示する。今回、承認済み source で受理が実行順に依存する箇所は確認しておらず、意味の選び直しや質問ノートはしない。

[C380 一覧](../design/dots-cycle-380-i65-step1-skeleton.md) の S01–S03 と層の注記を I-67 に合わせた（変更理由を一覧記載）。S04 以降の物理的条件の旧 draft は検査器側に留保し、宣言側の新規前提とはしない。一覧の blob は `60c27922594aa2223ced47ec78bd72cfb857f6d3`。

## 残り（I-66、全ラベル据え置き）

- S01 未証明 — `classifies_unpacks_actual_source`
- S02 一部 — `selected_source_inversion`
- S03 一部 — `selected_mixed_k2_priority`
- S04 一部 — `elected_occurrence_has_general_head`
- S05 一部 — `selected_actual_ordered_capture`
- S06 一部 — `selected_ordinary_literal_receipt`
- S07 一部 — `selected_typed_actual_owner_and_retention`
- S08 一部 — `ordinary_or_typed_node_assembly`
- S09 一部 — `general_local_meaning`
- S10 未証明 — `selected_frontier_to_general_node`
- S11 一部 — `lower_selected_general`（tree/forest を返す一補題）
- S12 一部 — `general_tree_sound`
- S13 未証明 — `general_meaning_to_dictionary`

**未解決 13 件 = 未証明 3 + 一部 10。** I-65 Step 1 未完、2/3 未着手、S1/S2 未完、C 後回し。停止性・旧 `Local`・旧 C334 接続・fixture 追加なし。

## 検証と公開

- 開始 `2026-11-24T02:30:58.007Z`、前周 `c263f57150f5509dbc3824c345a23887cfa44fcf`。I-67 正本 `integration/m1-final` `d24d654817367e7a565b1ee97c1306931332d19d`、inbox `a87744968aacd0c51cf7f82e263009a914ed48c6`。常設指示・roles/inference・前周完了心拍を確認。技術 pin `bc4e51de28548ba3dc01d2766bea0e6e4d4fd45f`、同 Lean tree `4b0f7cf8bd7c1cb51a327bd0e2a4cea4d2efe3a3`。
- Lean 4.35.0 の `lean --trust=0 -DwarningAsError=true`: 7 module、7 独立 Audit、合成 import は exit 0。公開バイトで取り直した 7 監査ファイルはそれぞれ `lake env lean --trust=0 -DwarningAsError=true` でも exit 0。29 監査項目は標準 `propext`, `Classical.choice`, `Quot.sound` のみ（`Classical.choice` は非計算的な支持付き view の filter）。公開ソース/Audit の exact Git bytes を別のローカル出力先で再実行し、依存 3802 source blobs が integration と一致。新規 14 ファイルの末尾・改行・禁止トークンも確認。全体 Lake、CI、Rust は未実行。
- `work/dots-main` のみ expected-head / non-force。累積 18 パス（Lean 7、独立 Audit 7、barrel 1、C380 一覧 1、心拍 1、報告 1）で、元 barrel の完全 bytes に 7 import 追加。凍結 2 パスは metadata のみ照合。使用量の枠は不明。
- 最終照合開始 `2026-11-24T03:21:02.538Z`、開始から 50 分。
