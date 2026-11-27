この周に閉じた G の行: なし。I-84 の全元 where を備えた正確な K2 報告を、実同入力が保証される局所範囲で累積入口につないだ。same-role の実等式を一般に拾う段階は未証明。G03 は未完、残り19行。

# C453: I-84 の全元位置を持つ報告を累積入口につなぐ

- 実開始 `2026-11-27T00:31:17.371Z`。実終了と経過は同じコミットの heartbeat。使用量の枠は不明。
- I-84 / inbox `2090aabcfcbeaaf7a37f73fe6762109168047354`。作業開始の正本 `integration/m1-final@c6569e6701c1b107b34a46e3dd17758993eb154a` は C452 の exact Lean `0f84913b1d969faf9f29ec1edcfb975f6886758b` を採用済み。
- 技術 pin `work/dots-main@7cd070a53a73255a29f5fb53e73424280df2e0b5`、Lean `88e58b23ec1184d08b29c63eff9bc38420216087`。終了時の正本 `integration/m1-final@c6569e6701c1b107b34a46e3dd17758993eb154a`、Lean `0f84913b1d969faf9f29ec1edcfb975f6886758b`。 C453 の Lean が正本に入ったとは未確認。

## 正確な報告と同じ累積入口

1. `WhereGroupedEntry453.GroupedReport` は、実親の出現 path・impl ID と、各 cyclic 類の全元位置の列を持つ。列の内側は宣言順。報告に raw の任意なラベル、表示位置・代表はない。外側は多重度を保つ置換同値で、類どうしの表示順を規定しない。`matches_reflects_exact_origins453` が実比較をこの関係に反映する。I-84 どおり、利用者に表示する位置の決定は延期のまま。
2. 親は実に選ばれた C450 list-binder frame、where は出力指定のない一引数 literal 位置。互いに異なる元の節すべてを実 source から戻す。`whole_roster_check_reflects_sufficient_scope453` / `certified_class_iff_same_inputs_at_both_actual_sites453`: 任意の二つの真の indexed `SourcePointAt` について、同 role が一つの checked raw Alias 類に収まる十分条件のもとで、実同入力 iff 同類を示す。異なる role は併合しない。元 source から構成された peer にだけ適用し、ラベルを自己申告させない。実 C452 発行行は空で raw 不変、その同じ相だけで証明する。
3. `exact_scoped_grouped_report_iff_finite_wire453`: 独立した実親と元 where 証拠、全体条件、報告の正確さから、同じ report の有限 data-only witness を得る。逆向きも成立。`check_full453` の追加組はこの読みを使い、旧組は**昇格済み** `WhereSites450.NoSiblingMerge.check_full450` をそのまま呼ぶ。`all_previous_witness_Bools_unchanged453` は全入力で旧 Bool を保存する。違う種類どうしの report/witness は通さない。
4. `check_full_sound453` は任意の受理入力で独立判断と同じ State の全 FitsFull モデルの報告証拠を返す。`every_reported_group_has_all_its_actual_ordered_origins453` は各報告類が実に対応する全元位置を宣言順で持つことと、各位置で実 K2 が起きることを取り出す。`exact_child_cycle_is_in_report_after_actual_output_emission453` は同じ発行相で見つかる任意の実元 K2 が報告に入ることを示す。`accepted_grouped_has_original_positional_trace_and_no_writes453` は旧の原順序 trace と発行 0 を別に保持する。短縮した類を旧 WhereForest に渡さない。

## 実入力と境界

- 実 authored fixture: 元節 60・61 は異なる捕捉名 1・6 を持つ同 role の raw Alias。適合モデルには再帰 nominal と Bool がある。二つの元 path `[27,31,0]` / `[27,31,1]` を一つの K2 類に保持し、他 role の安全な第三子は別の実 authored leaf 証拠で選択。ラベル改名でも通る。元順序反転・原位置落ちや重複・類割り・類重複・誤った親 path/宣言・古い raw 証拠・実親 K2 への差し替え・安全というだけの子・種類違いを拒む。異なる二つの真の cyclic 類では外側を入れ替えても通し、類をまとめたり落としたりすると通らない。
- G03 の原型の「第二の元 where 子だけ K2」は通り、同じ証拠を親位置の報告に移すと通らない。既存の昇格 C450 入力も累積入口から真、旧同 role guard の失敗も保った。Lean の authored source bundle の試験であり、parser/Rust を通した意味ではない。
- **未完成が実際に起きる**: 同 role の元節 60・61 で、両中心が同じ constructor RHS を持ち、実際の FitsFull が存在して全適合モデルで二中心が同値でも、raw Alias は別、元 raw K2 は片方だけになりうる。C452 の実元位置読みは [[60]] を返すが、今回の guard はその scope 外をどちらの報告でも受理しない。これは Yulang の拒否ではなく、証拠 reader の範囲外。実 `centerPair` を追加すると旧 ordinary 模型全体が同じなのに、元は安全だった 61 に raw K2 が出る。したがって模型の保存だけで元の K2 を移さない。非公開の別検査では、この実例を変更後 raw で新たに読み直すと [60,61] の一類が通ること、二相の FitsFull がこの零 retained 実例では同値であること、古い wire の流用は通らないことも確認した。実 solver がその遷移を生むとは主張しない。別の非公開の厳格検査では、旧 `GeneralNominalSaturationState.merge` の空出力の場合は、**需要の出現 ID** の alias を追加するだけで、旧型 context、全 Models、FeedbackK2 の各型 edge と各元需要の root K2 は不変と示した。これは `centerPair` による型 graph 更新とは別操作である。

## 検証と次へ

公式 Lean 4.35.0 (eb6cafb7290e8bd5f2937522d8d804f58f02bafc) `--trust=0 -DwarningAsError=true`。exact 2 production・6 standalone Audit の独立物理検証と、公開 Git bytes を取り直した focused 再検査はすべて exit 0。29 公理出力はいずれも標準のみ。5 件の守られた `#eval` は実行対照で証明には未使用。Audit の import: Yulang.* 以外 0 件。既存 7753 production と 2159 Audit の blob、凍結2ファイルの ID は不変。集約は2 import追記のみ。変更は Lean 9 パス・design 1・heartbeat 1・本報告 1。全体 build、verify-lean.sh、Rust は実行していない。

残り: (1) 一般の同 role の実原入力について、author/capture から根拠のある equality と区別を検査する（raw 非 Alias を区別として扱わない）、(2) 実際に更新された raw がある場合は、真正な phase 遷移・元パス/依存 retained を証明し、新しい raw K2 で再読する。範囲外の類や solver は閉じていない。表示位置は I-84 で決定を延期しているため、新しい質問はなし。G04、構造 where・非空関連出力を広げる G15–16、一般診断完全性、NoFalseRejection は対象外。G03 は未完、残り19行。
