この周に閉じた G の行: **G03（I-85 の同じ相）**。元の literal where 全子を、同じ raw graph で同 role・raw Alias 類に分け、K2 が実際にある類について全ての元位置を宣言順に報告する範囲。**G03b（相の遷移）は未完。残り19行。**

# C454: 同一相の where の K2 類を、元位置を失わずに累積入口で検査

- 実開始 `2026-11-27T01:30:00.001Z`。終了と経過は完了 heartbeat が示す。使用量の枠は不明。
- 正本開始 `integration/m1-final@fa6ed2185643d29e9280c3abc4e5e573d55fdbe2`（C453 を exact Lean `88e58b23ec1184d08b29c63eff9bc38420216087` で採用）。I-85、inbox `0022cfc8f8bc0c6a6cde21c7b1d9fe7564466b5d`。終了前に読んだ正本 `integration/m1-final@fa6ed2185643d29e9280c3abc4e5e573d55fdbe2`・Lean `88e58b23ec1184d08b29c63eff9bc38420216087`。C454 の実装定理は work 上で検証済み、正本採用は未確認。
- 技術 pin `work/dots-main@1fec459925d53156473f90e3efd686cd400ebaac`、Lean tree `70c45bac822ff9e58c2b1b1a5a589b41125a732f`。設計 `notes/design/dots-cycle-454-i85-same-phase-g03.md`。I-84 の表示判断は保留のまま（`yulang3@3162a7b99d99144c390ed883a815ff4488743cbf` の `spec/06-roles.md` §6.3 行264、blob `16da40eb041bf38daa9d8b2acb7ea0ddf22d907e`）、代表を設けない。

## I-81 の三条件と I-85 の境界

1. **独立な source 規則・保存と反映。** `SamePhase454.Exact` は checker の成功ではなく、実の `ParentSelection` で繰り出した全元子に対する `OriginalDiagnostic`（実際の raw Alias 関係と root K2 の真偽で索引づけた独立証拠）と、空でない正確な cyclic 類の報告。 `same_phase_key_iff_same_role_and_raw_alias_at_actual_marks454` は任意の二つの実元位置について、類一致と同 role・同相 raw Alias の両方向。 `every_reported_group_keeps_every_actual_origin454` と `each_actual_cycle_has_exactly_one_internal_reported_group454` は、返した各類には実 cyclic 類の全元 `where` のみが相対順序を保って入り、実 cyclic な各元子は正確に一つの内部診断類に入り、報告に現れることを示す。元 ordinal・節 ID・完全な occurrence path・role・実入力を保持。類番号/代表は報告にない。類どうしの並べ替えだけを許し、類の中の並べ替え/省略/重複は許さない。
2. **data-only の実行分岐。** `check_full454` の `.rawGrouped` は独立な checker 成功の仮定を受け取らない。`SourceDiagnosticWire` の有限な索引・raw 証拠を同じ `FullProblem` の元選択と元節から読み直し、全位置の raw 状態と全対の類関係を確かめ、実報告を比較する。C453 の一 role 一類という十分条件を新分岐は要求しない。raw-safe 子は元列に保存するが、実に選択された leaf であることを要求も含意もしない。何も cyclic でなければ、この K2 分岐は true にならない。旧入口は `.previous` で `check_full453` へ委譲し、`all_previous_witness_Bools_unchanged454` はすべての旧引数で元 Bool と一致。既に正確だった C453 grouped-true は、同じ元の証拠部分で新分岐にも通る（`inherited_grouped_positive_replays_same_original_wire454`）。
3. **正確な報告と同じ State の健全性・有限 witness。** `check_full_sound454` は任意の `p, report, witness` で true なら独立な分類、かつ任意のモデル `m` が同じ `p.state` の `FitsFull` を満たせば同じ実親の head/本文の意味、元 `kids`、固定出力条件（この範囲は元の出力無し）と正確な診断証拠を導く。拒否された子に辞書を作ったり、安全な元子まで解決したと主張しない。 `exact_same_phase_report_iff_finite_wire454` は独立な正確な報告 ⇔ true になる有限 wire。特に `cyclic_original_of_any_actual_scoped_parent_has_exact_witness454` はすべての独立な実親・任意の実元 ordinal の子で実 root K2 があれば、元列から証拠と正確な報告を構成する。先に checker が true、既製の類・raw status、raw-safe 子の選択を前提としない。これは有限 witness の存在定理で、witness を検索する実行 solver や停止性を主張しない。

範囲は C443 G03 の **実 authored invariant list-point 親・可視一候補（複数の親 head 引数なら元の binder は相異なる）、出力指定の無い unary literal binder where**。親の実入力は既存 frame が読む。節数・元 ordinal の上限を置かない。親自身の K2 を子の K2 としてすり替えない（`exact_grouped_raw_report_never_substitutes_parent_K2454`）。C452 の実 output-equation emission 演算はこの範囲で実際に空列で、その部分の raw graph は同一（`real_output_emission_at_this_substep_leaves_the_graph_unchanged454`）。親 prefix 選択と元子の K2 診断の証拠であって、グループ化済みの報告を古い `WhereForest` と同一視しない。全ての子が解決する、親の他の診断（保留／曖昧／一般の拒否）に勝つ、という全 solver の規則も立てていない。

類番号を選び替えても、同じ実親から作った厳密な報告値は変わらない（`same_parent_reports_are_independent_of_all_wire_label_choices454`）。同じ元 ordinal は同じ実位置なので、異なる類が同じ公開位置列になることもなく、受理した報告に同じ類を重ねない（`accepted_raw_diagnostic_never_duplicates_a_projected_group454`）。

## 検証

- Git から上記 immutable commit の 9 ファイルを再取得し、独立 physical build の対象と exact 照合。公式 Lean 4.35.0、各 production `lean --trust=0 -DwarningAsError=true` を焦点付きで別々にコンパイル、各 Audit は peer Audit のない production-only path で独立起動。Git の exact 内容でも同じフラグの `--stdin` をファイルごとに実行しすべて exit 0。既存 `7755` production、`2165` Audit は blob 単位で unchanged、既存変更は集約の末尾4 import のみ。凍結ファイルは識別子のみ。全体 `lake build`、`verify-lean.sh`、Rust／parser は実行していない。
- 公開 19 行の `#print axioms` は `propext`、`Classical.choice`、`Quot.sound` のみ。3 つの `#guard_msgs / #eval` は実行試験で証明には使っていない。
- 同 role の cyclic 類 [60,61] と [62] が真に別の raw 類で、適合モデルが存在。exact 報告と類間交換は true、混ぜる／類内逆順／欠落／重複／親位置や分割を変える／親自身に実 K2 を足す対照は false。安全な元子が実に G02 選択不能でも raw 元位置を保存すれば true、その元 raw 状態を削れば false。全元安全 profile は正しく読めるが空の K2 診断は false。
- 非公開の追加 QA では、実 C453 の「適合モデル全部で入力同値だが raw Alias は別」の fixture を再生。新分岐は **現相** にある 60 の K2 のみを通し、同値だけで 61 を含める報告は通さない。旧 Bool は変えない。別試験で最終位置だけ実 K2・先行元子は安全の結果を確認。別の同 role 例では、実適合モデルが再帰 nominal と再帰 variant の両方を持ち、rank 0 の観測で二つの類の値を区別できる。同一相の入力証拠を数値ラベルから独立に定義した仕様と有限 wire の両方向も補助検証した（いずれも公開19行に数えない）。

- `lean/Yulang/GeneralDeclarativeI65I74WhereSamePhase454.lean` — Git `73a75cb2161032c821a0cd1c2542bc2653d8a969`; exit 0, 公理出力 0, 実行 guard 0。
- `lean/Audit/Cycle454I74WhereSamePhase.lean` — Git `255921e24c9e232fe4e7477846aa47a110281dd3`; exit 0, 公理出力 5, 実行 guard 0。
- `lean/Yulang/GeneralDeclarativeI65I74WhereSamePhaseSource454.lean` — Git `91258cf57c6135cabb5aeec6bc03199a7ed3d23f`; exit 0, 公理出力 0, 実行 guard 0。
- `lean/Audit/Cycle454I74WhereSamePhaseSource.lean` — Git `2fbd4d96f2769db18a35209babd4a12d8ffd0f14`; exit 0, 公理出力 5, 実行 guard 0。
- `lean/Audit/Cycle454I74WhereSamePhaseActual.lean` — Git `437545d8fbf46a802b4264f71dd77433bf69f1f7`; exit 0, 公理出力 4, 実行 guard 3。
- `lean/Yulang/GeneralDeclarativeI65I74WhereSamePhaseLabels454.lean` — Git `91d8cffdd233deeb68c35e64eb64abfd2c9d7aae`; exit 0, 公理出力 0, 実行 guard 0。
- `lean/Audit/Cycle454I74WhereSamePhaseLabels.lean` — Git `c5afc4435cea948a7cdf2ed77e3e4341da514612`; exit 0, 公理出力 2, 実行 guard 0。
- `lean/Yulang/GeneralDeclarativeI65I74WhereSamePhaseContinuity454.lean` — Git `6d2cdd8265e633567e6dc3049e14cbac34e5bbc7`; exit 0, 公理出力 0, 実行 guard 0。
- `lean/Audit/Cycle454I74WhereSamePhaseContinuity.lean` — Git `182f8fd070192bbb62ec5fb76b1768f6e2a2645d`; exit 0, 公理出力 3, 実行 guard 0。

## 未確認・次の作業

- I-85 は G03 をこの同相範囲で閉じ、同相外を G03b に残す。G 全23行の **G00–G03 が閉、残りは G04–G21 と G03b の19行**。G03b は author/capture の実等式による相遷移と、新しい正当な raw graph の読み直し。raw 非 Alias は一般の不一致を意味しない。モデルを保つだけでは K2 を保てない。 `centerPair` を role 併合の標準操作と認定せず、現相から相をまたぐ公開分岐も追加していない。
- 代表・ユーザ向け表示位置は決めない（I-84）。任意構造の where／名前付き出力／一般の診断・実装の意味および全体の `NoFalseRejection` は未検証、G15–19 等を先取りしない。この周に質問ノートは増やしていない。
- 次は live 指示が変わらなければ G04。G03b は I-85 が認めるとおり G15–19 と近い段階で、実 source の整合、許された graph の形成、fresh raw K2 を別々に検証する。
- 変更は終了 heartbeat とこの報告を含め13 paths。途中の試行・追加 QA は公開 Lean の本数に数えていない。
