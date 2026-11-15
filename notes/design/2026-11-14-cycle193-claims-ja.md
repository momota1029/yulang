# Cycle193 — 定理名と量化範囲

以下の固定ソースはすべて既存の GeneralNominalExamples の Display(List Int)。
正確な全81定理の型は Cycle193FinalTypes.lean と final-public-types.log に保存。
各節の名前はそのモジュールの公開定理全件。私有補題・生成宣言も最終148宣言公理検査に含む。

## GeneralNominalNonleafAdministrative193

具体的な finish の raw/center sites は親と子の2個。任意の記録済み2site が SameInputs を満たすなら既存 Alias がある（違う親子の SameInputs は具体的モデルで否定）。したがって親と子の AdministrativeReady を仮定なしで得る。

定理名: `raw_sites`, `center_sites`, `raw_closed`, `center_closed`, `child_ready`, `parent_ready`。

## GeneralNominalNonleafChild193

具体的な finish の displayChild について actual head-only Survivor・Prepared・Unique key3 []・Frame・SafeKnown を証明する。wrong_failed は具体的な不適合 Display list 候補についての失敗。子 Installable をここではまだ結論しない。

定理名: `survivor`, `prepared`, `wrong_failed`, `unique`, `frame`, `safe`。

## GeneralNominalNonleafInstallation193

同じ具体的な親 plan は Installable、かつ未記録。したがって start から finish への実際の Step が存在し、finish は到達可能、子は生成済み、具体的な model は finish の Models。任意の割当について finish の Models なら同一割当で子と親の再帰 Evidence を持つ。さらに finish の Models と元のソース Models は同値であり、start の任意のモデルにも同じ再帰 Evidence が成り立つ。start は Stable でない。finish の Stable は主張しない。

定理名: `installed_requests_empty`, `installation_models`, `enabled`, `novel`, `actual_step`, `reachable`, `final_model`, `child_generated`, `leaf_evidence`, `recursive_evidence`, `source_recursive_sound`, `final_models_iff`, `initial_recursive_evidence`, `source_not_stable`。

## GeneralNominalNonleafLocal193

同じ具体的な start・registry・displayRoot について、head-only 候補は key1 と子[displayChild]に一意。出力要求は空であり、必要な安全性・効果準備・出力衝突の不存在を証明して、実際の WF Local.selected を得る。任意のソースの分類完全性ではない。

定理名: `prepared`, `frame`, `known`, `survivor`, `wrong_failed`, `unique`, `requests_empty`, `effects_ready`, `no_output_conflict`, `safe`, `selected`。

## GeneralNominalNonleafPlan193

既存の具体的な Display(List Int) 宣言・ソースについて、検査結果、捕捉、中心、子需要の列が指定値に等しい。任意の割当 m が元の state true の Models を満たすなら plan の Equations、branch、Holds を満たす。start は実際の WF Initial であり、任意の m について start の Models と元のソース Models は同値。新しい言語断片を定義していない。

定理名: `query`, `raw_report`, `inherited`, `bindings`, `binder_zero`, `named_empty`, `input_empty`, `head_schema`, `first_child`, `equations`, `branch`, `holds`, `children_exact`, `initial_source`, `source_models`。

## GeneralNominalNonleafReuse193

具体的な子 plan について、任意の raw current.state のモデル assignment は childPacket.Holds を満たす。従って全 raw-journal モデルに対する Committed を得る。任意の根の出力要求は空。実際の WF 子 Local.selected、choice/value guard、旧親効果を含む InstallationModels、Installable をすべて証明する。child_build は生成済み葉の記録再利用によるゼロ Step、source_build は実際の親 Step とその子再利用からなる非葉の Build。source_tree_sound は到達可能性・最終モデル存在、および全最終割当について同一割当の初期 Models と再帰 Evidence を結論する。全般 EvidenceNode、最終 Stable、親 Classify、完全性、主性の証明ではない。

定理名: `query`, `report_exact`, `packet_models`, `committed`, `head_schema`, `head_equations`, `holds`, `requests_empty`, `ready`, `selected`, `alias_identity`, `choice`, `support_ready_at`, `value_guard`, `installation_model`, `child_enabled`, `child_build`, `source_build`, `source_tree_sound`。

## GeneralNominalNonleafSafety193

具体的な finish では任意のソース番号の feedback cycle と任意の origin の centered cycle が存在しない。全 Fin2 ソース位置は ReadyAt。任意の需要・key・子列について旧 fixture の feedback Local.selected を仮定すれば finish の feedback Local.selected に移せる。旧 centered 境界の親子 selected は補助結果であり、最終の実際の WF 親 Classify ではない。

定理名: `feedback_acyclic`, `graph_tests`, `center_distinct`, `centered_acyclic`, `ready_at`, `child_decision`, `parent_decision`, `feedback_selected`, `child_center_selected`, `parent_center_selected`。
