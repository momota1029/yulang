# cycle2 pattern / F1 boundary claims

基点: 新spec `3fdd6c3ac`、旧Y2 `d4c8bc8fc`。表は今回の限定した比較。実機全文は `runtime-cycle-2-effects-patterns.md`、詳説は各リンク先。

| ID | 出典 | 規則 | 例 | 実機の結果 | 新spec | Lean | 分類 | 備考 |
|---|---|---|---|---|---|---|---|---|
| C2-PAT-01 | lowering/pattern.rs:529–553、X22 | default無しrecord patternは旧ではrequired入力を作る | `case x: {port:p}->p; _->80` に `{}` | check0、dump required port、run1 missing port。present443はrun0 | 3b.3 optional inputはmiss可能 | CommonSourceOptionalX22.x22_proved（指定optional subjectとsource arm generator、actual evaluator） | 違う | exact optional annotationは旧lowering未対応。推論形の局所観測であり、Lean PROVEDを変更しない。 |
| C2-PAT-02 | lowering/control.rs lower_case_arm、X23 | 全case armのbody effectを合流 | wildcard1の後にping arm | check0、dump f:any->[ping]int、run0:1。[] filterはcheck1 | 3.7 | CommonSourceArmGeneration.EnvironmentTyping（全armの共有行制約）、source全体のparser橋渡し未検証 | 一致 | unreachable guardも標準prelude付きcheck/dump/run成功、静的ping残存。 |
| C2-PAT-03 | lowering/control.rs catch scrutinee、X24 | pipe後の省略scrutinee catch構文 | `ping::get() \| catch: ...` | check1 missing-catch-scrutinee。標準preludeでも同じ | 3.9は直接catchと同じと確定 | source pipe parser橋渡し未確認 | 違う | X oracle分類は「実機で表せない」。ここの違いはsyntax入口の対応差で、handler意味論反証ではない。明示handler関数pipeは7。 |
| C2-EFF-01 | propagate.rs:234–245、specialize/lib.rs:305–313 | F1明示高階row境界 | higher(f:[ping]int->[ping]int)、higher plain | check0/poly0、mono1/runtime-ir1 conflict。arg-rowだけは7 | 5.5c通るべき具体境界 | Common.common_arrow_iffに特例なし、strictApp効果joinは別 | 違う | f1-cycle-2-boundaries.md。backend2種類同じ。全F1を否定しない。 |
| C2-EFF-02 | 上記runtime原ログ、wildarg比較 | glob引数＋明示戻りrowで直接/etaを比較 | higher(f:[_]int->[ping]int)にplain / lambda x.plain x | 両check0、直接run1 unhandled、eta run0:7 | 5.5/5.5c、全eta同値の規定はこの監査では確定しない | source/coercion adapterへの対応未確認 | 未確認 | 具体差は確定。一般eta法則の成否やどちらが正しいかは決めない。 |
| C2-PAT-04 | pattern.rs:529–553、lambda.rs connect_lambda_pattern_annotation | default由来effectの表面関数境界 | pick{a=ping::get()}=a、handle(pick{}) | check0、表示行からping欠落、外側handleでrun1。直接catchは7、default内handleも7。[]結果注釈もcheck0 | 3b.3のeffectful照合、5.5のfilter | CommonAlignedPatternSafeDefaults.typing_matchesはDefaultSound仮定、任意effectful defaultのsource統合は未確認 | 違う | default-effect-boundary-cycle-2.md。意味論を旧失敗へ合わせない。 |
