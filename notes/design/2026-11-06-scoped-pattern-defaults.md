# 回答 Q4〜Q7 と joint payload coverage の接続

状態: **Draft（検証済みの核とsource接続の境界を記録。言語仕様は追加しない）**

Q4 の B と Q5〜Q7 の回答を、名前解決済みの pattern/data case kernel に反映した。
Q8 の `JointCaseCoverage` と同じ具体 evaluator で進行を証明した。
source parser、名前解決、全言語推論器までの接続を完了したという意味ではない。

## 1. 使う入口と旧入口の関係

Q4 の default scope を含む照合の入口は `ScopedCasePatterns.run`、
順序つき arm の入口は `ScopedCaseEvaluation`、具体 data syntax の入口は
`ScopedCaseDataProgram.eval` である。pattern 自体と data expression 自体は既存の
`CasePatterns.Pattern` と `CaseDataTerms.Expr` を再利用する。

`CasePatterns.run`、`CaseEvaluation`、`CaseDataProgram.eval` は環境に依存しない
default callback の参照系として残す。これらの既存定理の主張は変更しない。
`ScopedCasePatterns.run_constant_defaults` は、任意の float comparator、任意の
環境非依存 default evaluator、任意の外側環境・pattern・入力値について、
新しい照合の **trace と成功・miss・error を含む観測全体** が旧照合と一致すると示す。
旧入口を Q4 B の source lowering 先として使うことはしない。

後続 component の default evaluator には、直前までに成功した component の束縛を
現在の環境の前へ追加して渡す。型判断も同じ位置で `leftBindings ++ types` を渡す。
名前 lookup は先頭優先なので、pattern の束縛が外側の同名変数を隠す。
or の左右は同じ incoming environment から始める。左枝の miss までに発生した
観測は残るが、その枝の束縛は右枝へ渡さない。

## 2. scope つき安全性の契約

`ScopedCasePatterns.DefaultSound DefaultTyped defaultEval` は次を意味する。

- 任意の型環境 `Γ`、default code `d`、値型 `T` について、
  `DefaultTyped Γ d T` が成立するとする。
- 任意の値環境 `ρ` について `BindingsHold Γ ρ` が成立するなら、
  ある値 `v` が存在し、`defaultEval ρ d` の結果が `ok v` かつ `T v` となる。

`ScopedCasePatterns.typing_matches` は、この契約を満たす任意の default evaluator、
任意の float comparator、任意の独立型導出 `Typing DefaultTyped Γ p A Δ`、
任意の `BindingsHold Γ ρ` と `A v` について、`run … ρ p v` が miss または
型 `Δ` に従う束縛で成功し、error にならないと示す。成功を前提にはしない。
`typed_match_no_error` と `typed_match_bindings` はそれぞれ error 排除と成功時の型を取り出す。
`Typing.binding_names` と `Typing.aligned` は束縛名と構文整合を保存する。

`CaseDataTerms.default_scoped_sound` は、任意の float carrier について、
`DefaultTyped = CaseDataTerms.Typing` と `defaultEval = CaseDataTerms.defaultEval` が
この契約を満たすと示す。default が `var` であっても、実行時の累積環境と
同じ累積型環境で得た独立な expression 型導出が安全性を支える。

`TotalTyping` は、単一の反駁不能 arm を証明する構文的な型判断である。
`TotalTyping.matches` は、任意の `DefaultSound`、float comparator、
`TotalTyping DefaultTyped Γ p A Δ`、`BindingsHold Γ ρ`、`A v` について、
ある束縛 `b` が存在し、`(run … ρ p v).result = ok (some b)` かつ `BindingsHold Δ b` と示す。
`ScopedCaseDataProgram.typing_evaluates` は、独立に型づけた scrutinee・各arm・
default・guard・body と、このような guard のない arm の存在から、
任意の妥当な外側環境で具体的な case の成功と結果型を導く。

## 3. 静的な重複束縛の拒否

`PatternBindingChecks.check` は、同じ照合経路での重複束縛を拒否し、
or の枝間には同じ名前集合を要求する。二つの異なる枝で同じ名前を使うことは許す。
外側環境の名前はこの検査へ入れないので、合法な shadowing を妨げない。

`check_exact` は、任意の pattern `p` について、実行可能な検査の成功と独立な
`NamesValid p` の同値を示す。`checked_path_nodup` は、任意の accepted pattern と
その任意の構文的 `BindingPath p names` について `names.Nodup` を示す。
到達可能な入力の有無によらず、各構文経路を検査する。
`duplicate_pair_rejected` と `duplicate_as_rejected` は任意の名前の重複を拒否し、
`same_name_in_alternatives_allowed` は任意の名前を or の別枝で再使用できると示す。

`ScopedCaseDataProgram.checkedEval` はこの静的検査に失敗した program を、
scrutinee/default/guard/body の評価より前に拒否する。
`checkedEval_rejects_iff` は、任意の comparator・外側環境・program について、
その拒否と名前規則を満たさない arm の存在が同値だと示す。
この関数は全言語の型 checker ではない。

## 4. 網羅性と scope を同時に使う

網羅性は default code ごとの `Domain` を使う。
`ScopedCaseCoverage.DefaultBounded DefaultTyped domains` は、任意の `Γ,d,T` について、
`DefaultTyped Γ d T` なら `T ≤ (domains d).denote` と要求する。
異なる scope の型が同じであるとは仮定せず、選んだ coverage domain が各型を覆うと要求する。

`ScopedCaseCoverage.typing_total_matches` は、任意の comparator、default evaluator、
`DefaultSound`、`DefaultBounded`、`Typing DefaultTyped Γ p A Δ`、
`CaseCoverage.Total domains p C`、`BindingsHold Γ ρ` について、任意の値 `v` が
`A v` と `C.denote v` の両方を満たすなら、ある束縛 `b` で照合が成功し、
`BindingsHold Δ b` となると示す。入力型 `A` と coverage domain `C` は同一に限定しない。
従って、arm は merged row 全体で型づけ、網羅性は個々の payload cell で確認できる。
全 pattern constructor、`narrow`、merged nominal/variant、list snoc、or を扱う。

`covered_arms_match` は、独立に型づけた全armと `Covered`、妥当な環境・入力値から、
元のarm列に guard のない成功armが存在すると示す。
`checked_arms_evaluate` は、全armの独立型導出、default/guard/body の型付き評価契約、
環境と入力の妥当性、実行可能な coverage check の成功を前提に、任意の開始indexから
順序付きarm評価が成功し、結果型を満たすと示す。

`ScopedJointCaseCoverage.tag_covered_arms_match` と `row_covered_arms_match` は、
同じ契約と `JointCaseCoverage.TagCovered` / `RowCovered` を使い、
別々の arm が別々の payload cell を覆う場合にもこの存在証明を供給する。

具体接続の `BoundedDefaultTyping domains Γ d T` は
`CaseDataTerms.Typing Γ d T ∧ T ≤ (domains d).denote` である。
`ScopedJointCaseCoverage.typing_evaluates` は、任意の comparator・domains・型環境・
program・結果型について、この default 判断を使う独立な program 型導出があれば、
任意の妥当な外側環境で `ScopedCaseDataProgram.eval` が成功し結果型を満たすと示す。
型導出には scrutinee、全armの型導出と `NamesValid`、joint `RowCovered` を含める。
実行成功、既に成功するarm、純粋なcallback oracleを前提には含めない。
`typed_checkedEval` と `typed_no_unmatched` は、静的名前検査で拒否されないことと、
妥当な外側環境で unmatched にならないことを取り出す。

## 5. 量化した具体例

`ScopedCaseExamples` は、任意の内側・外側の整数について、外側の値ではなく先行する
pattern 束縛を default が読むことを観測全体で示す。nested pattern の先行束縛、
失敗した or 枝からの束縛漏れの不在、先行 miss 後の任意 default の省略、
guard が偽なら次の arm へ進む観測も示す。

`ScopedJointCaseExamples` の payload は `bool × record` である。
false/true の二つの反駁可能な arm が tag 全体を覆う。
各record patternは整数を束縛し、後続fieldのdefaultがその整数を読む。
`program_typed` は任意の Bool と入力整数について独立な型導出を構築する。
`typed_program_progress` はさらに任意の外側整数を量化して concrete evaluator の進行を導く。
`default_uses_pattern_binding` は同じ全入力について返る値が内側の整数であると示す。
`joint_coverage_checked` は新checkerの成功、`whole_payload_checker_rejects` は旧checkerの
保守的な拒否を示し、旧定理を弱めずに拡張を区別する。

## 6. 残る境界

- source parser、解決前の名前、source 型annotation checker、主型推論器への lowering は未接続。
- `CaseDataTerms` の具体式は既存の有限data syntaxである。全言語の関数・再帰・effect handler・
  cast と統合した source safety ではない。抽象 matcher は任意の観測を持つ default を扱える。
- 既存 `CaseTree` の有限nested case tree は旧入口のまま。
  今回の nested pattern と、case式を含む default/guard/body のscope統合は別の義務である。
- or の静的名前検査は名前集合で比較するが、独立型判断は従来どおり両枝の束縛型listが
  同じ順であることを要求する。source lowering で異なる束縛順序を正規化する証明は未接続。
- coverage domain の計算・default型からの最良近似の自動導出・全source patternに対する
  coverage checker の完全性は主張しない。明示した有限domainと既存の構造的分割を使う。

Q4〜Q7 は回答済みの内容に従って実装した。このまとまりから新しい仕様質問は生じていない。
