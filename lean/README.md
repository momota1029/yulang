# Yulang3 型推論の形式化

このディレクトリは [`spec/10-inference-core.md`](../spec/10-inference-core.md) の核を Lean で検証する。古い型推論器や proof sprint は復元せず、現行仕様に対応する定義と定理を置く。

Lean は `lean-toolchain` の **4.35.0** に固定する。依存は Lean/Std のみで、Mathlib や外部 solver は使わない。

```sh
cd lean
lake build --wfail
lake env lean --trust=0 Audit.lean
```

## Core (M0)

[`統合計画の M0`](../notes/design/2026-11-06-integrated-inference-plan.md) に対応する。
`Core.Expr` は型・shape 添字を持たない共有構文で、全ローカル参照は de Bruijn 添字である。
operation/key/scope・float 内容・opaque atom の carrier は `Core.Signature` で指定する。
未束縛名は `free`、旧 named let の名前は復元用の hint として保持する。
ordered case の guard/default、単一/複数/部分 handler、nominal 構築 site、内容つき literal、
method 要求、cast site を表現する。旧 computation-argument の `app` と `strictApp` は区別し、
Multi の `.core` は `StrictApplication.compile` を経由する。

`Core.Typing model` はモデルの独立な構成子判断であり、旧型付けの存在で定義した関係ではない。
required-field と presence の carrier・判断は別に保持する（M1 の境界）。
下表の同値は任意の旧式・環境・結果について成立し、推論成功・solver 解・fuel は前提にしない。
定理名の接頭辞は `Yulang.Core` である。

| 接続・定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `Required.conservative` | 任意の model、捕捉された poly/signature を含む環境、式、computation について旧 `Inference.Typing` ⇔ Core 判断 | required-field への `recordDefault` 規則追加 |
| `Effects.conservative` | 任意の model・row view・署名・環境・式・computation について旧 `RecursiveEffects.Typing` ⇔ Core 判断 | 他断片との混合、operation-local 多相の統合 |
| `Qualified.conservative` | 任意の model・method table・role theory・環境・式・computation について旧判断 ⇔ Core 判断 | method lookup・辞書 elaboration の統合 |
| `Presence.conservative` | 任意の data 型環境・式・意味的結果型について旧判断 ⇔ Core 判断。strict な `recordDefault` を含む | required-field/regular 型との同一視 |
| `Data.conservative` | 任意の名前付き型環境を名前列と型列に分け、旧 `CaseDataTerms.Typing` ⇔ de Bruijn 化した Core 判断。shadowing・未束縛構文も量化の対象 | source の名前解決 pass の証明 |
| `Case.conservative` | 任意の `CaseTree.Expr`・環境・結果型について旧判断 ⇔ Core 判断。arm 順・guard・default・通常/variant coverage を保持 | scoped default への旧 CaseTree の意味変更、effect/cast を含む case 推論 |
| `Scoped.conservative` | 任意の環境・入力型・束縛型列について、具体 data default を持つ旧 scoped pattern 判断 ⇔ Core default で具体化した同じ汎用判断 | この module は pattern AST。全 source の pattern elaboration は含まない |
| `Resolved.operational_core` / `multi_core` | 任意の shape 環境・注釈付き式・結果 computation 型について、旧型付け ⇒ 同じ環境/結果型での Core 消去式の型付け | 両 AST とも同じ元の式への逆向きは不成立。lambda/handler/widen の注釈を消し、Core の subsumption も許す。`annotation_erasure_typed` / `annotated_not_pure`（Multi は `multi_` 接頭辞）で両方の反例を証明 |
| `Construction.conservative` | 任意の parameter 数・compatibility・registry・期待型・construction・plan について旧 `PlanTyping` ⇔ Core site の planner 判断。site 順・元型・parameter 割当てを保持 | 旧 module は式 AST を持たない。site の実式の推論/実行、nominal 値型の推論ではない |
| `Literal.conservative` / `matches_conservative` | 任意の float carrier・literal・kind について kind 分類と Core 判断が一致。任意の float 比較関係の下で matching も双方向に保持 | 旧 module は式型付けを持たない。Kind を言語全体の主型とすることや marker literal との統合ではない |
| `Block.definition_conservative` / `scc_conservative` / `generate_exact` | SCC は式の外。宣言 head と Core body を分離し、任意の旧環境・slot 割当て・宣言列で全 body 検査が同値。実際の同時再帰環境と旧 `generateSCC` の充足にも接続（後者は `EnvRel` 前提）。全注釈の局所値型変数も全称量化 | SCC 発見・求解・closure・一般化の統合、effect/case body の SCC 推論（M3） |
| `required_principal_exact` / `effects_principal_exact` / `qualified_principal_exact` | 既存の `EnvRel`（effect は `SigRel` も）の下で、任意の結果 computation について旧 principal scheme の充足 ⇔ 対応する Core 型付け | 混合 Core 全体の新しい scheme/solver ではない |

機能の相互作用を扱う統一判断、`Core.infer`、混合断片の拒否完全性・unsupported の排除は未証明である。
`cast` は site の構文のみで、統一した挿入/型付け規則は M4 に残す。
literal の内容・presence・nominal の planner 結果を一つの値型 carrier に統合したとは主張しない。
`Core.Expr.isValue` は旧 required/effect 判断用の構文検査であり、新構成子の値制限を決めない。

### M1: 型モデルの接続（部分完了）

`CoreRequiredDemands` は有限の required demand が一致する断片を明示する。
`Required` は optional/lacks を除き、union/intersection・pair・variant・任意の payload 参照を許す。
`encode_exact` は任意の payload 述語割当て・mask・data 値について、presence demand を
legacy layer へ戻して再翻訳した意味が元の意味と同値であることを示す。
`finite_exact` は任意の有限 legacy payload 型割当てについて、独立な
`DataTypeSemantics.Holds` との保存・反映を与える。
`translate_required` により全旧 layer の data 投影がこの断片に入り、`required_mask` により
shadow 操作でも閉じる。旧 `{}` は引き続き全 record の上界であり、exact empty ではない。

`CorePresenceAlternatives.normalise` は有限 layer を相関を保つ選言標準形へ移す。
`normalise_exact` は任意の payload 述語・mask・data 値で所属を保存・反映し、
`mask_exact` は各枝全体への mask 適用を独立意味と一致させる。
これは presence 述語上の分配であり、旧構造的部分型に分配則を追加しない。
工程3の有限表現であり、この標準化自体は矛盾検出・飽和・regular 解の抽出を行わない。

`PresenceBoundCoalescing` は工程3のうち、有限個の変数間の flow と固定された
presence 上下界の消去を扱う。任意の payload 述語・mask の下で相関を保ち、
自由 parameter を有限個の値へ制限しない。

| 定理（接頭辞 `PresenceBoundCoalescing`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `expand_satisfies` / `coalesce_satisfies` | 任意の有限 flat 制約集合で、伝播した下界が全制約を満たすなら、任意の自由述語 parameter（後者は layer parameter）から構成した解が全制約を満たす。layer 版は任意の payload 割当て・mask を量化 | constructor/open-tail の分解と整合性の自動証明、関数・行を含む regular graph の解 |
| `expand_retraction` / `expand_retraction_eq` / `coalesce_retraction` | 同じ flat 制約の任意の独立な解を共有 parameter に戻すと、全元 slot の述語を回収。述語版は外延的に等しく、後続の観測に正位置性を要求しない | 循環 graph の同時構成・負位置を含む regular 型の回収 |
| `consistent_iff_satisfiable` | 任意の固定境界解釈と、その包含を正確に決定する checker の下で、有限整合性検査の受理 ⇔ 独立な解の存在。fuel・solver 成功を仮定しない | 任意の述語境界に対する包含 checker の構成、presence graph 全体の拒否完全性 |

flat な自由 parameter 消去は証明済みだが、以下の四つの regular/source 契約はまだ閉じていない。

Core 上で実行する二つの既存入口への接続も追加した。**統一入口ではない。**
`InferenceSyntax.embed_decode` が入口の構文検査から round trip を保証し、対応外の Core 構文が
`Required.decode` の既定 literal として推論されることを防ぐ。

| 接続・定理（接頭辞 `Core`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `RequiredInference.infer_embed` / `legacy_instances_exact` | 任意の legacy 式で推論結果そのものが旧入口と等しい。全 scheme・全自由 parameter・拒否・unsupported を保存 | presence モデルとの scheme 等価 |
| `RequiredInference.legacy_inferred_exact` | 任意の旧式・旧入口が返した principal・任意の結果型について、その全 instance と Required Core 型付けが同値。行反対称性を仮定 | 新 presence 規則を含む型付けへの反映 |
| `RequiredInference.recordFree_principal` / `recordFree_instances_exact` / `recordFree_rejected_iff` / `recordFree_ne_unsupported` | 任意の `RecordFree` Core 式・任意の regular 値型/行結果について、独立型付け ⇔ 実際の返却 scheme の全 parameter instance からの subsumption。拒否 ⇔ 型付けなし、unsupported を排除。行反対称性のみを代数の追加仮定とする | record 構築・default を含む断片の solver 完全性 |
| `PresenceInference.infer_instances_exact` / `infer_rejected_iff` / `data_ne_unsupported` | 任意の Core 式・任意の data 述語結果について型付け ⇔ 推論した exact Shape の包含。構文的 `Data` で拒否 ⇔ 型付けなし、unsupported を排除 | lambda・branch・regular parameter・effect 行の統合 |

`RequiredInference.RecordFree` は var/lit/lam/app/let/branch/pair/fst/snd/emptyRecord/field/variant を許す。
`PresenceInference.Data` は var/lit/let/pair/fst/snd/emptyRecord/record/recordDefault/field/variant を許す。
いずれも let の hint は `none` で、不正な射影・未束縛添字・不正な record 操作も断片に含める。
型付け可能性・solver 成功・fuel はこれらの構文断片の条件ではない。
Core の M0 model が `Type` に固定されているため、Required Core 定理の行 carrier も `Row : Type` である。

`CoreInferenceExamples` は実際の Core data 入口で present/absent、shadowed payload の消去、
採用されない不正 fallback の拒否を計算し、同じ fallback が既存 data runtime で評価されることも示す。
`unknown_default_principal` / `unknown_default_union` は任意の payload/fallback 述語に対する
開いた default operator の Core **型判断**であり、未知 base を推論した実行例ではない。
effectful fallback の推論例、未知 base を持つ lambda の推論例は未完である。

**M1 は未完了。** 関数・行を含む共通 carrier/部分型と presence 制約生成の exactness がないため、
所属の同値を `SourcePrincipalInference` と presence 推論の全 instance の同値へ読み替えない。
統合メモ5節の工程3〜5で必要な未証明の補題は次の通りである（以下は契約であり、Lean の定理名ではない）。

- `presence_coalesce_satisfies`: 任意の有限 presence/open-tail 制約 graph と入力制約について、
  飽和手続きが整合する閉 cache を返したなら、**すべての自由な値/行 parameter 割当て**から構成した
  regular 解が全 constructor・入力制約を満たす。旧 `coalesceGraph_satisfies` の拡張が必要。
- `presence_coalesce_retraction`: 同じ graph/cache の**任意の独立な解**について、その解を parameter として
  coalesce すると、**すべての元 slot** が新部分型の双方向比較で回収され、共有関係・負位置・mask を保つ。
  旧 `coalesceGraph_retraction` は fixed record spine のみで、この主張を与えない。
- `presence_solve_complete`: 宣言する入力 graph 断片の**すべての graph**で飽和が停止し unsupported を返さず、
  rejected ⇔ 解が存在しない。上の二補題とともに、自由 parameter に残余制約を課さない全 instance 抽出に必要。
- `presence_generate_exact` と `presence_legacy_instances_exact`: 共通モデルを定義した上で、任意の対応環境・式・
  値/行割当てについて生成制約の充足 ⇔ 独立 presence 型付けを示し、任意の旧 supported 式・任意の旧結果型で
  旧 instance ⇔ 埋込み後の新 instance を示す。各枝の solver exactness があれば `collect` の証明は再利用できるが、
  現状の補題だけではそこから統一入口の全 instance exactness を導けない。

旧 `Layer.record` の tail は有限 layer、open-record graph の tail は node 参照であり、
単純な置換は観測深さを減らす位置を変える（spec 10.32.5）。さらに旧 regular 部分型は構造的関係で、
presence の data 述語包含との同値はない。これらを既存 data 観測の橋だけで埋めることはできない。
関数/行の意味、上記の解構成と retraction は新たな数学的義務として残し、統一入口の公開を止めた。
既存 `collect_instances_exact` の変更、既存 theorem・test expectation の変更、仕様の仮決定は行っていない。

## Case の照合・順序・presence

`CaseValues` は内容つき literal、pair、record、variant、解決済み nominal identity、有限listを持つ。
`CasePatterns.Pattern` は wildcard、名前、literal、整数範囲、pair、record field/default、
list nil/cons/snoc、variant、nominal、or、as を持つ。record の残りを照合するときは
入力record全体を渡し、list tail には残りの要素だけを渡す。

独立な `CasePatterns.Typing` は照合で得る束縛の値安全性を扱う。
任意の型付け、入力型を満たす値、型付けに健全なdefault evaluatorについて、
`typing_matches` は照合がruntime errorにならず、成功した場合は宣言された束縛型を満たすことを示す。
`mergedVariant` は `VariantsMerged` のlookupが返す**payload全体**に子patternを型付けし、
他tagを持つ入力はmissとする。`mergedNominal` は同じ形で、単一nominal identityの
全constructor行を入力にして各constructorを分岐できる。orの名前集合と裸`..`の禁止は `Typing.aligned` に従う。
同じ名前集合の異なる束縛順をそろえるsource passは未証明である。

`CaseEvaluation` は上から順に照合し、成功したpatternのguardだけを評価し、guardが真の最初のbodyだけを評価する。
訪問列はscrutinee、arm、guard、bodyと葉の評価を保持する。
`runArms_typed` は束縛をguard/bodyへ渡す際の安全性、`runArms_progress` は型付きarm列と
実際に合うunguarded armの存在から、型を満たす結果が返ることを示す。
この定理単独の照合witnessは、次の網羅性の節で検査結果から構成する。

`CaseDataTerms` は具体的なdata葉のAST・評価器・独立型判断を持ち、
`typing_evaluates` からdefault/guard/bodyの健全性契約を導く。
guardは実際のbool値から判定する。構築のrecordDefaultはstrict、pattern defaultは欠如時のみである。
現時点のdata葉には関数、再帰、effect handler、cast、nested caseを含めない。
caseのscrutinee/body・pair・letへの有限な入れ子は、後述の `CaseTree` で追加する。

回答済みQ4を反映する `ScopedCasePatterns.run` は、前の部分で得た束縛を外側環境の前へ置き、
後のdefaultへ渡す。nested patternにも同じ環境を運び、orの失敗枝の束縛は次の枝へ漏らさない。
独立な `ScopedCasePatterns.Typing` も同じ順に型環境を延長する。
任意の型・値環境に健全なdefault evaluatorと独立型判断を前提に、`typing_matches` は
型に適合する任意の環境・入力から、missまたは型の合う束縛を導き、runtime errorを排除する。
`run_constant_defaults` はdefaultが環境を読まない場合に旧matcherと訪問列を含め完全に一致する。
`ScopedCaseEvaluation` はこのmatcherを既存のarm/guard/bodyの順序へつなぐ。
`ScopedCaseCoverage.typing_total_matches` は、独立なscope付き型判断と既存の構造的 `Total` から
実際の照合成功と束縛型を導く。defaultの型が各使用scopeでcoverage domainに含まれる条件を明示する。
`covered_arms_match` / `checked_arms_evaluate` により、旧coverage checkerを変更せずに
scope付きarm列のprogressへ接続する。比較するdomainと型入力は異なってよいが、実値は両方を満たす必要がある。

`CaseDataTerms.default_scoped_sound` は具体data式を各時点の環境で評価してこの契約を充足する。
`ScopedCaseDataProgram.typing_evaluates` は、独立な構文型判断と整合する任意の外側環境から
実際に結果型の値へ返ることを示す。この簡単な入口は少なくとも一つのunguarded armについて
独立な構造判断 `TotalTyping` を要求し、照合成功を前提にしない。
`PatternBindingChecks.check_exact` は名前検査と独立な `NamesValid` を一致させ、
`checked_path_nodup` は検査を通る任意のpatternの任意の構文経路に重複binderがないことを示す。
別のor枝の同名束縛と外側の名前を隠すことは許す。
`checkedEval_rejects_iff` により不正なbinderを持つarmがあればscrutineeの実行前に拒否する。

Q5・Q6は回答済みの規則として維持する。先行missなら後のdefaultを実行せず、
orは最初の照合成功で確定し、その後のguardが偽なら次のarmへ進む。
回答済みQ7の同一経路の重複名拒否は上の静的検査で実装する。
旧 `CaseDataProgram` / `CaseTree` のscope非依存defaultの定理は特殊な場合として残し、
source全体のdefault環境の割当てやeffectfulな葉の翻訳を証明済みとは扱わない。

`CasePresenceValidation` はoptional宣言metadataを許可し、requiredを拒否、unknownを未解決とする。
literal内容を旧marker値へ射影したrecordについて、lookupとrequired/optional要求の一致を示す。
`validated_binding_evaluates` は許可されたoptional metadata、型付きfallback、射影済みの適合入力から、
実際の束縛成功とpayload/fallbackのunion所属を導く。
**意味的なrequired≤optionalだけでは、必須fieldへのdefaultを拒否したことにはならない。**
sourceからmetadataを求めて全patternへ検査を適用するpassは残る。

### 網羅性の独立判断と実際のcase評価

`CaseCoverage` の `Cell` / `Total` / `Handles` / `Covered` は、checkerや評価成功を
前提にしない構造的な判断である。任意のdefault型表・arm列・入力domainについて、
`check_exact` は `check = true ↔ Covered`、閉じたmerged variant行について
`checkVariants_exact` は `checkVariants = true ↔ VariantsCovered` を示す。
`guarded_cons_ignored` によりguard付きarmは網羅性へ寄与しない。
bool、unit、tuple積、listのnil/cons、unionを分割する。これは値の有限サンプル検査ではなく、
任意の整数・文字列・任意長の有限listを含むdomainの全要素についての証明である。

`CaseCoverageSafety.check_matches` は、受理済みdomainの任意の値から、実際に合う
unguarded armを構成する。defaultの健全性は、arm構文に現れるコードだけに要求する。
`CaseDataProgram.typing_evaluates` は任意の具体的なprogram、型環境、default型表、結果型、
その独立な型付けと環境の `BindingsHold` から、評価結果が `.ok (some value)` となり
結果型を満たすことを示す。照合・guard・bodyの評価成功を追加の前提にしない。
`checked_evaluates` / `checked_variants_evaluate` では実行可能な網羅性検査で判断を充足できる。

variantの `residual_lookup` は、処理したtagを丸ごと除き、未処理tagのpayload全体をそのまま残す。
`residual_empty_iff` はこの残余の空性と独立な `VariantsCovered` を一致させる。
このcheckerは、一つのunguarded armでpayload全体を覆えることを十分条件としている。
この旧checkerの受理範囲は変更せず、回答済みQ8は次の拡張で扱う。

`JointCaseCoverage` は同一tagのpayloadを既存の構造的cellに分け、各cellを異なるunguarded armが
覆うことを認める。`checkTag_exact` / `checkRow_exact` は実行検査と独立な `TagCovered` / `RowCovered` を一致させる。
`old_check_preserved` は旧checkerの受理を保ち、bool payloadのfalse/true二armでtag全体を除ける。
`residual_lookup` は除去できないtagのpayload全体を残し、`residual_empty_iff` は空残余と `RowCovered` を同値にする。
guard付きarmとfloat literalは網羅性に数えない。`checked_program_evaluates` は旧scope非依存の
具体caseについて、独立なscrutinee/葉/armの型付けと検査成功・環境整合から成功する型付き結果を導く。
`ScopedJointCaseCoverage.typing_evaluates` はこのjoint被覆とQ4のscopeを同じ具体評価器へ接続する。
前提は独立なscrutinee/arm/data葉の型付け、各scopeのdefault型のdomain包含、名前の静的整合性、
独立な `RowCovered`、および任意の外側環境の型整合性であり、実照合成功を仮定しない。
boolとrecordのpairを持つ一つのtagをfalse/trueの別armで覆い、record内の先行束縛をdefaultが読む例を、
任意のbool・内側の整数・外側の同名整数について型付けと実結果の両方で示す。

**checkerのfalseは未認証であり、sourceの非網羅エラーとは同一視しない。**
例えば整数の `..0` と `1..` は任意の整数を覆うと証明したが、現checkerは受理しない。
recordのbool fieldをfalse/trueの二armに分ける場合、listを長さ0/1/2以上の三armに分ける場合も
現checkerの対象外である。`CaseCoverageBoundaryExamples` はこのrecord/list/整数の三例について、
checkerのfalseと任意の実値への意味上の網羅性を別々に証明する。
一般のRust pattern matrix・区間合併・再帰的な複数armの組合せは残る。
`RunCaseCoverage.lean` はguardとarmの訪問順、present/absentのdefault、nil/cons、
variant残余、二constructorを持つenumからのpayload束縛を実行する。
enumの例は解決済みの値からの分解であり、source構築子のelaborationの証明ではない。

### 有限構文木として入れ子になったcase

`CaseTree.Expr` / `Arms` は、caseをscrutinee・選ばれるbody・pair・letの内部へ再帰的に閉じる。
`CaseTree.typing_evaluates` は任意のfloat比較関数、型環境、有限式、結果型について、
独立な `Typing` と任意の適合する実行時環境から、実評価が `.ok (some value)` を返し結果型を満たすことを示す。
型判断は各caseの独立な `Covered` または `VariantsCovered` と、実際に使うdefaultの構文型付けを要求する。
scrutineeやbodyの成功は相互帰納法から導き、実行時の成功契約を外から仮定しない。
`checked_case_evaluates` / `checked_variants_evaluate` はcheckerの成功をこの判断へ接続し、
`typed_no_unmatched` は型付き式が全arm不一致で終了しないことを示す。

`CaseTreeExamples.nested_written_order` は任意の整数について、scrutinee内とbody内の両方にあるcaseが
その値を束縛・参照して返すことと、訪問列全体を証明する。
guard/default内の式はdata葉のままで、その内部のcase・関数再帰・application・effect・castは残る。
sourceの名前解決・束縛順・default環境を構文木に正しく割り当てる証明も含めない。

## Literal の中身と比較

`LiteralValues.Literal FloatValue` は任意精度の `Int`、decoded `String`、`Bool`、unit の中身を持つ。
整数の閉区間・片側区間の実行可能検査は、任意の上下端と literal に対して
独立な `InRange` 判断と同値である（`intRangeCheck_exact`）。
literal の `matchCheck_exact` は、任意の float 比較関数とその独立関係の正確性を前提に、
全 literal に対して実行比較と帰納的 `Matches` の同値を示す。
`FloatValue = Empty` の整数・文字列・bool・unit では通常の値の等号に一致する。

小数 token は符号・任意精度仮数・十進指数を保持する `DecimalToken` とし、
旧 `ofDecimal` は解釈関数を明示して渡す入口として残す。
回答済みQ2・Q3の具体値は `Binary64.Value` とし、符号1bit・指数11bit・仮数52bitを保存する。
`ofWord_toWord` と `toWord_ofWord` は任意の値と64bit wordの相互変換を示す。
有限値は最小subnormalの単位 `2^-1074` による符号付き整数として厳密に解釈し、
数値比較 `eqCheck_exact` をこの独立な意味と一致させる。
`signed_zeros_match` は正負のzeroが合うこと、`nan_never_matches_left/right` は
任意の相手についてNaNが合わないことを示す。保存値の等号とは区別する。
`LiteralValues.binary64MatchCheck_exact` はこの比較を内容つきliteralの独立判断に接続する。
`Binary64Rounding.roundFinite_correct` は、任意の符号・分子 `n`・正の分母 `d` について、
絶対値が最大有限値以下という前提から、二分探索の結果が全有限binary64候補に対して
厳密な距離 `|n - units(candidate) * d|` を最小にし、異なるrankとの同距離では
fractionの下位bitを偶数にすることを示す。符号はzeroへ丸める場合も保存する。
`n/d` は `2^-1074` 単位の絶対値であり、有限サンプルとの比較ではない。
`Binary64Decimal.magnitudeFraction_exact` は任意の小数tokenを厳密な有理数へ変換する。
`convert_success_iff` は実装の成功を「厳密な絶対値が最大有限値以下」と同値にし、
`convert_correct` は任意の成功結果について上の全候補への丸め契約を導く。
`LiteralValues.binary64OfDecimal_correct` が具体的なfloat literalへ接続する。
この部分converterは範囲外を内部の `outsideFiniteRange` として区別する。
回答済みQ11のsource規則は、最大有限値を超えても丸めが有限なら受理し、無限大へのoverflowを静的errorにする。
`Binary64Overflow.finiteRounding_iff_exists_value` は任意の符号・分子・正分母について、
拡張した指数grid上の全候補に対する最近接偶数丸めが有限値を持つことと、
絶対値が厳密に `2^1024 - 2^970` 未満であることを同値にする。
境界ちょうどは偶数rankの上側sentinelへ丸まり、最大有限値以上かつ境界未満なら最大有限値へ丸まる。
sentinelは数学的な次の2冪であり、無限大に有限の距離を割り当てるものではない。
`round_agrees_with_finite` は旧成功範囲で旧丸めと全称的に一致することを示す。
`Binary64SourceDecimal.convert` はこの境界を全decoded tokenへ接続する。
`convert_success_exact` と `convert_overflow_exact` は、任意tokenについて成功／静的overflowと
独立な全grid最近接偶数の有限結果の存在／不存在を同値にする。
成功時の符号・有限性・非NaNを保ち、`convert_agrees_with_old` は旧converterの任意の成功値をそのまま保持する。
`LiteralValues.binary64SourceOfDecimal` はこの全域入口をfloat literalへ写す。
`RunBinary64.lean` は0.1、2^53付近の両方向のmidpoint、subnormal境界、最大有限値、zero/NaNを実行する。
新しい `RunBinary64Source.lean` とkernel内の回帰定理は、両符号について最大有限値を超えた
`1.7976931348623158e308` の受理、midpoint直前の受理、midpoint一致・直後・`1e309` の拒否を確かめる。
旧runnerと期待値は変更していない。
極端な非零十進指数の資源使用量の最適化とRust f64との対応は残る。
既存 `Inference.Base` に float はなく、`legacyBase` は float に `none` を返す。
旧 base-marker 評価器を具体 literal 評価器へ黙って置き換えていない。
字句解析・escape の正しさ、数値演算、source への翻訳はこの定理群の対象外である。

## Nominal構築・保留cast・listの観測

`CaseDataTerms.Expr.nominal typeId ctorId payload` はpayload式をstrictに評価し、
結果を解決済みのtype/constructor identityで包む。独立な `Typing.nominal` と既存の
`typing_evaluates` がこの構築にも適用される。structのrecord fieldを式から計算する例、
enumのlet/var payload、listのnil/cons構築について、任意の整数の値と訪問列全体を
`NominalDataConstructionExamples` で証明した。宣言のlookup・固定fieldの宣言型・default・castのelaborationは含めない。

`NominalConstructionRuntime` は決定25の既存planに保留された不変parameterの元の構築位置を、
元の順に評価して `PureCasts.Plan` の純粋な変換を挟む。適合する位置では変換を呼ばない。
`accepted_requestTree` は任意のruntime・registry・construction・expectation・受理planについて、
実行のrequest treeが元の引数列を順に読むrequest treeと等しいことを示す。
全response分岐、payload、正負の重みを保持し、返り値そのものの等号はこの定理の結論ではない。
`execute_eof` は全parameterの期待型が未解決の場合に変換せず、元の実値を保つ完全な計算等号を示す。
constructor identity・enum tag・構築位置・引数個数も保持する。

`runValues_typed` は元の値の型付け契約と変換コードの値型保存契約を別に必要とする。
registryのground境界検査から正しい変換コードを合成する証明は未完であり、
`finish` の受理だけからtarget型の構築値が得られるとは主張しない。
`NominalDataAssembly.execute_runtime` はsite実行器の結果を具体 `CaseDataTerms` 構築ASTへ渡すことを
完全な計算等式でつなぐ。`accepted_requestTree` は受理planについて元の全siteの要求を保ち、
`execute_eof` は未解決parameterで元値を変換せずassemblyへ渡す。
`typing_evaluates` はplan受理・元siteの型契約・明示 `CastContract`・独立なassembly型判断から、
返る各分岐でmetadata保存、具体ASTの評価成功、結果型への所属を導く。
適合境界のidentity保存と、許可された非適合境界のpure codeの型保存をcontractとして要求する。
隠れるstruct fieldも要求を残し、実際のstruct/enum/list値を構築する等式を含む。
sourceからsiteとassembly codeを作るpass、固定field/defaultの宣言検査、cast code合成は残る。

`NominalListSpread` は解決済みの有限listについて、通常要素と任意位置のspreadを記述順に評価する。
通常要素の純粋変換は明示的に受け取り、spreadは既に型付けされた内容をそのまま連結する。
`data_typing_evaluates` は独立なsource型判断・環境適合性・変換の値型保存契約から、
各sourceの訪問列を一度ずつ左から右へつなぎ、全要素が指定型に属する実listを得る。
`data_typed_views` は同じ前提から、具体list値・nominal metadataを持つ構築結果・Fold順序・
全自然数位置のcursorと内部Indexが同じ要素列を観測することまで導く。
空spread・連続spread・途中のspreadでも順序と重複を保ち、source失敗後は後続を評価しない。
回答済みQ13・決定45は任意のFold値をsource spread対象とし、forと同じ辞書・effectを使う。
一般の走査と要素型union、非停止を含む実行は下記の解決済みprotocol核へ接続する。
sourceの高階Fold本体からこの核への意味保存と推論全体への統合は残る。
既存listの各要素へ新しい保留cast位置を作るか（Q14）は未回答である。
sourceのsite抽出・変換選択と保留planへの自動接続も残る。

`FoldTraversal` は任意stateの走査protocolをdone・内部step・yield・operation別のrequestで表す。
有限collectionや終了を仮定せず、各requestのsigned occurrence・payload・response別継続を保つ。
`prefix_safe` は任意の局所安全性契約・有効な開始state・有限prefixから、終端stateの不変条件、
全yield要素の型、全requestの行への所属を導く。`progress` は未回答requestも正当な停止位置として区別する。
`repeat_safe`・`repeat_prefix`・`repeat_never_done` は任意個数の安全なyieldと非終了を同時に許す。
`selected_driver_exact` はrigid role検査の成功から得た一意な辞書planが、供給された実装tableの
同じdriverを選ぶことを示す。tableのmethod実装が正しいことは別の契約である。
既存forの純粋cursorとの一歩の一致もあるが、高階でaccumulator多相なsource `Fold.fold` の
method本体からこのprotocolを作ること、そのcallback/effectの意味保存は残る。

`FoldListSpread` はsource評価の開始・内部step・requestと、選択済み辞書の走査を一つのmachineにする。
各partの独立な型判断が通常要素の型、spreadのitem型、source行、走査行を持ち、
`typing_union` が全partの要素型と行のunionを構成する。
`typed_prefix` と `typed_prefix_progress` はsourceと辞書の局所不変条件、純粋変換契約、
独立なpart列の型判断から、任意の有限prefixの型・行保存とtypedな次の観測を導く。
sourceもFoldも有限であることや全体の成功を仮定せず、返る場合の全要素型は `returned_items_typed` が導く。
`traversal_prefix` は途中の任意prefixでも後続sourceを保持し、yield列だけを元順で結果列へ追加する。
`meaning_prefix` は各sourceとFoldが有限に完了した独立な実行判断から、記述順の合成を示す。
これは終了の型定理ではない。`FoldListSpreadFinite.finite_run_correspondence` は任意の
旧 `NominalListSpread.Meaning` の導出から、旧runの結果と新machineの返却値が同じflatten列であること、
旧source traceが同順・同回数の `raw (inl event)` の要求列として観測されることを示す。
この有限実行の対応だけが成功した各sourceと有限走査を使い、一般prefix安全性の前提にはしない。
観測eventと既存errorの埋め込みは抽象signature上のもので、sourceのoperation名を追加しない。
`typed_finite_run_correspondence` は旧独立型判断・SourceSound・純粋変換契約からこの有限対応を導く。
`data_typed_finite_run_correspondence` は任意の具体 `CaseDataTerms` 型判断・環境適合性・変換契約から、
旧evalの成功と全要素型、新machineの同一返却列と同じsource traceを導く。
具体data版ではSourceSoundと実行成功を呼出側から受け取らず、既存の型安全性から充足する。
`FoldListSpreadRoles.Slot` はcontainer/itemのrigid termと、供給されたFold goal encodingに対する
`CheckedRoles.resolve` の成功を持つ。`spread_typing` は任意の型付きprotocol registry・局所SourceLayer・
slot・container型を持つsourceから、slotのitem型とsource行/選択body行のunionを持つ実際のspread型判断を導く。
`engine_uses_selected_dictionary` は同じgoalの任意の独立なDictionaryについて、driverと宣言行が一致することを示す。
registry内のbodyは開始stateと局所 `Safe` の契約を持ち、role受理だけからmethodの意味を仮定していない。
Fold goalのsource encoding、source methodからのregistry生成、実際の `for_in` との意味保存は残る。
`FoldListSpreadDivergence.no_later_source_or_return` は任意の辞書・後続構文・有効state不変条件について、
局所 `Safe` と全有効stateでdoneにならない条件を前提に、任意の有限machine prefixでも
同じ辞書と後続構文が走査中に保たれ、どのlist値も返さないことを示す。
独立に型付けされた `[3, ..repeat 7, 11]` の解決済み例では、repeat段階へ到達した後も
型安全性を保ち、後続の11を始めず返却しない。停止を型安全性の前提にはしない。

`NominalListViews.index_exact` は任意の有限list・自然数位置・要素について、内部lookupの成功と
独立な位置判断 `At` を同値にする。`cursor_index` と `fold_records_order` により、
Indexの内部lookupとFold用cursorが同じ順序の要素を観測する。`loopMachine` は既存loop評価器へ同じcursorを渡す。
回答済みQ9・Q10に対応する `NominalListIndex` は任意精度整数を受け取り、
`integerIndex_some_iff` により成功と `0 ≤ i < length` を同値にする。
負数は末尾相対にせず、`integerIndex_cursor` が非負indexと同じFold cursorの観測を保つ。
`effectIndex` は無効indexを既存の非再開error要求に変え、`wrap_effectIndex` が通常の
error wrapperで成功値または指定された範囲外errorが得られることを示す。
汎用定理は任意の `ErrorEffects.Encoding` と `Int → Error` を引数に取る。
回答済みQ12は `error index_err: out_of_range int` と無効だったindexのpayloadを確定した。
`NominalListIndexError` は任意の外部signatureと直和を取り、PayloadがInt・ResponseがEmptyの
一つの解決済みoperation、`Cases`、正しい `Encoding` を具体化する。
`invalid_index` は任意の無効indexについて、負・空list・上限超過のいずれも同じoperationへ
元のIntをそのままpayloadとして渡すことを示す。`invalid_bind` は後続を実行しない。
`wrap_index` と `catch_index` は通常返却／範囲外armへの完全な計算等式を持ち、
wrap後は空行、catch後は明示されたarmの行で全要求が上から抑えられる。
source文字列・宣言identityからこのfamilyへの対応、role辞書選択・Index本文のelaborationは残る。
`RunLiteralConstruction.lean` で大きな整数・範囲比較と実際のstruct/enum/list構築を実行できる。

## 複数 operation の shallow handler

回答済みQ1に対応する `MultiOperationPayloadHandlers` は、同一keyを複数回書ける
順序付きpayload armを追加する。実際のdispatchは最初に合うarmを選び、行から引くkeyは
guardなしの反駁不能armがあるものだけとする。`missed_retained` と `partial_key_retained` は
照合できない要求、またはその証明を持たないkeyの出現が残余に残ることを示す。
`handle_selected` は捕捉armへ元の継続を渡し、`handle_missed` は元の要求・payload・重みを
外に保ち、再開後に未完のhandlerとvalue armを続ける。`handle_ofOperations` により旧全域表は特別な場合になる。
許可maskは全armのkeyへ検査する。純粋payloadテストと純粋guardの解決済み層であり、
effectfulなpattern default/guard・source束縛のelaborationは示さない。

`Expr.partialHandler` はこのdispatchを既存の構文核へ接続する。
出力行は `residual removedKeys action.row` にvalue bodyと全operation bodyの行を加えたものとなる。
`MultiOperationHandlerTyping.infer_exact` と `typing_evaluates` は入れ子のpartial handlerも含む
同じ量化された主張を保つ。`eval_total_as_partial`、`infer_total_as_partial`、
`typing_total_as_partial` は旧全域表との実行・checker・型判断の一致を示す。
`MultiOperationPayloadInference.infer_exact` は明示incoming maskを全armに検査するwrapperと
独立な型判断を一致させ、`inferred_operationally_valid` は推論成功と整合する外部環境から
評価の全response分岐の安全性を導く。不許可keyは到達不能なpayload armでも拒否される。

`MultiOperationHandlerTyping.Expr.handler` は、相異なる解決済み operation key の有限表、
各 operation body、1つの value body を持つ。ordinary application は左から右へ strict に評価し、
再開する継続には action の元の行を保つ。`MultiOperationHandlerTyping.infer_exact` は
全ての解決済み式・型環境・出力型について、実行可能 checker の成功と独立な `Typing` 判断の同値を示す。
`typing_evaluates` は、その型判断と開いた環境の `EnvValid` から、全 response 分岐の request 上界と
返り値の型を導く。action/arm ごとの実行時上界を追加の前提にしない。
閉式の行が空なら `closed_empty_row_returns` により、対応する型の値へ返る。

`MultiOperationHandlers.checkedIncoming` は incoming action 用の別入口である。
許可 mask にない key の arm があれば拒否し、`checkedIncoming_success_iff` は
全 key の許可と実行結果の等号を成功の必要十分条件にする。
一般の非零の符号付き重みを保つ forwarding と、許可された raw 要求の dispatch を証明した。
通常の checker が source から mask を発見することはまだ示していない。

`MultiOperationIncomingInference.Handler` は明示されたincoming maskを同じtop-level handler構文に付ける。
その `infer` は許可検査の後に既存の構文checkerを呼び、独立な `Typing` との同値を `infer_exact` で示す。
任意の型環境・handler・armについて、不許可keyが一つあれば `denied_arm_rejected` が拒否を導く。
`inferred_operationally_valid` は推論成功と外部環境の型適合性だけから、実構文の評価の `Valid` を導く。
action/armのruntime上界は仮定しない。pureなactionでも不許可armがあれば拒否する実例を含む。
`inferred_opens_incoming_gate` は同じmaskとoperation表のgateが開くことまでの対応である。
構文評価と `enterTree` を施した実行の等号はまだ示しておらず、
fresh座標への構文・closure・潜在行の移送、arm側を境界の外に保つ意味保存は残る。
入れ子のhandlerへのmask割当てもこのtop-level wrapperの範囲外である。

`MultiOperationHandlerExamples.nesting_not_equivalent` は任意の境界座標数について、
operation 0 の元の継続が operation 1 を要求する具体例を分離する。
一つの handler では 0 の捕捉時に両 arm の delimiter が外れ、1 が外へ出る。
singleton handler の入れ子では外側の 1 が残り、同じ arm が 99 を返す。
従って operation ごとの入れ子化は一般に意味を保存しない。

この核の payload/response は既存の一様な `Atom` carrier である。
source の名前解決、payload patternから解決済みarm表と束縛への翻訳、operation-local 多相署名、
source から mask を求めて checker に渡す elaboration は残る。
回答済み [Q1](../notes/questions/2026-11-06-open-questions.md) の残余規則は上のpartial handlerへ反映した。
旧 `Operations` 表のkey一意性は旧核の表現条件であり、新しいpayload arm表には要求しない。

## Presenceと旧required-field推論の橋

[統合の工程案](../notes/design/2026-11-06-presence-inference-integration.md)を追加した。
`PresenceLegacyBridge.translate` は任意の有限legacy型・hidden label列・旧data値について、
旧 `DataTypeSemantics.Holds` と同じ意味を持つpresence述語を構成する（`translate_exact`）。
旧 `{}` は `records` のままであり、exact emptyやfield不在には変えない。
隠れたfieldはunion/intersectionを含むtailの中でも要求を足さず、
任意のShadow部分型導出は翻訳後の包含を保存する（`shadow_subtype_preserved`）。

`closed_typing_translates` は任意の行代数・supportedな閉data式・raw Shadow型判断について、
同じ式の返り値型をpresence判断へ移す。評価成功は仮定しないが、effect行の移送は結論していない。
`legacy_data_plan_translates` は任意の行代数・式・受理されたfinite-data planについて、
一つのpresence推論結果が存在し、そのexact型が、旧planの**任意の自由parameter代入**から得る型の翻訳に含まれることを示す。
parameterの個数は有限だが、代入する有限raw型を有限候補へ制限していない。
このplanは `RigidRecordValueInference` のもので、regularな `SourcePrincipalInference` のschemeではない。

`PresenceLayers.Layer` はrequired・optional・不在を別々に持つ有限の型層であり、
union/intersectionの全構造を残してfield間の相関を保つ。子parameterは任意のdata述語へ割り当てられる。
`Layer.check_exact` は任意の割当てとそれに正確な子membership checkerについて、
任意のlayer・実値の所属判定を独立な意味と一致させる。部分型判定や全述語の決定可能性は主張しない。
`mask_exact` / `meaning_mask` / `record_shadow` は任意のmaskとtailについて隠れた同名fieldの要求を消す。
`independent_fields_lose_correlation` はfield別のoptional化が元の二field間の選択肢を広げる反例である。

`PresenceRegularObservations.check_exact` は任意のgraph・全有限深さ・全state・全data値の観測を判定する。
`observe_morphism` / `subtype_morphism` はgraphと可換な任意のrenameについて保存・反映を示す。
renameの単射性は要求しない。`Blocks.close_observe_exact` / `close_subtype_exact` は
任意の有限同時再帰blockと内部・外部rootについて、閉じる前後の全有限観測を保つ。
`PresenceRegularLegacyBridge.observe_exact` / `layer_exact` / `data_subtype_exact` は旧regular graphの
全有限data観測と新しいpresence観測を一致させ、`legacy_block_observe_exact` が既存common carrierのblockへ接続する。
ここでの包含はdata述語間のもので、旧structural subtypingや関数・行の意味の同値ではない。

`optional_iff_absent_or_required` と `optional_never_iff_absent` は既存述語の意味から無条件に成り立つ。
旧width型からabsenceやexact emptyは導けない反例も保持する。
旧runtimeのliteralはbase markerで、関数型の翻訳はdata上ではneverである。
regular再帰型のdata投影の橋は上で与えた。内容つきliteral・closure・自由row parameter・全source主型推論への一般化は残る。

旧 `SourcePrincipalInference.infer_instances_exact` は任意の行代数と行順序の反対称性の下で、
任意の `supported e = true` の入力について成立する。`RecordFree` はsupportを構文から保証する十分条件であり、
inferの必要条件ではない。optional構文のunsupportedを型エラーへ変える変更は加えていない。

## 決定42–44：評価順とspread-first record

元の `Inference.Expr` に `recordDefault label base fallback` を追加した。
`SourceDataRuntime.eval` は `base`、`fallback` の順に両方を評価してから、
baseのfieldが存在すれば保持し、なければfallbackを末尾へ追加する。
`Fields.lookup_insertDefault_same` は結果の同名fieldを
`(lookup label fields).or (some fallback)` と特徴付け、
`lookup_insertDefault_other` は他のfieldの保持を示す。
baseの評価が失敗すればそこで止まり、baseが非recordの値まで評価された場合は
fallbackを評価した後で `expectedRecord` とする。field選択による式の省略はない。

`SourceDataOrder.Evaluates` は実行関数を参照しない独立な帰納判断である。
子式への進入、左右の成功・失敗、最後の値操作を別規則にし、失敗前の訪問も保持する。
`evaluates_iff_run` はtraced実装との双方向対応、`runtime_iff_evaluates` は元の
`SourceDataRuntime.eval` との双方向対応を示す。`Evaluates.successful_order` は
成功時に構文の全訪問列が書いた順に一致し、`run_trace_prefix` は失敗時もそのprefixだけを
訪問することを示す。`EvaluationTrace` の値を捨てるsequencingの補題は、先に生じた
観測を消さない。このdata評価器自体はeffect operationを実行する評価器ではない。
`SourceDataOrderLaws` はhidden fieldの成功と失敗、present/absentなdefault、既存fieldに
隠されないfallbackの失敗、未使用letの右辺、二回読まれても一回だけ評価されるletを扱う。
`lake env lean --trust=0 --run RunSourceDataOrder.lean` で実際の結果と訪問列を確認できる。

従来の `Inference.Model` / `Typing` / `generate` はrequired-field用の体系で、
optional-fieldやfield不在の型を持たない。この判断での `recordDefault` は未対応であり、
`Expr.requiredFieldsOnly` と `SourcePrincipalInference.infer_optional_unsupported` により
旧solverは入れ子の新構文も `unsupported` とする。これを言語の型エラーとは扱わない。
既存の `{}` は引き続き任意のrecordの上界であり、exact emptyへの読み替えはしない。
以下の旧主型定理・全core graph対応は、このrequired-field判断についての主張である。

### presenceを区別するdata推論の閉じた主定理

`PresenceDataTypes` は実際のdata値上の述語を型、包含を部分型とする。
`required` / `optional` / `lacks` を別の述語として定め、`records`（旧 `{}` の意味）と
`exactEmpty`（ちょうど空の値）を区別する。`records_not_le_lacks` /
`records_not_le_optional_int` は、幅の上界だけから不在や任意のoptional payload型を
推論できないことを反例で示す。旧Shadow部分型関係の定義を変更していない。

`PresenceDataInference.infer` は元の `Inference.Expr` に対するtotalな実行可能入口である。
変数・literal・非再帰let・pairと射影・record・default・field・variantを構文再帰で合成し、
有限の型descriptor `Shape` を返す。評価器は呼ばず、type-level lookup/insertionを使う。
`Typing` は算法も評価器も参照しないconstructor/subsumptionの独立判断である。
`infer_instances_exact` は任意の式 `e` とこのdata意味論の任意の型 `T` に対して
次の同値を証明する。

```text
Typing [] e T ↔ ∃ shape, infer e = solved shape ∧ shape.denote ≤ T
```

callerが推論成功やsolverの解を前もって渡す必要はない。`infer_success_iff` は推論成功と
型付け可能性の同値、`infer_rejected_iff` は対応するdata構文上での拒否と型付け不能の同値を
示す。関数・application・branchは `unsupported` と区別する。
この主型はfieldの不在まで記録する新しいdata意味論の精密な型であり、旧型grammar上の
全core自由parameter主型を求めたという主張ではない。literalは引き続き既存ASTのbase tagである。

`PresenceDataSafety.typing_evaluates` は任意の型適合する実環境で実際の
`SourceDataRuntime.eval` が成功し、その値が指定された型を満たすことを示す。
`inferred_evaluates` は実inferの成功だけから同じ保証を得る。
`default_operator_principal` は実AST `recordDefault l (var 0) (var 1)` について、
任意のbase型 `R`、fallback型 `B`、結果型 `T` を量化し、`R ≤ records` の下で
`Typing [R,B] ... T ↔ recordDefault(l,R,B) ≤ T` を証明する。
したがって未知baseの契約も既知の有限record例に限られない。
`optional_operator_principal` / `optional_operator_union` は `x?: A` のbaseから
必須field `x: A | B` を導く。known-presentでは元のpayload型、known-absentではfallback型を
保持し、他fieldのlookupも保存する。fallback式自体はどの場合も型付け・評価される。

`lake env lean --trust=0 --run RunPresenceDataInference.lean` はpresent/absent、computed base、
非recordの拒否、隠れるfallbackの失敗、unsupportedとrejectedの区別を実行する。

`PresenceDataCompatibility.eval_success_iff_synth` は任意のexact descriptor環境と元Exprに
ついて、別々の算法である型合成と実評価の成功を双方向に一致させ、返り値の等号も証明する。
`infer_rejected_iff_eval_error` は支持されたdata構文について拒否と実行時エラーを同値にする。
新推論器が評価器を呼ぶ定義へ変更したのではなく、独立な構造再帰同士を帰納法で接続した。
`shadow_typing_infers` / `shadow_quotient_typing_infers` / `shadow_principal_infers` は
以前のraw型付け・商型付け・principal formulaの解から、新inferの成功と旧targetの値意味論を
導く。`shadow_plan_infers` は一つの同じ新推論結果の値が**全ての旧parameter instance**を
満たすことを示す。型宇宙・部分型関係・主型の定義を同一視する定理ではない。

決定43の一般的なstrict引数評価と、歴史的な `OperationalTyping` のcomputation引数渡しは
区別する。`OperationalTypingExamples.unusedArgument_eval` は未使用の引数を実行しない
旧模型の定理であり、現在のsurface言語の評価順を証明するものではない。
`StrictApplication.compile` はresolvedな式を再帰的に走査し、関数の評価、引数の評価、
適用という順を二つのcomputed letで表現する。de Bruijn変数のshiftを含めて
`compile_correct` が独立なstrict評価器との実行木全体の等号を証明する。
lambda本体・handler両arm・返された関数・継続・符号付きweightも対象である。
`infer_forceApplication` は結果行が関数の行、引数の行、戻りの行の順で合成されることを示す。
行の包含自体は順序を観測しないため、評価順の保証はこの行上界ではなく実行木の等号による。
`closed_inferred_bound` / `closed_inferred_values` は実checkerの成功からstrictな実行の上界と
返却値の型適合を導き、`unused_argument_bound_iff` は任意の未使用引数の要求を保持する。
`StrictApplicationPrincipal.principal_operationally_valid` は実際にloweringした式の
既存principal formulaの解から同じ実行保証を導く。shape解決、注釈、surfaceの境界挿入や
この一般formulaの求解を完了したという主張ではない。

## errorのwrap・upとsignature付き要求木

`SignatureRequests.Tree` はoperationごとにpayload型とresponse型を持ち、既存の
`Directed.Occurrence` とcapture判定をそのまま使う。`toDirected_ofDirected` /
`ofDirected_toDirected` と `ofDirected_shallowHandle` は、uniform signatureの場合に
旧要求木との双方向同型と実shallow handler全体の等号を示す。

`ErrorEffects.Cases` は宣言のoperationとerror値のconstructorを対応させる。
error operationのresponseは `Empty` へ写せるため、`up_captured` は元の継続を使わずに
変換先のabortive requestを構成する。任意の結果型の値を捏造しない。
`raise_bind` はerrorの後のコードへ進まないこと、`wrap_returns` は全要求が捕捉可能な
当該errorである任意の入力木から実際にresultを返すことを示す。
`wrap_up_exact` は宣言keyの非重複とconstructorの対応だけから、任意の木について
`target.wrap (source.up action)` と直接の `wrapFrom` が一致することを示す。
外部のeffect、保護された要求、負のweightは転送される。
複数の直接の `from` は対応表の合成で扱う。nominal宣言のelaboration、推移的なfrom探索や
複数経路の選択規則はここで決めない。要求木はwell-foundedであり、一般再帰の停止定理ではない。
このhelperの入力は計算の要求木であり、ordinaryなstrict applicationへそのまま写した値引数とは
同一視しない。actionのeffectがhandlerの外で先に起きないようにするsurface展開と、その型・実行の
対応は未接続である。`StrictApplication` とこれらのhelperを個別に証明しただけで、両者を統合した
source elaborationの正しさまで得られたとは扱わない。

## junctionの短絡とmulti-shot実行

`JunctionEffects.run` はsignature付き要求木上で、`or` / `and` の継続をまず `true` で
再開し、必要な場合だけ同じ継続を `false` で再開する。`ret` はBoolを返して脱出する。
`run_is_shallow` は既存shallow handlerとの等号であり、継続を再度包む処理がlibraryの
armに明示的に存在することを示す。kernelの継続を暗黙にdeepへ変更していない。
`disjoin_short_circuit` / `conjoin_short_circuit` は短絡、`run_external` / `run_nonzero` は
外部effect・保護・負のweightの転送を実行木の等号で示す。
`closed_returns` は全要求が捕捉可能なjunctionである任意のwell-foundedな入力木について
Boolへの実終了を導く。`run_any` / `run_all` / `run_all_any` は任意の有限リストと述語に対し、
計算結果が `List.any` / `List.all` およびその入れ子と一致することを示す。
`lake env lean --trust=0 --run RunEffectExpansions.lean` はerrorの変換、短絡で飛ばす枝、
false枝へ進む順序、外部観測と保護された要求を実行する。
effectfulなsurface `if` をこのhelperへ包むelaborationとsource再帰の停止性は別の義務である。

## for・last・next・redoの有限実行

`LoopEffects` はlabelなしのloop展開を、同じsignature付き要求木上の小ステップmachineで
記述する。任意のcursorによる要素選択と外部effectのinterpreterを明示的なparameterに持つ。
独立な `Step` / `Pending` / `Prefix` と実際の `step` / `run` の一致を
`step_progress_iff` / `step_blocked_iff` / `prefix_iff_run` が証明する。
fuelは観測する有限step数であり、型付けの前提や言語の停止仮定ではない。

`run_last` はUnitで終了し、`run_next` は残りcursorへ進み、`run_redo` は同じ要素のbodyを
先頭から再設定する。いずれも操作の古い継続は再開しない。
`external_then_redo` は外部effect後の**現在のstateとevent**を保持したまま再開することを
示す。`run_add_exhausted` は予算を追加して現在のconfigurationから続きを実行した結果が、
初めから合計予算で実行した結果と一致し、過去のtraceをappendで保持することを示す。

`normal_finite_traversal` は明示された有限 `Traverses` とpureな各bodyの下で、長さから
計算した予算 `2 * length + 2` によりUnitへ終了することを証明する。
`redo_forever` は逆に、有限bodyでもすべてのfuelで予算切れとなる例を証明する。
一般のfor/redoの停止性を主張しない。保護されたloop要求や応答のない外部要求は元の
configurationを保って中断する。外部interpreterへsigned occurrenceを渡すが、その
interpreter自身のmask適合、effectfulな `Fold`、label値のsource束縛・method・衛生性と
入れ子loopを含むsource elaborationはこのmodelの外に残る。
`lake env lean --trust=0 --run RunLoopEffects.lean` はstateを更新してredo→next→lastと進む
実例、途中からの再開、abort後の未実行、保護された要求、有限走査と無限redoを確認する。
評価順・presence推論・error/junction・loopの4 runnerもCIへ追加した。

## 決定40：隠れたfieldの型等価

`ShadowSemanticRecords` は決定39の全規則を保持し、任意のtail `R` について
`record(l,A,record(l,B,R)) ≃ record(l,A,R)` の両方向を追加した最小関係である。
`Subtype.minimal` がこの規則範囲を特徴付ける。一般のtail共変性や分配則は加えていない。
`ShadowRecordQuotient.shadow` は、任意の商型のhead・hidden payload・tailについて、
この等式が実際の型の等号になることを示す。`int` と `str` は引き続き異なる。

`ShadowRecordInference` は以前の型付けを保存する。`ShadowRecordQuotientInference`
の `formula_exact`・`closed_typing_exact`・`compiled_typing_exact` は、任意の元core式・
結果型と行について、新しいraw関係、商、実際の全core graph出力を接続する。
`ShadowRecordExamples.source_has_equal_instances` は、10.28.3で分離されていた
同じsource式の二つのopaqueな結果を保持した上で、その商型が等しいと証明する。
unionと`never`で隠れた重複も `shadow_under_union_bottom` が扱う。

旧 `Rigid*` 関係とその否定定理は、決定39時点の比較用として変更せず保持する。
以下で記すopaque結果の別型性はこの旧関係についての事実であり、決定40後の言語の
区別ではない。新関係の有限ground checker・cut elimination・商の等号判定も下記の通り完成した。
未知変数を持つ一般graphの求解と全coreの自由parameter主型推論は未完である。

`ShadowRecordNormalization.normalize_exact` は、計算された正規化結果どうしの旧rigid関係と、
元の型どうしの新関係を双方向に一致させる。`normalize_equivalent` は各正規化結果が元の型と
新関係で等価なことを別に示す。tail全体が同名headを持つrecord atomと旧関係で等価な場合だけ
headを除き、残りtailのconstructor depthが真に減る。unionの枝ごとの消去や分配則を加えていない。

`ShadowRecordChecker.check_true_iff`・`check_false_iff` は任意の有限型に対する実判定の
完全性を示す。前提は正確なBoolean行checker・行preorder・`DecidableEq Row` である。
`cut_elimination` は新関係のcutを計算済みnormal formsの既存cut-free判断へ接続する。
`ShadowRecordQuotientDecisions.equal_true_iff`・`decideEq` は実際の商型等号を判定する。
外部fuel・新関係の意味的oracle・未知の中間型は渡さない。表示用のcanonical文字列や
正則再帰値型のcheckerを構成したという主張ではない。

```sh
lake env lean --trust=0 --run RunShadowRecordCheck.lean
```

## 全coreのrecord要求と正則モデルへの接続

`ShadowRecordDemands.record_mask_exact` は、任意の供給head `A`・tail `R` とrigid要求 `P` について、
`record(l,A,R) ≤ P` を、要求に `l:B` があれば `A ≤ B`、および `R ≤ erase(l,P)` と同値にする。
新しいshadow規則を含む導出全体から必要性を証明し、十分性も実際の規則から導く。
行の法則、供給tailの形、決定可能性は前提にしない。

`SingletonRecordDemands.good_generate` と `SingletonRecordGraph` は、元の全core式で、
生成される要求の明示的なrecord spineが空かsingletonになることを示す。
lambda・application・両let分岐を含み、rename・scheme置換・normalise・pack・prepare・
実際の `compileSource` まで保存する。閉式では環境の不変条件を空環境から証明する。
未知slotに代入できる型をsingletonへ制限するものではない。
任意の外部schemeでは強めた `GoodEnv` が必要で、旧前提だけでは足りないことも反例で証明する。

`maskReference` と `compileSource_erasure_closed` は、残りの要求が元のnodeか既存のempty-tail
nodeへの参照になることを示す。`compileSource_upper_record_tail` はprovenanceだけでなく
actual graph tagがemptyになることまで導く。追加の型変数やmask nodeを確保する必要はない。

`RecordDemandInspection.inspect` はそのnode tagを直接読み、同名fieldならhead比較とtailの
empty要求、別名なら元tailへの同じ要求を返す。未対応pairは拒否せず元の辺を保持する。
`expand_exact`・`expandCompiled_instances_exact` は、同じvalue/row割当てと共有slotを保ったまま
制約集合と全instanceを双方向に一致させる。`SourceRecordDemandInspection.prepareSource` は
実際の全source alternativeへこの一回の分解を適用する。

`ShadowRegularValueTypes` は既存 `Layer`・graph・観測関数を保持し、各有限観測の比較に
決定40の関係を使う。任意の既存Layer tailでshadow等価・合同性・rigid要求への共変性が成立し、
`finite_conservative` は有限treeの比較を保存・反映する。共通carrierの
`ShadowRegularInferenceModel.embed_subtype` も `iff` であり、finite blockの埋込みも正確である。
`SourceRecordDemandInspection.shadow_source_typing_exact` と
`shadow_regular_source_typing_exact` は、分解後の全graph instanceと、それぞれのモデルでの
元Typingを一致させる。両方にgraphの `Models` 条件が残る。

**全core solverへの残る義務は、分解を含む飽和と、open-tail graphから自由parameterの
正則解を構成するcoalescingである。** 既存 `Layer.record` のtailは有限Layerであり、
graph-state参照ではない。一般のtail参照をそのまま既存blockへ写す証明はなく、
全parameterでの充足と任意の元解へのretractionを新しい関係で証明する必要がある。
これはtail-cycleが解を持たないという主張ではない。旧solverの新関係についての完全性や
`RecordFree` の除去は、この接続だけからは導かない。

## 最新record関係でのデータ推論

`ShadowRecordValueInference` と `ShadowRecordValueQuotient` は、既存の
`RigidRecordValueInference.infer`・`Plan`・自由parameter tupleをそのまま使い、
決定40のraw関係と商モデルで全instance主型性・拒否完全性を再証明する。
`infer_complete` は型付け可能な任意の `Data` 式で実際の推論が成功することを、
`infer_instances_exact` は推論したschemeの全instanceと独立な元Typingの一致を示す。
以前の型付けの保存だけでなく、新しい等式で増えた型付けも完全性の対象とする。
`inferred_boundary_instances_equal` は以前のopaqueな両instanceを同じ商型として保持する。
対象はliteral・emptyRecord・pair・variant・record構築と、不正なdata tailである。
一般lambda/application・let・effect式はこの推論入口の対象外である。

`ShadowRecordFunctionScheme`・`ShadowRecordFunctionQuotient` は、以前の
`lam (record l (lit b) (var 0))` の同じdescriptorについて、決定40後の全instance主型性を
再証明する。自由な3個の値型と1個の行を保ち、opaqueな入力tailも含める。
これは当該関数族の推論schemaであり、一般関数の新しいdispatcherではない。

## 元の型付け・推論結果から実際の評価へ

`SourceDataRuntime.eval` は元の `Inference.Expr` と実行環境だけを受け取る。
shapeで添字付けされた式、型付け導出、推論plan、fuelを渡さない。recordは実際の有限field列で、
同名の古いfieldを保存データから消す。headとtailはその消去前に両方評価する。

`SourceDataSafety.typing_evaluates` は、変数・literal・pair/射影・record/field・variant・
非再帰letを含む元の宣言的Typingから、実際の評価成功と返り値の型適合を導く。
単相letと値制限付き多相letの両方を扱う。多相letの右辺は一度だけ評価され、
その同一の保存値が全instanceの意味を満たす。型ごとの再評価には置き換えない。

`ShadowDataSafety.quotient_typing_evaluates` はこれを決定40の商モデルへ接続する。
部分型の値意味保存は `subtype_preserves` で新規則の全ケースまで証明してあり、
実行安全性を外部の仮定にはしない。`principal_evaluates` は元のprincipal formulaの解から
同じ保証を導く。値意味は部分型についてsoundであり、意味的集合包含から部分型へ戻る
完全性は主張しない。

**`ShadowDataSafety.inferred_evaluates` は実際のデータ推論の成功だけから、単一の実行結果を
構成し、全自由商parameterによる型がその同じ値を記述すると証明する。**
`instance_evaluates` は最後のsubsumptionを含む全instanceを扱い、`inferred_no_error` は
評価器の全エラー結果を排除する。

| 入口 | 証明の対象構文 | 結論 |
| --- | --- | --- |
| 実際の `infer` の成功 | literal・emptyRecord・pair・variant・record構築 | 評価成功、全parameter/instanceで同じ返り値が型に適合 |
| 元 `Typing` / principal formulaの解 | 上記に変数・let・field・fst/sndを加えた第一階断片 | 評価成功、宣言された値型に適合 |

literal payloadは既存core ASTと同じbase tagへ抽象化している。lambda/application・branch・
effect・再帰sourceの実行、Rust runtimeとparserからのelaborationは対象外である。
未対応構文を評価器に渡すと明示的に `unsupported` を返す。全言語の実行停止や
preservation/progressまで証明したとは扱わない。

```sh
lake env lean --trust=0 --run RunSourceDataSafety.lean
```

## 決定41：incoming actionのhandler許可

`HandlerPermissions.check` は注釈の許可maskとarmのkey一覧を受け取り、許可されない
armがあれば拒否する。`diagnostics` は該当keyを元の順序・重複を保って返す。
`diagnostic_iff_unreachable` は診断対象であることと、そのkeyの**すべてのincoming
occurrence**が当該handlerに捕まらないことを同値にする。

境界座標は入口内でfreshに構成する。既存の正の保護も負の解除差分も保持され、
古い`−1`と新しい`+1`を同じ座標で相殺することはない。`discard_denied_arms` と
`denied_arm_bodies_irrelevant` は任意のincoming request tree全体について、不許可armの
削除・本体変更が実行結果に影響しないと示す。許可keyかつ既存重み0のrequestは
`permitted_request_dispatches` により実際のoperation armへ進み、shallow継続は元の行動を保つ。

`checkedHandleIncoming` は検査後に既存のshallow handlerを実行する入口で、成功と
非空の診断一覧による拒否が静的条件と一致する。対象はその注釈付きincoming actionであり、
arm内で局所的に発生するeffectに同じmaskを押し付けない。sourceからの注釈抽出や
mixed-origin action全体の許可推論は未接続である。

```sh
lake env lean --trust=0 --run RunHandlerPermissions.lean
```

## 実際に型を求める入口

**全coreの求解は未完。以下の一般solverは決定39以前の参照モデルを使う。データ式については上節の定理が同じ算法を決定40のモデルへ接続する。** 下記の `SourcePrincipalInference.infer` は旧reference modelのままで、`RecordFree` による無条件のsupport保証もその構文範囲のままである。新しい `RigidSemanticRecords` は決定38の合同関係に、要求tailがrigidな場合だけの共変性を加える。任意admissible tailのhead/幅、hidden fieldを比較しないrigid要求の必要十分条件、完全ground checkerとcut elimination、その商と全core graph compilerの接続を閉じた。さらに新商モデルで、閉じたデータ式の自由parameter scheme・全instance主型性・拒否完全性と、引数recordを拡張する関数族の全instance主型性を証明した。opaqueな要求型での同一視の境界と、一般の残余graph制約の求解は区別して下に明記する。

**`SourcePrincipalInference.infer` は、元の閉じた `Inference.Expr` から主型スキームを計算する。** 元のprincipal formulaの生成、存在変数とletの選択肢の正規化、共有graphへの変換、値型と行の求解、正則再帰型スキームの構成を実行する。型graph、途中の型、行の割当て、制約の解、成功cache、fuelを呼出側から渡さない。

record構築を含まない既存の核について、推論が対応範囲外にならないことも証明した。lambda・application・値制限付き多相let・分岐・pair・fst/snd・field access・variant・空record・literal・変数を含む。`recordFree_instances_exact` は、計算結果の自由な型・行parameterによる**全instance**と、元の独立な `Inference.Typing` の全結果を一致させる。`recordFree_rejected_iff` は拒否と型付け不存在の同値で、成功やモデル存在を前提にしない。`recordFree_principal_formula_exact` は元のprincipal formulaそのものへ接続する。

```sh
lake env lean --trust=0 --run RunSourceInference.lean
```

実行例は元の式から、恒等関数、`any` を入力に持つ定数関数のinstance、自己適用、関数適用、多相letと単相引数の違い、構造型、拒否と未対応の区別を確認する。`SourceInferenceExamples` は計算されたschemeの全instanceが、それぞれ `A ! R -> A ! R`、`any ! R -> int ! ∅` の族と一致することを別途証明する。ここで `! R` は説明用のcomputation行の記法であり、surface構文ではない。定数関数でも未使用引数の行 `R` は自由なまま残る。

`SignedSourceInference` は同じ定理を既存の `RecursiveRows.SetRow` に具体化する。自由な行には保護済みの出現、負の差分、無限supportを含められ、行の深さや重みを打ち切らない。行のempty・join・包含は既存モデルと同じで、`rowView` のdecodeは恒等写像である。これはcore式の推論を符号付き行モデルで解釈する定理であり、operation・handler・protect/releaseを持つ全effect式を、この入口で求解したという主張ではない。

戻り値は `unsupported`・`rejected`・`inferred alternatives` を区別する。成功した全let alternativeを保持し、型矛盾と証明されたalternativeだけを除く。一つでも未対応のalternativeがあれば、全体を未対応とする。record構築の境界と全言語へ残る接続は [10.25–10.27](../spec/10-inference-core.md#1025-record-tailの意味論上の境界) にまとめる。sourceは核のASTであり、parserからのelaborationや表示文字列の正しさを含まない。

## 決定38の基礎と保存した証明

`SemanticRecords.Subtype` は、旧構造・束の規則とrecordのhead/tailの相互部分型による置き換えからなる**最小の合同閉包**である。`Subtype.minimal` がこの意味を特徴付ける。これは旧関係をそのまま商にしたものではない。まず合同性を加え、`SemanticRecordQuotient.QTy` がその相互部分型を同一の値型にする。任意のlabelとfield型について、`record(l,A,{})` と `record(l,A,{} | never)` はこの商で実際に等しい。`int` と `str` は等しくならない。

`SemanticRecordInference.old_typing_preserved` は、旧有限モデルの**任意の環境・式・結果計算型**について型付けを保存する。捕捉した多相束縛と明示署名も環境写像で保持する。`SemanticRecordQuotientInference.formula_exact` と `closed_typing_exact` は、行関係の反射性の下で、合同閉包のrawモデルと商モデルの間の元の任意Formulaおよび全閉core式の型付けを双方向に一致させる。`literal_typing_iff` は以前の反例のliteralの全instanceを通常の有限record型と空行の上位型として特徴付ける。`Typing.record` に構文条件は追加していない。

**ground checker:** `SemanticRecordChecker.check` は任意の有限型2個を受け取り、入力のconstructor depthから必要な層数を内部で計算する。row関係の反射性・推移性、`DecidableEq Row`、渡したrow checkerの正確性の下で、`check_true_iff` と `check_false_iff` が最小合同関係の成立・不成立と一致する。`cut_elimination` の構造atomの前提は前層の実際のBoolean比較であり、意味的なatom比較oracleや外部fuelは不要。既存 `StructuralDecisions` の有限束checkerとcut-free判断に接続する。row checkerそのものは引数である。

`SemanticRecordQuotientDecisions` は同じ前提の下でcheckerの代表元不変性を証明し、商型上に実行可能な部分型判定と等号判定を降ろす。`equal_true_iff` の結論は実際の商型等号である。canonicalな表示や代表元の選択は要求しない。

```sh
lake env lean --trust=0 --run RunSemanticRecordCheck.lean
```

**全coreのcompiler:** `RecordConstraintSupport` は元の生成器の全constructorとletの両経路を扱い、左辺のunionを分割して元の型・row割当てを保存する。`OpenRecordConstraintGraph.compileSource` は元の `Expr` から `principal → normalise → prepare → compile` を実行する全域関数である。record nodeはheadとtailの参照を両方持ち、未知tailをproper spineへ置き換えない。未使用inputも含めて元slotを保つ。`compile_assignment_exact`・`compile_retraction`・`compile_instances_exact` は任意の `Inference.Model` でgraphと元制約の全解を一致させる。

`SemanticRecordQuotientInference.compiled_typing_exact` は、任意のrow join algebra、任意の元core式 `e` と商モデル上の結果 `C` について、**実際に `compileSource e` が返したgraph族のinstanceであることと `Typing [] e C` が同値**だと示す。ここに `RecordFree` はない。しかしgraphの `Models` 条件は残っており、自由parameterだけで全解を表す主型schemeの定理ではない。

**決定38時点の境界:** 最小合同閉包は必要な基礎であって、任意のadmissible tailを持つrecordがheadを使え、fieldを忘れて `{}` に幅包含できるという既存の義務をすべて満たすモデルではない。例えばこの関係では `record(l,A,never) ≤ {}` が導けない。この否定は中間関係の境界であり、意図する言語の型エラーではない。当時の確認点だったtail共変性には、決定39でrigid要求に限定する回答が入った。`SemanticRecordVarianceBoundary` は、明示したフィールド存在の局所法則だけから一般共変性が導けない有限代数を示す。payload・実行・inhabited性を含むYulang全仕様からの独立性は主張しない。

決定39はこの確認点に対し、要求tailがrigidな場合だけの共変性を指定した。その証明は次節の新関係で行い、この最小合同閉包の定理・負例は歴史的な参照として保持する。正則再帰型/coalescing、新graphの実際の制約求解、`SourcePrincipalInference` の全instance主型性と拒否完全性への接続は残る。effect式、再帰SCCと全注釈多相再帰、注釈の一般化直前の確定、role・cast・EOFは各層の既存定理のままで、この入口には未統合。表示の標準形・`as`の最終表示・一般の禁止点付きgraph到達も今回の変更に含めない。

## 決定39：rigidな要求への共変性と先勝ち

`RigidSemanticRecords` は旧関係を保存し、`IsRecord S` と `R ≤ S` から `record(l,A,R) ≤ record(l,A,S)` を導く規則だけを追加する。一般の要求tailへの共変性、分配則、bottom strictnessは追加していない。`record_head` と `record_width` は、任意の `R ≤ {}` についてheadの利用と `{}` への幅部分型を導く。特に `record(l,A,never) ≤ {}` が成立する。旧モデルの否定定理や期待値を変更せず、新関係について別の定理を証明している。

`RigidRecordDemands.record_mask_exact` は、任意のrawな供給head `A`・tail `R` とrigidな要求 `P` について、次の必要十分条件を示す。行関係の法則は前提にしない。

```text
record(l,A,R) ≤ P
  ↔ (Pにlがあれば、その最初のfield型Bに対してA≤B)
    ∧ R ≤ erase(l,P)
```

`erase(l,P)` は要求側の同名fieldをすべて除く。`checkDemand` はこの分解を実行し、任意の正確なBoolean row checkerと行preorder、および `DecidableEq Row` の下で、rigidな要求型に対する成功・失敗が宣言的関係と一致する。`checkDemand_hidden_payload` は隠れたpayloadを変更してもBoolean結果が変わらないことを示す。この省略は当該record層についてで、visible payload内の比較は再帰的な型比較に委ねる。

`RigidRecordChecker.check` は非rigidな要求も含む有限ground型の**参照関係**全体を同じrow前提で完全に判定する。`cut_elimination` は計算されたatom比較を持つcut-free判断へ接続する。`RigidRecordQuotientDecisions` は代表元不変性から、商の順序・実際の等号の実行可能な判定を構成する。商上の `Rigid` はproper代表元の存在であり、単なる構文判定ではない。

```sh
lake env lean --trust=0 --run RunRigidRecordCheck.lean
```

`RigidRecordInference` と `RigidRecordQuotientInference` は、旧有限モデルの任意環境の型付け、前回の合同関係とその商の全閉式instance、元Formulaのraw/商同値を保存する。`compiled_typing_exact` は任意のrow join algebra・元core式・結果について、実際の全core graph出力のinstanceと新商モデルの `Typing` を一致させる。これは依然として残余graph制約を持つcompiler定理である。

**opaque要求の境界:** `RigidRecordOpaqueBoundary.hidden_field_rigid_comparison` は、任意のtail `R` と全rigid要求 `P` について、`record(l,A,record(l,B,R))` と `record(l,A,R)` が同じ比較結果を持つことを示す。一方、`R = never`、および `R = {y:int} | {z:str}` の具体例では、両型はadmissibleでも互いに部分型ではない。後者のunionも、proper spineと同値な代表元を持たないことまで証明した。この限定規則だけでは、rigid要求で省略できるhidden fieldを任意の型同士の同一視まで省略できない。これらは関係の境界であって、sourceの拒否や一般solverの不可能性ではない。

`RigidRecordSourceBoundary.source_has_incomparable_instances` は、この二つの型が同じ元core式の型付けに現れることを示す。式は外側から `x:int`、`x:str`、`y:int` の3つのrecord構築であり、`y` のrecordを上のunionへ広げる経路と、内側の `x` のrecord全体を同じunionへ広げる経路を使う。任意のrow join algebraで両結果が元の `Typing` とprincipal formulaのinstanceになり、全rigid要求への比較は一致する。下の実際のschemeも両instanceを保持する。opaque型を同一視する新法則は追加していない。

この別型性は、今回明示した規則のみの最小関係の性質である。4.3のfirst-field-winsと決定38を、nonrigidな推論tailに隠れたfieldの型等価へ適用する範囲は確認事項として残る。「同じ式のinstanceである」ことだけから二型の等価は導けず、また、この最小関係の非比較を仕様全体からの独立性や確定した言語の区別とも扱わない。

前回の `SemanticRecordVarianceBoundary` の有限field存在代数は、今回のrigid要求への共変性を満たす。`RigidRecordVarianceBoundary.local_laws_with_rigid_without_general_covariance` がそれを示し、旧反例の右辺unionはnonrigidなので決定39の反例にならない。payload・実行を持つ言語全体のモデルであるとは主張しない。

## recordを含むデータ式の自由parameter推論

**`RigidRecordValueInference.infer` は元の `Inference.Expr` から有限のschemeを実際に構成する。** `Data` はliteral・emptyRecord・pair・variant・record構築を再帰的に含む構文で、不正なrecord tailも入力範囲に含む。返り値は `unsupported`・`rejected`・`inferred plan` を区別する。`infer_unsupported_iff` は `unsupported` がちょうど `Data` の外であることを示す。型付けの導出・constraint graph・成功cache・意味的な包含checkerは入力にしない。

各recordで自由な値型parameterを2個残す。子のschemeの値型を `H,T` とすると、構築する型は次である。

```text
record(l, H | α, (T | β) & {})
```

tailのplanがrecord形なら `T ≤ {}` がすべての子parameterについて成り立つため、任意の `α,β` が有効なinstanceを作る。逆に元の型付けが構築に使ったhead `A` とtail `R` をparameterに選ぶと、`H ≤ A`、`T ≤ R ≤ {}` から `H | A ≃ A` と `(T | R) & {} ≃ R` が成り立つ。record合同性で元の構築型を回収するので、opaqueな要求tailへの一般共変性を仮定しない。これらの型付け由来の選択は完全性の証明内で行い、推論の呼出側には渡さない。

任意のrow join algebra、任意の `Data e`、任意の結果計算型 `C` について、`RigidRecordValueInference.infer_instances_exact` は、計算されたplanの**自由parameterによる具体化とsubsumptionだけ**が元の `Typing [] e C` と一致することを示す。`infer_principal_formula_exact` は元のprincipal formulaへ接続し、`infer_rejected_iff` は実際の拒否と型付け不存在を同値にする。`Good`・graphの解・parameterに対する残余制約は定理の外部前提にしない。

`RigidRecordValueQuotient` は同じplanを決定39の商モデルで評価する。自由parameterは商型全体を動き、`infer_instances_exact`・`infer_principal_formula_exact`・`infer_rejected_iff` が同じ量化範囲で成立する。`infer_plan_sound` は実際に返されたplanの任意parameter tupleが元の式の型付けを与えることを示す。`inferred_boundary_has_both_instances` は上のopaqueな二つの結果を実際の計算結果が両方保持し、`boundary_quotient_types_distinct` はその二型がこの商でも異なることを示す。

```sh
lake env lean --trust=0 --run RunRigidRecordInference.lean
```

この定理の値型carrierは**有限raw型とその商**である。literal、任意深さのrecord・pair・variantの入れ子、およびscalar/pair/variantをtailに置く不正入力を含む一方、変数・一般lambda/application・let・field access・effect式・正則再帰値型はこの入口の対象外である。既存の `SourcePrincipalInference` と統合した定理ではなく、その `RecordFree` 制限は外していない。

## 引数recordを拡張する関数族

`RigidRecordFunctionScheme.scheme l b` は、元の核式 `lam (record l (lit b) (var 0))` に対する有限の `CompTerm (Fin 4)` を計算する。任意の値型 `α,β,γ` と任意の行 `ρ` に対して、次の型を構成する（`!` は説明用のcomputation行記法）。

```text
I = α & {}
H = b | β
T = (I | γ) & {}
(I ! ρ) -> (record(l,H,T) ! ρ)     外側の行はempty
```

`instantiate_eq_eval` はこの構成と実際のdescriptor評価の一致を示す。任意のrow join algebra・label・base・結果 `C` について、`instances_exact` と `principal_formula_exact` はこのschemeの全instanceを元の式の全型付け・principal formulaと一致させる。3個の値型と1個の行はすべて自由であり、入力からtailへ必要な包含は型の式自身に組み込む。入力行を出力行でも共有し、元の型付けがさらに広い出力行を持つ場合は通常のsubsumptionで保持する。反変入力を独立な `any` に消して、この共有を落とす変更は行わない。

`RigidRecordFunctionQuotient.instances_exact` と `principal_formula_exact` は同じ全instanceの一致を商モデルへ移し、`instantiate_sound` は任意の商parameter tupleに対して元の関数の型付けを与える。これはこの関数族についての完全な主型schemeであり、任意の関数を解析する新しいsource dispatcherや、正則再帰型を含む全core solverではない。

## 個別のsolverと従来の入口

`ValueInference.solve` は既存の核の式を受け取り、変数・リテラル・分岐・let・pair・variantの型を構成する。途中の型や生成制約の解を引数として渡さない。分岐では `ValueBounds.solve` が結果の未知型を解く。評価時のeffectは空で、入力環境の既知値型には符号付きの潜在effectを含められる。

次の実行例は、実際のsolverを呼び、想定と違う結果なら失敗する。

```sh
lake env lean --trust=0 --run RunValueInference.lean
```

混在した分岐の `int | str`、その結果を使うletとpair、不正な条件と未束縛変数の拒否、循環bound、負の潜在effect、無限row、恒等関数の型・行の相関を確かめる。入力はparser後の `Inference.Expr` であり、surface source文字列を処理するcompiler frontendではない。一般のlambda/applicationは `unsupported` として返す。これは `unsat` と異なり、型付けの不在を意味しない。

`closed_principal_solved_exact` は、求めた型 `T` の上位型全体が、元の `Inference.principal` の許すすべての結果と一致することを示す。`closed_principal_unsat_iff` は対応する構文について、solverの拒否と、元のprincipal formulaの解の不在を同値にする。単なる「解を与えれば正しい」という入口から、この断片では解の構成と失敗判定まで進んでいる。

関数については別に、`ValueBoundEliminationExamples.identity_principal_exact` が実際の `principal [] (lam (var 0))` をsolverで構成した型族へ接続する。引数の型 `A` と行 `R` を自由なparameterに残し、内部結果だけを解くと、意味的に `A [R] -> A [R]` になる。一般化する変数をsourceから発見する算法や、任意の関数の推論まで閉じたとは主張しない。詳しい算法・量化子・対象外の範囲は [`spec/10-inference-core.md` 10.18](../spec/10-inference-core.md#1018-未知の値型の求解) にまとめる。

決定36・37に対応し、`any` を核のtop型へ追加した。`ValueUpperBounds.solveGreatest` は上界の交差から最大解を構成し、負の位置の未知型の消去を全インスタンスについて証明する。`ValueBoundSchemes.solve` はさらに、正負が混在する出力でも共有parameterを保つ、制約のない型スキームを構成する。`solve_models_exact` と `principal_exact` は、計算されたスキームの全具体化が元のflat boundの全解を正確に表すことを示す。式と量化子は [10.19](../spec/10-inference-core.md#1019-any上界の双対全解の型スキーム) にまとめる。

入れ子の未知型と循環には **`RegularSchemeInference.infer`** を使う。有限の型node graph・制約・出力nodeからregular principal schemeを構成し、`infer_principal_exact` が実際の呼出し結果の全instanceと元の独立な制約モデルの全instanceを一致させる。`infer_none_iff` は正則再帰型を含むモデル不存在と失敗の同値である。rowはこの入口では固定され、source ASTからの全変換や行の同時求解は別の層にある。

```sh
lake env lean --trust=0 --run RunRegularInference.lean
```

この実行例は恒等関数適用・自己適用のgraphからschemeを作り、再帰する自由parameterを代入する。反変入力とnested pairの矛盾の拒否、共有parameterを守る簡約も実行する。有限深さの実行チェックと、全深さについて証明されたmodel/主型定理を区別する。Simple-subとの対応と参照revisionは [`REFERENCES.md`](REFERENCES.md)、算法の主張は [10.20–10.22](../spec/10-inference-core.md#1020-共有parameterの意味を保つ簡約) に記す。

元の型項からは **`TypeConstraintInference.infer`** が、`TyTerm (Fin n)` の不等式列を共有node graphへ変換し、同じsolverからregular schemeを構成する。`infer_correct` は実際の呼出しについて、未対応・解なし・推論成功の三分岐を証明する。対応範囲では `infer_models_exact` が元の全割当てと自由parameterによる全具体化を一致させ、`infer_instances_exact` が任意の出力slotの全instanceを一致させる。行の割当ては、この入口では固定される。型のconstructorと再帰blockは `RegularInferenceModel` の一つの型carrierに収まる。

行には `RowFlowSchemes` と `NestedRowRequirements.solveRows` を追加した。後者はshapeの飽和で必要になる全arrow行比較を回収し、明示された行制約と合わせて共有parameterの行schemeを求める。関数入力の行比較は反変方向のままである。値型・行の未知数の番号を保つsource clauseの分割は `ConstraintProblems.closed_source_problems_exact` で元の型判断に接続する。値型との統合は `JointConstraintInference`、元の式への接続は上の `SourcePrincipalInference` が担う。

旧モデルのrecord境界は反例として保持する。`RecordTailBoundary` は、空recordと相互部分型であるtailに置き換えても、旧reference algebraではrecord全体が同値にならないことを示す。決定38後の新しい合同関係では、この具体的な障害は解消する。旧否定定理の主張や旧solverの期待値を書き換えず、移行先の保存定理を別に証明している。証明範囲は [10.25–10.27](../spec/10-inference-core.md#1025-record-tailの意味論上の境界) に記す。

## 証明対象

| モジュール | 閉じる主張 | それだけでは示さないこと |
| --- | --- | --- |
| `Yulang.CaseValues` / `CasePatterns` / `CasePatternSafety` / `CaseEvaluation` / `CaseDataTerms` | 具体値の分解、独立な束縛型判断から照合安全性、whole merged payloadの型付け、orの名前集合、上から順のarm/guard/body評価、具体data葉から健全性契約の導出 | 全Rust pattern matrix、sourceの名前解決・型注釈検査・束縛順の整列、関数/effect/再帰との統合 |
| `Yulang.ScopedCasePatterns` / `ScopedCasePatternSafety` / `ScopedCaseEvaluation` / `ScopedCaseTotal` / `ScopedCaseDataProgram` / `PatternBindingChecks` | 先行束縛を読むdefaultと同じ順の型環境、型判断から照合安全性、独立TotalTypingから具体caseのprogress、同一経路の重複binderの静的拒否、Q4–Q7の実値・訪問列 | sourceの環境/presence導出、effectfulな葉、CaseTree・統一ASTへの接続 |
| `Yulang.CaseCoverage` / `CaseCoverageSafety` / `CaseDataProgram` / `CaseCoverageExamples` / `CaseCoverageBoundaryExamples` | 保守的な網羅性checkerと独立判断の同値、guard除外、merged tag残余の正確性、具体programの型付けから実評価・全arm不一致の不在、順序/default/enum payloadの実値例 | false側のsource拒否完全性、record内の複数arm合成、list長さの深い分岐、整数区間合併、source全体のRust pattern matrix、source nominal構築子elaboration |
| `Yulang.JointCaseCoverage` / `ScopedCaseCoverageSafety` / `ScopedJointCaseCoverage` / `ScopedJointCaseExamples` | 複数の反駁可能armによる同一tagのpayload cell被覆、独立判断との同値、旧受理の保存、全tag単位の残余、各scopeの型付けとdefault domain包含から具体caseのprogress、Q4とQ8が同時に働く量化例 | 一般pattern matrix、record/list/整数の既存未認証例、sourceの拒否完全性、effectfulな葉・CaseTree・統一ASTへの接続 |
| `Yulang.CaseTree` / `CaseTreeExamples` | scrutinee/body・pair・letへの有限case入れ子、独立型付けから実評価の型安全性と未一致の不在、任意整数について値と訪問列を保持する入れ子例 | guard/default内部のcase、一般再帰・関数/application/effect/castの統合、source名解決とscope付きdefaultの統合 |
| `Yulang.CasePresenceValidation` | 宣言presenceのoptional許可/required拒否/unknown未解決、具体recordの旧markerへのlookup保存、required/optional所属の対応、型付きlazy defaultからunionに入る実束縛 | sourceからpresence metadataを導出し全patternへ適用するpass、旧markerにないfloat/list/nominalの射影、source defaultのscopeを割り当てるpass |
| `Yulang.LiteralValues` / `LiteralValueExamples` / `Binary64` / `Binary64Rounding` / `Binary64Decimal` | 内容つきliteral、整数範囲、64bit codecの相互逆、数値Eqと独立判断の同値、正負zeroの一致・NaNの不一致、任意tokenの厳密な分数化と有限範囲の全候補最近接偶数丸め | 数値演算、parser/escape、Rust f64との対応、非零巨大指数の資源最適化、既存base-marker ASTとの全体統合 |
| `Yulang.Binary64Overflow` / `Binary64SourceDecimal` / `Binary64SourceExamples` | 全正分母有理数の有限丸めと厳密なoverflow境界の同値、全decoded tokenの成功/静的overflowと独立な有限丸め結果の存在/不存在の同値、旧成功値の保持、両符号のnear-max/midpoint回帰 | lexer・source span/診断・無限大定数の名前との接続、Rust f64との対応、巨大非零指数の資源最適化 |
| `Yulang.PresenceLegacyBridge` | 任意の有限legacy型とmaskのdata意味を保存するpresence翻訳、Shadow部分型の包含保存、閉supported型判断の移送、finite-data planの全parameterを同じexact結果が一方向に包含、optionalの分解と旧width型の反例 | 逆向きの部分型完全性・scheme等価、regular型と自由row parameter、closure/effect行の意味、SourcePrincipalInference全体への統合 |
| `Yulang.PresenceLayers` | required/optional/lacksを保つ有限layer、任意の子述語と正確なmembership checkerから全値で判定同値、mask合成とhidden field消去、field別optional化で相関が失われる反例 | 任意述語の決定可能性、全深さの部分型判定、closure/effect行の意味、拡張solverの主型性 |
| `Yulang.PresenceRegularObservations` / `PresenceRegularLegacyBridge` | 任意graphの全有限観測判定、可換なrenameと有限block closureでの保存・反映、旧regular型のdata所属・data包含との同値、既存common carrierのblockへの接続 | 旧structural subtypingとの同値、arrow/closureと行の意味、全深さの判定算法、presence制約の飽和/coalescing、全source schemeのinstance同値 |
| `Yulang.NominalConstructionRuntime` / `NominalConstructionExamples` | 不変parameterの元の構築位置の順序、適合時のcast抑制、純粋cast後の全request tree保存、EOFの実値保持、metadataとarity保存 | ground境界検査から値型に正しい変換codeの合成、固定struct field・宣言defaultを含むsource elaboration、sourceからのsite/構築AST生成 |
| `Yulang.NominalDataAssembly` / `NominalDataAssemblyExamples` | site実行器から具体ASTへの完全等式、元のrequest treeとEOF値の保持、受理plan・局所CastContract・元site型・独立Code型判断から返却分岐の構築成功と結果型、struct/enum/listの実値例 | sourceのsite抽出・Code生成、固定field/defaultの宣言検査、cast code合成、Fold/Indexのsource辞書との対応 |
| `Yulang.NominalListSpread` / `NominalListSpreadExamples` | 任意位置の有限list spread、独立data型判断と環境・変換契約から実評価と全要素型、記述順に各sourceを一度読む全訪問列、同じ列に対する具体list・nominal metadata・Fold・内部Indexの一致 | 回答済みQ13のsource Fold本体からの意味保存、spread要素の保留cast境界（Q14）、source site抽出・変換選択・保留planの自動生成 |
| `Yulang.FoldTraversal` | 任意stateの走査protocol、局所契約から全有限prefixのitem型・signed request行・有効state保存、終了を仮定しないprogress、無限yield例、rigid roleの一意辞書planと供給driverの一致、純粋cursorと既存forの一歩の対応 | source高階Fold.fold本体からのprotocol生成・意味保存、供給method tableの検証、sourceの型/effect一般化 |
| `Yulang.FoldListSpread` / `FoldListSpreadFinite` | source評価と辞書走査の順序付け、各partのitem型とsource/走査行のunion、局所契約と独立型判断から全有限prefixの安全性/progress、返る場合の要素型、任意の途中走査で後続source保持、独立data型判断・環境・変換契約から旧/新の同一返却列・同順同回数のsource trace | 高階source Foldからの意味保存・method table検証、source推論/辞書elaboration、観測signatureからsource effectへの翻訳、Q14のcast境界 |
| `Yulang.FoldListSpreadRoles` | acceptedなrigid container/item slotから実spread型判断へ、型付きregistryの選択bodyによるitem型・source/走査行union、任意の同goal Dictionaryとのdriver/行の一致 | source Fold goal/associated typeのencoding、source methodから型付きregistryへの生成・意味保存、既存evidenceの再利用、source for_inと全推論器への接続 |
| `Yulang.FoldListSpreadDivergence` | 局所Safe・有効stateでdoneにならない条件から全有限prefixで後続source保持・行保存・非返却、型付き非空literal内の無限repeatと安全性の共存 | 任意のsource Fold本体の非停止判定、source method/protocol対応、停止性を含む全sourceの主張 |
| `Yulang.NominalListViews` / `NominalListIndex` | 同じlistに対するcursor・index・foldの一致、整数indexの成功と有効区間の同値、無効indexの非再開error要求、既存wrapとの一致 | sourceのFold/Index辞書の選択・署名と本文の対応、source名/宣言identityから解決済みerror familyへのelaboration |
| `Yulang.NominalListIndexError` | Q12の解決済みInt/Empty宣言・Cases・Encoding、任意Intの成功区間、全無効原因で同一operation/原index payload、abortiveなbind、wrap/catchとの完全等式と残余行上界 | source名と宣言identityの解決、source Index辞書・本文へのelaboration、統一推論器への行の組込み |
| `Yulang.NominalDataConstructionExamples` | 解決済みnominal構築式、任意整数から計算するstruct/enum/list payloadの型付けと実評価・全訪問列 | 宣言のlookup・型引数・payload宣言型の検査、source constructor default・castの挿入 |
| `Yulang.MultiOperationHandlers` / `MultiOperationHandlerTyping` / `MultiOperationHandlerInference` / `MultiOperationHandlerExamples` | 有限の複数operation表と1つのvalue arm、shallow/multi-shot、重みを保つdispatch、incoming maskの静的拒否、独立型判断とcheckerの同値、型付けから全request/returnの安全性、入れ子化で意味が変わる反例 | 一様Atom以外のoperation署名、operation-local多相、source patternから束縛付きarm表への翻訳、sourceからmaskを求めるelaboration、全言語の主型推論・再帰の安全性 |
| `Yulang.MultiOperationPayloadHandlers` / `MultiOperationPayloadInference` / `MultiOperationPayloadExamples` | 同一keyの順序付きpayload dispatch、missのforwardと残余保持、unguarded反駁不能armだけのkey減算、既存構文のchecker/型判断/安全性の拡張、旧全域表との一致、全armへの明示mask検査 | source patternの束縛、effectful default/guard、個別operation署名と多相、mask導出とfresh移送、全sourceの主型推論 |
| `Yulang.MultiOperationIncomingInference` | 明示incoming maskを実構文checkerに合成、独立型付けとの同値、不許可armの静的拒否、推論成功と環境適合性から既存構文評価のValid、同一maskのruntime gate対応 | source maskの導出と入れ子handlerへの割当て、fresh座標へのclosure/潜在行の移送、構文評価とenterTree後の実行の意味保存 |
| `Yulang.Types` / `Yulang.Inference` | 構造再帰する有限制約生成、独立な宣言的型付けとの双方向の一致、制約schemeの主性、非再帰の値制限付き多相let | 全制約の判定、再帰SCC、sourceのoperation/handlerのelaboration、公開型の正規化 |
| `Yulang.StructuralBase` / `Yulang.Structural` | 行の解釈を共有する具体的な構造部分型モデル、`never`/`any`・union/intersection・幅部分型・関数の分散、生成制約の正例と反例 | 完全なMLsub意味論、再帰型。決定手続きは `StructuralDecisions` で扱う |
| `Yulang.Polymorphism` | effect付きcomputation変数の単相let束縛を受理し、そのeffectを空行へ消す生成制約を拒否すること | 再帰的な一般化、sourceのalias解析 |
| `Yulang.Effects` | 出現ごとの保護・解除、任意の行置換での非capture、well-founded computation treeでの非capture、shallow handlerのeffect上界 | sourceからのelaboration、operation署名の型安全性、全言語のpreservation/progress |
| `Yulang.EffectInference` | core生成器を使うrequest・boundary・shallow handler規則の健全性と完全性、有限個のoperation-local型変数の呼出側での存在具体化・handler側での全称検査、結果と外側環境へのescapeの構造的排除、単相規則と明示された実行時上界の合成 | sourceからのelaboration、atomのpayload内部にある局所変数、局所変数のrole制約、型付けから実行時上界を導く証明 |
| `Yulang.RowInference` | 同じrequest・boundary・handler制約生成を非負行と符号付き行に具体化する共通の双方向定理、operation-local型変数の存在具体化・rigidな全称検査、行置換と評価の両立 | sourceからのelaboration、atomのpayload内部にある局所変数、局所変数のrole制約、型に沿った潜在行の変換、量化を含む制約のsolver |
| `Yulang.SignedStructural` | 実際の符号付き行を持つ構造部分型モデル、operationのeffectと負の解除差分を保持する生成制約の正例・負例、局所型の任意の具体化と独立した二回の呼出し、rigidなpayloadを継続に渡す正例と固定int結果へ返す負例 | 完全なMLsub意味論・solver、sourceの由来条件の保存 |
| `Yulang.HigherOrder` | 有限の型shapeに沿ったproduct/list等の格納callbackの保護と非capture。単純なerase解除の限界を示す反例 | 任意の高階の境界の意味保存。`guard ∘ release` はこのモデルでは恒等でない |
| `Yulang.Directed` | 符号付きの境界差分、両方向の相殺、非負保護listの埋込み、明示した由来条件の下での非capture | sourceから動的な境界を構成し、由来条件を保存すること |
| `Yulang.FreshBoundaries` | 任意の単射による境界座標の拡張、既存の符号付き重み・capture・残余・handler実行の保存、新しい座標の割当てによる原点条件の構成と任意の元のrequest treeの非capture | sourceの全呼出しがこの割当てを使うこと、返り値・payload・response内部の潜在callbackの変換 |
| `Yulang.FreshRowInference` | 全有限RowExprについての境界名の写像と評価の可換性、任意の未知tailを含む評価結果のfresh原点条件、T3のsnapshot・保存履歴・formulaのgateの不変性 | source境界の発見、型slotのfreshening、潜在callbackの変換、型付けからruntime上界を導くこと |
| `Yulang.DirectedHigherOrder` | 任意の有限shapeと値における両方向の高階transportの相殺、由来条件付き非capture、混在した由来のcallbackの例 | 再帰型、atom・operation payload内部のtransport、sourceのelaborationとpreservation/progress |
| `Yulang.DirectedBounds` | 符号付き行でのshallow handlerのeffect上界、保護・解除による上界の双方向のtransport | sourceの型付けからaction・armの上界を導くこと、値内部の潜在行 |
| `Yulang.DirectedHandlerInference` | 成立した共通のhandler生成制約とaction・armの実行時上界から、実際の符号付きhandler全体の上界を導くこと | action・armの前提そのものをsourceの型付けから導くこと |
| `Yulang.Annotations` / `Yulang.AnnotationSnapshots` | 注釈時点の可視effect検査と正確性、符号付きの観測履歴の固定、T3 の具体化時に再検査しない規則と主制約生成器の接続、未知行の後の具体化と当初から既知で可視な禁止effectの区別 | 何がその時点で既知かを決める solver、source 注釈から観測時点を構成する elaboration |
| `Yulang.AnnotationFinalization` | binding/SCC全体の有限Horn制約を解いてから符号付き観測を固定する入口、最小解の真のfactと全モデルで強制されるfactの一致、制約順序・重複・member順序に依存しない受理、一般化前の検査と後の具体化の分離 | 構造型推論から有限fact interfaceへの翻訳、無限のsigned stackを含む全体solver、sourceのSCC発見と名前の振り直し |
| `Yulang.RecursiveInference` / `Yulang.RecursiveExamples` | 有限の同時再帰制約生成と独立な SCC 型判断の一致、全注釈の値型変数だけを具体化する多相再帰、明示的なeffect行の共有、SCC 後の値の一般化と computed slot の保持、depth型再帰の全注釈受理と `any -> int` での単相受理 | source の SCC 発見と全注釈認識、local/captured slot 分類の推論、解の探索、評価依存の検査 |
| `Yulang.QualifiedInference` / `Yulang.QualifiedGeneralization` | resolved method からの role 制約生成と独立な型判断の一致・主性、raw role 制約の自動分配、抽象辞書での定義検査と利用時の証拠要求、環境slotの共有、通常のletでの値型・行の独立した一般化 | 未解決の構造制約から一般化interfaceを発見するsolver、source の method lookup、任意に入れ子になった source qualified let の elaboration |
| `Yulang.ModuleRoles` / `Yulang.QualifiedExamples` | 与えられた部分割当てとinterfaceに対するEOF検査、実際のresolverによる残留role制約の確認、公開型に使う未確定slotの拒否、公開schemeの意味と解の拡張に対する独立性、辞書の有無・型の後決め・非空の潜在行の正例と負例 | module全体から未解決制約を漏れなく収集するsource pass、部分型の解を探索すること、opaqueな意味的型の内部表現に関する閉性 |
| `Yulang.ModuleVisibility` / `Yulang.ModuleDictionaries` | 自file・import・accessの可視判定を実際のEOF検査と辞書木の構成へ接続、非可視宣言の変更・宣言順序・重複による不変性、公開schemeの意味保存、全nodeの可視な由来、file間で渡された辞書木の保持 | source module/import/access解析、未定型の推論、source宣言identityの割当て |
| `Yulang.EOFNoDefaulting` | EOFの未定slotをimpl検索より先に拒否、既存`finishModule`・file可視な`finish`との成功の同値、可視implに依らない未定型の拒否、型確定後の失敗goal、公開型の閉性・同じexportの保持、impl増加で同じexportまたは具体的な曖昧さになること | sourceからの全残留制約の収集、一般化slotの分類、通常の型推論、source診断の位置・文言 |
| `Yulang.EOFRoleInference`（旧仕様の参考実装） | ground headからcompletion候補を列挙する独立した実験の正確性。追加公理の監査には含める | 決定33により現行Yulang3の推論入口ではない。`Yulang`からはexportしない。未定型を唯一implから補完する規則は採用しない |
| `Yulang.RoleEvidence` / `Yulang.RoleEvidenceExamples` | role要求を持つ既存のPolySignatureについて、呼出側の存在具体化と証拠要求、handler側のrigidな全称検査と署名辞書、qualified生成器を使った双方向の一致、実際の符号付きモデルでの辞書使用と証拠欠如の負例 | sourceのoperation/handler構文全体のelaboration、atomのpayload内部の局所変数、型付けから実行時の上界・安全性を導くこと |
| `Yulang.Roles` | 第一階 impl 集合の一方向照合、Paterson 型条件による置換後の型サイズの真の減少と深さ制限なしの解決の停止、健全性、到達する head に重なりがない場合の完全性、到達可能な head の重なりと曖昧さの同値、正例・負例 | generic role の method dispatch、章6.4の receiver 下界による解決保留、effect との相互作用、operation-local role 制約、推論の制約言語との統合 |
| `Yulang.RoleVisibility` / `Yulang.RoleDictionaries` | 可視impl増加で成功は成功または曖昧、曖昧性保存、順序・重複不変、実際のresolverから全where子を持つ辞書木を構成、成功とのiff、成功継続時の木全体保存、受け渡した辞書の保持と既存WithEvidenceへの接続 | source method bodyの実行、未知型の代入探索、重複するgiven binderのsource選択規則 |
| `Yulang.RolesAssoc` | 第一階の関連型の明示定義と default、解決成功時の宣言済み各名前の全域性・一意性、where の導出や照合置換によらない値、goal の変数だけを含む結果、明示定義の置換後のサイズ公式、正例・負例 | 関連型を含む method 署名、`value ~ int` 等の等式制約や where 条件との単一化、receiver 下界による解決保留、source 宣言検査。他 role の関連型を右辺で参照することは2026-11-05の決定により対象外 |
| `Yulang.RoleConstraints` | 具体的なresolverの成功と導出・非曖昧性の一致、関連型選択から普通の等式の追加への接続、全置換について等式制約追加の可換性・冪等性・順列不変性、既存制約との矛盾を上書きしないこと | 未知の置換を探索する単一化器、構造部分型とrole制約を合わせた全体solver。`Store.check` は与えられた置換での検査 |
| `Yulang.CheckedRoles` | 有限の宣言検査と全変数についての Paterson 適格性の同値、証明を入力に要求しないresolver入口、不適格な宣言の拒否、適格な集合での成功・曖昧さの正確性 | source parser/name resolution、関連型宣言の全検査、診断位置・文言、疎な変数番号での計算量最適化 |
| `Yulang.ImplHeads` | impl headの各holeを別の変数へ下ろす処理、全匿名識別子の一回性と名前付き変数の共有、whereから匿名変数への参照不能性、ref全体の照合と部分特化 | source parser・型/行のkind検査、未束縛名の診断、methodの可視性や段階ごとの検索 |
| `Yulang.Horn` | 任意の有限Horn制約に対する解の存在判定と最小モデル。成功・失敗の両方向の完全性 | 構造部分型、再帰型、無限の保護stack、roleの解決 |
| `Yulang.RecursiveRows` | 保護・解除・残余を含む正の再帰的行制約 `E ≤ slot` の最小集合解、全解で強制される出現との一致、固定上界との両立の必要十分条件、既存の有限行解釈の保存、有限行では解けない保護反復の例 | 解への所属の決定手続き、任意の右辺を持つ行包含、構造型solver、sourceからの制約抽出、すべての再帰行の有限表示 |
| `Yulang.InfiniteRowHygiene` | 任意の無限集合行での両方向相殺・包含保存・残余、境界再indexと全行式・再帰最小解の可換性、fresh原点と非capture、同じkeyを含む無限tailの保持、無限行によるrequest tree上界 | 一般の所属決定、無限行のsource型付けからruntime上界を導くこと、潜在closure変換 |
| `Yulang.RecursiveRowGraph` | 有限行制約から有限guard付きgraphへの実行可能なコンパイル、任意の無限行割当てでのモデル保存、独立な到達可能性と既存最小解の一致、有限の到達key・slot支持 | 無限configuration空間の到達判定、半線形な解表示、包含・等価判定 |
| `Yulang.RowTransportNormalForm` | 固定keyに対する有限programの平行移動＋有限禁止入力点への正確な正規化、各途中residualの保存 | guard付きpath全体の半線形性、単なる総変位によるpath判定 |
| `Yulang.FinitePointGuards` | 逆方向に、任意の有限禁止点付き整数平行移動を既存protect/release/residualで表現し、有限graph全体を既存の行問題へ埋め込むこと、独立なgraph到達可能性と最小解の一致 | 一般の到達可能性・半線形性・決定不能性の結論、巨大整数のbit長に対する効率 |
| `Yulang.AffineRows` | 任意の有限境界数・整数周期ベクトルを持つ一つのrayの有限候補による所属判定、二つのrayの包含・等価判定と両方向の正確性 | 任意の相互再帰制約の求解、複数rayのunion同士の包含判定 |
| `Yulang.SymbolicRows` | affine segment・union・差集合からなる有限表現の所属判定、既存の全行式操作についての閉包性と評価保存。shiftは基点を動かし、residualは有限raw点を除去 | 未知の最小解への人為的な上限、全再帰問題の解がこの形を持つこと、任意の有限式同士の包含 |
| `Yulang.SegmentDecisions` | 任意の二つの有限または無限segmentについて包含・等価性を決定し成功・失敗を意味と一致させること。有限sourceは真の上端まで列挙 | 複数segmentのunionの包含、全再帰問題の求解、有限上端に依存しない計算量 |
| `Yulang.CyclicRows` / `Yulang.CyclicRowDecisions` | 一つの初期programと一つの反復programからなる既存の二規則問題について、途中guardを保った最小解の有限表示、所属・包含・等価性の実行可能な判定、実際のDerivesと最小モデルへの接続 | 分岐・複数cycleの相互作用を含む一般graph、一般の半線形最小解の構成、sourceの再帰SCCからこの形式への翻訳 |
| `Yulang.RecursiveRowDisplay` | 推論表示の単一 `as` binderの最小解意味論、展開・折り畳み、一つのslotを持つ任意の有限問題から意味を保つ本体構成、確定した `as` binderと現行の一境界・一tail表示における所属・包含・等価判定の接続 | 一般binder本体のsolver、表示文字列のparser/roundtrip、複数境界の整形と未確定の相互再帰変数の表記 |
| `Yulang.SemilinearWeights` / `Yulang.WeightedPaths` | 任意次元の符号付き整数重みについて、半線形集合の有限union・和・starの構成と意味保存、有限graphのstate elimination、独立な全有限pathとの双方向一致、到達重みの有限半線形表示 | 有限禁止点を含むgraph、半線形集合の一般所属・包含・等価性の決定、性能・最小表示 |
| `Yulang.SemilinearRows` / `Yulang.SemilinearRowExamples` | 固定keyで全normalized guardが空の任意有限row graphについて、元のDerivesと計算した有限半線形表示の一致、実行可能なguard検査、複数seedを混ぜないこと、相互再帰・複数cycle・正負2座標の無制限な例 | 禁止点が残る一般graph、一般の半線形所属・包含・等価判定、source SCCからの制約抽出 |
| `Yulang.GuardedAffineRows` / `Yulang.CertifiedRowSummaries` | 指定座標とslot potentialの有限検査から全中間点のguard通過を導出、非空禁止点を含む複数cycleの半線形表示、固定keyの正規化と元の任意row AST problemの到達・Derivesの同値、検査成功から元の最小解への直接接続、全Slot列挙不要 | certificateの探索、検査を通らない一般guard問題の求解、一般の半線形所属・包含・等価判定、sourceからの制約抽出 |
| `Yulang.FiniteBooleanReachability` / `Yulang.BinaryCarries` / `Yulang.SemilinearDecisions` | 任意次元・任意符号の有限周期集合について、無制限の自然数係数を二進carryの有限到達問題へ変換し、半線形集合への所属・非所属を完全に判定。零周期・相殺・空集合・0次元も含む | 任意のguard付きgraphの半線形表示の構成、実用的な大入力性能 |
| `Yulang.FiniteAutomata` / `Yulang.SemilinearDigits` / `Yulang.SemilinearAutomata` | 全有限語についてのNFA包含・等価性、全整数vectorの符号付き二進表示、全表現での受理との一致、任意の半線形集合の包含・等価性・非包含時の整数反例の存在 | 全guard付きgraphの到達集合が半線形であること、最短反例の抽出、productionの計算量 |
| `Yulang.FiniteWorklist` / `Yulang.FiniteWorklistExamples` | 実際の到達状態だけを列挙する探索と全有限pathとの同値、有限全状態数による完全性と停止、NFAの全冪集合積を実行時に作らない包含判定、無限集合の共同被覆の実行確認 | 最悪時の指数的状態数の回避、言語に対する探索打切りや任意のfuel制限 |
| `Yulang.GuardedRowErasure` / `Yulang.AutomaticRowSummaries` | 正規化された元のrow ASTについて、各slot edgeの禁止点への到達不能性を自動検査し、成功時の半線形表示・所属・非所属を元のDerivesへ接続。外部potential・座標・Slotの有限列挙不要、既存の座標certificateが通る場合を包含 | guardが実際に到達する一般問題の求解。`none`はこの算法の未対応で、言語の拒否や非所属ではない |
| `Yulang.StructuralCut` / `Yulang.StructuralDecisions` | 既存の有限構造部分型preorder全体のcut除去、union/intersection・pair・variant・record幅/先勝ち・関数の型と二つの行の分散を含む完全な比較器、符号付き有限行に対する真偽・同値判定 | 未知型変数のbound探索、再帰値型、Simple-sub全体のextrusion/intrusion/generalization、sourceの推論器 |
| `Yulang.ValueBounds` / `Yulang.ValueBoundSolvers` | ground下界・変数間包含・ground上界から未知の値型を実際に構成するsolver、循環を含む有限graphの停止、全構造型割当てに対する最小性と成功・失敗の完全性、無限半線形latent rowを持つ入力と任意のSetRow割当てに対する完全性 | constructor内部に残る未知型の求解、再帰値型、最小解を多相主型と同一視すること、全Simple-subの一般化とsource全体への接続 |
| `Yulang.RecursiveValueBounds` | 元の再帰row制約から潜在行を解き、未知の値型を構成する入口、元のDerives解に対する健全性・最小性・解なしの完全性、未対応と矛盾の区別 | 一般のguard付きrow問題、任意のrow解と値型の同時探索。rowは元の再帰問題の固定最小解で解釈する |
| `Yulang.ValueBoundElimination` / `Yulang.ValueBoundEliminationExamples` | 既存TyTermの極性検査、正の内部未知型の存在量化の正確な消去、自由なparameterと行の保持、実際のprincipal恒等関数とsolverが構成した型族の同値、負の位置の無条件最小化への反例 | 一般化するparameterの自動発見、constructor内部の未知型を含むboundの解消、任意のlambda/applicationを推論するsource算法 |
| `Yulang.ValueUpperBounds` / `Yulang.ValueUpperBoundsExamples` | 上界の逆伝播と交差、空交差 `any`、全割当てに対する最大性・成功と失敗の完全性、負の位置の全インスタンスを保つ消去 | 正負が混在する変数の独立した既定化、nested bound、再帰値型 |
| `Yulang.ValueBoundSchemes` | flat boundの全解を表す制約のない有限型スキームの構成、任意の自由parameterが解になることと全解を再現できること、任意の混在極性の出力についての全インスタンス保存 | constructor内に未知変数を持つbound、再帰値型、sourceからの一般化interface発見 |
| `Yulang.ValueBoundSchemeInference` | 既存TyTermとfixed rowsから混在極性のprincipal output schemeを計算、元の全bound modelとのinstance exactness、rowsの保持 | 未知record spine、sourceからのgraph抽出 |
| `Yulang.TypeSimplification` | 正のみをnever・負のみをanyへ置く変数除去、認証された共起mergeとsandwich、自動有限passの全instance保存 | 全ての安全なmergeの発見、constructor分配則、唯一の表示標準形 |
| `Yulang.FiniteHorn` / `Yulang.NestedValueSolver` | 型constructor内の未知変数を扱う有限飽和、n²対での停止、独立モデル保存、rigid/row矛盾の拒否 | 単独では成功cacheからの再帰解構成。この接続は次のcoalescingで証明する |
| `Yulang.RegularValueTypes` | 全有限観察による独立な再帰値型意味論、有限型での保守性、guardedな循環導出の健全性、入力/出力の再帰例 | 最終的なas文字列、循環導出体系全体の決定手続き |
| `Yulang.RegularNestedModels` / `Yulang.RegularValueCoalescing` / `Yulang.RegularSchemeInference` | 任意自由parameterから元のnested graphの解を構成、元の全regular modelを再現、subsumptionを含む全instanceの主型性、実際の推論入口と解不存在の完全性 | 未知rowの同時求解、source全体のlowering、一般化・intrusion/T3との全統合、完全な表示標準形 |
| `Yulang.ConstraintNormalForm` | 任意の元Formulaを有限の存在的clauseへ変換、全Exprの元Typingとの同値、letの両枝・capture・結果slotとrowsの保持 | 個々のatomの求解、DNFの大入力性能、source全clauseがnested solverの対応範囲に入ること |
| `Yulang.RegularInferenceModel` | constructorと有限再帰blockに閉じた単一のInference.Model、有限graphの保存・反映、全自由parameterからの解構成と全instance一致 | surfaceのas表示、意味論を追加したrecord正規化 |
| `Yulang.TypeConstraintGraph` / `Yulang.TypeConstraintGraphEquivalence` / `Yulang.TypeConstraintInference` | 元TyTermの共有変数を保つgraph化、semantic realizerの反映、実際のsource型制約solverの全モデル・全出力instance一致、regular model不存在と拒否の同値 | 未知record tail、非対応位置のunion/intersection、未解決行と値型の統合入口 |
| `Yulang.RowFlowSchemes` / `Yulang.NestedRowRequirements` / `Yulang.TypeConstraintRowInstantiation` | core行の共有parameter scheme、shape飽和と行代入の可換性、全arrow行obligationの求解、元の行モデルの回復 | operation head・protect/release・residualを含む一般RowExprの制約消去 |
| `Yulang.ConstraintProblems` | 型・行の同一slotを保つclause分割、元Typingのsubsumption、全閉式から計算した問題のinstanceとの同値 | 各問題の求解や全構文の対応判定 |
| `Yulang.RecordTailBoundary` | 旧reference modelについて、同値tailの置換がrecordの同値を保たない反例、元principalの全instanceをproper spine一つで表せないこと | 決定38後の新モデルの反例、一般solverの不可能性 |
| `Yulang.SemanticRecords` | 旧構造・束規則と任意record head/tailの合同性からなる最小閉包、全旧部分型の保存、10.25のrecord型の同値、基本型が潰れないこと | 任意admissible tailのhead/幅の全義務、一般tail共変則、分配・bottom strictness、再帰型solver |
| `Yulang.SemanticRecordQuotient` / `Yulang.SemanticRecordQuotientInference` | 新しい合同関係による値型の商と全constructorのwell-definedness、任意Formulaと全閉core Typingのraw/商間の双方向保存、record literalの全instance、全coreの実際のgraph compilerとの同値 | 最終的な任意tail規則、商の表示標準形、graph残余制約の求解と自由parameter scheme |
| `Yulang.SemanticRecordAtoms` / `Yulang.SemanticRecordViews` / `Yulang.SemanticRecordAtomNormal` / `Yulang.SemanticRecordLatticeCheck` / `Yulang.SemanticRecordChecker` | 最小合同関係の有限ground型について、構造atomの有限化・proper record view・既存StructuralDecisionsへの接続・入力depthから計算する完全checker・計算されたatom比較を持つcut elimination | 追加tail規則のchecker、未知変数と正則再帰型の求解、row checker自体の構成 |
| `Yulang.SemanticRecordQuotientDecisions` | 上のrow checker/preorder前提の下での代表元不変性、商型の実行可能な部分型判定と意味的等号判定、Decidable/DecidableEqの構成 | 表示標準形やcanonical代表元、最終record関係の未知型solver |
| `Yulang.InferenceModelMap` / `Yulang.SemanticRecordInference` | model写像による任意Formulaの保存、反映・全射の明示前提下での双方向一致、任意の旧環境の型付け保存、literalの全instanceの有限record型による特徴付け | 旧関係と合同閉包の逆向き保存、全coreの実際の求解、表示標準形 |
| `Yulang.RecordConstraintSupport` / `Yulang.OpenRecordConstraintGraph` | 元の全coreからのpolar制約準備、未知tail参照を持つ全域compiler、任意modelでの全割当て・全instance・retractionの一致、union-join/preorder前提下の全core Typingとの同値 | 制約を満たす割当ての探索、充足可能性判定、自由parameterによる主型scheme、SourcePrincipalInferenceのRecordFree除去 |
| `Yulang.SemanticRecordVarianceBoundary` | head/幅・同値置換・既知field存在・冪等性・交換を含む明示した局所法則を満たすが一般tail共変性を満たさない有限のfield存在代数 | payload型・値の実行・inhabited性を含む言語全体のモデル、全仕様からの独立性、sourceの型付け不能 |
| `Yulang.RigidSemanticRecords` | 決定39のrigid要求tailへの共変性だけを加えた最小関係、旧関係の保存、任意admissible tailでのhead/幅、never tailの幅 | 一般tail共変性、分配、bottom strictness、opaqueな型同士でのhidden fieldの同一視 |
| `Yulang.RigidRecordFields` / `Yulang.RigidRecordDemands` | proper recordの最初のfieldによる比較、要求側maskによる任意供給tailの必要十分条件、hidden fieldを比較しないことの完全性 | 非rigid要求へのmask規則、未解決型変数の求解 |
| `Yulang.RigidRecordAtoms` / `Yulang.RigidRecordViews` / `Yulang.RigidRecordAtomNormal` / `Yulang.RigidRecordLatticeCheck` / `Yulang.RigidRecordDemandCheck` / `Yulang.RigidRecordChecker` | 新参照関係の有限ground checker・計算済みatom比較によるcut elimination、rigid要求の別入口とhidden payloadに依存しないBoolean結果 | 任意opaque要求でhidden比較を省く言語規則、未知変数・正則再帰型のsolver、row checkerの構成 |
| `Yulang.RigidRecordQuotient` / `Yulang.RigidRecordQuotientDecisions` | 新関係の商、意味的にrigidな要求tailへの共変性、代表元によらない実行可能な順序・等号判定 | 表示標準形、opaque hidden fieldを消す新しい同一視 |
| `Yulang.RigidRecordInference` / `Yulang.RigidRecordQuotientInference` | 旧型付け・前回商の閉式instance保存、raw/商のFormula・全閉式Typingの同値、新商モデルでの全core graph compilerとの同値 | graph残余制約の求解、全core自由parameter schemeと拒否完全性 |
| `Yulang.RigidRecordOpaqueBoundary` | 全rigid要求でのhidden fieldの除去、never/unionのopaque tailにおけるadmissibilityと非比較、隠れたpayloadに関する比較の正確な特徴付け | 全言語仕様からの独立性、source拒否、一般solver不可能性 |
| `Yulang.RigidRecordSourceBoundary` | 同じ元の閉record式に対するopaqueな2型の型付けとprincipal instance、両型の非比較と全rigid要求での一致 | opaqueな型を同一視する法則、主型schemeやsolverの不可能性 |
| `Yulang.RigidRecordValueInference` / `Yulang.RigidRecordValueInferenceExamples` / `Yulang.RigidRecordValueQuotient` | 全Data構文から自由parameter schemeを実際に構成、有限raw型と商型での全instance主型性・拒否完全性・元principalとの同値、opaqueな代替instanceの保持 | 一般lambda/application・let・field access、正則再帰値型、一般の制約graphの求解、SourcePrincipalInferenceとの統合 |
| `Yulang.RigidRecordFunctionScheme` / `Yulang.RigidRecordFunctionQuotient` | 引数recordにliteral fieldを足す関数族の有限descriptor構成、3自由値型と1自由行での全instance主型性、元principalと商モデルへの接続 | 任意の関数を推論するsource入口、正則再帰値型、全coreのRecordFree制限除去 |
| `Yulang.ShadowSemanticRecords` / `Yulang.ShadowRecordQuotient` / `Yulang.ShadowRecordQuotientInference` | 決定40の任意tailでの隣接同名field消去の最小閉包、商の型等号、旧型付け保存、全core graphと元Typingの全instance一致 | 一般graphの求解、自由parameterによる全core推論 |
| `Yulang.ShadowRecordNormalization` / `Yulang.ShadowRecordChecker` / `Yulang.ShadowRecordQuotientDecisions` | 新関係の有限ground完全checker、意味を保存する停止的正規化、計算されたnormal formsによるcut elimination、実行可能な商等号判定 | 未知graph変数、正則再帰値型、表示canonical化、row checker自体の構成 |
| `Yulang.ShadowRecordDemands` / `Yulang.SingletonRecordDemands` / `Yulang.SingletonRecordGraph` | 決定40のrigid要求の必要十分条件、全元coreのsingleton要求不変条件、実graph tagと既存参照内のerasure閉包 | 任意外部schemeへの無条件singleton化、未知slot値のsingleton制限、飽和済みgraphの完成 |
| `Yulang.ShadowRegularValueTypes` / `Yulang.ShadowRegularInferenceModel` | 既存正則carrierでのshadow等価・合同性、有限型およびfinite block埋込みの保存反映、旧/有限モデルからの型付け保存 | 一般tail参照のcoalescing、正則部分型のchecker、旧solverの新関係についての完全性 |
| `Yulang.RecordDemandInspection` / `Yulang.SourceRecordDemandInspection` | 元nodeだけを使う実行可能なrecord分解、有限/正則モデルの全割当て・全instance保存、元全core Typingへの接続 | 飽和と自由parameter解の構成、残余Models条件を除いた全core推論成功 |
| `Yulang.ShadowRecordValueInference` / `Yulang.ShadowRecordValueQuotient` | 既存の実データ推論算法について新raw/商モデルの全instance主型性、推論成功の完全性、拒否完全性 | 一般lambda/application・let・fieldを含む全core solver |
| `Yulang.ShadowRecordFunctionScheme` / `Yulang.ShadowRecordFunctionQuotient` | 同じopen-record拡張関数族の自由parameter schemaを新関係の全Typingと一致させること | 任意の関数のsource dispatcher、正則再帰型 |
| `Yulang.SourceDataRuntime` / `Yulang.SourceDataSafety` / `Yulang.ShadowDataSafety` | 元の第一階式のTyping・principal formulaから実eval成功と返り値の型適合、実データinfer成功から全商parameterで同じ値の適合、strict/poly letと実field lookup | 関数・branch・effect・再帰sourceの実行、literal具体payload、Rust/elaboration、意味論から部分型への完全性 |
| `Yulang.HandlerPermissions` | incoming actionのarm許可の実検査と診断、fresh境界後の全treeでの非capture、許可requestのdispatch、shallow継続、検査付きruntime入口 | sourceのmask抽出、mixed-origin action全体の許可推論、局所effectへの一律mask適用 |
| `Yulang.RigidRecordVarianceBoundary` | 前回の局所field存在代数がrigid要求への共変性を満たし、旧右辺unionがnonrigidであること | payloadや実行を含む言語全体のモデル |
| `Yulang.JointConstraintInference` | 元の型・行制約から共有parameterのregular schemeを計算、全値型・行モデルおよび全出力instanceの一致、対応範囲での失敗の完全性 | right-join等の非対応行制約、一般のRowExpr求解 |
| `Yulang.SourceConstraintSupport` / `Yulang.SourcePrincipalInference` | record構築以外の全既存Exprが対応範囲内である証明、元の式からの実際の推論、計算された全scheme instanceと元Typing/principalの一致、拒否と型付け不存在の同値 | record構築、surface elaboration、effect operation/handler・SCC・T3・role/castとの統合 |
| `Yulang.SourceInferenceExamples` | 恒等関数の型・行共有、定数関数の負位置のany化と自由な入力行、実際のsource推論結果とcanonical familyの全instance一致 | 返り値blockの構文的な表示簡約 |
| `Yulang.SignedSourceInference` | 上のsource主型定理を無限・符号付き集合行へ具体化、既存effect algebraとの恒等RowView | protect/release/residual制約を生成する全effect ASTの同時求解 |
| `Yulang.ValueInference` / `Yulang.ValueInferenceExamples` | 既存Exprのvar/lit/branch/letE/pair/variantから型を構成し、元のTyping・principal formulaとの成功時の主性と失敗の完全性を証明、値letの両経路、未対応との区別 | 評価時effectを持つ式、一般のlambda/application、SCC、variantのtag合流・case残余、parserからのelaboration、表示の完全な標準形 |
| `Yulang.SemilinearNormalization` / `Yulang.SemilinearFastInclusion` | 零・重複周期と同じ成分の除去の意味保存、単一周期への全座標を使う正確な所属判定、健全な包含の高速成功と完全なNFA判定へのfallback、最適化前後のBoolean結果の一致 | 全半線形集合の最小正規形、異なる成分の共同被覆を一成分比較だけで判定すること、一般の多項式時間 |
| `Yulang.SemilinearRowAlgebra` | 有限key支持と無限の整数重み集合を持つ行の包含・等価性、重複keyの和と欠けたkeyの空解釈、既存SetRow代数との一致、その行を潜在行とする有限ground構造型の比較 | 未知型変数・再帰値型の求解、元のrow制約からの解抽出は別層 |
| `Yulang.SolvedRecursiveRows` | 元の有限row制約から到達可能な全keyを列挙し、guard検査が通る場合の行全体を構成、元のDerives最小解について包含・等価性・非包含の反例存在を完全に判定 | 一般のguard付き問題、すべての後続具体化での開いた行変数の等価性。未対応の`none`と否定の`some false`は区別する |
| `Yulang.RecursiveRowQueries` / `Yulang.RecursiveRowConstraints` | 任意の既存row式をfreshな出力slotへ接続して元の最小解を保存、固定した半線形上界の有限列について元の下界・上界の充足可能性を判定、否定結果と全モデルの不存在の一致 | 未対応のguard問題、未知上界との相互求解、開いた行の全具体化に対する上界保証 |
| `Yulang.StructuralRowResolution` / `Yulang.SemilinearRowQuotient` | 行の表現変更による部分型の保存と単射な意味符号化による反映、同じ集合を表す半線形行を商で同一視し、元のSetRow上の部分型関係を全有限ground型について完全に判定 | 未知の値型変数や再帰値型の求解、半線形集合の最小正規形の構成 |
| `Yulang.StructuralRowTraversal` / `Yulang.SolvedRecursiveTypes` | 型に実際に現れる行slotだけを解き、元の再帰最小解を各行位置へ代入した有限型の部分型・相互部分型を完全に比較、未対応との区別、行を持たない型に無関係なguardの成功を要求しないこと | 未知値型の推論、すべてのモデルや後続scheme具体化に関する部分型関係、source型の抽出 |
| `Yulang.InfiniteOperationalCorrespondence` | 同じresolved式の既存principal制約を任意の集合行で解釈した解から、同じ実行木の全request上界・返却値の構造型解釈・fresh境界非captureまでの接続。handlerの各armの上界と元の継続行は型判断から導出 | 無限行solverの完全性、source elaboration、異種payload署名、runtimeの再帰構文、潜在closureの衛生wrapper挿入 |
| `Yulang.RecursiveEffects` | 全既存core式とrequest・boundary・shallow handlerを同じ再帰ASTに置く有限制約生成、任意の入れ子について独立な型判断との双方向一致・制約schemeの主性、値制限付き多相letと署名のambient slotの保持 | operation-local多相・roleを含む統合、再帰SCC、source elaboration、制約solver、型付けからruntime安全性への接続 |
| `Yulang.RecursiveEffectsConservativity` / `Yulang.RecursiveEffectExamples` | effectを含まない全core式で実際の生成formula・principal schemeを保存する等式、旧型判断との一致、入れ子handler・多相let・computation引数・保護と負債の正例と負例 | source parserからの翻訳、全制約solver |
| `Yulang.OperationalTyping` / `Yulang.OperationalTypingExamples` | 形状解決済みの単相核の実行可能なcheckerと独立型付けの一致、checker受理から実際の全requestの推論行上界と返り値の潜在関数の健全性、shallow継続・複数回再開・arm再送出・格納callbackの実行例 | 未知shapeの推論、一般再帰、source elaboration、異なるpayload型を持つoperation、値内部への衛生変換の挿入 |
| `Yulang.OperationalCorrespondence` / `Yulang.OperationalCorrespondenceExamples` | 形状解決済み式の消去結果に対する任意の既存再帰型判断から実行上界・返り値の意味を導くこと、union/intersection・値制限付き多相letの解釈、実際のprincipal formulaの解から閉式の全request上界への接続、具体的な解と空行解の拒否 | annotated checkerとの受理集合の一致、未知shape・再帰型の推論、異種operation署名、sourceの注釈や潜在値の衛生変換のelaboration |
| `Yulang.CheckedHygiene` | checker受理または実際のprincipal formulaの解から実行上界を導き、推論行のfreshな表現または実際の座標割当てから原点条件・新境界での非captureを導くこと | sourceが全境界を正しく割り当てること、payload・response・返り値の潜在closureのtransport |
| `Yulang.OperationalTransport` | 実際のcomputation引数を持つ関数・pair内の関数・request treeの高階wrapper、任意の値での両方向の相殺、対応する引数との呼出し・sequencingの等式 | sourceでのwrapper挿入、任意の未変換引数でのdispatch不変性、freshな世界へのclosureの構成 |
| `Yulang.OperationalTransportTyping` | 有限行checkerの型・部分型・実行時適合性の変換前後の同値、既存checker受理から潜在closureまで包んだ同じ評価の型保証 | 未知shapeの推論、sourceでの境界選択、非captureに必要な原点条件の発見 |
| `Yulang.InfiniteOperationalTransport` | 任意の無限集合行を含む既存構造型と高階実行値の対応、principal解から潜在closureのinterface、静的出力行の原点条件から返却関数の呼出しの非capture | sourceでのwrapper挿入、古いclosureのfresh化、record・variantのruntime表現、計算の停止、Simple-sub全体 |
| `Yulang.OperationalTransportSubtyping` | 任意の集合行について、既存の構造部分型関係全体とcomputation部分型の変換前後の同値。recordの幅・先頭field優先、variant、union/intersection、関数の両方の行も含む | 未知型boundのsolver、record・variantの実行時表現、source elaboration |
| `Yulang.OperationalTransportExamples` | checkerで受理される実際の式の評価による格納callback・遅延producerの保護と解除、変換後入力型との適合、負の出力差分の復元、内側globによる外側保護の保持 | sourceによるwrapperの自動挿入、静的原点条件なしでの一律の非capture |
| `Yulang.FiniteReachability` | 有限隣接リストから計算する到達集合と独立な有限経路の判断の一致、空の始点集合からの到達不能性、辺・始点の順序と重複に対する不変性 | source の依存関係抽出、未具体化の多相 cast 集合の有限性、実用的な計算量 |
| `Yulang.EvaluationOrder` | 名前解決済みの有限宣言・module 文からの評価依存計算と独立な推移的依存判断の一致、computed 自己依存・未来の computed binding の拒否、受理された初期化・文の全依存が元の順序で利用可能なこと、lambda による遅延と直接適用時の依存の復帰 | source の名前解決、局所 closure/alias や格納された関数のフロー、任意の高階 callback の実行が依存判断に含まれること、全言語の副作用順序の保存 |
| `Yulang.EvaluationSafety` / `Yulang.EvaluationReads` | 名前で決まらない呼出しへのmodule全体の関数本体近似、独立なCBV読み取りprefixの上界、closure由来の保存、局所・返却・格納closureの読み取り安全性、既評価prefixからの参照先の利用可能性 | source elaboration、外部由来closure、可変store、計算全体の停止・progress。module内のlambda由来とsource位置の構造を明示 |
| `Yulang.Initialization` | 同じresolved本体のSCC生成と二つの初期化検査への接続、値制限の一致、型の割当てによらないcomputed cycle拒否、生成制約から実際の読み取り先の先行性と既評価prefixでの値の存在を導くこと | 全注釈を持つsource moduleのelaboration、module文の結果型検査、全言語のprogress/preservation |
| `Yulang.Methods` | unionの相異なるreceiver候補の0・1・複数の三分、全memberから選択先へのcast検査、選択と変換検査全体の順序不変性 | method lookupの優先順位・可視性、未確定receiver下界の保留、source unionの正規化。refは特別扱いせず全体を照合する（`ImplHeads`） |
| `Yulang.MethodResolution` / `Yulang.FrozenMethods` / `Yulang.FrozenMethodExamples` | SCC最終snapshotの未知receiverで可視role候補0/1/複数を決定、既知の構造field優先、独立な選択・型判断と実際のprincipalの一致、任意の後続代入後も選択と宣言要求を保持、Size/boxの受理・拒否 | SCC知識の算出、nominal/inherent/effect methodのlookup全体、scopeと宣言tableの整合性検査、source全体のelaboration |
| `Yulang.Casts` | 普通の適合性と別の境界変換判断、関数の入力反変・出力共変、tuple・record field・variant payload の共変変換の実行可能な検査と正確性、固定nominal引数を変えるには外側全体の規則が必要なこと | 普通の部分型の決定手続き、effectを持つcastの実行意味、等価な型表記の正規化、未具体化のcast宣言のground化 |
| `Yulang.PureCasts` | 空の符号付き行によるcast宣言検査、チェック済み本体から合成した構造変換の純粋性、境界挿入と関数wrapperによる実際のrequest tree・任意の行上界の保存 | 宣言本体のoperationalな行上界をsource型付けから導くこと、`Casts.Boundary`からtyped planを合成するelaboration、異なるcast経路の値の一致 |
| `Yulang.CastGraph` / `Yulang.CastExamples` | 有限ground登録の検査と深さ制限なしの経路判定、直接重複拒否と複数の間接経路許容、適合時の変換省略、nominal全体からpair・関数・unionへのunbox、source unionの全member検査 | 多相endpoint探索とのsource表現の接続、経路コードの合成、異なる経路の実行結果の一致。登録された直接sourceはnominal/baseに限定 |
| `Yulang.ParametricCastRules` / `Yulang.ParametricCastUniverse` / `Yulang.ParametricCasts` | 多相castの宣言検査と全置換後のサイズ非増大、入力と有限宣言から導く有限alphabet・サイズ上界・到達型集合、任意の有限経路との同値を満たす実行可能な探索、等サイズ循環と固定ground型の拡大の許容 | 明示規則のendpoint探索からsource境界へのelaboration、直接規則の重複・重なり診断、構造変換を混ぜた全言語のsolver、実用的な計算量 |
| `Yulang.LiteralCasts` | list literal の元の構築位置を保持した変換計画、期待要素型が決まった場合の全要素の境界検査、EOFで期待型がない場合の元の要素型のunionと変換省略 | 弱い要素型を解くsolver、cast本体の実行・effect、構築済みlistの変更、空unionを含む表示上の正規化 |
| `Yulang.NominalConstructions` | 任意の有限個の不変パラメータを持つstruct/enum/list構築、各元の位置での境界検査、パラメータごとのEOF unionと変換省略、構築子・tag・位置の保存、既存list plannerへの厳密な特殊化 | 全パラメータ出現位置のsourceからの収集、弱い型変数の解探索、未使用パラメータの既定値・公開可能性 |
| `Yulang.Variants` / `Yulang.VariantsMerged` | support の分割・残余の最小性と最大性、同一 tag の payload 合流と tag 一意性、合流と残余の交換、tag 全体の選択・除去、全 tag 処理と空行の同値、merge 準同型による payload 置換 | payload 内部の source pattern 網羅性（2026-11-05 の決定により対象外）、guard 付き arm の被覆（章3b.4により数えない）、payload の部分型 solver、open row の solver、source 全体の case 検査への接続（保守的な核との接続は `CaseCoverage` で証明） |

`Variants.Merged.Row` は tag の重複がない有限行を表す。`normalize merge` は同一 tag の payload を入力順の右結合で合流し、`lookup_normalize` はその結果を `mergeAll` と一致させる。該当 tag がなければ `none`、一つならその payload、複数なら指定した `merge` を用いる。tag の列順は最後の出現順の逆順である。これらの定理に結合則・交換則・冪等則は不要で、入力の並べ替えや重複挿入で payload が等しくなるとは主張しない。`normalize_map` だけは `f (merge a b) = merge' (f a) (f b)` を仮定する。`variant_union_upper_bound` は既存の構造部分型規則から `variant l a ∪ variant l b ≤ variant l (a ∪ b)` の一方向を導く。case の入力型を閉じる推論器や、部分型モデル全体の正規化を証明したものではない。

`Roles.Term` は変数と有限引数列を持つ型構築子だけを表す。型構築子・型変数を各1と数え、複数引数の head / where 条件の大きさは型サイズの和とする。role 識別子と引数列の spine は数えない。`Impl.WellFormed` は各 where 条件について、head より真に小さいことと、各変数の出現回数が head を超えないことを要求する。`Term.subst_size` / `args_subst_size` は、置換後のサイズを元のサイズと各変数の出現回数に基づく増分の和で表す。`size_decreases` はこの二条件から、任意の置換の下での真の減少を導く。`resolve impls wf goal` は全 impl の適格性の証明を受け取り、goal の引数サイズを測度として停止する。`wellFormed_cons` は、impl の追加時も適格性が宣言ごとの条件であることを示す。適格性の診断を返す source 宣言検査器は未接続である。

照合は impl の変数だけを置換し、goal の変数は rigid に保つ。繰り返し現れる変数には同じ型を要求する。`matches_iff` は実行可能な照合と存在的な head 一致の同値を、`constraint_variables_in_head` は head にない変数が where 条件にもないことを示す。`matched_constraint` により、照合に使う置換の未使用変数の既定値は where 条件の結果に影響しない。`Impl.key` は宣言の識別子であり、同じ head / where を持つ別宣言も別候補として表せる。同じ impl 値の繰り返しは同じ宣言として除重複する。入力リストは可視な impl 集合を表し、import・可視性の検査は扱わない。

曖昧さは where 条件を調べる前の head 一致で判定する。head 候補が二つ以上あれば、条件の成否によらず `ambiguous` となる。一意な候補の全 where 条件を調べ、子の `ambiguous` は兄弟の `noImpl` より優先する。`resolve_resolved_iff` と `resolve_noImpl_iff` はこの成功・失敗条件を正確に述べる。`Derives` は resolver を参照しない存在的な宣言的導出であり、重なる impl でも導出自体は存在し得る。`resolve_sound` は成功から導出を、`resolve_complete` は導出と到達する head の非重複から成功を導く。`ReachesOverlap` は一意な候補の条件をたどって重なる head に至る有限経路であり、`resolve_ambiguous_iff` はその存在と `ambiguous` を同値にする。`Examples` は二重 list の成功、str impl の不在、rigid 変数、変数を複製する条件の拒否、サイズが増える Foo impl の不適格性と有限導出の不在、head が重なる例を検証する。Foo の有限導出の不在は適格性を仮定しない帰納法で示し、宣言的導出の健全性と解決の実行可能性を区別する。

`Yulang.RolesAssoc` の `Roles.AssocImpl` は既存の `Impl` を包み、関連型名から右辺 `Term` への辞書を添える。既存の `Impl` と定理は変更しない。`RoleDecl` は引数数と宣言済みの名前・default を表し、default の変数は `0..arity-1` の引数位置だけを指す。辞書の名前の無重複性と、同じ元の impl に同じ辞書を対応させる `AssocEnv.coherent` は表現上の不変条件である。source の重複宣言の診断や意味は定めない。`AssocHeadVars` は明示定義の変数が head に現れること、`AssocComplete` は署名との引数数の一致と必須定義の充足、`AssocDeclared` は未宣言名を提供しないことを要求し、`AssocWellFormed` は全 impl に対してこの三条件を要求する。

`assocOf` は既存の `resolve` が成功したときだけ、一意な impl の右辺を head の照合置換で一度具体化する。明示定義がなければ、default の引数位置を goal の型引数で置換する。`Term` に関連型参照はなく、別の関連型の展開や新しい再帰・停止測度は不要である（章6.3、確定, 2026-11-05）。`assoc_independent_of_constraints` と `assoc_explicit_eq` は、解決成功を前提として値が選ばれた impl と照合置換で決まり、where の解決導出によらないことを示す。`assoc_derivation_agrees` / `assoc_derivations_unique` は、resolver を参照しない `AssocDerives` の二つの導出でも値が一致することを示す。Paterson 適格性と関連型適格性の下で、`assoc_total_closed` は、解決済み goal の**宣言済みの各名前**について結果が存在し、その変数がすべて goal に現れることを証明する。`assoc_unique` はその値の一意性を示す。`assoc_explicit_size` は明示定義について既存の `Term.subst_size` と同じ正確なサイズ公式を与える。`AssocExamples` は str・box・定数と引数位置の default・明示定義による default の上書き・rigid な goal 変数の正例と、head 外の変数・必須定義の欠落・未宣言名の提供を拒む負例を検証する。関連型を含む method 署名や where 条件との単一化は `RolesAssoc` 単体の対象外である。関連型選択から普通の等式を追加する規則は確定済みで、`RoleConstraints` がその接続と解集合の順序不変性を扱う。未知の置換を探索する全体solverは別に必要となる。

`Horn.solve` は全 `2^n` valuation を列挙する参照実装で、実用solverの性能を主張しない。有限性は `Fin n` という入力型に明示されており、任意のYulang制約がそこへ落ちるという未証明の仮定を入れていない。

`FiniteReachability.closure` は有限グラフの始点と辺を Horn 制約に翻訳する。`closure_exact` は、結果の真の成分と、始点から有限回辺をたどる独立な `Reach` 判断とを双方向に対応させる。経路長の打切り・非循環性・解決成功の仮定はない。`closure_empty` により、循環する辺だけでは到達点は生じない。評価依存と ground cast の探索で共有する基盤であり、このモジュールだけでそれらの source 規則との対応を主張しない。

`EvaluationOrder` は局所変数と有限個の global 宣言を区別する式を入力とする。評価位置に現れた global 名から、その宣言の関数本体へ推移的に進む。関数を引数として渡す場合も同じ辺をたどる。名前付き宣言の `invokedReferences` は先頭の引数lambdaだけでなく、分岐の結果やcallee位置から返るlambdaも再帰的に開く。独立な `InvokedUses` 判断との一致と、旧来の有限回の直接適用で見つかる依存をすべて保持することを証明した。`check_exact` は computed binding の初期化と、位置を持つ module 文の両方について、実行可能な判定と独立な `Ordered` 判断が一致することを示す。到達した computed binding の位置には真の不等号を要求するので、自己依存・未来への依存は拒否される。関数だけの相互再帰を禁止する規則はない。

`lambda_no_dependency` は lambda **構築時**の依存がないことを示す。`applied_lambda_preserves_body_dependency` は直接適用すれば本体の依存が戻ることを示し、curried な直接適用にも負例がある。`accepted_initializer_earlier` / `accepted_statement_available` は、この依存判断で必要とされる computed binding が、並べ替えていない宣言順序で先行することを証明する。任意の source callback の実際の呼出しをこの判断が過大近似することはまだ示していない。分岐からlambdaを返す名前付きfactoryの即時呼出しには拒否・受理の回帰例がある。この基礎層だけでは局所変数を通るclosureを追わないため、決定23に従うmodule全体の近似と実行時の接続を、次の `EvaluationSafety` / `EvaluationReads` に追加する。

`EvaluationSafety` は、名前で決まらない呼出しで、宣言とmodule文に含まれるすべてのlambda本体の参照を候補にする。直接のlambda、または宣言本体がlambdaである名前だけは、その本体を使う。`EvaluationReads` の `Eval` と `Reads` はcheckerを含まないCBV意味論で、後で発散する実行の読み取りprefixも扱う。`Reads.read` はstoreに値があることを要求せず、未初期化の読取りも表せる。`reads_needed` はmodule由来のclosureを持つ任意のstore/environmentに対し、実際の読みが計算した依存集合に入ることを示す。`eval_closed` はclosureと捕捉環境の由来を実行に沿って保つ。`accepted_read_initialized` は、先行するcomputed bindingの結果を記録したprefix storeに対し、読まれる値の存在を導く。`initialize_next` は実際の初期化結果を記録するとprefix不変条件が進むことを示す。さらに `EvaluatedPrefix` は空storeから始めたcomputed宣言の実際の初期化履歴を表し、`EvaluatedPrefix.invariants` がclosureの由来と先行値の存在を導く。`accepted_prefix_read_initialized` はこの履歴から、現在の式の終了を仮定せず読み取り先の値が存在することを示す。位置を進めるときは、その位置の宣言が一意であることを要求する。間にあるmodule文の実行・終了や、その履歴全体の存在は別の義務である。これは保守的な上界であり、実際に読まれる集合との同値や全実行の停止を主張しない。

`Initialization.toCore` は同じ依存構文の本体を型推論の式へ翻訳し、global名の添字をlambdaの局所束縛の数だけずらす。有限のscope検査で、不正な局所添字がglobal名を指してしまう場合を拒む。`value_restriction_agrees` により両側のcomputed分類は一致する。`generate_exact` は、生成制約の解と「同じ本体の同時単相型判断＋初期化順序判断」の一致を示す。`computed_cycle_rejects_generated_constraints` は任意のモデル・割当てについて、computed cycleが合成後の生成制約を満たせないことを示す。対象にはunit・Boolean・pairのprojectionを含み、module文はこの層では依存だけを検査する。生成器は `EvaluationSafety.check` も要求し、`generated_initializer_read_earlier` は実際の読み取りprefixに対して先行性を導く。`generated_prefix_initializer_read_initialized` は、生成制約の解と実際の既評価prefixから、次の初期化の読み取り先に値が存在することを導く。現在の読み取りの被覆や利用可能性を別の前提として要求しない。

`Methods.resolve` は member ごとの method の有無が確定した段階を扱う。`resolve_unique_iff` / `resolve_missing_iff` / `resolve_ambiguous_iff` は、それぞれ相異なる候補が 1 個・0 個・2 個以上である条件を示す。`select_ext` はリストの membership が同じなら結果も同じことを示すため、順列だけでなく同一 member の繰り返しも曖昧さを増やさない。

`CheckedRoles.checkImpl` は各 where 条件のサイズ減少と変数出現回数を検査する。条件側の変数番号上界より上の出現回数は 0 なので、有限回の検査と無限個の変数についての `Impl.WellFormed` が一致する。`CheckedRoles.resolve` は全宣言を先に調べ、成功した場合だけ既存の停止性証明付き `Roles.resolve` に渡す。`resolve_exact` は適格性を前提にせず、結果が成功することと「宣言集合が適格で、導出があり、到達する head に重なりがないこと」の同値を示す。不適格な宣言は、その goal の解決で使われなくても拒否する。

`RoleConstraints.addAssociated` は既存の関連型解決が返した値を、普通の型変数との等式として蓄積する。`Store.permutation_preserves_solutions` は一つの選んだ置換だけでなく、**すべての置換**について解集合が順序に依存しないことを示す。`conflicting_constraint_rejects` は同じ変数への char と str の要求が、後からの代入で上書きしても解にならないことを示す。`Store.check_dichotomy` は固定した置換での整合・矛盾の二分であり、解となる置換の存在判定器ではない。

`Casts.accepts_exact` は、与えられた普通の適合性の判定と明示castの探索を用い、独立な `Boundary` 判断と実行可能な追加変換の検査を対応させる。適合すればそのまま通し、不一致の場合だけ構造に沿った変換を調べる。recordはfield名で照合し、既存の構造型モデルと同じく最初のfieldが後の同名fieldを隠す。`union_mismatch_iff` は不一致の場合に全memberの検査が必要なことを示す。無条件の `union_boundary_iff` では、普通の適合性がunionの除去則を満たすことを明示的に要求する。`structural_union_boundary_iff` は既存の `StructuralBase.Subtype` と一致する適合性からこの前提を導くが、本層自体は部分型判定器を実装しない。有限構造型の判定は `StructuralDecisions` で別に実装・証明する。

このground型構文で、登録先の同一性と固定nominal引数には構文的等号を用いる。nominal引数内のunionの並べ替えなど、意味的に等価な型を同じ表現にする正規化は前段の課題である。`equalityCompatibility` は検査の具体例用の適合性であり、Yulangの部分型solverを置き換えるものではない。

`CastGraph.Registry.find_exact` は、有限のground型の登録と、先に証明した有限経路判断を結ぶ。登録は型ごとに一つの頂点を持ち、同じ直接のsource/target対の重複を拒否する。異なる間接経路が合流するdiamondは許容する。`compatible_kept` は適合する境界で変換探索を使わないことを示す。`Methods.checkCall_exact` はmethodを持つ相異なる型がちょうど一つであり、すべてのreceiver memberからその型への境界変換が成立することを要求する。`checkCall_perm` はこの変換検査まで含めた結果の順序不変性を示す。例は固定した`list user_id`から`list int`への要素castの不許可と、list全体の明示規則による許可を区別する。 `cast(x: box 'a): 'a` の具体化ではtargetがpair・関数・unionにもなり得るため、直接sourceのnominal/base条件を保ちつつtarget制限を外した。`nominal_mismatch_iff` は任意のtargetについて外側全体の規則を要求する。source unionは引き続き全memberを個別に検査し、whole-unionだけのoracleでは欠けたmemberを隠せない。

`ParametricCastRules.Rule.substitution_nonincrease` は、targetのサイズと各変数の出現回数がsource以下なら、どの置換後もサイズが増えないことを証明する。固定したground castはサイズを増やしてよいので、全到達型には初期型のサイズと宣言のtargetサイズの最大値を上界として使う。構築子の有限性も仮定せず、初期型と有限個のtargetからalphabetを作る。`ParametricCastUniverse.reachable_types_finite` はこのalphabetとサイズ上界から計算した有限リストが、すべての有限cast経路の到達先を含むことを示す。等サイズの循環そのものは許される。`ParametricCasts.query_success_iff` は「宣言が適格、出発型がground、独立な明示規則の経路が存在すること」と成功を同値にし、`query_failure_iff` は同じ検査済みの領域で経路の不在と失敗を同値にする。有限instanceグラフは入力ではなく、証明済みの有限リストから実際に構成する。この探索は全候補型とBoolean valuationの列挙による参照実装で、実用的な性能は主張しない。構造的な持ち上げを自由に混ぜた全言語の探索とは区別する。サイズはnominal引数の内部も数える `Roles.Term.size` であり、構造変換の停止測度でnominal引数をopaqueにする `Casts.Ty.size` とは用途が異なる。

`LiteralCasts.finish_exact` は、保持された各要素の構築位置と元の型に対し、期待要素型が与えられた場合だけ境界検査を要求する独立な `PlanTyping` と実行可能な計画作成を対応させる。どちらの場合も元の構築位置を保持する。EOFまで期待型がなければ、元の型の列をunionとして記録し、要素の命令はすべてkeepになる。これはコンパイル時に保留された構築位置へ変換を割り当てる規則であり、すでに構築したnominalなlistの型引数へcastを通す規則ではない。`expected` を決める弱い変数のsolverは別に必要である。

`PureCasts.Declaration` は実際の `Directed.Computation` 本体と、その推論行による上界を持つ。宣言の検査は行全体の空性を要求し、保護されたheadや負の差分も純粋と誤認しない。`Plan.run_eq_pure` はチェック済みの基本変換から合成した任意の有限planの純粋性を導く。`insert_requestTree` は返り値を除いた実際の要求木（payload・継続の分岐・符号付き重みを含む）を保存し、`insert_bounded_iff` は任意の行上界について同値を示す。関数の `wrapper_requestTree` は、変換後の引数で元の関数を呼んだ場合との対応である。入力値を変える前後で同じ実行になるとは主張しない。宣言本体の上界をsource型付けから導くことと、境界判断から実行planを合成することは別の接続義務である。

`NominalConstructions` は各元の構築位置を有限の不変パラメータslotへ対応させ、同じslotに属する全値を検査する。未解決のslotは、そのslotに属する元の型だけのunionを記録して変換しない。複数field・別々のパラメータ・enum tagの例があり、`finish_literal_exact` は一つのslotのlist構築を旧 `LiteralCasts.finish` へ射影すると、失敗も含め結果が厳密に一致することを示す。出現しない未解決slotは `unionOf []` という記述のままであり、bottomや既定型への決定・公開可能性をこのplannerで作らない。

`ImplHeads` は名前付き変数を偶数、各holeを別の奇数の識別子へ下ろす。`anonymous_occurrences` は任意の有限headと任意の匿名識別子について、割り当てた範囲では一回、範囲外では零回の出現を証明する。`named_occurrences` は名前を共有する箇所の出現回数を保ち、whereの名前は匿名識別子へ触れない。`two_holes_accept_all_types` と `repeated_name_matches_iff_equal` は任意の二つの型について、この違いを実際のhead matcherで示す。refも同じ全体照合を使うため、intのmethodをrefの中身へ自動委譲せず、`ref _ int` の特化は任意のeffect引数に適用できる。

`EffectExamples` は、同じfamilyの保護されたtail、境界ごとの解除、繰り返した保護、型引数を含むkey、shallow/multi-shot、handler armが新しく起こすeffectを検査する。nested `sub` の核の例は`0`、保護を消した比較例は`2`と計算される。これらはsource例に対応して手で構成した核の式で、parserからの翻訳の正しさを主張しない。

`shallowHandle_bounded` は、value armとoperation armの実行時effect上界を前提として、結果のeffectが`residual input ++ armEffects`で抑えられると証明する。継続の上界には元の入力行を保つ。この前提を型付けから導くsource handler推論器まで証明した、とは読まない。

## 高階の衛生性

`HigherOrder` のerase解除では、先に解除してから保護する往復が壊れる。`Directed` は許可されていないkeyについて、各境界の整数weightを保護で `+1`、解除で `−1` だけ変える。同じ境界と同じ許可maskの一対について両方向の相殺が成り立つ。handlerがcaptureできるのは、keyが一致し、すべてのweightが0のときだけである。

`DirectedHigherOrder.transport_opposite` は、product・sum・list・arrowで構成する任意の有限shapeと、その任意の値に対してこの相殺を証明する。関数の入力では方向を反転し、戻りcomputationと値では方向を保つ。新鮮性・weightの上限・fuelの仮定はない。

一方、非captureには由来の条件が必要である。weight `−1` に `+1` を足すと可視になるため、任意の符号付き入力を保護すれば必ず非captureになるとは主張しない。`guard_arrow_noncapture` は、反変方向に引数を変換した後の関数呼出しについて `ZeroAt` を仮定する。

`contravariant_debt_preserves_local_callback` は、callbackを奪う内側handlerの結果 `99` と、transportを入れて呼出側のhandlerへ届く結果 `7` を比較する。引数側の負の差分が内側でのcaptureを阻止し、帰りの正の差分が元の可視性を回復する。

`FreshBoundaries` は、古い境界を単射で埋め込んで新しい座標を割り当てる。既存の負の重みも保ったまま、新座標での `ZeroAt` を構成する。`FreshRowInference.fresh_eval_zero` は未知tailを含む全 `RowExpr` で同じ条件を導く。`CheckedHygiene.inferred_fresh_origin` はその静的な行の表現とchecker受理から、実際の評価木の原点条件を得る。行の表現は明示的な前提であり、checker自身がsourceの境界割当てを発見したとは扱わない。

`CheckedHygiene.closed_checked_boundary` は閉式のchecker受理だけから、評価木を実際にfresh化して保護した後の行上界と、任意の内側shallow handlerによる非captureを結合する。action・armの上界や `ZeroAt` は入力に要求しない。このfresh化は即時request treeに作用し、返り値の型は元の `Value n` のままである。値の内部に格納されたclosureを新しい境界へtransportする定理とは区別する。

`CheckedHygiene.principal_fresh_boundary` は同じ結論を、実際の `RecursiveEffects.principal` の解を入口にして導く。`OperationalCorrespondence.principal_effect_bound` によってruntime上界を構成するため、annotated checkerの受理を別途仮定しない。

`OperationalTransport` は上の値渡しの模型ではなく、実際の `OperationalTyping.Value`・`Tree` に高階wrapperを定義する。関数はcomputation引数全体を逆方向へ戻し、呼出し結果のrequestと返却値を順方向へ写す。`value_opposite`・`tree_opposite` はすべての有限resolved shapeについて両方向の相殺を示す。`value_apply_tree` は関数と入力interfaceをともに写した呼出しの正確な対応であり、未変換の引数に対するdispatchの不変性ではない。

`OperationalTransportTyping.valid_iff` は有限行checkerの型について、`InfiniteOperationalTransport.compHolds_iff` は任意の集合行を持つ既存構造型について、変換前後の型と実行の対応を双方向に証明する。後者は無限行・負の重み・型のunion/intersectionを許す。`closed_inferred_transport_valid` と `principal_transport_valid` により、checker受理または既存principal formulaの解から、即時requestに加えて返却・格納されたclosureの潜在interfaceも導く。runtimeのshapeはatom・pair・arrowであり、record・variantの実行時表現までは追加しない。

`InfiniteOperationalTransport.guarded_call_noncapture` は、型に適合する変換後の引数と、元の出力行の静的な `ZeroAt` から、保護した呼出しの非captureを導く。実行時の上界と原点条件は関数の型から構成する。`principal_guarded_arrow_calls` は、この保証を変換後の評価が返す各closureへ接続する。これは `AllReturns` の保証であり、値が返ることや停止性を主張しない。`fresh_output_call_noncapture` は、既に拡張された境界集合で型付けされ、出力行が `liftRow` である関数への系であって、任意の古いclosureをfreshな世界へ持ち上げる構成ではない。sourceでwrapperを挿入するpassは別の義務として残る。

`OperationalTransportSubtyping.subtype_iff` は実行時の解釈とは独立に、既存の `StructuralBase.Subtype Included` 全体を保存・反映する。recordの幅と先頭field優先、variant、推移則を含む。`comp_subtype_iff` は実際の集合行推論モデルの `Inference.Comp.le` まで接続する。したがって、この型変換だけで新しい部分型関係を作ったり、元の制約を失ったりしない。未知のboundを解くことまでは意味しない。

`OperationalTransportExamples` はcheckerで受理される既存の式を評価する。即時境界だけでは内側handlerがpair内のcallbackを奪い `99` を返すが、高階wrapperでは要求が通過し、対応する解除後に呼出側がpayload `7` を受け取る。callbackを生成する途中のrequest `13` も、computation引数全体の反変変換で保持する。混在した由来のinvokerについては、実際の引数が変換後の入力型に適合することと、出力行にraw要求が残ることも検査し、純粋性や無条件の非captureを主張しない。別の境界のglobが外側の負の差分を消せないことも確認する。

## 型推論の主定理

`AnnotationSnapshots.observe` は、現在の行式に含まれる concrete な頭を符号付き行として計算し、残った行変数をこの観測では opaque とする。観測を取る前に、その時点ですでに分かっている置換は適用されている必要がある。`TrackedRow.subst` は行式を具体化し、注釈時点の履歴をそのまま保つ。`principal_observed_exact` は、保存した観測の許容性と既存の宣言的型判断の連言が、観測を付けた主制約schemeの意味と一致することを示す。許容された観測から後の行変数へ上界・等式は追加しない。T3 の例では、未知行を観測してから禁止effectへ具体化した履歴は受理され、その具体化後の行を**新しく**観測すれば拒否される。当初から既知で可視な禁止effectを未知tailの横に置いても拒否される。

`AnnotationFinalization` は有限Horn factの層で、SCCの全memberの制約を集め、実際の `Horn.solve` の最小解を計算した後に観測する。`known_iff_forced` は、その解で真のfactが全モデルで強制されるfactと一致することを示す。`finalize_constraint_order` と `scc_member_order` は制約の生成順序・memberの収集順序に依存しないことを示す。並べ替えても名前解決済みのfact/row識別子は固定する。`principal_finalized_exact` はこの検査を既存の主制約生成へ接続し、`gate_subst` は後の具体化で再検査しないことを示す。同じSCCの別memberから伝わるeffectは検査対象で、入れ子のbindingは自身の単位を先に確定する。この実装は既知の置換を外から渡すだけの層より進んだ有限solverだが、sourceの全制約がその有限interfaceへ翻訳できることまでは証明していない。

`RecursiveInference.generateSCC_exact` は、任意の有限 member 列について、同じ再帰仮定環境で全本体を検査する生成制約と独立な `SCCTyping` を双方向に対応させる。`closeSCC_exact` は slot 群を全本体の外側で存在量化するため、呼出しごとに型を選び直さない。全注釈の `FullAnnotation` は値型の有限変数だけを呼出側で具体化し、定義側ではそれらすべての割当てで本体を検査する。`rowsCaptured` の構文検査により、注釈中の明示的な行slotは外側の共有割当てを参照する。同じ SCC の別 member からも同じ注釈schemeを使う。これらは制約生成の正確性であり、source の SCC 発見や制約の解探索そのものの証明ではない。

`generalizeMember_exact` は、SCC全体を検査した後の一つの値memberの具体化を記述する。存在量化するlocal slotに属する全unannotated memberへ、構文上の値かつpureに型付けされるという検査を入れる。computed memberはcaptured slotに残り、別々の具体化で同じ割当てを参照する。`RecursiveExamples` では、SCC後のidentityをintとstrで独立に使うこと、別memberを公開するときにもcomputed memberをlocal slotへ隠せないこと、全注釈の関数と単相関数が互いに呼び合う例を検証する。

`unannotated_depth_typable` は、`x`を`(x,x)`へ変えて再帰する同じ式を、単相型 `any -> int` で受理する。再帰引数のpairを `any` へ広げることができるため、決定36以前のtopを持たないモデルでの単相拒否は、現在の体系では偽になる。`generated_unannotated_depth_satisfied` と `closed_unannotated_depth_satisfied` は、この実際の割当てを生成制約・closed SCCへ接続する。`generated_annotated_depth_satisfied` の全注釈のschemeによる受理も維持する。source例の算術と条件値はliteralへ抽象化しており、実行の停止性は主張しない。

`QualifiedInference.principal_exact` は、resolved methodの有限のrole要求を制約に加えた生成器と独立な宣言的型判断の一致を、元の構造的な式の全ケースについて証明する。この層の通常の `letE` は単相で、qualifiedな値の一般化は `qualified_let_exact` の別規則で接続する。一般化interfaceはlocal slotと環境slotを明示する。`partition_exact` はraw role要求を自動で分け、local slotを含む要求をschemeへ、環境slotだけの要求を残留制約へ移す。混合した要求の環境slotは量化せず共有する。定義は抽象辞書を仮定して全local割当てで検査し、利用時にその具体化の証拠を要求する。

通常のqualified letは `Comp` slotを量化し、値型とeffect行の両方を独立に具体化できる。operation-localの型変数や全注釈による多相再帰とは量化の種類が異なる。`QualifiedRowExamples.independently_instantiates_latent_row` は一つのschemeを任意の符号付きcallback行で具体化できることを示し、相異なる非空行でも確認する。`QualifiedExamples` は、具体的なimplがなくても未使用の`twice`を定義できること、そのschemeを証拠なしでは使えないこと、実際の`Add int`解決が利用を可能にすること、環境に由来する制約が消えないことを示す。これらは供給された有限interfaceの正確性であり、未解決の部分型制約からそのinterfaceを発見するsolverまで証明したものではない。

`ModuleRoles.finishModule` は、EOFで渡された部分割当てとinterfaceについて、公開型およびraw role要求に現れるすべてのambient slotが確定しているか検査し、残留role要求を実際の `Roles.resolve` で確認する。`finishModule_no_unresolved_exports` と `finalized_scheme_exact` は、受理した公開schemeが元のschemeと同じ意味を持ち、未使用の未確定slotをどう補完しても意味が変わらないことを示す。未確定weak slot、同じファイル内でintに決まる例、証拠のないstr、implなしで公開する抽象qualified関数の各場合を検証する。module全体から全残留制約を収集するpassと、その部分割当てを求めるsolverはこの入口の前段である。

`RoleEvidence.Signature` は既存の `PolySignature` にrole要求を追加する。`request_constraints_exact` は局所型を存在的に具体化して呼出側の証拠を要求し、`handler_constraints_exact` はactionとvalue armの型を先に決めてから、すべての局所型で署名の辞書を加えてoperation armを検査する。外側の環境と結果はその局所型によらず、継続は元のinput rowを保つ。`RoleEvidenceExamples` は実際の符号付き構造モデルで、抽象payloadにAddを使ってからresumeする腕を署名辞書つきで受理する。同じ腕の辞書なしの場合は**すべての外側の結果型・行**で拒否し、呼出側に証拠がないrequestも拒否する。handlerの型判断からoperationalなeffect上界を導く定理ではない。

`principal sΓ e` は一つの結果slotを持つ有限の制約schemeを返す。`principal_exact` は任意の型・行のモデル、対応する入力環境、型と行の割当てについて、次を証明する。

```text
(principal sΓ e).Holds m (extend ρ (A, ε))
  ↔ Typing m Γ e (A, ε)
```

環境の前提 `EnvRel` は、入力schemeと入力bindingが同じ型の候補を表すという条件であり、solverの成功や式自身の型付けを仮定していない。空環境には無条件に成立する。`Typing` と `BindingTyping` は `generate` や `Formula` を参照しない独立の帰納的判断である。

対象の式は変数・基本literal・lambda・computation application・非再帰let・分岐・pairとprojection・recordとfield・variant注入。多相letは純粋な構文的値の有限schemeを保存し、利用ごとにfreshなslotへ代入する。外側の環境のslotは共有したまま。単相letはすべての右辺に使え、一つの型を共有して右辺と本体の実行行を合流する。構文的な値にはこの二つの経路の選言を生成する。`Polymorphism` は、computation引数を指す変数を束縛でき、そのeffectが消えないことを検証する。

`Structural`では、混合分岐が`int | str`を持ち`int`だけにはならないこと、多相identityの二回の利用で`pair(int, str)`が得られること、余分なfieldを持つrecordから`int`を取り出せることを、**生成された制約の意味について**検証する。record spreadのtailには `restType ≤ emptyRecord` を要求し、scalarをtailにする式は任意の結果型・行について拒否する。任意の制約を受理する空虚なモデルではない。

`RowInference.handler_constraints_exact` はcore生成器とhandlerの規則を接続し、同じ定理を非負行と符号付き行に使う。継続には元のactionの行を持たせ、結果にはactionの残余と両armの行を加える。既存の単相署名と定理は維持する。潜在行を含む高階の型変換はこの定理の対象外である。

`EffectInference.PolySignature α n` はambient slot `α` と局所型変数 `Fin n` を分け、署名の入出力を `TyTerm (α ⊕ Fin n)` で表す。局所slotは値型だけを具体化し、行成分は空行とする。`poly_request_constraints_exact` は、呼出側の生成制約が「ある局所型の割当てで独立なrequest規則が成立する」と同値であることを証明する。各呼出しの存在量化は独立し、好きな型を選べる。

両モジュールの `poly_handler_constraints_exact` の型判断は `∃ input returned, … ∧ ∀ ι, ∃ operated, …` の順序である。actionとvalue armの型・行を先に固定し、すべての局所型割当て `ι : Fin n → m.Ty` についてoperation armの型付けと結果への包含を要求する。継続は元のactionの型・行を保持する。結果 `out : CompTerm α` と外側のscheme環境 `SchemeEnv α` は局所slotを含まない。`local_result_no_escape` は局所割当てを変えても結果の型・行が同じであることを、`local_outer_environment` は任意の局所割当てで同じ外側binding環境を表すことを示す。これはescapeを構造的に排除する核の規則であり、source上のescape検出・エラー報告の証明ではない。atomのkey・追加effectは局所割当てによらず固定され、atomのpayload内部の局所変数とrole制約は扱わない。

`SignedStructural.generated_poly_request_at_any_type` は任意の構造型（複合型・effect付き関数型も含む）で呼出制約が成立することを、`generated_poly_requests_independent` は同じ署名・同じ外側の割当てでintとstrへの二回の独立した具体化が成立することを示す。`generated_poly_handler_resumes_payload` は任意の局所型のpayloadを同じ型を受け取る `k` へ渡す腕を受理する。`generated_poly_handler_payload_escape_rejected` はそのpayloadを固定のint結果へ直接返す腕を拒否する。後者は局所型をstrとしたときの `str ≰ int` による具体的反例であり、任意のモデル・任意の結果上界についての拒否を主張しない。

`SignedStructural` は実際の符号付き行を使い、生成されたoperationの制約が自身のeffectを含む行で成立し、空行では成立しないと証明する。保護前の解除が作る `−1` の差分についても、生成された境界制約がその行を保持し、空行へ消せないことを証明する。型構築子・部分型規則・scalarの分離は `StructuralBase` を通して非負モデルと共有し、別の型体系を複製しない。

`DirectedHandlerInference` の `generated_signed_handler_composes_effect_bounds` は、成立した `RowInference.handlerConstraints` から得たaction・armの型付けと、明示された実行時の上界を組み合わせる。結論は実際の `Directed.Computation.shallowHandle` の出力上界である。制約の定理とoperationalな定理を別々に置くだけでなく接続しているが、型付けから実行時上界を得る前提そのものを証明したとは扱わない。

`RecursiveEffects` は全core構文とrequest・boundary・handlerを一つの再帰ASTにまとめる。生成の双方向定理は、型モデルと行代数の空・和・包含を整合させる `RowView` の下で成立する。`RecursiveEffects.Conservativity.generate_preserved` は旧 `Inference.Expr` の全constructorについて、fresh slotや値制限letの両分岐まで含め、生成formulaが旧生成結果の埋込みと等しいことを証明する。`principal_core_exact` は旧 `Inference.Typing` 自体との対応を導く。新しい生成器へ置き換えたことだけを理由に、既存coreの意味を変更しない。

`RecursiveEffectExamples` は入れ子のhandlerとlambda内部のhandlerを検査する。同じkeyをarmで再送出する式、保護された要求、負の解除差分は、任意の結果型・slot割当てでも空行には型付けできない。未使用computation引数を純粋に扱う一方、computed letが実行する右辺のeffectを消せないことも示す。

`OperationalTyping.infer` はshapeが解決し、lambdaの入力型とhandlerの結果型が与えられた単相核のcheckerである。`infer_exact` は実行可能なcheckerと独立な構文的型判断の一致であり、未知の構造型や全言語の主型を求めるsolverの完全性ではない。`typing_sound` はaction・armを含む部分式の型付けに帰納法を適用し、実際のrequest treeの上界と、返された関数を任意の適合するcomputation引数へ適用したときの上界を同時に導く。閉式の `closed_inferred_bound` はchecker受理だけを前提とする。

この評価は関数へ引数をcomputationとして渡す。引数の行を無条件に呼出し結果へ加えず、computed letは右辺を実行する。shallow継続の型には元のaction行を保ち、armが新しく出す要求は残余の外へ加える。`OperationalTypingExamples` は未使用引数、明示的に許可した引数の処理、再開後の未処理要求、同じ継続の二回利用、同じkeyの再送出、pair内のcallback、負の差分についてchecker結果と実際の評価を確認する。即時boundaryが返り値内のcallbackを勝手に変換しないことも検証する。

`OperationalCorrespondence.erase` はこのresolved式からlambda入力注釈・handlerの結果型・明示的なwidenを消し、`RecursiveEffects` の同じ演算へ写す。`erasure_typing_sound` は消去結果の任意の再帰型判断を解釈する。既存の `StructuralBase` のunion・intersection・関数の分散を含み、値制限付き多相letでは純粋な右辺の一つの評価値が各使用箇所の型を満たすことを導く。atomは一つのopaqueなcarrierで、構造型ではunitをそのmarkerにする。source literalの型をunitへ変更する規則ではない。

`principal_operationally_valid` と `principal_effect_bound` は、閉じたresolved式の実際のprincipal formulaの解だけから、返り値の意味と全requestの上界を導く。個々のaction・armのruntime上界もannotated checkerの受理も前提としない。二つの入口は同じ評価に対して健全だが、受理集合の一致は主張しない。注釈の不一致でcheckerが拒否しても、注釈を消した式の制約には解があり得る。source注釈を保持するelaborationの正しさは別の義務である。

`OperationalCorrespondenceExamples` は実際のrequestと、lambda内部のhandlerが許可したcomputation引数を処理するapplicationについてprincipal formulaの解を構成し、同じ評価の行上界へ接続する。requestのformulaには、どの結果値型を選んでも空行の解がないことを示す。この入口の前提が具体的に充足でき、effectを自由に消せる空虚なモデルではないことを確認する。

## 検証ゲート

`lakefile.toml` は全モジュールのコンパイルに `--trust=0` を指定する。`Audit.lean` はYulangの各モジュールからimportされた**すべての宣言**について依存公理を走査し、`propext` / `Quot.sound` / `Classical.choice`以外があれば失敗する。私有宣言も対象とする。その後で主要定理の依存を個別表示する。

`sorry`、追加の公理、`native_decide` での証明を使わない。Lean が通常使う公理と、未証明の主張を公理化することを区別する。GitHubの`Lean inference kernel` workflowも、ビルドとこの監査を実行する。

構文例の計算確認と一般定理も区別する。全言語の推論器、Rust との接続、公開型の表示、実行時の型安全性については、対応する定理を持つまでは完了と呼ばない。
