# 次の source integration 義務（cycle262 終盤の読取り・小probe）

Status: proof plan, not a completed compiler. 2026-11-18 UTC.

## 1. 今回の top-level が実際に要求すること

`GeneralRebaseSemanticTrace262.source_certificate` は、source Initial から一つの有限request
poolを構成する。その後の `inspect/roots/plans` は依然外から供給する関数である。

- source Initialは既存mixed-source boundaryの実Initialであり、展開するとformed source、
  point root、ground root labels、constructor coverage等を持つ。無条件の任意プログラム受理ではない。
- `inspect s` は同じsource startから個別に到達可能。`inspect before` と `inspect after`
  が相互に旧Stepで接続される条件はない。
- `roots s` の各rootを Generated として導出していない。
- `plans s root` を実candidate inspectionから構成したわけではなく、Frame/Preparedや
  current context等号も自動ではない。
- 一つのfixed Planとownerを解釈の基準にしている。全sourceの異なるowner/declarationを
  一つのそのPlanで扱ったとは主張できない。
- LayoutCompatibleは翻訳dataを固定し、BaseCompatibleはbaseモデルにおけるbinder/center値
  の同値を要求する。これらはsource pool有限性の帰結ではない。
- 成功は実行条件であり、全プログラムのchecked成功やSATの証明ではない。

ここをhidden仮定で埋めず、次のcompiler構成で一つずつ供給する必要がある。

## 2. 複数ownerへ向かう表現の分解

`GeneralNominalSourceOwnerCandidates252.mixed_finite_owners` は実source Initialから有限な
(root identity,declaration id)列を与える。ただし、到達state・Generated focus・Installable・
未Committedという実installation条件が付く。任意root/任意Planまでそのまま拡張しない。

`GeneralNominalOwnerCandidates252.owners` はPaterson lineage frontier×有限declaration。
このpairを `GeneralNominalIdentities.pair` でtable ownerとして符号化する案なら、現在の
`RequestBodyKeys260.key_identity` のowner injectivityを使える。ownerを単にdeclaration id
だけにすると、異なるrootの同じ宣言を誤って同一tableにするため不適切。

終盤の `Audit/Cycle262OwnerProbe.lean` で次のowner provenanceをkernel検証した（さらに§5の二補題も検証）:

- 任意Plan/owner/output列のStableClass factsには、そのownerのkey provenanceがある。
- 一つのfactが二ownerに由来すればownerは同じ。
- 異なるownerの任意tablesはfactを共有しない。
- 別ownerに由来するfactについて、あるownerのStableClass.Holdsはvacuousに成立する。

これは複数owner tableの局所独立性である。複数owner scheduler・sourceへのowner対応・
Plan代表の選択・model意味の全体合成はまだ定義していない。次は有限ownersと
`representative : owner → Plan` のtable unionを定義し、上記分離から全owner Effectsとの
iffを証明してから、新observerのselectionにownerを含めるのがよい。

`OwnerExecution250.public_execution_iff` はprivate slot reserve/runとpublic model射影を
接続するが、SafeOrder/oldPrivate/Permittedなどが明示前提。これを今回のsource observerと
取り違えない。必要なら次に新finite-stateとこのFrameの対応relationを独立に定義する。

## 3. BaseCompatible の実source由来をどう縮めるか

今回のSemantic Compatibleは全binder名と全default center位置を比較する。これは正しいが
強い十分条件であり、実associated bodyが読まない名前まで本来は比較する必要はない。

既存 `GeneralDictionaryDefaultExpression209.value_equivalent` はexpression.namesに入る
名前だけの意味同値で足りる。`DefaultBodyTransport209.actual_equivalent` もactual-modeだけ
のこの局所版を既に持つ。次はbodyごとにsupport-scoped条件を使うとよい。

実宣言の `Declaration.Scoped` が保証するのは **normalized RHS** の変数がinputNames又は
outputNamesに入ることだけである。19:18の追加読取りで重要な既存回帰を確認した:
`GeneralDictionaryDefault214ActualShadowRegression` の `declaration_scoped`, `translation`,
`raw_dependency`, `normalized_absent`, `not_raw_scope`。同名record fieldの隠れた枝に77が
残ると、翻訳されたraw Expr.namesは77を読むがnormalized RHSの変数には77がない。
したがって「翻訳後Expr.names ⊆ normalized RHS.variables」を次の補題にする案は誤りで、
採用しない。これは既存214の補助support回帰の再発見であり、新しい言語反例ではない。

正しい再利用先は `GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized`
（compiled total式とnormalized patternの**意味同値**）と
`GeneralNominalCenteredHeadMatSemanticSubstitution.eval_congr` である。
`GeneralDictionaryHistoricalBody227.explicit_value_equivalent` は既にこの方法を実装し、
同じPlan・異なるassignmentのもとでFinished、両head SchemaHolds、headRootsとoutput binder
のAgreeから、全名のbinder一致を要求せずbody意味同値を証明している。
`registered_body_iff` は旧208境界のregistered pathと両ModelsからFinished/head条件を供給する。
新262が必要とするのは**異なるPlan・同じassignment**への移植であり、この旧境界の定理を
そのまま新source observerの証明と呼んではいけない。

`GeneralNominalVersionedEffects231.body_holds_iff` はversioned bodyと旧bodyの意味を既に
接続している。これは再利用できるが、異なるPlanの比較やsource baseのhead保存までは
供給しない。raw式から隠れた変数を消して定義を変える必要はない。

inputNamesに対しては `GeneralNominalHeadSchemaSemantic186.binder_same` が既にある。
ただし同declaration/context constructors/interpretation、semantic center agreement、
両Planのhead SchemaHolds、headInspectionのFinishedを要求する。これはsource到達だけから
出る無条件binder同値ではない。source Modelsから新boundaryのbaseにこれらの前提を保存する
橋が要る。outputNamesは同seed/root/declarationから実purpose2 allocationが一致する
`GeneralRebaseBinderShape262.outputs` を使える。

defaultは位置つきcenter lookupなので、center列の単なる集合一致や並べ替えでは足りない。
今回のsemantic条件はgetD0のfallbackまで同じ位置で比較しており、次の弱化でも維持する。

## 4. Evidence側へ勝手に飛ばない

`DefaultSemanticTerminal213.terminal_replay` はterminal declarationで既存packetを運べるが、
current raw Models、Ordinary、ProjectionModels、capture Fits、head/schema等の前提が必要。
新rebaseのoutput ClassEffectsを証明しただけではこれらを供給できない。
同じことは非terminal childrenとmixed-time Evidenceにも当てはまる。

優先順候補:
1. source由来の有限ownerとtable合成、実selected owner/root/Planを構成する小さいobserver。
2. 読まれるbody変数だけのsemantic transportを、実head証明とsource baseから供給。
3. new state↔source Frameの独立relation、step simulation、packet/Permitted/EvidenceNode。

新しい言語意味の選択は発生していない。これらは実装と証明の義務で、承認で消せる数学的
仮定ではない。既知239旧Stepループは新rebaseの仕事全体を止める理由には使わない。

## 5. 次周のmulti-owner top-level型を先に固定する（未実装）

有限`owners : List Nat`、`representative : Nat → Plan roles`、source由来の同じ
`pool : List Output`から、各ownerのStableClass factsをflatMapした`basis`を作る案。
`Meaning assignment fact := ∀ owner ∈ owners, StableClass.Holds (representative owner)
owner assignment fact`とする。OwnerProbe.foreign_holdsにより、あるownerのtableにあるfactは
異なるownerの意味に新条件を課さない。`OwnerProbe.combined_holds`で、owner membershipと
factのowner provenanceから、この全owner解釈が当該owner解釈とiffであることも検証した。同じownerがlistで重複しても代表Planは同じ関数で
取るので、意味は重複するだけ。ただし有限stateの残りlist長の上界には重複も数える。

この設計なら期待する有限write上界は
`owners.length * (pool.length + pool.length * pool.length)`。
根拠は各tableの既存`QuadraticBudget262.facts_bound`とflatMap長の和であり、compiler時間の
上界ではない。19:20にOwnerProbe.tables_boundとしてこの**table長**の積の上界だけをLean証明した。
multi-owner state/Stepを定義していないため、multi-owner実行のwrite上界まで証明したとはしない。

各選択を`(owner, root, observedPlan)`として保持し、以下を別々に供給する:
- ownerが有限ownersにある（実source installation由来のmembership）。
- observedPlanのLayoutがrepresentative ownerと一致する。
- baseモデルの範囲で、そのownerのrepresentativeとobservedPlanが意味的にcompatible。
- そのrootの実requestがpoolに入り、選択されたbody checkが成功する。

ownerを選べばsourceの実候補が見つかるとは仮定しない。`representative`を未構成の任意関数に
したままsource compiler完成と呼ぶこともできない。異なるownerに異なるdeclarationを許す
表の合成と、actual sourceから各representativeを構成する証明は分離して進める。

## 6. 終盤のnormalized cross-Plan probe（19:22、検証済み）

§3の正しい経路を `Audit/Cycle262NormalizedProbe.lean` の二補題で実際に試した。
任意の二Plan first/last、同じassignment、Layout一致、任意explicit equationについて、
normalized RHSに現れる名前だけのactual binder値がEquivalentなら:
- compileBodyが成功する同じexpressionの評価値はEquivalent (`explicit_value`)。
- 同じtargetに対するversioned explicit BodyHoldsはiff (`explicit_body`)。

`compiled_normalized`でraw total式からnormalized patternの意味へ移り、`eval_congr`で
必要な名前だけを運び、versioned body_holds_iffで戻した。raw式の意味や構文は変更していない。
compile失敗時は既存empty schemaの両辺が一致するだけで、Readyや受理を保証する結果ではない。

これで「異なるPlan・同じassignment」のsupport-scoped body補題の型はkernelで通った。
ただしこれはprobe二補題であり、28 production modulesの205/412宣言数には含めない。
全ClassEffectsの置換、選択された宣言のScopedからbinder条件を導く橋、source baseのhead保存、
default centers、owner schedulerへの組込みは引き続き未完である。
