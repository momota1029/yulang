# 境界入力の台帳: 実ソースに戻すための第一〜五巡

状態: Draft。日付: 2026-11-10。根拠: integration `434d3ceef` の I-13、
cycle69 の未公開ソース `94cf57484`。対象は B4 の現在の source/capture 経路、
その graph adapter、関連型 annotation を受け取る既存の診断経路、Main の外側境界。

**I-13 は部分達成。** cycle62〜69 の8モジュールの実入口・補助入口・証明前提を
読み、これらの入力を下に列挙した。旧い graph / annotation 経路も列挙したが、
全 `lean/Yulang/` の全モデルを網羅したとは主張しない。H節でcycle71の追加照合と機械的inventoryを、J節でcycle73のDynamicIndex境界、K節でcycle74の区間候補・有限展開を、L節でcycle75のgraph読出し/候補制約を記録した。
残る未列挙経路はI節。定理を増やさず、意味論も変更しない。

## 先に分かったこと

1. 「source」と呼ばれていたものは少なくとも四種類ある。ambient endpoint 名、
   ordinary type/row slot、局所 binder の需要名、解決 invocation のアドレスである。
   同じ `Nat` でも相互に置き換えられない。
2. cycle69 の公開入口が導くのは有限 visit 列内の numeric identity。
   root の実ソース由来、visit の到達可能性、全義務の網羅性は入力のまま。
   実 children が空の親の「999番目の子」を名乗る visit でも `follow` は成功する。
   これは定理の誤りではなく、未接続の生成橋の具体例である。
3. 任意の補助 table と公開入口が計算した table を混同できない。
   `compile []` は異なる invocation を両方0へ写す。`compiled_identity` は
   二つの visit が対象列に属する前提を持ち、`follow` は実際に全入力列から
   table を作るので、この反例はその定理を破らない。
4. 非線形 head の同名 binder は仕様6.2に既に根拠がある。
   `supported` が Nodup を要求するのは実装断片の制限であり、言語の拒否ではない。
   普通の where-only 変数は6.3の出現回数条件が既に排除する。
   関連型の糖衣が導入する変数と、その条件の数え方は別に調べる必要がある。
5. `follow_models_exact` の一つの共有 valuation は結論で存在量化される。
   caller が実行時に witness を選んで渡す、という未達ではない。
   一方 `slots`、source 側の宣言/goal、有限 visit 列は実行入力である。
6. caller が与えた全候補を一つの trace に並べ、全制約を無条件に連言にして
   言語 resolver とみなしてはならない。既存の候補 guard / ancestor correlation
   の問題を再導入する。cycle23/24の質問ノートと既存の path-local annotation
   経路を参照し、候補選択の意味をこの台帳で新しく決めない。

## 表の読み方と仕様の判定

- **確定・実装未接続**: 利用者から見える意味は spec が指定している。
  データ構造の選択と意味保存を実装側で示す。新たな言語規則は質問しない。
- **表現の自由・証明が必要**: spec/06-roles.md 冒頭は解決アルゴリズムを
  Lean 側に置く。slot番号、table順、graph storage、worklist順を spec が
  定めないこと自体は仕様の穴ではない。外部の結果に影響しない証明が必要。
- **要確認**: 利用者から見える共有範囲や宣言の受理範囲が変わり得て、
  既存の確定事項だけでは今回その橋を閉じられなかった箇所。
  個別の質問ノートを作り、遅延案を先頭に置く。

型の略記: `D α = CommonRoleSourceIntervalBatches.Demand α = Nat × Argument α`、
`A α = α → Core.PresenceGeneration.Comp Common.model`。
ここで `Argument α` は ordinary `TyTerm` の下端/上端対。
`G = CommonRoleIntervalPaterson.Goal`、
`Decl = CommonRoleStablePaterson.Declaration`、
`B = CommonRoleIntervalCapture.Bindings = List (Nat × (Form × Form))`。
以下の短いモジュール名はすべて `Yulang.` の下にある。

## A. cycle62〜69: 実行入力と局所前提

### A1. CommonRoleSourceIntervalBatches

| 名前と型 | 使う入口・定理 | 実ソースからの導出と仕様 |
|---|---|---|
| `initial : List (D α)`、`batches : List (List (D α))` | `run_exact`, `run_order_independent` | 元制約と実生成の各差分から作る。今は任意有限列。6.3の共有型変数・更新安定化に対応するが、全差分を生成して停止する橋は無い。確定・実装未接続。 |
| 需要の `Nat` source 名、下端/上端の `TyTerm α` | `generate_exact`, `step_exact` | lexical binder/義務の解決済み同一性と ordinary 生成から導く。同名文字列や同じ型の値から名を付けない。6.2の名前つき変数、6.3の普通の型変数と等式。番号は表現の自由。 |
| `assignment : A α` | `generate_exact`, `run_exact` | 独立意味論を全 assignment で検証する量化変数。実行に渡す oracle ではない。 |
| `state : State α` と `invariant : All … state.atoms ↔ Models … state.requests` | `advance_exact` | 任意 state の補助前提。`run_exact` は `start initial` からこの invariant を構成する。公開入口の追加条件ではない。 |
| `n : Nat`, `existing : List (Atom (Fin n))` | `compile_run_exact`, `compiled_reflects` | source ordinary 生成から有限 slot数と既存制約を導く。既存 atoms を捨てず連言する。6.3の既存制約との整合。 |
| `rows : Fin n → Common.Row`, graph `values`, graph-model 証明 | `compiled_reflects` | 任意の compiled model を反映する定理の量化/前提。graph はここでは compiler が作るので任意 graph 入力ではない。一般 ordinary solver 完全性は別。 |

### A2. CommonRoleCaptureBatchModels

| 名前と型 | 使う入口・定理 | 実ソースからの導出と仕様 |
|---|---|---|
| `Job.declaration : Decl` | `capture_job_exact`, `run_satisfiable_exact` | 可視 impl を正規化して role/key/head/requirements を作る。6.2の根呼出し側の可視性、6.3の where。parserからの変換は未証明。 |
| `Job.goal : G` | 同上、`compile_returned_exact` | source obligation と ordinary state から role と区間引数を導く。型が未知でも単一 impl から勝手に決めない（6.3）。 |
| `Job.source : Nat → Nat` | `demands_fits`, `run_satisfiable_exact` | local binderから共有需要名への写像。scope/instantiationを考慮して構成する。6.2の名前共有、6.3の共有変数。再訪寿命は Q1。 |
| `slots : Nat → α`（compile時 `Nat → Fin n`） | `demands`, `run_satisfiable_exact`, `compile_returned_exact` | Formのambient名から既存ordinary slotへの写像。source mapとは別。有限支持上で名解決とtype/rowの対応を証明し、支持外は観測されないことを示す。番号は表現の自由。 |
| `old : List (D α)`, `jobs : List Job` | `run_satisfiable_exact` | 前状態と有限選択列。root/候補の選択・全義務の網羅性は導かない。6.2/6.3との橋が必要。 |
| `bindings : B`, `Captured slots jobs batches` | `capture_fits`, `run_models_exact` | 補助の独立 capture derivation。公開 `run_satisfiable_exact` は実行成功と独立capture境界を iff で扱い、callerに成功を要求しない。 |
| `assignment`, `values : Nat → Common.Ty`、returned/model証明 | `demands_fits`, `returned_models_exact`, `compiled_reflects` | 数学的量化/局所前提。公開の共有 values は存在結論。source map を構成したという意味にはならない。 |

### A3. CommonRoleWhereSourceModels

| 名前と型 | 使う入口・定理 | 実ソースからの導出と仕様 |
|---|---|---|
| `slots`, `old`, `declaration : Decl`, `goal : G`, `source : Nat → Nat` | `run_exact`, `returned_sources` | A2と同じ5入力。実 inspect と expand は内部で呼ぶが、registryの可視性/候補選択/associated feedbackは外側。6.2/6.3。 |
| `Decl.requirements : List (Nat × List Form)` | `accepted_where_fits`, `expanded_member_fits` | 元whereと関連型糖衣の生成子から作る。順序と重複を保持する。6.3の連言と順序独立。糖衣の検査は Q2。 |
| `bindings : B`, `accepted : Accepts declaration goal bindings` | `generated_models_exact`, `accepted_where_fits` | 独立なlinear structural scannerの境界。`run_exact`では結論側にある。非線形head、join、未束縛whereを言語拒否としない。 |
| `ambient`, `locals : Nat → Common.Ty` | `instantiated_fits`, `accepted_where_fits` | 任意の意味論的割当。generated childのrole辞書の存在ではなく、元templateが区間に入ることを示す。 |
| substitutionの全域fallback | `total`, `accepted_child_sources`が依存 | 実 captureのbound検査から、必要な名前でfallbackが使われないと証明する。未捕捉名をfallbackで言語上の型に決めない。 |

### A4. CommonRoleWhereSourceAllocation

| 名前と型 | 使う入口・定理 | 実ソースからの導出と仕様 |
|---|---|---|
| `slots`, `old`, `declaration`, `goal`, `bindingSource : Nat → Nat` | `prepare_conservative`, `prepare_exact`, `prepared_allocation` | A3の入力を継承。`parentTable goal`とchild endpointのowner列は計算済み。元goalのsource正しさは未接続。 |
| `table`, `names : List Nat`, `owners : List (Fin table.length)`、`locate … = some owners` | `locate_exact`, `ownerAt_canonical`, `allocated_snapshot` | 任意tableの補助入口。公開prepareはparent/childのsyntaxからtableとownersを作る。6.2/6.3、番号は表現の自由。 |
| `graph : Graph (parentTable goal).length`, `role : Nat`, `visible : List VisibleHead` | `returned_allocation`, `prepared_allocation` | 任意graphのsnapshot保存。graphのordinary-state adequacyやvisibleのsource可視性は前提にも結論にも無い。6.2/6.3とK2へ接続が必要。 |

### A5. CommonRoleRecursiveSourceAllocation

| 名前と型 | 使う入口・定理 | 実ソースからの導出と仕様 |
|---|---|---|
| `slots`, `root : G`, `goal : G`, `history : History slots root goal` | `history_included`, `history_allocation` | Historyの各edgeは実capture成功と実child所属を持つ有限帰納証明。有限endpoint名の起源は示すが、全goal/全訪問が有限とは示さない。6.3のPaterson/K2への接続が必要。 |
| `History.step` の `old`, `declaration`, `bindingSource`, `result`, returned/child-member証明 | 同上 | edgeごとに異なる入力を許す。連続するordinary state同士の整合や全兄弟網羅は要求しない。実driverから正しいHistoryを生成する橋が必要。 |
| `Instruction.declaration : Decl`, `.bindingSource : Nat → Nat`, `.childIndex : Nat` | `next_history`, `follow_history` | 一つの選択済みpathを外から指示する。childIndexは実child位置から導くべき。6.3の全where連言を一経路だけで置換しない。 |
| `Cursor.goal : G`, `.requests : List (D α)`, `instructions : List Instruction` | `follow_history` | 初期goal/旧需要と有限path列。全候補探索・再訪・停止は含まない。 |
| `table : List Nat`, `graph`, `role`, `visible`, lookup証明 | `prepareAt_exact`, `history_allocation`, `owner_identity_exact` | source tableは公開history入口ではrootから計算。graph/readoutのadequacyはA4と同じく未接続。 |

### A6. CommonRoleFreshCaptureSources

| 名前と型 | 使う入口・定理 | 実ソースからの導出と仕様 |
|---|---|---|
| `slots`, `old`, `declaration`, `goal` | `run_exact`, `generated_fresh` | local source mapを`boundary old + binder`で計算する。ambient slot mapは未解決のまま。 |
| `Instruction.declaration`, `.childIndex`, `Cursor`, 有限`instructions` | `follow_models_exact`, `follow_history` | cycle66のpathからbinder-map入力だけを除いたもの。実生成の全仕事を列挙したとは言えない。 |
| `root`, `History`, returned証明 | `history_owners` | root domainとの接続には既存の実履歴前提が残る。 |
| `previous`, `locals : Nat → Common.Ty`, `assignment : A α` | `extend_shared`, `generated_models_exact` | 数学的witness。freshnessは計算済みだが、同じinvocation再訪でもfreshになるのでQ1の寿命/意味保存が必要。 |

### A7. CommonRoleRegisteredCaptureSources

| 名前と型 | 使う入口・定理 | 実ソースからの導出と仕様 |
|---|---|---|
| `invocation : Nat` と `Visit.invocation : Nat` | `run_exact`, `follow_models_exact` | callerが共有キーを選ぶ。同じinvocationとbinderを再利用し、別キーは分離する。sourceからの導出はcycle69で部分置換。Q1。 |
| `State.boundary : Nat`, `.table : List (Nat × Nat)`, `.requests : List (D α)` | `run_exact`, `follow_shared_exact` | helperは任意Stateを受ける。`follow_models_exact`は`start old`から始め、境界を旧需要最大値より上に構成。任意Stateでfreshnessが成立するとは言わない。 |
| `Visit.declaration : Decl`, `.goal : G`, `visits : List Visit` | `follow_models_exact` | 各visitのcaptureモデルを同時に満たす有限列。実reachable/選択済み/網羅的であるという保証は無い。 |
| `slots`, `old`, `bindings : B`、任意`table/keys : Table` | `generated_requests_exact`, `source_identity`, `register_old/new` | slots/oldはA2。bindingsは実inspectから導く。source identity補助はmember前提付き。 |
| `values`, `locals : (Nat × Nat) → Common.Ty`, `agrees` | `follow_shared_exact` | arbitrary-state補助の対応前提。最終 `follow_models_exact` は整合するvaluationを構成する。 |

### A8. CommonRoleAddressedCaptureModels

| 名前と型 | 使う入口・定理 | 実ソースからの導出と仕様 |
|---|---|---|
| `Address.root : Nat` | `follow_models_exact` | 元source義務のidentityをelaboratorが作る必要。別module/別instantiationの同じ数字を混ぜない。6.2/6.3、Q1。 |
| `Address.path : List (Decl × Nat)` | `child_address_exact`, `step_children`, `follow_models_exact` | 実`childAddress`は親宣言と元where位置を付けるが、Visitのcallerは任意pathも渡せる。到達可能性型/生成関係との接続が必要。 |
| `Invocation.declaration : Decl` | `compiled_identity`, `shared_models_exact` | 完全な宣言値を含む。異なるbodyの同numeric labelは区別するが、異なる可視implに同じ完全recordを与えるsource生成は依然禁止する必要がある。6.2は別ファイルの同head implの曖昧さを指定。source key生成の証明不足であり新しいcoherence規則ではない。 |
| `Visit.goal : G`, `visits : List Visit` | `follow_models_exact`, `follow_append`, `reorder_models` | finite traceは入力。順序独立は同一addressed visitsの順列で、元where順を書き換えた二プログラムの辞書同値ではない。6.3への橋が残る。 |
| `names : Table = List Invocation`, arbitrary registry `state` | `compile`, `step_no_new_failure`, `step_children` | helperはtable completenessを保証しない。public `follow`は`table visits`と`start old`を使う。member前提を消してhelperだけを外側に露出しない。 |
| `slots : Nat → α`, `old : List (D α)`, `assignment : A α` | `follow_models_exact` | slots/oldは未接続。assignmentは全モデル量化。共有localsは存在結論であって入力ではない。 |

## B. 共通のsource構文、graph、更新の境界

| モジュール | caller入力（型）と代表定理 | 導出の素案・仕様の状態 |
|---|---|---|
| `CommonRoleStablePaterson` | `Decl`の`role/key : Nat`, `head : List Form`, `requirements : List (Nat × List Form)`。`check_sound`は`check = true`。 | 可視implの構文・糖衣から作り、6.3の宣言検査を実行。keyを意味的型同値から作らない。Q2以外は確定・実装未接続。 |
| `CommonRoleIntervalPaterson` | `Goal.role`, `Goal.arguments : List (Form × Form)`, `Substitution = Nat → (Form × Form)`。`every_where_decreases`。 | ordinary区間と実captureから作る。既存Form文法は全Common型ではない。6.3の停止主張全体へ昇格しない。 |
| `CommonRoleIntervalCapture` / `CommonRoleIntervalCandidates` | 宣言/goal、bindings、`supported`, `namesBound`, `Accepts`。`capture_arguments_exact`, `inspect_accepts_exact`。 | Nodup headは局所grammar。6.2の同名変数を一般に拒否する根拠ではない。未捕捉where変数は6.3/Q2。 |
| `CommonRoleSourceIdentity` | `table : List Nat`, `state : State table.length`。`atoms_exact`, `extend_exact`。 | resolved source名からoccurrence tableを作る。同じsourceのtypeだけを同値化し、row成分まで共有したとは言わない。6.3とspec/05-effects.mdの効果を区別する。 |
| `CommonRoleSourceDescent` | table、`values : Slot table → Comp Common.model`, `fallback : Common.Ty`, `Coherent`。`descend_factors`。 | fallbackはtable外の名前用で、既存occurrenceでは観測されない。任意slotモデルの因子化の証明前提。新しい言語入力ではない。 |
| `CommonRoleDynamicIndexResidualBatches` | `Problem.seeds : List (Slot table)`, `.links : List (Slot table × Slot table)`, `.requests : List (Nat × Nat)`、有限`updates : List (Problem table)`。`advanceMany_models`。 | scalar注釈/同一性制約/関連型要求からloweringする必要。現状はpositive-str/equality断片。6.3の一般associated feedbackの導出ではない。 |
| `CommonRoleScalarSourceEndpoint` | `State n`, `Endpoint n`、`assignment`, models証明。`eval_sound`, `observe_exact`。 | stateからscalar読出しを計算。一般stateでunknownが意味的未決定であるとは言わない。ordinary完全性が必要。6.3の既知性に接続。 |
| `CommonRoleScalarSourceInspection` | table/Problem/updates、`role`, `visible : List VisibleHead`、source slot。`solve_inspect_string_exact`, `snapshot_unknown_exact`。 | graphはscalar stateから構成済み。visibleは6.2の可視implから作る必要。一般recursive graphへの意味保存は未達。 |
| `CommonRoleCanonicalSourceGraph` | table/Problem/updates、visible、role。`root_identity_exact`, `inspect_string_exact`。 | source名の等しさからcanonical rootを計算。型の値が同じことはsource identityではない。6.2/6.3、storage番号は表現の自由。 |
| `CommonRoleCanonicalSourceGrowth` | `table/extra : List Nat`、graph/観測値、割当/fallback。`newRoot_old_exact`, `newRoot_identity_exact`。 | 追加occurrenceのsource名からold-firstで割当。callerのextraが実生成かは別問題。6.3、番号は表現の自由。 |
| `CommonRoleRegularGraph` | `n : Nat`, `graph : Fin n → Node n`, root。`recursive_at_exact`。 | Nodeはunresolved/scalar/structural/nominal。ordinary正則型からnode/edgeを導く一般adequacyは無い。6.3と末尾K2の名つき/無名再帰の確定判断に従う。 |
| `CommonRoleAllocatedGraph` | table/extra、old graph、`fresh : Slot (table ++ extra) → Node (table ++ extra).length`。`path_exact`, `snapshot_allocated`。 | growは任意freshを受け、allocateは未解決nodeを使う。old-edge保存をsource生成・ordinary更新の意味保存と取り違えない。 |
| `CommonRoleChildSourceAllocation` | table、unary `registry : Registry`, `parent/child : SourceRequest n`, `graph`, role/visible、production/位置証明。`allocated_identity_exact`, `allocated_snapshot`。 | dependency ownerは計算済み。registry/root/graphが実ソース由来である橋は残る。6.3のPatersonに沿うunary/int断片。 |
| `CommonRoleClosureSourceAllocation` | table、unary registry/root、`Trace registry root child`、graph。`entries_exact`, `trace_allocated`。 | この断片では全structural child closureを計算する。一般Formのcycle69 traceと同じ型ではなく、結果をそのまま移せない。6.3/K2の一般化が必要。 |
| `CommonRoleAllocatedGraphUpdates` | `edits : List (Fin n × Node n)`, old graph/table/extra、Trace。`run_allocate`, `actual_history_updated_allocation`。 | 実ordinary solverの変更をold-node editsへloweringする証明が必要。任意有限edit列の可換性だけではsolver生成や停止を導かない。 |

## C. 関連型annotationの明示入力

`CommonRoleAssociatedStateFlow.Request n` は
`receiver : Roles.Goal`, `name : Nat`, `output : Fin n` を持つ。
`source_store_agrees` / `value_exact` はこの入力、`env : Roles.AssocEnv`、
`roles : Roles.RoleDecls`、`wf : Roles.WellFormed env.cores`を取る。
receiverを単一候補から推測してよい証明ではない。6.3の普通の型変数/等式から
receiver/name/outputを作るlowering、6.2の根呼出し側の可視性からenvを作る橋が必要。
int/str以外のRHS、未確定receiver、糖衣の新しい関連型参照はこの断片の外側。

次の共通入力束を **P** と略記する。型を省略するための呼び名であり、
どれかを証明済み入力と扱うものではない。

- `registry : CommonRoleOpenProducer.Registry`。中身は有限`declarations`、
  各宣言の`checked`証明、`Declaration.key`列の`Nodup`証明。
  6.2の可視implから生成する。Nodupはdecl identityの一意性でありcoherenceではない。
- `root : CommonRoleMaterializedDomain.SourceRequest n`。
  `role : Nat`、`lower/upper : Endpoint n`をsource義務から作る。
- `env : Roles.AssocEnv`, `roles : Roles.RoleDecls`,
  `wf : Roles.WellFormed env.cores`。declarative版では
  `awf : Roles.AssocWellFormed env roles`も必要。宣言検査から構成する。
- `annotations : CommonRoleCorrelatedPaths.Route registry root →
  CommonRoleSettledSyntax.Declaration → List (CommonRoleAssociatedStateFlow.Request n)`。
  full ancestor/candidate pathを保った実associated RHS loweringから導く必要がある。
  6.3は等式の意味を与えるが、任意annotation関数の妥当性を認めない。Q2と既存Q23/24。
- `seed : CommonRoleSettledConstraints.State n`。既存ordinary source制約から導く。
  `assignment : Fin n → Comp Common.model`は全モデル量化で実行入力ではない。

| モジュール | P以外の入力・使う定理 | 残る境界 |
|---|---|---|
| `CommonRoleCorrelatedEquations` | `mask : History registry root → Node registry root → Declaration → Bool`, `observation : State n`。`activate_exact`, `view_exact`。 | 選択方針と観測状態はcaller入力。任意maskのlanguage妥当性はない。6.3の安定化と既存cycle24質問。 |
| `CommonRoleGlobalChoiceEquations` | `observation`, `table : CommonRoleGlobalChoices.Table registry root`, `Valid … table`。`infer_models_exact`。 | 有効tableの意味だけを扱う。sourceからannotation/choiceを導く必要。 |
| `CommonRoleStableGlobalChoices` | tableと`Stable`、`check_exact`, `search_exact`。 | table候補は有限に探索するがStableの存在は保証しない。 |
| `CommonRoleStableGlobalModels` | table/Stable、`infer_models_exact`, `infer_declarative_models_exact`。 | 共有モデルiff。source境界の入力はPのまま。 |
| `CommonRoleNormalizedGlobalChoices` | table、`infer_models_exact`。 | scalar正規化は計算するがPをsourceから導かない。 |
| `CommonRoleDirectedGlobalChoices` | table/Stable、`infer_models_exact`, `searched_tree_complete`。 | 方向つきbound closureとself-output検査。全言語飽和/存在ではない。 |
| `CommonRoleStructuralGlobalChoices` | table/Stable、`infer_models_exact`。 | structural正規化でもPが残る。 |
| `CommonRoleConflictFilteredInference` | `infer_models_exact`, `empty_excludes_stable_model`。 | scalar矛盾を除く。空の診断探索をlanguage rejectedとしない。 |
| `CommonRoleStructuralFilteredInference` | `infer_models_exact`。 | structural矛盾除去、入力Pは不変。 |
| `CommonRolePathFilteredInference` | `infer_models_exact`。 | path矛盾除去、入力Pは不変。 |
| `CommonRoleRecursiveFilteredInference` | `infer_models_exact`。 | recursive構造の矛盾除去、入力Pは不変。 |
| `CommonRoleDecomposedInference` | `infer_models_exact`。 | 分解した反証によるprune、入力Pは不変。 |
| `CommonRoleSaturatedStructuralInference` | `infer_models_exact`。 | structural反証closure。名前にsaturatedがあってもB4生成・停止の橋ではない。 |
| `CommonRoleScalarStructuralAbsorption` | table、models前提を持つ観測定理、`self_output_models_pre/post`。 | scalar/structural passの吸収。一般iterationの停止ではない。 |
| `CommonRoleDiagnosticTree` | registry/root、table、observation、`build`の`Nat`深さとRoute、`diagnose_visit_exact`, `searched_tree_models`。 | public `diagnose`はcarrierから深さを計算。helperの任意深さを全体停止証明としない。Pを用いたtreeでもannotation由来は未証明。 |
| `CommonRoleDiagnosticCanonical` | registry/root、二table/二Stateとactive/membership同値、P。`output_membership`, `diagnose_eq`。 | 同じ有効義務集合に対する列挙差を消す。別where source順の辞書観察同値は未接続。 |

この節の仕様根拠は6.2（根呼出し側の可視性、別候補は別証拠）と6.3
（関連型は普通の変数/等式、兄弟連言、安定後の最終化）。Pを任意関数で
与えて得たiffを、実ソースのB4 iffと呼ばない。既存の
`2026-11-09-cycle23-support-fixedpoint.md` と
`2026-11-09-cycle24-candidate-guard-policy.md` を再利用し、同じ問いを増やさない。

## D. Main.B4Target の最外境界

`Main.lean` の `Vocabulary` は `Registry/State/Demand/Model : Type u`。
現在の各断片のcarrierを結び、実sourceに対応する一つのinstanceにする必要がある。
`SourceBoundary` の全13入力を次の通り監査した。単に定義可能であることと、
実sourceに忠実であることは別である。

| フィールド（型） | 使うtarget | 導出・仕様 |
|---|---|---|
| `Checked : Registry → Prop` | 全5項 | 可視宣言のPaterson/K2関連条件、HeadDeterminesAssociated。6.2/6.3、Q2。 |
| `Models : State → Model → Prop` | `SaturationTotal`, `DictionarySound` | ordinary source制約/共有graphの独立意味。6.3。 |
| `Step : Registry → Demand → State → State → Prop` | `SaturationTotal` | 実ordinary更新と再生成の進行。任意rank/fuelを定義して終わらない。6.3。 |
| `Stable : Registry → State → Demand → Prop` | `SaturationTotal` | 兄弟/親再生成が意味を変えない閉包。6.3。 |
| `Generated : Registry → State → Demand → Demand → Prop` | `SaturationTotal` | 実where/糖衣childの関係。有限trace入力では代用しない。6.3。 |
| `RootPending`, `RootK2`, `CandidateK2`, `InspectionPending : Registry → State → Demand → Prop` | `Exact`, `NoFalseRejection` | ordinary既知性と実graph検査から導く。6.3とK2の到達/構造inspection時拒否。 |
| `Survivor : Registry → State → Demand → Nat → List Demand → Prop` | `Exact` | 実可視候補と全子。最終child失敗の分類は既存質問の回答どおり診断treeに保持。 |
| `Evidence : Registry → State → Model → Demand → Dictionary → Prop` | `DictionarySound` | 元head/全whereに対する独立証拠。6.2/6.3。 |
| `Reorders : Registry → Registry → Prop` | `OrderIndependent` | visible/whereの順序だけの変更。source obligation対応を保つ。6.3。 |
| `DictionaryEquivalent : Dictionary → Dictionary → Prop` | `OrderIndependent` | 2026-11-08-cycle4質問の2026-11-09回答: 遅延、正規source義務順の方向。未承認の単純multiset化をしない。 |

`Executor.run : Registry → State → Demand → State × Result` もcallerから渡す未接続入力。
`Main.B4Statement boundary executor` は上記の停止/閉包、四方向exactness、順序独立、
辞書健全性、偽拒否なしの**目標Prop**。その引数を作ることと証明することを分ける。
source instanceは未完成であり、この台帳はその未完成を減らすための調査である。

## E. 仕様照合と質問

### 既に答えがあり、新しい拒否規則にしてはいけないもの

- 同じhead内の同名変数: spec6.2の `_` との対比が根拠。
  `impl R ('a, 'a)` をscannerのNodupの都合で拒否してはならない。
  raw captureは重複bindingを返せるが、where付きscannerへの一般接続が未達。
- headにも関連等式にも出ない普通のwhere変数:
  `impl Parent (box 'a) where Child 'b` は6.3の出現回数が
  `'b`について0→1となる。新しい未決定の言語機能として扱わない。
- 構文が同じでも別の可視impl: spec6.2はcoherenceを課さず、両方見えると曖昧。
  source identityを値の等しさから付けず、実宣言のoriginを保持する。
- 行番号/slot番号/graph storage順: spec6冒頭がアルゴリズムをLean側に置く。
  任意に意味を変える許可ではないが、番号の形式自体を新しい意味論として質問しない。

### 新しい質問ノート

1. [Q1: 再訪時の局所binder共有の境界](../questions/2026-11-10-cycle70-invocation-sharing-boundary.md)。
   実sourceへのadequacyを証明するまで、fresh版/永続版のどちらも全体の代わりにしない。
2. [Q2: 関連型糖衣と宣言検査の数え方](../questions/2026-11-10-cycle70-associated-sugar-checking.md)。
   普通のwhere-only変数の拒否と、関連型の等式で決まる生成変数を区別する。

両方ともYulang例は仕様照合用の概形で、parser/実機での受理を主張しない。
新しい言語意味論は採用していない。

## F. 追加で照合した旧経路

| モジュール | caller入力（型）と代表定理 | 導出の素案・仕様の状態 |
|---|---|---|
| `CommonRoleSourceWorklist` | unary `registry : Registry`, `root : SourceRequest n`, `s : State n`、有限closureのsubtype `Node registry root`。`saturate_exact`, `saturate_actual_closed`。 | 一つの固定ordinary stateでfirst-hit productionの到達可能性を計算する。有限domainは計算済みだがstate変更/全候補選択の橋ではない。6.3の兄弟安定化が残る。 |
| `CommonRoleCorrelatedPaths` | registry/root、`mask : History registry root → Node registry root → Declaration → Bool`, `observation : State n`, `Route = History × Node`。helper `pathsUpTo`は`fuel : Nat`、public `collect`はrootからboundを計算。`collect_exact`, `path_measure`。 | mask/observationはC節と同じ未接続入力。Historyはparent/candidateを保持するが同一tripleの重複where位置を区別しない。cycle69のAddressへの対応には重複位置を保存する橋が必要。6.3の連言、既存の辞書同値回答。 |
| `CommonRoleGlobalChoices` | registry/root、`observation : State n`, `table : List (Route × Declaration)`、`Valid`証明。`search_exact`, `siblings_closed`。 | public searchは候補tableを計算する。Validは全到達routeが一つの候補を持つ強い診断certificate。存在や一般のpending/ambiguous処理は保証しない。6.2/6.3をこれで置換しない。 |
| `CommonRoleGraphInspection` | `graph : Fin n → Node n`, `Pattern`, root `Fin n`, `role : Nat`, `visible : List VisibleHead`。`VisibleHead`はrole/key/pattern、`Captures = List (Nat × Fin n)`。`inspect_visible_exact`, `inspect_all_visible_exact`, `snapshot_unknown_exact`。 | pattern/visibleを6.2の可視宣言、graphをordinary正則型から生成する。graph読出しと実source型のK2/knownnessの一般adequacyは未証明。captureのNatはpattern binderでありsource名ではない。 |
| `CommonPresenceConstraintGraph` | `atoms : List (Atom (Fin m))`、`assignment : Fin m → Comp Common.model`、反映方向でrows/values/model証明。補助には`Pool m`, term-membership証明。`compile_atoms_exact`, `compile_atoms_reflects`。 | public compileはatomからpoolとgraphを生成する。A節のordinary atomへのsource loweringを証明する必要。生成graphは`CommonRoleRegularGraph.Graph`と異なる型であり、同じ「graph」という語だけで接続しない。 |
| `CommonRoleOutermostResolver` | `Request : Type u`, `Protocol.frontier : Request → Frontier Request`, `.Local : Request → Frontier Request → Prop`, `exact : FrontierExact protocol`, `accessible : Acc (Child protocol.Local) request`。`resolve_tree_exact_of_frontier_exact`。 | 明示的な二つの未証明橋を持つ条件付き外側定理。sourceからLocal/producerを作り、Paterson/K2からAccを導く必要。子は更新stateを兄弟へ返さないため、source飽和の完成として使わない。6.3と既存classification-boundary回答に従う。 |

この照合で、annotation経路の`Route`とcycle69の`Address`は同じidentity型ではなく、
旧Routeが区別しない重複where位置を新Addressは区別することも分かった。
二つの経路をつなぐ際、単に`Nat`へ変換して同じキーとみなしてはいけない。

## G. 次の照合範囲とB4の残り

I-13全体の完了には、上の列挙と `Main/Audit` の全関連依存を機械的に照合し、
未列挙の旧source/graph/resolver adapterを同じ粒度で監査する必要がある。
F節の六経路は今回追加で照合したが、そこから全推移importに漏れが無いことまで
監査したわけではない。`CommonRoleCorrelatedCarrier`とguarded候補の生成、
source-specific Protocol instance、ordinary-stateとgraphの変換は
cycle71のH節で追加照合した。ただし全推移importの入力監査は未完了。
この未監査分を「入力が無い」とは扱わない。追加質問は既存ノートとの重複を確認する。

B4の主要橋は5本のまま:
`source_boundary_adequate`, `generated_work_closed`,
`saturate_terminates_and_closes`, `saturated_frontier_exact`,
`resolve_dictionary_order_sound`。
今回の成果は、最初の橋で隠れていた入力と、既に仕様が答えている範囲を区別した台帳。
全体証明の完成、X13〜X16の外側入口、M1三つ組の完成ではない。


## H. cycle71: Protocol・guarded carrier・ordinary 境界の第二巡

根拠はlocal source `23170ca83`。この追記は実ソースの意味を決めるものではない。
**任意Protocolの二前提が残ることと、具体的なsettled断片では二前提を構成済みであることを区別する。**
また、有限carrier、現在activeな義務、過去に発行した更新、最終辞書は同じ集合ではない。
以下の`State`は `CommonRoleSettledConstraints.State n`、`SourceRequest`は
`CommonRoleMaterializedDomain.SourceRequest n`。`Registry`は
`CommonRoleSettledFrontier.Registry`。これらはA節の一般Form/interval型とは異なる。

### H1. 具体的Protocolとordinary state

| モジュール | caller入力の名前・型と依存する入口/定理 | 導出の素案・仕様と残る境界 |
|---|---|---|
| `CommonRoleSettledSyntax` | `Ty`（unknown/int/opaque named/unary wrap/一節点構造loop）、`Pattern`、`Template`。`Declaration.role/key : Nat`, `head : Pattern`, `requirements : List (Nat × Template)`。`checked_child_decreases`は宣言check・元requirement所属・`Inspect`証明を取る。 | 可視宣言と正規化済み型からlowering。6.2、6.3、K2の名つき/無名の区別に従う。multiple arguments、一般区間、関連型更新はこの型に含まれない。これらの欠落を言語拒否にしない。 |
| `CommonRoleSettledConstraints` | `State.atoms : List (PresenceNormalForm.Atom (Fin n))`、`child : PresenceGeneratedChildGrammar.GoodAtoms atoms`、`width : PresenceGeneratedWidth.WidthAtoms atoms`、`rows : PresenceSourceConstraintSupport.GoodAtoms atoms`。`generated_state_exact`はstate、`names : List Nat`、assignment、新しいpayloadを量化。 | ordinary生成からatomsと三つのgrammar証明を作る。全言語の任意stateを無条件に入れられない。`State.Models`は型のfieldではなくモデル存在命題。元ordinary slotとsettled payloadは分離される。6.3のsource共有への接続が必要。 |
| `CommonRoleSettledFrontier` | `Registry.declarations : List Declaration`、`checked : ∀ d ∈ declarations, d.check = true`、`identities : (declarations.map Declaration.key).Nodup`。`Request.role : Nat`, `lower : Option Ty`, `upper : Ty`, `settled : ∀ t, lower = some t → upper = t`, `state : State n`。`frontier_exact`は任意`visible : List Declaration`。 | Registryは6.2の根呼出し側の可視宣言と6.3の宣言checkから作る。identityの一意性は同head implを禁じるcoherenceではない。Requestのsettled証明はlower=upperの断片を明示し、一般の開区間は受け付けない。childrenは同じstateを保持する。 |
| `CommonRoleSettledResolver` | `registry : Registry`, `q : CommonRoleSettledFrontier.Request n`。`resolve_tree_exact`, `resolve_exact`。補助`where_state_recollection`は実child所属、assignment、`actualPayload : Comp Common.model`。 | `frontier_exact`と`accessible registry q`を内部で構成済み。**この断片のcallerにAccやfrontier exactnessを要求していない。** 6.3/K2のunary settled断片の局所健全性・完全性。関連型が共有stateを変える場合は断片外であり、一般B4の橋が閉じたという意味ではない。 |
| `CommonRoleOpenProducer` | `visible : List Declaration`, `q : CommonRoleOpenDescent.Request`（role/lower/upper）。`frontier_exact`, `scan_exact`。 | concrete Protocolと独立Localを作るが、ordinary stateを解かず端点を狭めない。visibleの実可視性は6.2から導く。単一候補から型を決める許可ではない（6.3）。 |
| `CommonRoleOpenProducerAccess` | `registry : Registry`, `q : Request`。`accessible`。origin補助はvisible、宣言、二payload、選択/scan成功証明。 | strict descentとAccはchecked宣言から導出済み。ここでもpublic runに外部のfuel/rank/Accを残していない。source生成の完全性とassociated feedbackは別。6.3/K2。 |
| `CommonRoleOpenPropagation` | `Allocation n = Ty → Fin n`、`visible : List Declaration`, `q : Request`, `s : State n`。`prepare_exact`, `produce_exact`。assignmentはモデル量化。 | allocateはcaller入力で、一般のsource occurrence allocatorではない。実sourceからslot対応と意味保存を作る必要。任意定数allocateも型が許し、異なるpayloadを同じslotへ送れる。局所定理はその明示mapに対するexactnessであり、source aliasingの正しさは前提外。6.2/6.3、Q1を再利用。 |
| `CommonRoleOpenRecursivePass` | `registry`, `allocate : Allocation n`, `q : Request`, `s : State n`。`run_exact`。低位`runAcc`だけは`Acc (Child (Local registry.declarations)) q`を取る。 | public runはAccを内部構成し、兄弟へ返却stateを渡して親/兄弟を再検査する。**一passのexactness**であり、再生成後の新しいchildをすべて処理する飽和の完成ではない。6.3の最終化とは分ける。 |
| `CommonRoleOpenPassStability` | `registry`, `allocate`, `q`, `s`, `assignment : Fin n → Comp Common.model`。`run_models_exact`, `run_semantically_idempotent`。低位`thread_models`は`worker : Request → State n → β × State n`、`property : Request → Prop`、各childのmodel iffを取る。 | public iffはGoodを結論側に置き、Goodの証明をcallerに要求しない。意味的冪等性は固定structural要求とmapに対するもの。6.3のstate依存source再生成や順序独立へそのまま昇格しない。 |
| `CommonRoleOpenClosureAllocation` | `registry`, `root : Request`, `s : State (table registry root).length`。`run_exact`, `run_models_exact`。`selected_prepare_exact`はreachable証明と`interpret : Ty → Comp Common.model`。lookup補助はtable所属。 | finite closureからTy値のtableを計算しallocateを除去済み。しかし**等しいTy値は同じslot**となり、別source occurrenceのidentityを作るものではない。interpretのsource適合性も未接続。6.2/6.3の普通の共有変数と混同しない。 |
| `CommonRolePotentialAllocation` | 同じregistry/root/interpret、加えて`visible : List Declaration`と`subset : ∀ d ∈ visible, d ∈ registry.declarations`。`filtered_prepare_exact`, `filtered_state_child_endpoints`。 | 任意候補部分列に耐えるtableを計算する。部分列を選ぶ言語方針は証明しない。source identityではなくTy値の有限表現。6.2の全可視候補、6.3の安定化との接続が残る。 |

### H2. State依存carrier、候補guard、関連型更新

| モジュール | caller入力の名前・型と依存する入口/定理 | 導出の素案・仕様と残る境界 |
|---|---|---|
| `CommonRoleOrdinaryKnownness` | `atoms : List (Atom (Fin n))`, `slot : Fin n`, `base : Inference.Base`。`detect_exists`, `materialize_sound`。後者はassignmentとAllモデル証明。`checked_exact`はstate、receiver/output slots。 | 検査対象は同slotの明示的な二方向base atoms。任意の意味的含意を完全に検出する定理ではない。encodeはint/strのみでbool/unitはnone。6.3の既知性をこのnoneだけから結論しない。一般ordinary entailmentとの橋が必要。 |
| `CommonRoleMaterializedDomain` | `Endpoint = fixed Ty / slot (Fin n) / wrap Constructor Endpoint`、`SourceRequest.role/lower/upper`、state、checked registry、有限sources。`domain_exact`, `materialized_child_present`。後者には実production、root/source所属など。 | slot読出しはintだけ。strがordinary側で既知でもEndpointではunknownとなる。variantsはlower/upperを独立に列挙し、同じslotでも不整合な組を含む**過大近似**。6.3のsource共有を弱めた言語ではなく、有限carrierを作る補助。新しいtemplate生成は対象外。 |
| `CommonRoleSourceTemplateClosure` | registry/root、補助のparent/child・membership、`Generated`または実production証明、`captureDepth d.head = some depth`、state。`closure_exact`, `actual_child_all_states`。 | closureとboundは宣言と元sourceから計算。capture位置を持つunary template断片で全future stateを覆うが、A節の一般Form/任意where引数への橋ではない。6.3のPatersonとordinary state変更をこの断片で結ぶ。 |
| `CommonRoleGuardedCandidates` | registry/root、`mask : SourceRequest n → Declaration → Bool`、`s : State n`。`collect_exact`, `collect_capacity`。candidate補助は宣言所属と実candidateNext所属。 | 各候補をsingletonで調べ、first-hitによる後続候補の消失を防ぐ。mask=falseはchildを落とせるため、callerが選んだmaskを言語可視候補の集合と呼ばない。6.2/6.3、既存cycle24質問を再利用。 |
| `CommonRoleGuardedEquations` | registry/root、`annotations : Node registry root → Declaration → List (CommonRoleAssociatedStateFlow.Request n)`、上のmask、observation、env/roles/wf、seed。`view_declarative_exact`はさらに`Roles.AssocWellFormed env roles`とassignment。 | entriesは有限source/candidate/annotationを計算するが、annotationそのものとbranch方針は入力。6.3のRHS等式からloweringすべき。任意maskの全active等式を連言にしても言語解ではない。ancestor相関を持つC節のRoute版と同一視しない。 |
| `CommonRoleCorrelatedCarrier` | registry/root。`path_retained`は`mask : History registry root → Node registry root → Declaration → Bool`、observation、Route、独立Path証明。helper pathsUpToはfuel。 | public carrierはsourceWeight rootから計算され、mask/observationを必要としない。全state/maskのactive ancestryを**含む**証明であり、carrierの全entryが同時にactiveとは言わない。実source completenessやcycle69 addressへの同一性は別。6.2/6.3。 |
| `CommonRoleFiniteFeedback` | registry/root、`k : Nat`, `decode : List (Fin k) → State n`, `emit : Node registry root → List (Fin k)`。`collect_closed`, `visits_exact`。低位loopはrules/fuel/seenとNodup/enough前提。 | public collectはfuel=k、seen=[]を構成。有限更新tokenを外から固定した境界で停止/最終閉包を示す。decodeの意味保存・emitの実RHS由来は未接続。非単調rulesも許し、過去tokenを消さないため、最終supportの最小解や順序独立は出ない。6.3、既存cycle23質問。 |
| `CommonRoleFeedbackTrace` | registry/root、同じdecode/emit、有限start/finish、`Trace`証明、factのfinish所属とstart非所属。`trace_origin`。 | Traceは実到達時点で発行したtokenの起源を証明。最終stateでそのsourceがなおactiveとは要求しない。source/reachabilityとtoken履歴の差は既存first-hit反例と整合。6.3の最終安定解との橋を残す。 |
| `CommonRoleAssociatedFeedback` | registry/root、`env : Roles.AssocEnv`, `roles : Roles.RoleDecls`, `wf : Roles.WellFormed env.cores`、`seed : State n`, `table : Fin k → Request n`, `emit : Node registry root → List (Fin k)`。`final_models`, `reachable_equation`, `final_visits_exact`。 | 任意decodeを実関連型batchで置換済み。table/emit、固定receiver/name/outputのsource由来は未接続。final_modelsのassignmentはモデル量化で実行oracleではない。6.2/6.3。 |
| `CommonRoleSourceAssociatedAdapter` | registry/root、`annotations : Node registry root → List (Request n)`、env/roles/wf、seed。`adapter_exact`, `reachable_equation`, `collected_source_origin`。 | table/emit/kをannotationsから計算して除去済み。annotation生成、固定receiverのadequacyは残る。candidate情報を持たないこの版をguarded/path相関版と取り違えない。6.3、Q2と既存cycle23/24質問。 |

### H3. Graphの小さい橋を「橋が全く無い」とも「一般接続済み」とも読まない

| モジュール | caller入力の名前・型と依存する入口/定理 | 導出の素案・仕様と残る境界 |
|---|---|---|
| `CommonRoleUnaryGraphBridge` | `source : UnaryGraph n = Fin n → Nat × Fin n`, node、depth、bisimilar=true証明。`common_observe`, `bisimilar_common`。 | 同じ有限unary variant graphからrole graphとCommon型を両方構成し、有限観測と同値を接続済み。任意ordinary solver graphからの逆変換ではない。6.3/K2の構造再帰に対応する局所adequacy。 |
| `CommonRoleRecordGraphBridge` | `source : RecordGraph n = Fin n → Nat × Fin n`、node/depth。`common_observe`。 | unary required-field graphの有限観測橋。多field・presence・open row・union・arrowを一般変換するものではない。spec4.3と6.3/K2。 |
| `CommonRoleSettledGraphBridge` | tag/label/name/depth等のNat、`lowerRepeatedTag`の`List (Nat × Nat)`。`variant_common_observations`, `record_common_observations`, `boxed_common_observations`, `named_body_opaque`。 | settled型の特定shapeを上二つの橋へ結ぶ。意味的depthは観測定理の量化変数で、languageの解決深さ制限ではない。6.3/K2。一般ordinary-state→RegularGraphはなお未接続。 |

### H4. 境界回帰の結果

cycle71の15検査と7入口の公理監査は `notes/handoff/dots-cycle-71.md` に
再現可能なLean本文とログを保存。新規production theoremは0。

- ordinary materializeはstrを返すが、旧Endpoint slotは同じstateをunknownと読む。
  boolにはさらにencodeの制限がある。いずれも既知性の一般否定ではない。
- 同じsource slotをlower/upperに持つRequestのvariantsは4通りで、unknown/intの
  異なる組も含む。これは有限carrierの過大近似であり、実evalの共有は失われていない。
- 任意Allocationはintと別のopaque named payloadを同じslotに送れる。
  同じ型の値と同じsource義務を同一視してよいという根拠にはならない。
- 同じchecked registry/stateでmaskを変えると、guarded childの有無が変わる。
  candidate carrierの保持とlanguage selectionの正しさを別々に監査する必要がある。
- 2tokenの非単調rulesでは最終列[1,0]に、最終rulesでは発行されない0が残る。
  `collect_closed`は「現在enabledなら含まれる」方向なので矛盾しない。

この追加範囲に、既存質問に含まれない新しい言語意味論の選択は見つかっていない。
Q1/Q2、cycle23/24の質問を重複作成しない。旧Yulang2監査の
`y2-claims-role-boundaries-cycle-2.md` ROLE-MORE-001〜005は候補/whereの境界を、
`x-oracle.md` X13〜X16とC3-PARENTは有限例と一般証明の差を確認する根拠として再読した。
新しいYulang2実行はしていない。

## I. Import inventoryと残る監査範囲

[`2026-11-10-boundary-input-coverage.tsv`](2026-11-10-boundary-input-coverage.tsv) は
`python tools/boundary-input-inventory.py` で生成し、同コマンドの`--check`で照合できる。
Main/Auditの推移importに現れるCommonRole系242モジュールを列挙した。
Mainからは93、Auditからは242。各行はsource SHA256、根からの到達、
台帳にmodule名が出るか、直接local importを持つ。**名前の出現は全入力監査済みの印ではない。**
Lean theorem bodyの定数依存、実行到達性、全量input coverageの検査でもない。
Main/Auditから届かないmoduleとCommonRole以外の一般核はこのinventoryの範囲外。

cycle70終了時に名前が出ていたCommonRole系は51。cycle71はH節の具体入力を増補した。
残りには旧点モデル、反例、回帰だけのmoduleも含むので、未記載module数をそのまま
未達の意味論境界数にしない。一方、未記載だから入力が無いとも扱わない。

cycle71時点の次の意味論監査batchは、(1) DynamicIndex系とchecked source/diagnostic、
(2) interval candidate/frontierとordinary graph adapter、
(3) Mainに再掲されるassociated/where exactnessの前提対応だった。
(1)はcycle73のJ節、(2)のinterval candidate/frontierはcycle74のK節で照合した。
(2)の一般ordinary graph adapterの主要六モジュールはcycle75のL節で照合した。
(3)と他の未記載経路はI-13の残りとして明示する。**I-13全体はなお部分達成で、公開も未完了。**
B4の主要5橋は増減せず、既存の閉じた断片を否定したものでも、全体証明を完成したものでもない。

## J. cycle73: DynamicIndexの実行入力・残余・元の診断の境界

cycle72で中断した照合を、local source `23484c084` のまま再開した。
対象はDynamicIndex系15モジュールと、その実producerを持つ1モジュール。
下記は16行の入力監査であり、242モジュール全量の監査完了ではない。
型の略記はこの節だけで用いる。

- `Table = List Nat`、`Slot table = Fin table.length`。
- `State n = CommonRoleSettledConstraints.State n`。
- `Requests = List (Nat × Nat)`、`Links table = List (Slot table × Slot table)`。
- `Assignment table = Slot table → Core.PresenceGeneration.Comp Common.model`。
- `Problem table` は `seeds : List (Slot table)`、`links : Links table`、
  `requests : Requests`。`Packet table` は `state : State table.length`、
  `pending : List (Slot table × Slot table)`。

### J1. 固定された有限入力の入口

| モジュール | caller入力の名前・型と依存する入口/定理 | 実ソースからの導出・仕様の根拠と残る境界 |
|---|---|---|
| `CommonRoleOrdinaryKnownness` | `atoms : List (PresenceNormalForm.Atom (Fin n))`, `slot/receiver/output : Fin n`, `s/out : State n`。`detect_sound`/`evidence_unique`にはassignmentとmodels証明、`index_from_detected_str`には`detect = some .str`、`checked_exact`はproduced stateを量化。 | ordinary生成のslot/atomsから読む。`produceIndex`はcaller registryを取らず、固定の`Roles.AssocExamples.boxImpl`、`requiredRoles`、`box_paterson`、関連名0、key型intを内部で使い、receiverを`box payload`にする。6.2の一般可視impl探索ではない。spec6.2の`Index str int → char`の例をこのstr→str断片と混同しない。6.3の通常の型変数/等式への局所橋。`checkedProduceIndex = none`は一般stateでは未確定・未対応RHS・矛盾の区別を持たない。 |
| `CommonRoleDynamicIndexClosure` | `s : State n`, `edges : List (Fin n × Fin n)`、helperの`xs : List (Fin n)`/`fuel : Nat`/`Trace`、`P : Fin n → Prop`とseed/step閉包前提。`saturate_exact`, `least`, `stopped`, `saturate_executes`。最後の実行定理には`a : Fin n → Comp Common.model`とoutput models証明が必要。 | source義務からedgesを、既存ordinary制約からstateをloweringする。public saturateは有限`Fin n`列を計算し、その上の停止・最小閉包は証明済み。有限nとedgesを実動的生成から導く橋は無い。6.3の更新安定化の固定carrier断片で、Paterson/K2から全source生成の有限性を導いた定理ではない。models witnessは証明前提であり実行入力ではない。 |
| `CommonRoleDynamicIndexSource` | `table : Table`, `s : State table.length`, `requests : Requests`、lookup対象`i/j : Slot table`。`saturate_exact`, `output_models`, `scoped_request_present`。後者に`WellScoped table requests`とrequest所属。 | tableは各source occurrenceの名前、requestsはreceiver/outputのsource名対として作る。6.3の共有変数/関連型等式。alias edgesと全represented request edgesは計算済み。tableに無い名前のrequestはraw edgesでは消えるため、source由来/coverageはまだ入力境界。input tableの同じ数字を同一sourceとみなす正当性はA節/Q1と同じ。 |
| `CommonRoleDynamicIndexSourceExecution` | table/s/requests、helperの`xs : List (Slot table)`とclosure `Trace`、`a : Assignment table`と最終outputのmodels証明。`trace_executes`, `saturate_executes`, `output_fixed`。 | aliasはsource同一性からの等式伝播、named requestだけが固定producerを呼ぶ。この区別は実行traceで保持済み。6.3の等式とrole義務を混同しない。任意stateの整合性は構成しておらず、model前提を残した条件付き実行定理。 |
| `CommonRoleDynamicIndexCheckedSource` | table/s/requests、返値`out : State table.length`または`errors : Requests`、run成功/失敗証明。`run_ok_iff`, `run_error_iff`, `success_models`, `success_executes`。実行可能性の定理だけはassignmentとoutput models証明も必要。 | public runは全requestの両端名の存在を検査し、欠落を元の順と重複込みで返す。6.3のsource義務を落とさないためのadapter検査。okはscope成功であり全義務の解決成功ではない。欠落をlanguage rejected、okをselectedとしない。意味論の新しい選択ではなくloweringのcoverage責任。 |
| `CommonRoleDynamicIndexConsistentSource` | table、`seeds : List (Slot table)`、`links : Links table`、requests。`input_models`, `output_has_model`, `saturate_executes`, `checked_success_iff`。`reachable_checked_step`にreceiverのDerived証明。helper `addEqualities`は任意stateとlinks。 | 任意opaque stateを、strの正のseedとtype等式だけの構文へ制限し、全str・空effectのモデルを内部で構成する。整合性をcallerへ押し戻したままではない。ただしこの旧版はlinksをfeedback edgeにしていないので、等式の意味保存と伝播の完全性は別。6.3のordinary等式、spec5.5のeffectとtypeの区別。linksはeffect rowを同一化しない。 |
| `CommonRoleDynamicIndexEqualitySource` | table/seeds/links/requests、helper xs/Trace、`P : Slot table → Prop`と四規則の閉包前提。`saturate_exact`, `saturate_executes`, `least`, `reachable_checked_step`、`output_fixed`。 | explicit linksの両向きedgeを内部で加えることで、逆向きに書いた型等式でもstrが伝播する。public実行定理のmodel前提は除去済み。6.3の等式・更新安定化に対応するが、固定table、正のstr制約、有限requestという断片は残る。全言語の矛盾/区間/候補競合を処理する定理ではない。 |
| `CommonRoleDynamicIndexSemanticSource` | table/seeds/links/requests、i/j、`a : Assignment table`、`Derived`またはその否定の証明。`forces_str_iff`, `detect_str_iff`, `checked_success_iff`, `unreachable_underdetermined`。 | inputは前行から導出する。all-strモデルとunreachableをintにする分離モデルは内部で構成する数学的witness。6.3のreceiver既知性への局所完全性は証明済み。ただし量化先はoutput atomsのモデルであり、残ったconditional requestを含む元sourceのモデルと等しいとはまだ言わない。 |
| `CommonRoleDynamicIndexSourceSemantics` | table/seeds/links/requests、i/j、modelを量化するassignment。`source_forces_iff`, `checked_source_exact`, `checked_pending_iff`。`checked_request_models`だけは元request所属と成功runの証明も取る。 | 独立`SourceModel`はseed、type等式、alias、`receiver=str → output=str`の四条項。6.3の条件付き関連型更新の正の断片で、一般Indexの意味ではない。sourceとoutputのstr強制は同じだが、model集合の同一性は反例で否定済み。`checked_source_exact`のoutput slot jは任意で、義務の存在や辞書生成を保証しない。実request所属を落として`checked_request_models`を使わない。 |

### J2. 残余を保持した更新と元のrequest診断

| モジュール | caller入力の名前・型と依存する入口/定理 | 実ソースからの導出・仕様の根拠と残る境界 |
|---|---|---|
| `CommonRoleDynamicIndexResidualSource` | table/seeds/links/requests、任意`packet : Packet table`、`a : Assignment table`、成功run証明とrequest所属。`build_models_exact`, `run_models_exact`, `run_covers_requests`, `model_order_independent`。 | public buildは未解決receiverの条件付きrequestをpendingに計算する。atomsとpendingを合わせれば元sourceとの全model iffを構成済み。runはscopeを検査する。任意packetの`Models`を使うことと、buildされたpacketの正しさは別。6.3の保留/再計算に対応し、四分類/辞書は含まない。 |
| `CommonRoleDynamicIndexResidualResume` | table/seeds/links/requests、追加の`extra : List (Slot table)`、i/j、assignment。`resume_models_exact`, `resume_checked_exact`, `resume_pending_exact`。 | extraは後で入ったstr制約から作る必要。保持するseedとpending名は計算され、既に解決した制約を忘れず再開する。6.3の遅延と更新。任意ordinary refinementやtableの拡大ではない。pendingNamesはslot対から戻すため同じ名前対を複数持ち得る。元の欠落名の検査は上位runの責任。 |
| `CommonRoleDynamicIndexResidualBatches` | `table : Table`, `p : Problem table`, `updates : List (Problem table)`、返値packetと成功run証明、assignment、比較するleft/right更新列と要素所属同値。`solve_models_exact`, `run_models_exact`, `update_order_models`。 | p/updatesは実ordinary生成と関連型義務の各差分から作る予定だが、今は任意の有限list。全更新のsource conjunctionとのiffは証明済みで、無限更新を有限にする橋ではない。6.3の兄弟連言/安定化。compactは欠落名を作業用listから落とし得るが、runは元の全batchを先に検査するので診断は失わない。table固定もproof断片の制限。 |
| `CommonRoleDynamicIndexResidualFrontier` | table/p/updates、i/j、返値packetとrun成功証明、request所属、比較列とmembership同値。helper `compact_requests_unknown`/`advanceMany_requests_unknown`にはassignment、元sourceモデルとreceiver非str証明。`solve_residual_exact`, `run_covers_original_requests`, `solve_pending_rebuild`, `update_order_pending_list`。 | public境界はhelperの反例modelをcallerに要求せず、元の全requestの未確定receiver iffを導く。6.3の兄弟順序独立のうち、固定slot対列上のpendingはlist等号まで証明済み。一般の辞書・候補・四分類の順序独立に拡大しない。元sourceからp/updatesを生成する橋は前行と共通。 |
| `CommonRoleDynamicIndexOccurrenceDiagnostics` | table/p/updates、helper `inspect`の任意packetと`r : Nat × Nat`、定理のi/j、`waiting : Bool`、rの元全request所属。`diagnose_represents`, `inspect_exact`, `inspect_checked`, `original_order`、比較更新列とmembership同値を取る`update_order_inspect`。 | public diagnoseは元batch/request順を入力から保持し、観測だけsolve結果から作る。6.3の保留と兄弟順序、既存classification-boundary回答に関連。missing名も空endpointsとして保持する。任意packetをinspectしたfalseは単にpendingに無い印で、解決の証拠ではない。実solve結果と元request所属を伴う定理でのみstr強制と結ぶ。辞書/selected/ambiguous/rejectedは未実装。 |
| `CommonRoleDynamicIndexExamples` | 外部caller入力なし。固定`chain : Edges 3`, `initial : State 3`とその証明。`actual_two_steps`。 | 小さい実行回帰の固定値であり、source抽出/有限性の新しい前提を隠していない。6.3との一般接続をこの例から主張しない。 |
| `CommonRoleDynamicIndexSourceExamples` | 外部caller入力なし。固定table `[10,10,20,30]`、requests、seed、aliasRecordedとその証明。`well_scoped`, `alias_and_downstream_present`, `actual_named_steps`。 | 同一sourceの二occurrenceと後続requestの例。6.3の共有等式への素材だが、source名を実programから導く定理ではない。 |

### J3. 三種類の「成功」と二種類の順序を分ける

1. `CheckedSource.run = ok` はscope成功。seed無しのrepresented requestでもokになり、
   そのreceiverへのproducerはnoneのままでよい。
2. `checkedProduceIndex = some out` は固定producerの局所成功。output slotは任意なので、
   呼出しだけでは元source義務の存在や妥当な辞書を示さない。
3. `ResidualBatches.run = ok packet` の全model iffと診断の`Represents`は、
   同じ固定有限断片では実際に閉じている。callerの整合性oracleが残ると誤記しない。
4. residual listはslot対の正準列なので同じrequestの重複回数を保存しない。
   diagnoseは元request列から作るので順と重複を保存する。逆にaliasの二slotから
   pendingNamesに同名対が二つ現れることは、元requestが二回あったことを意味しない。
5. `update_order_pending_list`と`update_order_inspect`は内部listの等号を証明する。
   diagnose全体の外側batch順は意図して元順を保持する。この二つを矛盾とみなさず、
   一般where辞書の観察同値を証明済みとも言わない。

cycle73で15境界回帰と10定理の公理確認が成功した。再現本文と出力は
`notes/handoff/dots-cycle-73.md`。cycle72の同じ回帰ではstate等号を汎用の決定手続へ
渡した1箇所だけが型クラス不足で失敗していた。既存定理
`CommonRoleDynamicIndexEqualitySource.reverse_equality_checked`をそのまま使うことで
命題・期待結果を変えずに修正した。production Leanは無変更。

### J4. 仕様・質問・未達範囲

このbatchでは新しい言語意味論の空白は見つかっていない。固定carrier/str/有限update、
任意packet、scope成功の読み方は実装・証明境界であり、新しい言語拒否を質問しない。
Q1/Q2、cycle23/24の共有/糖衣/candidate guardの質問はそのまま再利用する。
Yulang2の追加実行はせず、既存`y2-claims-role-boundaries-cycle-2.md`の
ROLE-MORE-001〜005と`x-oracle.md` X13〜X16/C3-PARENTを再読した。
旧whereの挙動を新specへ逆輸入せず、固定box fixtureを一般Indexの検証としない。

I節の最初のDynamicIndex batchはここに記録した。残る順はinterval candidate/frontier、
一般ordinary graph adapter、Main associated/where exactnessの前提対応。
Main/Auditの他の未記載moduleも全量監査済みではない。**I-13は部分達成のまま**で、
cycle72までの公開期限は満たせていない。公開拒否後に書込を回避する別経路は使っていない。
B4の主要5橋は増減しない。

## K. cycle74: 区間候補・有限展開・ordinary graphへの受渡し

状態: Draft。integration `434d3ceef`、local `c4043b524`のproduction Leanを読んだ。
下の16モジュールの公開入口と補助入口を照合した。A/B節に短く登場したcapture等も、
今回この経路で入力の型と前提を区別し直した。Lean本体・言語意味論は変更していない。

略記: `F = CommonRoleCaptureNormalization.Form`、
`IG = CommonRoleIntervalPaterson.Goal`、`ID = CommonRoleStablePaterson.Declaration`、
`IB = CommonRoleIntervalCapture.Bindings = List (Nat × (F × F))`、
`IA α = CommonRoleIntervalGeneration.Argument α = TyTerm α × TyTerm α`、
`IF α = CommonRoleIntervalRecordResidual.Fields α = List (Nat × IA α)`。
`assignment : α → Comp Common.model`は任意の意味論的割当で、solverに渡す成功oracleではない。

### K1. 区間のordinary制約とrecord残余

| モジュール | caller入力の名前・型、依存する定理 | 実ソースからの導出案と仕様 |
|---|---|---|
| `CommonRoleIntervals` | `first/last : Interval Common.Ty`、`intervals : List (Interval Bound)`、`eval : Bound → Common.Ty`、既存`problem : Problem n Bound`。`valid_merge_exact`, `checks_real_argument_exact`, `append_checks_exact`。`actual : Common.Ty`と`values : Fin n → Common.Ty`は意味論の量化変数。 | ordinary生成が持つ二端点から作る。spec6.5の中心を持たない区間、自己整合と両交差条件が根拠。`checks`は全ordered pairを生成し、空リストも許す。意味論上の存在witnessは実行時のhead選択ではない。evalのsource忠実性は外側。確定・実装未接続。 |
| `CommonRoleIntervalGeneration` | `arguments : List (IA α)`、`existing : List (Atom α)`、有限compileでは`α = Fin m`。`generate_exact`, `generate_real_argument_exact`, `compile_append_exact`。`compiled_reflects`は任意`rows/values`とgraphの`Models`証明。 | 実区間の再調整から既存`TyTerm`へloweringする。spec6.5の通常部分型として返す規則に対応。graphは内部でcompile済みで任意graph入力ではない。solver成功も、実source loweringの正しさもこの定理の結論ではない。 |
| `CommonRoleIntervalRecordResidual` | `labels : List Nat`、`fields : IF α`、補助`mapPayload`の任意`f : Payload → Other`と`row : Row Payload`。`capture_map`, `residual_endpoints`。 | 既知のrecord spineとheadで明示されたfield名から作る。spec4.3の先頭field優先・隠れfield消去、6.3のtailを引き算で決める規則。有限Listを渡せることは、未確定tailが存在しないとsourceから判定した証拠ではない。上下端点は同一の正準残余から計算される。 |
| `CommonRoleIntervalRecordGeneration` | `labels`, `fields`, `requested : IA α`、compileの`existing : List (Atom (Fin m))`。`generate_exact`, `generated_fit_exact`, `compile_exact`。 | 既知spineの引き算の結果と元要求の二端点を受ける。`recordTerm [] = .emptyRecord`の幅を許す終端。spec4.3/6.3/6.5との接続では、sourceのrecordがこの終端を意味すること、headの明示field payload検査、未知tailの保留が必要。これらを入力の型だけから仮定しない。 |
| `CommonRoleClosedIntervalRecordGeneration` | 同じ`labels`, `fields`, `requested`, `existing`と意味論的`assignment`。`recordTerm_eval`, `generate_exact`, `compile_exact`。 | こちらは`recordTerm [] = .exactEmpty`の閉じた終端。Commonの閉record構成子への解釈は証明済みだが、sourceのspineが閉じていることは外側の責任。前行と同じ入力型でも交換不可。spec4.3/6.3に従い、未確定tailを閉recordとみなさない。 |
| `CommonRoleClosedIntervalInspection` | `first/last : IF α`、`assignment`。`checks_exact`は`shape : SameLabels first last`を要求。公開`reconcile_exact`ではラベル一致のBool検査を実行し、返ったatomsのモデルと`SameLabels ∧ Compatible`をiffにする。 | sourceの既知・閉spineから有限field列を得る。spec4.3のlookup/先頭field優先、6.5の自己二本・交差二本の比較。`reconcile = some atoms`はラベル検査の成功のみで、payload制約の充足成功ではない。closed-fragmentのラベル不一致を一般record部分型拒否と同一視しない。 |

### K2. scalar候補のfeasibilityと有限source occurrence

| モジュール | caller入力の名前・型、依存する定理 | 実ソースからの導出案と仕様 |
|---|---|---|
| `CommonRoleCandidateStateFrontier` | `s : State n`, `slot : Fin n`, `visible : List Candidate`、`Candidate.key : Nat`, `.head : Inference.Base`。`collect_exact`, `collect_after_equation`。`collect_antitone`はbefore/afterと全モデルを戻す`retains`前提。 | state/slotはordinary生成から、visibleはspec6.2の根呼出し側の可視implから導く。keyはsource宣言identity。今はscalar headしかなくwhere/associated bodyを含まない。spec6.3の一意候補だけで変数を決めない規則に従い、各候補を同じ旧stateの私有拡張で調べる。返すのは候補Listで共有stateの更新ではない。 |
| `CommonRoleIntervalCandidateFrontier` | `s : State n`, `q : Request n`の`lower/upper : Fin n`, `c : Candidate`, `visible`。`collect_exact`, `solutions_exact`。`fromSource`と`source_bounds_preserved`は`requests : List CommonRoleOpenDescent.Request`, `index : Fin requests.length`, `interpret : CommonRoleSettledSyntax.Ty → Comp Common.model`。 | 元義務の上下occurrenceを計算したtableへ置く。ただしinterpretはcallerの任意関数で、source nominalの意味保存を証明しない。異なるoccurrenceを共有sourceへ結ぶ一般橋も残る。spec6.2/6.3/6.5。`solutions_exact`のrows/parametersは結論側の全solution familyの表現で、与えられたassignmentだけを選んでよいという意味ではない。 |

`Candidate.key`や`visible`には一般のsource一意性・網羅性を保証する型がない。
`collect`はList.filterなので入力順と重複を保持する。後述の`Roles.distinct`を使う有限展開とは
重複の扱いが異なり、そのまま同じ外側resolverへ置き換えられない。
source可視性・identityの不足はspec6.2の確定済み要件であり、新しいcoherence規則の質問ではない。

### K3. capture・Paterson・独立辞書の境界

| モジュール | caller入力の名前・型、依存する定理 | 実ソースからの導出案と仕様 |
|---|---|---|
| `CommonRoleIntervalCapture` | `form : F`, `argument : F × F`, `forms : List F`, `arguments : List (F × F)`, `bindings : IB`。`capture_exact`, `capture_arguments_exact`, `bound_exact`。`supported`は`declaration : ID`。 | source head/goalを有限Fへloweringする。capture helperは非線形headから同名のbindingを複数返せるが、一般の再調整ではない。公開inspectの`Nodup`/linear条件を落として使わない。spec6.2は同名変数の再利用を認め、6.3は合流payloadの捕捉を指定するので、このgrammar外を言語拒否にしない。 |
| `CommonRoleIntervalCandidates` | `declaration : ID`, `goal : IG`, `bindings : IB`, `declarations : List ID`。`inspect_accepts_exact`, `inspect_rejects_exact`, `scan_exact`。`accepted_child_decreases`には実checkerの`check declaration = true`, `Accepts`, 元requirement所属が必要。 | source declaration/goalと全可視候補から生成する。`inspect`はgrammar検査をrole比較より先に行う。`none`は範囲外、`some none`は対応する局所Rejects、`some (some bindings)`は局所Accepts。三つを最終pending/rejected/selectedへ写す橋は無い。normalizeは既存の有限idempotence passで全source型正規化ではない。spec6.2/6.3/6.5、前節Q2以外は既知の実装未接続。 |
| `CommonRoleIntervalPaterson` | `declaration : ID`, `binding : Nat → (F × F)`, `requirement : Nat × List F`、`accepted : check declaration = true`と所属。`every_where_decreases`。 | 有限scannerの実captureと宣言checkerから導く。両端点を別々に代入して正規化し、サイズ和の減少を示す。spec6.3の宣言時停止検査に対応。binding全域関数は補助入力であり、実入口は有限bound検査で使う名前を確保する。一般associated feedback・source graphの変化をこの固定Fサイズに取り込んだわけではない。 |
| `CommonRoleIntervalExpansion` | `declarations : List ID`, `goal : IG`、helper `expand`には`checked : Checked declarations`。公開`run_tree_exact`はcheckerを内部実行。`Traversal`の選択・child証拠は独立関係の構成要素。 | spec6.2の可視registryとsource義務から導く。有限線形F断片で、実checkerと実scanにより全where子を再帰展開し、補助fuelや任意rankは不要。`outside/noHead/overlap/node`は構造treeの分類で、ordinary矛盾やK2の全判定ではない。`Roles.distinct`は宣言record全体で重複を消すため、別source implを同じrecordに潰さないidentity生成が必要。 |
| `CommonRoleIntervalExpansionChecks` | `tree : Tree`, `evaluate : F → Common.Ty`, `values : Fin n → Common.Ty`。`constraints_exact`, `original_goal_checks`。`interval_checks_exact`は任意arguments。 | 実runのtraceから全元goal/captureの自己整合checksを生成する。公開定理は任意に組み立てたTreeにも成り立ち、Treeのreachable/selected性は証明しない。spec6.3/6.5。overlapの全候補captureも保持するが、候補の言語上のconjunctionを決定するための定理ではない。 |
| `CommonRoleIntervalDictionaries` | `declarations`, `goal`、helper `build`の`checked`と`finished : complete (expand …) = true`。`Dictionary`は一意な独立Selectionと全where子の辞書を持つ。`complete_iff_dictionary`, `elaborate_prepared_exact`, `Dictionary.erase_unique`。 | 公開elaborateはchecker/completeを計算するため成功をcallerに要求しない。ただしDictionaryは有限構造断片の証拠で、ordinary区間の充足は含まない。preparedでも元端点が矛盾しうる。spec6.3に接続するには残ったchecksを実ordinary solverへ渡す必要。erase_uniqueは同じregistry/goalでの一意性で、source順を変えた別プログラムの辞書同値ではない。 |
| `CommonRoleIntervalDictionaryCompilation` | `name : Nat → α`、`trace : Tree`、有限版の`original : List (Atom (Fin m))`。`generate_exact`, `compile_trace_exact`, `compiled_reflects`。後者は任意rows/valuesと実compiled graphのModels証明。 | source名解決・scopeからname map、実elaborateからtrace、ordinary生成からoriginalを導く。任意name mapは異なる名前を同じslotへ潰せる。定理はそのmapの下で正確だが、source identityの正しさは別。spec6.2/6.3/6.5。compiled graphは内部生成済みで、そのedgeをsolveした定理ではない。 |
| `CommonRoleIntervalReadyChain` | `count : Nat`の固定tower familyと、存在を否定する任意`rank : IA Empty → Nat`。`always_known`, `bounds_consistent`, `no_readiness_rank`, `growing_rejected`。 | 反例保存module。readyかつ各段階が整合しても停止の尺度は導けない。固定`R a where R (int, a)`は実Paterson checkerに拒否される。spec6.3の受理済みプログラムの反例でも、sourceに新しい拒否条件を課す根拠でもない。source入力を生成するモデルではない。 |

### K4. 境界回帰と質問の扱い

cycle74のscratch検査は次を区別する。productionに局所定理を増やしていない。

- 非線形helperのcaptureは同名bindingを二本返し、`total`は先頭を読む。
  公開`inspect`はその宣言を範囲外にする。helperの成功を一般非線形headの解決と呼ばない。
- 範囲外の宣言は別roleであってもscan全体を`none`にする。前後順を変えても同じ。
  これは保守的な局所scanの定義であり、別roleが言語上の解決を妨害する仕様ではない。
- scalar rigid mismatchと未確定endpointは`some none`/`none`で別になる。
- 変数headの構造辞書は、`int ≤ tick int`という不可能な元区間でもpreparedになる。
  一方、その元intervalのordinary不整合も独立に証明できる。既存の
  `elaborate_prepared_exact`の誤りではなく、preparedがordinary成功ではないことの具体例。
- 同一ID recordの重複はdistinctで一つになり、異なるkeyの同head宣言は二候補になる。
  spec6.2の別source宣言identityをloweringで保つ必要がある。
- 区間二本は自己二本・交差二本を生成する。recordの幅終端と閉終端は違う。
  隠れfieldの除去は両端点を同時に保存し、closedラベルgateはpayload成功と別である。
- name mapによる別名の併合は可能だが、map下の生成iffだけでsource共有を正当化しない。

新規質問ノートは0件。scope/identityは既存Q1、糖衣の宣言検査はQ2を再利用する。
今回の範囲外・preparedの観察は、仕様が黙っている新規の利用者可視意味ではなく、
実装済み断片の境界である。決定済みのspec6.2/6.3/6.5を弱める質問を追加しない。
実際のsource導出時に別の未決意味が現れれば、遅延案を先頭に別途質問する。

B4の主要5橋は未達のまま。K節は一般`source_boundary_adequate`や
`saturate_terminates_and_closes`を新たに証明したものではない。

## L. cycle75: ordinary graph読出しと候補制約の六モジュール

対象は以下の六モジュール。B節/H3節の短い紹介を、入力・定理の前提まで掘り下げた。
`Graph m = Fin m → CommonRoleRegularGraph.Node m`、`Problem n Bound =
List (LayerBoundTemplates.Constraint n Bound)`、`Assignment n = Fin n → Comp Common.model`。
ordinary slot数`n`とgraph node数`m`は異なる。node番号・source名・ordinary slotを
同じNatとして無条件に同一視する橋は存在しない。

### L1. graphの構成・同値・snapshot

| モジュール | 入力の名前・型、依存する入口/定理 | 導出の素案・仕様と前提の境界 |
|---|---|---|
| `CommonRoleRegularGraph` | `graph : Graph m`, `root/next : Fin m`。`returns_to_exact`, `recursive_at_exact`。`Node`は`unresolved / scalar Nat / structural Nat (List (Fin m)) / nominal Nat (List (Fin m))`。`nominal_not_recursive`等のfoundはnode形状の局所証明。 | source ordinary stateの下界から構築子と子を読み、ordinaryで同一化済みの未知slotをcanonical nodeへ写す必要がある。graphはcaller入力のまま。nominalは名前と明示引数だけを持ち、宣言bodyを展開しない。spec6.3と6.5末尾K2。有限nは全node集合の容量で、解決深さ制限ではない。 |
| `CommonRoleGraphBisimulation` | 同じgraphと`first/last : Fin m`。補助`relation : List (Fin m × Fin m)`、子node列、`read : Fin m → View`、`preserves`。公開`bisimilar_exact`は有限relationを内部探索。`bisimilar_iff_observations`と`observations_bisimilar`だけは`closed : ∀ node, graph node ≠ .unresolved`。`regular_at_exact`はclosed不要。`depth : Nat`は全深度の観測定理の量化。 | 未知nodeの同値は同じnode identityのみ。表示用`View.unresolved`はidentityを保存しないので、全深度の表示一致からbisimulationへ戻すにはclosedが必要。これを未確定ordinary graphの同一化器にしない。一般Common型とのadequacyはH3のunary/record断片以外に残る。spec6.3の共有変数、6.5末尾K2。番号/探索実装は表現の自由で、意味保存が必要。 |
| `CommonRoleGraphInspection` | `graph`, `pattern : Pattern`, `node : Fin m`。`Pattern`はvariable/shared/scalar/structural/nominal、`Captures = List (Nat × Fin m)`。`inspect`, `inspectAll`, `inspect_cycle_sound`。可視入口には`role : Nat`, `visible : List VisibleHead`と`VisibleHead.role/key/pattern`。`inspect_visible_exact`, `inspect_all_visible_exact`, `snapshot_unknown_exact`。観測値・reached node・観測成功の証明は定理の量化/局所前提。 | root caller側の可視implからvisible、正規化したheadからpattern、ordinary readoutからgraph/nodeを導く。whereと上界はこの入力に無い。visibleは順序/重複を保持しkeyの一意性も要求しないのでsource identityは別に保証する。spec6.2の可視性、6.3のplain capture、6.5末尾K2。`inspect`のvariableは再帰nodeを丸ごと捕捉する一方、`inspectSnapshot`はrootの再帰を先に記録する。これは入口の役割の違いで、どちらも最終分類ではない。 |

bisimilarの完全powerset探索は有限停止を与えるが、実用計算量の保証ではない。
また`inspectChildren`の単一Observationは左優先で、`inspectAllChildren`は全結果を連結する。
後者を用いても、K2の適用候補判定や兄弟stateの安定性まで自動で得られるわけではない。

### L2. ordinary lower contributionsから候補の制約へ

| モジュール | 入力の名前・型、依存する入口/定理 | 導出の素案・仕様と前提の境界 |
|---|---|---|
| `CommonRoleDeferredBounds` | `evaluate : Bound → Common.Ty`, `problem : Problem n Bound`, `node : Fin n`、`values : Fin n → Common.Ty`と`CommonBoundCoalescing.Models evaluate problem values`。`interval_exact`, `model_fits`。別入口`project : Bound → Option Head`は`lowerHeads_exact`, `pending_exact`, `known_exact`の入力。 | ordinary生成からlower/flow/upper/check列とbound意味を作る。projectは任意で、全boundをnoneにしても型は満たす。したがってpendingは「このprojectの下でlower headが無い」のみで、言語上の型未決定の完全判定ではない。spec6.3の通常制約・保留、6.4の下界でのmethod照合。model_fitsは既存モデルから区間適合への健全性で、モデル存在の生成ではない。 |
| `CommonRoleGraphDemandSnapshots` | `graph : Graph m`, `problem : Problem n (Fin m)`, `slot/source : Fin n`, `head : Fin m`, `role`, `visible`。`lower_origins_exact`, `lower_origins_project`, `inspect_all_contributions_exact`, `inspect_lower_heads_exact`。`unresolved_contribution_retained`は元lower seed/flowのorigin証拠と`graph head = .unresolved`を取る。 | projectをgraphのunresolved検査に固定済み。ただしgraphとproblemが同じordinary stateを表すadequacyはcaller側に残る。lowerOriginsはseedのsource slotと重複を保持し、flow経路の始点を失わない。lowerHeadsはunresolvedを省くがinspectAllContributionsはunknownとして保持する。複数lowerの合流・upperとの整合・graph更新後の再検査は別。spec6.3/6.4、6.5末尾K2。 |
| `CommonRoleCandidateConstraints` | `slotBounds : Fin m → Fin n × Fin n`, `observations : List (Observation m)`, `bindings : List (Nat × (Fin n × Fin n))`, `original : List (Atom (Fin n))`。`from_observations_exact`, `generate_exact`, `solve_sound`, `solve_empty_exact`, `prepare_all_instances_exact`。prepareにはgraph/pattern/headも渡す。完全性入口の三前提は`GoodAtoms original`（child grammar）、`WidthAtoms original`、`PresenceSourceConstraintSupport.GoodAtoms original`。 | 元sourceの各graph nodeに正しいordinary上下slotを結ぶmapを構成しなければならない。任意のslotBoundsを受ける今の型はその意味保存を保証しない。同名captureの全自己/交差比較を生成し、originalを保持して実ordinary solverへ渡す点は実装済み。spec6.3、6.5の区間。mismatch/unresolved/cycleはcaptureリストに入らないがPrepared.observationsには残る。schemesの非空を候補成立・K2安全・最終選択と読まない。 |
| 同上のsource生成入口 | `expression : Inference.Expr`, `clause : Clause (Option Empty)`, `generated : clause ∈ normalise (principal ([] : SchemeEnv Empty) expression)`, caller graph/pattern/head/slotBounds、`assignment : Assignment (clause.locals + 1)`。`generated_prepare_all_instances_exact`。 | この閉じたordinary式の実生成経路では三grammar前提を内部で証明済みで、callerに別々に要求しない。clause membershipは生成結果を選ぶ局所証拠。graph/slotBounds/source visibleへの接続はなお外側。returned schemeのrows/parametersとAssignmentEquivalentは結論の存在witnessで、実行oracle入力ではない。spec6.3のsource生成を全言語に拡張する必要がある。 |

### L3. 確認した境界と次に接続する順番

scratchの22境界assertionと1共有補助証明で次を確認した。

1. 異なる二つのunresolved nodeは全深度の`observe`が等しいが、bisimilarはfalse。
   `bisimilar_iff_observations`のclosed前提が実質的に必要で、既存定理の反例ではない。
2. 同じunrolled recursive graphのrootについて、variableの低位inspectはmatched、
   root snapshotはcycle。identityでのcycle検出はfalseでもregularAtはtrueとなる。
3. known/unknownの二lower seedに対し、lowerHeadsはknownだけ、all-contributionsは両方を
   返す。duplicate seedはduplicateのまま、flowを辿った寄与は元source slotを保持する。
   upperだけではlower contributionを作らない。
4. 空ordinary制約、scalar0 graph、scalar1 head patternのprepareでは、
   observationsはmismatchでもschemesは非空。この有限反例は「ordinary成功なら
   head候補」という誤った接続を否定する。元の定理はその含意を主張していない。
5. capture-only抽出ではmismatch/cycleの兄弟は除外されるが、成功兄弟のcaptureは残る。
   同名capture二本は重複を勝手に消さず、四つの自己/交差atomを生成する。

sourceからの接続は少なくとも次を同時に満たす必要がある（新定理はまだ置かない）。
(a) ordinary stateとgraph/problemの意味対応、(b) unknown identityとslotBoundsのscope対応、
(c) 元lower/upperの合流と候補ごとのordinary整合、(d) 全観測を保持した適用候補/K2判定、
(e) state更新後の再読出しとwhere/associated feedbackの安定化。
これらは`source_boundary_adequate`と`saturated_frontier_exact`の内部要件であり、
B4の主要橋の数を5から増やしたという意味ではない。

今回のgraphデータ構造の不足はspec6.2/6.3/6.4/6.5の確定事項に対する未接続であり、
新しい言語意味を選ぶ必要は無かった。新規質問は0。Q1/Q2とcycle23/24質問を維持する。
Yulang2のROLE-MORE-001〜005、X13〜X16/C3-PARENTを再読したが、未知node identity、
graph bisimulation、内部slotBoundsのadequacyを確かめる実機oracleではない。
新しいYulang2/parser実行はしていない。

## M. cycle76: associated/where exactnessの入力とsource modelの接続

Mainの既存の有限path入口と、別経路の有限associated closureを対応づけた。
Mainから直接読むのは`stateful_finite_path_parent_exact`、
`stateful_reverse_siblings_exact`、`named_finite_path_exact`。
associated declaration/finite graphの全定理がMainに再掲済みという意味ではない。

### M1. first-order associated型の入力

| モジュール | 入力の名前・型と依存する入口 | sourceからの導出・仕様と前提の境界 |
|---|---|---|
| `CommonRoleAssociatedStateFlow` | `env : Roles.AssocEnv`, `roles : Roles.RoleDecls`, `wf : Roles.WellFormed env.cores`; `q : Request n`はreceiver/name/output、`s/out : State n`。`value_exact`, `source_store_agrees`, `produce_exact`。`models_exact`はcomputed/producedと全assignment、`recollect_exact`はscalar head/Computed、`visible : List Candidate`とcandidate。`recollect_shared_exact`はtable、sibling slot、source同一性の証明。 | C節の入力に加え、ordinary整合はproduceでは検査しない。source_storeは単一の出力変数等式だけをlowerする。scalarはコード0=int、1=strのみで、他RHSのnoneを言語拒否にしない。sourceの宣言可視性、receiver/name/outputのbinding、兄弟のsource同一性が外側。spec6.2/6.3。 |
| `CommonRoleAssociatedDeclarationExact` | 同じenv/roles/wf、`g : Roles.Goal`、`name : Nat`、`result : Roles.Term`。`assocOf_sound`は返却証拠のみ、`assocOf_exact`と`computed_iff_declarative`はさらに`awf : Roles.AssocWellFormed env roles`。後者はqとscalar headも取る。 | awfは全implのhead変数へのRHS限定、署名arity/required/defaultの充足、関連名の宣言済み条件。envのcoherentは同一implの注釈一意性であり候補の非重複ではない。sourceから両well-formed証明を導く必要。6.3の糖衣参照まで扱うHeadDeterminesAssociatedへの拡張はQ2/I-8に残る。健全性だけとiffの前提を混同しない。 |

ここで`Roles.RoleDecls = Nat → Roles.RoleDecl`の各宣言はarity、
`assoc : Nat → Option (Option Term)`、defaultのscope証明を持つ。
`some none`はrequired、`none`は未宣言。`AssocEnv.impls`の各recordはcore impl、
関連名/RHS列、名前のNodup証明を持つ。`wf`のPatersonと`awf`の関連型検査は別である。
任意のwell-formed引数を受けることは、parser/名前解決から構成済みという意味でない。

### M2. 有限source graphの閉包

| モジュール | 入力の名前・型と依存する入口 | sourceからの導出・仕様と前提の境界 |
|---|---|---|
| `CommonRoleFiniteAssociatedClosure` | env/roles/wf、`p : Source n`、`s : State n`、`fact : Fin n × Inference.Base`。pは`identity : Fin n → Nat`と`occurrences : List (Occurrence n)`、各occurrenceはreceiver/output slot、name、`template : Inference.Base → Roles.Goal`。`saturate_exact`, `saturate_capacity`, `associated_closed`。 | initialはordinary明示二方向scalar atom、templateの各base入力に実関連型計算を行いHorn規則を構成する。4*nのfact universeと停止は内部計算。有限occurrence列の生成/網羅性とtemplateのsource忠実性は入力のまま。nominal/record等の一般区間はcarrier外。spec6.3。 |
| `CommonRoleFiniteAssociatedModels` | 同じ入力と`v : Fin n → Comp Common.model`。`run_models_exact`, `solver_exact`。順序比較はp/qと`SameSource p q`（identityの同値関係、occurrenceのmembership一致）。`emit_models`の任意fact列は補助入力。 | 任意の全assignmentについて旧制約とderived scalar等式を連言する。任意source名の同一性はscalar規則で伝播するだけで、未知slotのtype等式を自動追加しない。order-independentは同じslot/template集合のmodel/cache membershipであり、sourceのwhere再順序付けの辞書同値ではない。spec6.3。 |
| `CommonRoleFiniteAssociatedStable` | env/roles/wf、p/s、fact、全assignment。`cache_stable`, `models_stable`, `run_evidence`。`extend_evidence`/`emit_evidence`はslot/baseと任意fact列。 | 同じ固定pを再実行した明示scalar evidenceと全modelの固定点。更新から新しいwhere義務やtemplateを再生成する閉包ではない。spec6.3の全安定化への中間部品。 |
| `CommonRoleFiniteAssociatedDeclaration` | 同じ入力に`awf`を加える。`saturate_declaration_exact`, `run_declaration_exact`, `declaration_stable`。`declaration_congr`はp/qのidentity/occurrence同値と元state。 | `Computed`を独立`DeclarativeComputed`へ置換する橋は既にある。awfを消して同じiffとは言わない。source/template由来はなお未接続。spec6.2/6.3。 |
| `CommonRoleNamedAssociatedGraph` | env/roles/wf、`p : List NamedOccurrence`、`s : State (2*p.length)`、fact。NamedOccurrenceはreceiver/outputのNat名、関連name、template関数。`named_exact`, `named_capacity`, `occurrence_origin`, `slot_origin`, `generated_fact_origin`。 | 全occurrenceの二位置を計算してcaller slot mapを除去済み。同名でもreceiver/outputの位置自体は別。scalar伝播用identityは計算するが、一般ordinary source等式を追加する入口ではない。`generated_fact_origin`は任意slotの位置由来を示し、そのfactの構文生成由来/候補到達可能性までは結論しない。有限named listを実whereから導く橋は残る。spec6.3。 |

`template`は任意関数なので、引数baseを無視して固定receiver goalを返しても型が通る。
これは現定理の反例ではない。sourceから作る際は、受け取ったbaseが元receiverの
materializationと一致し、role/key/関連名/残り引数のscopeを保つことを示す必要がある。
この対応は既知性・名解決・宣言生成の実装責任であり、利用者向けに新しい規則を選ばない。

### M3. Mainの有限path入口

| モジュール | 入力の名前・型と依存する入口 | sourceからの導出・仕様と前提の境界 |
|---|---|---|
| `CommonRoleStatefulIndexSweep` | `edges : List (Edge n)`（receiver/output）、`s/out : State n`、trace : List Bool。`sweep_exact`, `visit_exact`, `sweep_preserves`。後者は全assignment/model。 | stateから各visitのreceiverを再materializeするが、registryは固定Index(box payload,int)断片。任意有限visit列はsource生成器ではない。falseはそのvisitでProducedが無いことで、最終pending/rejectedの区別ではない。spec6.3。 |
| `CommonRoleStatefulIndexPath` | `outputs : List (Fin n)`, `receiver : Fin n`, `s/out : State n`。`run_expected`はstrAssignmentのmodelとdetect=str、`expected_models`は全assignment。`from_declaration_exact`は空stateと固定Index(box str,int) seed。 | 固定strだけの証明と任意旧stateの後続入口を分ける。outputsは重複/再訪を許すが、終了はcallerの有限path列に構造再帰する。spec6.3の一般Paterson/生成閉包ではない。 |
| `CommonRoleStatefulPathComplete` | 同じoutputs/receiver/s/out。`checked_exact`, `checked_models_exact`。低位`run_expected_of_models`はModelsと明示str evidence、`successful_state`は成功/Models/evidence。 | public checked入口は固定宣言からseedを生成し、実ordinary整合を内部検査するため、成功/Modelsを外部前提にしない。元のeffect/type制約は残る。有限path/固定seedは入力断片に残る。spec6.3。 |
| `CommonRoleStatefulPathParent` | 同じpath/receiver/state、`argument : Roles.Term`, `answer : RoleDictionaries.Answer`。`outer_exact`, `success_visible`。 | Mainの`stateful_finite_path_parent_exact`はこの型を保つ。Parent/Left/Right registryとstr辞書は固定され、callerが任意のvisibleを渡す一般定理ではない。dict存在はFinalの結論側。`run_of_models`の仮定をpublic outer iffの外部前提に取り違えない。spec6.2/6.3。 |
| `CommonRoleStatefulParentExample` | public runは入力なしの固定3slot例。`outer_exact`はout/argument/answerを量化。final_modelsは全assignment。 | Rightの関連型seed、逆順2edge、2sweep、固定Parent辞書が内部にある。Mainの`stateful_reverse_siblings_exact`。2passを一般停止boundとしない。旧Yulang2 C3-PARENTはsource素材だが同じ内部graphのoracleではない。 |
| `CommonRoleNamedPath` | `seed : Nat`, `names : List Nat`、table長の任意s/out、argument/answer。`outer_exact`。`source_factorization`は成功と全modelを仮定。 | Mainの`named_finite_path_exact`。table/occurrence slots/identity atomsを内部生成し、初めにSourceIdentity.extendを通す。名前自体のscopeと有限path由来はcaller側。固定Index(box str,int)と固定Parent辞書の断片。spec6.2/6.3、Q1。 |

### M4. 今回閉じた有限modelの接続

新規`CommonRoleFiniteAssociatedSourceModels`はtableとoccurrence列からsource graphを作り、
**ordinary source等式を先に追加してから**有限associated closureを実行する。
入力はenv/roles/wf、`table : List Nat`、`List (Occurrence table.length)`、旧state。
独立declaration版のiffにはさらにawf、model定理では全assignmentを量化する。
`run_source_models_exact`の一つのsource valuationは結論の存在量化で、入力ではない。
`solver_source_exact`は同じ条件のmodel存在と実ordinary solverの受理を同値にする。

scratch境界検査では、同一source名の二slotにscalar seedもoccurrenceも無いとき、
従来finite closureの出力atomsは空であり、slot0=int、slot1=strの分裂modelも満たす。
新入口ではこの分裂modelを排除することをLeanで確認する。元のfinite閉包定理の
誤りではなく、scopeの正しいsource共有を付け足す必要があった接続である。
新しい意味を選ばず、effect行の同一性も勝手に追加しない。

B4主要5橋は依然未完。今回閉じたのは与えられた有限graphにおける共有modelの接続。
残るsource側義務はtable/occurrence/templateの生成とscope、動的whereの網羅性、
一般区間knownness、候補guardと安定後の診断/辞書である。
新規質問0件。Q1/Q2、cycle23/24の未決事項を維持する。

I節で挙げた(3)の有限Main path入口とassociated閉包の対応は今回列挙した。
他の未記載module、一般核、未監査入力は残り、**I-13は部分達成**。
過去節の「公開も未完了」は当時の記録であり、cycle75で69〜75分が公開済み。
新しいYulang2/parser実行はしていない。live auditのC3-PARENT/X13〜X16を読み、
内部table/templateの妥当性を直接測るoracleではないことを確認した。

## N. cycle77: finite named allocationをsource modelへ接続

`CommonRoleNamedAssociatedSourceModels`のcaller入力は、
`env : Roles.AssocEnv`、`roles : Roles.RoleDecls`、
`wf : Roles.WellFormed env.cores`、`p : CommonRoleNamedAssociatedGraph.Program`、
`s : State (CommonRoleNamedAssociatedGraph.table p).length`。
Programの各行はreceiver/outputのNat名、関連name、base→goalのtemplate関数。
任意の有限サイズ、重複、同名、cycleを許し、別のtable、occurrence slot map、
identity関数、燃料、成功結果、完成したfrontierを外部から受け取らない。

- `receiver_source`、`output_source`は各計算slotが元行のsource名を保つ。
- `prepared_evidence`は任意p/s/slot/headについて、ordinary identity追加が元stateの
  明示scalar Evidenceを変えない。semantic entailment全体の定理ではない。
- `allocated_to_named`、`named_to_allocated`、`allocated_named_exact`、`named_support`は
  任意env/roles/p/s/fact（またはname/head）と独立導出を量化する。wf/awfは不要で、
  executable resolverとのiffではなく二つの独立判断の対応だからである。
- `run_evidence_exact`、`run_source_exact`、`solver_source_exact`は同じ入力に
  `awf : Roles.AssocWellFormed env roles`を加える。model版は全assignmentを量化。
  一つのsource型valuationは結論の存在量化であり、callerが実行を選ぶ入力ではない。

`NamedDerives`のseedは**元のs**のscalar Evidenceを計算source名へ読む。
associated stepはpの行、独立`RoleConstraints.Resolves`、`Roles.AssocDerives`、
scalar decodeを使う。実resolverの出力や飽和済み集合は独立判断に混入しない。
同じsource名は同じ判断なので、名前版にはidentity専用規則が無い。

これによりM4のtable/slot入力は有限named programから導けた。残るcaller責任は、
そのprogramを実where/associated構文から網羅的に作ること、scope解決済みNat名の
正しさ、templateが受け取ったbaseをreceiverと残り引数へ忠実にmaterializeすること、
宣言可視性とwf/awfの検査である。spec6.2/6.3はsource共有、関連等式、安定後の
再計算を定めるが、Q1の再訪同一性、Q2の糖衣と検査、cycle23/24は未決のまま。
今回それらの選択を仮定した導出や新しい言語意味の採用はしていない。新規質問0。

この接続で全言語B4、動的whereの閉包、一般区間knownness、四方向の分類、辞書順が
完成したとは言わない。主要橋は5本のまま。I-13全量監査も部分達成のまま。

## O. cycle78: structural associated template generation

`CommonRoleStructuralAssociatedTemplates`の新規caller入力は次の通り。

- `Template`は`goal : Roles.Goal`と`scope_ok : argsBound goal.args ≤ 1`。
  `check : Goal → Option Template`がこの証拠を計算し、`check_accepts`/`checked_goal`
  は受理範囲と元goalの保存を示す。変数0だけのfirst-order断片で、引数は任意個、
  constructorは任意の有限入れ子、placeholderは0回以上・複数回出現できる。
- `Occurrence`はreceiver/outputのscope解決済みNat名、関連name、上記Template。
  `Program`はその任意有限リスト。compileは行数/順番と名前を保ち、template関数を
  構造的に生成する。別のslot map、identity関数、燃料は受け取らない。
- `fill_exact`/`fills_exact`は任意payload、scope内のterm/list、結果を量化し、
  独立構造導出と既存Roles.substを同値にする。`fill_ground`/`fills_ground`は任意
  ground payloadの閉性を示す。`encode_ground`は既存int/str encodingの閉性。
- `materializes_exact`/`materializes_shape`は任意Template/head/Goalを量化し、
  closed guardと独立Materializesのiff、role/arity保存を示す。
  `materializes_payload`はplaceholder出現の証拠を加え、その場所に実payloadが
  入ることを既存matcherで回収する。未使用の場合は定数skeletonを許す。
- `step_exact`/`derives_exact`は任意env/roles、行またはprogram、旧state、名前/headを
  取る。既存の任意関数Associated/NamedDerivesと、構造Materializesおよび独立
  Resolves/AssocDerivesに基づくStep/Derivesを同値にする。ここはwf/awf不要。
- `run_evidence_exact`/`run_source_exact`/`solver_source_exact`はenv/roles/wf/awf、
  任意program/旧stateを取る。evidence版はslot/head、model版は全assignmentも量化。
  source valuation、成功、完成frontierは結論側で、実行前提でない。

これによりN節の任意template関数は、このchecked first-order断片ではsyntaxから
導けた。spec6.2/6.3のsource共有・関連型等式に沿うが、実parserからこの有限listを
生成する網羅性、scope名の正しさ、roleの可視性、declared arityの検査とwell-formed
registry生成、一般interval receiver、動的whereは未接続。bool/unitのencodingを
新設していない。unsupported用のunbound sentinelは閉性guardで必ず止まり、
ソース意味の拒否規則にはしない。

Q1/Q2とcycle23/24の未決事項を選ばず、既存質問を維持する。新規質問0件。
B4主要5橋とI-13全量監査は依然未完。モジュール言及数は監査完了数ではない。


## P. cycle79: checked raw associated programs

`CommonRoleCheckedAssociatedPrograms` replaces proof-bearing Template inputs
with raw goal syntax at the finite-program boundary. Caller inputs are:

- `RawOccurrence`: scope-resolved receiver/output Nat names, associated Nat name,
  and a raw `Roles.Goal`. `RawProgram` is an arbitrary finite ordered list.
  The list's completeness and source scoping are still outside this checker.
- `roles : Roles.RoleDecls` is the existing total Nat→RoleDecl signature function.
  `Valid` computes goal scope ≤1, argument count = declared arity, and associated
  name membership. A total function cannot establish source role visibility.
  Signature lookup is not a proof of parser/name-resolution adequacy.
- `build` internally consumes the computed pointwise validity proof. The public
  `check` asks for no scope proof, successful resolver result, selected candidate,
  completed frontier, fuel, assignment or source valuation.
- `check_exact` quantifies all roles/raw/program and gives success iff erasure
  equals raw and every row is valid. `check_accepts` and `check_fails` characterize
  acceptance and an invalid-row witness. `erase_ofValid`, `erase_injective`,
  `eraseProgram_injective`, `erase_build`, `checked_length`, `checked_rows`
  support exact preservation of every occurrence and order.
- `materialized_declared` takes a successful check, a member row and an independent
  Materializes derivation; it concludes declared arity and name membership for
  the actual generated goal. No dictionary existence is assumed or concluded.
- `checked_source_exact` and `checked_solver_exact` additionally take env/core wf,
  associated awf, an accepted program, any old state, and (model version) any
  assignment. They package exact erasure with cycle78's model/solver iff, without
  changing that judgment. They are not independent new raw-source adequacy proofs.

Spec6.1–6.3 and existing RoleDecl/AssocComplete/AssocDeclared fix the signature
checks. Placeholder scope ≤1 and int/str encoding remain implementation-fragment
limits, not newly chosen language rejection rules. The runtime regression that
role999 can pass the total signature function while dictionary resolution fails
makes the visibility boundary explicit. Q1/Q2 and cycle23/24 remain unresolved.
No new semantic choice or question. I-13 remains partial; five B4 bridges remain.

## Q. cycle80: grouped associated clause extraction

`CommonRoleAssociatedClauseExtraction` replaces the externally selected raw row
list by extraction from finite grouped clauses. Its complete new caller inputs:

- `Equation` has associated `name : Nat` and ordinary source `output : Nat`.
  `Clause` has `receiver : Nat`, `goal : Roles.Goal`, and `equations : List Equation`.
  `Source` is a finite ordered list. Scope-resolved source identities, role names,
  raw structural goal syntax and complete clause selection still come from outside.
  This is not the Rust parser AST or a theorem about parsing actual Yulang text.
- `lower` computes every raw row, in clause/equation order. Caller does not supply
  a separate flattened list, slot map, identity function, occurrence number or fuel.
  `lower_exact`, `lower_cons`, `lower_append`, `lower_length`, `lower_position`
  quantify arbitrary finite lists, rows or prefix/clause/suffix/within-clause
  positions. They establish provenance plus order, counts and duplicate retention.
- `ValidSource`, `check`, `valid_exact`, `check_exact`, `check_accepts`, `check_fails`
  use the existing total `Roles.RoleDecls`. Validation is pointwise on equations,
  not whole role clauses. `checked_count`/`checked_occurs` additionally quantify
  any successful program returned by the checker. The check computes its proofs.
- `Step` uses env/roles, a clause/equation and arbitrary input/output scalar heads.
  It reads structural Fills and independent Resolves/AssocDerives, not resolver
  output. `step_exact` additionally relates a structural row by exact erasure.
- `Derives`/`derives_exact` take env/roles, source, accepted program and arbitrary
  old state. Recursive rules read original source clauses. The initial Seed rule
  still reads the computed table of that accepted program and existing ordinary
  scalar Evidence; source expression inference and general semantic knownness
  remain outside. Acceptance cannot be replaced by arbitrary program selection.
- `run_evidence_exact`, `run_source_exact`, `solver_source_exact` also require
  core `wf` and associated `awf`. They quantify every slot/head or assignment as
  appropriate. Source valuations occur in the conclusion, not as caller choices.

Spec6.3 fixes ordinary shared variables and associated equations. Spec6.1–6.2
fix declared signatures, while visibility and source registry construction are
not established by the total signature function. Empty equation lists produce no
edges, even when the clause has an invalid arity: this is intentional projection,
NOT proof that the bare role obligation is well formed or resolved. A regression
records this limit. Both differently named equations and repeated equations are
retained; duplicate source associated declarations are a separate question.

No source syntax/defaulting/coherence/revisit semantics was chosen. Q1/Q2 and
cycle23/24 remain unresolved. The proposed source derivation is a fragment model,
not a claim of full-language soundness or completeness. Five B4 bridges remain;
I-13 full audit is still incomplete and its cycle72 deadline was missed. Inventory
mention counts do not measure audited inputs.


## R. cycle81: retain bare and associated source role obligations

`CommonRoleSourceRoleObligations` takes the same finite scope-resolved Source as
cycle80. It does not supply a Rust AST-to-Source theorem or make dynamic children.
All new caller inputs and construction boundaries are:

- `RawObligation` contains `receiver : Nat` and `goal : Roles.Goal`; `Obligation`
  contains receiver and a checked structural Template. Public `check` computes
  these from every Clause. `Package` contains the ordered obligation list and
  existing equation Program. Erasure, count and occurrence theorems quantify
  arbitrary accepted packages; callers do not choose an independent role list.
- `ValidClause` and `ValidSource` use the existing total `Roles.RoleDecls` and
  compute scope ≤1, signature arity and all associated names. `valid_equations`
  establishes the previous projection's validity. `build` is an internal proof-
  carrying constructor. `check_exact`, `check_accepts`, `check_fails` expose no
  caller validity certificate. `checked_equations` preserves the previous entry.
- `runOne`, `runRoles`, `runSource` and independent `Discharges` receive an impl
  list and `WellFormed` proof, plus `heads : Nat → Inference.Base`. For each
  receiver this map provides an explicit int/str head for existing structural
  materialization. It is NOT computed from source inference or saturation.
  A future outer adapter must derive heads from an appropriate stable source
  state and prove that evidence agrees; no such adapter is claimed here.
- `run_one_exact` additionally takes one erased obligation/source equality.
  `run_roles_exact` and `missing_role_blocks` take an accepted package; the
  latter takes an explicit source member and independent missing evidence.
  `run_source_exact` computes validation internally, removing that successful-
  check premise. `run_source_permutation` takes only a source List.Perm witness.

Spec6.1–6.2 gives declaration signature shape. Spec6.3 requires every where child
and fixes sibling conjunction. Source visibility and environment construction
remain outside the total registry. The source-head map is a deliberately exposed
proof interface, not a specification answer about when a receiver becomes known.
Spec6.3 explicitly postpones language-visible finalization until sibling updates
stabilize; this module produces only a Boolean test and does not finalize anything.
Its int/str encoder also limits constant templates whose receiver is unused.
Those are implementation-fragment limits, not language rejection rules.

The associated-equation run and this role test are separate interfaces. No theorem
identifies the supplied heads with associated saturation output or combines their
results into full-source typing. Existing Q1/Q2 and cycle23/24 remain unresolved.
No new semantic choice or question. Five B4 bridges remain and I-13 is partial;
inventory mention counts do not measure completed input audits.


## S. cycle82: joint source evidence and all-role readiness

`CommonRoleSourceStateDischarge` retains the finite scope-resolved Source, total
RoleDecls, AssocEnv, core WellFormed and AssocWellFormed inputs. The accepted
Package is constrained by the actual cycle81 checker; it is not an arbitrary
replacement source. The initial State is indexed by the computed joint table.
Source expression inference and construction of that initial state remain outside.

- `table`, `roleSlot`, `equationSlot`, `liftOccurrence`, `occurrences`, `graph`
  derive every slot, name identity, equation edge and template from the Package.
  The table consists of every role receiver followed by equation endpoints.
  There is no caller slot map, universe, visit sequence or fuel. Bare roles do
  not need dummy equations. `occurrence_origin` and `occurrence_present` check
  both directions of the equation lowering; `slot_count` states its capacity.
- `prepared` adds existing source type identities. `runState` computes finite
  associated closure. `Derives` is the independent declaration graph judgment.
  `SourceDerives` has only original-state Evidence and original source clause
  equations; its step uses independent structural filling and AssocDerives.
  `allocated_to_source`, `source_to_allocated`, `run_source_evidence_exact`
  quantify every relevant slot/head; no successful execution is assumed.
- `runOne`, `runRoles`, `ready` derive scalar candidates from actual output
  evidence, call real role resolution and the ordinary solver. The caller
  head map from cycle81 is gone at this entry. Unsupported encodings and
  missing evidence yield false, not a new language diagnostic category.
- `Supported` and the intermediate readiness theorem quantify package positions
  in their conclusions. `ready_original_source_exact` removes those witnesses
  from its source-clause condition. `SourceModels` uses the old state, source
  coherence and SourceDerives only. `source_models_exact` and
  `ready_declarative_exact` remove executable saturation from the independent
  side. A valuation exists in the conclusion, never as a caller-selected map.
- `ready_has_models` needs only the concrete true result, not associated wf;
  it exposes the ordinary consistency guard. `derives_same_receiver` takes
  an explicit equality of two already computed receiver names.

Spec6.3 supplies source-variable sharing, associated equations, conjunctive
where requirements and waiting for stable sibling updates. Scope resolution,
visibility, complete semantic knownness and final language classification are
not supplied by these finite carriers. The computed graph saturates before role
checks; it is not a dynamic where driver. Existing Q1/Q2 and cycle23/24 remain
open. No new semantic decision. Five B4 bridges and the incomplete I-13 audit
remain; inventory mention counts are not audit completion counts.

## T. Cycle83: checked source entry from named scalar assumptions

`CommonRoleNamedSourceEntry` has the following public caller inputs:

- `env : AssocEnv`, `roles : RoleDecls`, `wf : WellFormed env.cores`, and
  `awf : AssocWellFormed env roles`. These existing checked declaration
  boundaries remain explicit. Real source declaration checking, visibility,
  namespace resolution and production of these proofs are not supplied here.
- `src : CommonRoleAssociatedClauseExtraction.Source` is a finite list of
  scope-resolved original clauses. Source syntax, binders, invocation identity
  and dynamic where construction remain outside. Spec6.3 provides equations,
  sharing and conjunction, not this parser-to-carrier construction.
- `input : Assumptions` is `List (Nat × Inference.Base)`: explicit named scalar
  equations, not a total head assignment. Their production from expressions is
  still a source-inference boundary. Only names in `names src` are interpreted;
  irrelevant bindings are outside this finite interface's domain. The module
  does not decide whether real source syntax permits an unused annotation.

Derived inputs and intermediate proof boundaries:

- `names` reads original receivers and equation endpoints. `check` computes
  the Package. `initialFacts` enumerates finite slot/base pairs and selects
  exactly the named input equations. `initialState` emits checked equality
  atoms. The public `runSource` computes these before saturation and role
  discharge. Package, State, slot maps, head maps, fuel and visit orders are
  no longer caller inputs at this entry.
- `initial_facts_exact`, `initial_evidence_exact`, `initial_models_exact` take
  arbitrary Package/input and, where needed, a slot/head or arbitrary valuation.
  The valuation is quantified for a model equivalence, not a chosen solver
  assignment. `table_names_exact` and `receiver_present` take successful check
  evidence only in the internal allocation lemmas.
- `Derives env roles src input name head` reads only named assumption membership
  and independent original clause Step. `allocated_to_named` needs an existing
  cycle82 source derivation; `named_to_allocated` additionally uses an accepted
  package internally to reach all its matching slots. `run_evidence_exact`
  combines these with the finite saturator and explicit wf/awf.
- `Models` existentially quantifies a source-name type valuation satisfying
  derived facts on the original name domain. `models_exact` relates it to the
  internal allocated model. `ready_exact` is the checked-package intermediate.
  `run_source_exact` removes that premise: source validity is a conclusion
  conjunct, with Models and every original role's independent discharge.
- `derives_transport` takes source/assumption membership implications.
  `names_member` describes the original domain. `run_source_congr` takes
  membership equivalences for source clauses and assumptions; both allocations
  and states are recomputed. It permits order changes and duplicates without
  a caller-provided reindexing or semantic preservation certificate.

This entry deliberately has only named scalar assumptions, not arbitrary old
ordinary atoms or effect constraints. The cycle82 general State entry remains
unchanged. Bool/unit are evidence but not encoded role receivers, scope ≤ 1 is
an implementation fragment, and false does not assign a language diagnostic.
No new language decision. Existing Q1/Q2 and cycle23/24 remain unresolved.
The total I-13 audit remains incomplete and the original cycle72 deadline was
missed. Mention counts do not measure completed semantic coverage. B4 still
has all five main bridges open.


## U. Cycle84 — source-name renaming and capture boundary

Module: `CommonRoleNamedSourceRenaming`.

- `renameEquation f`, `renameClause f`, `renameSource f`, `renameInput f` take
  `f : Nat → Nat` and existing finite source/input carriers. Only original
  receiver/output/input names change. Role IDs, associated member IDs and
  the local structural Goal binder remain unchanged. The allocator and initial
  ordinary state are recomputed by the cycle83 entry, not supplied by caller.
- `step_rename`, `valid_clause_rename`, `valid_source_rename`, `names_rename`,
  `derives_rename`, and `discharge_rename` permit any name map. They do not
  certify that an arbitrary map is safe for equality of solver results.
- `derives_original`, `derives_rename_exact`, `models_rename_exact`, and
  `run_source_rename` explicitly take `Function.Injective f`. This is a proof
  condition on the chosen encoding, not a language rule about invocation
  identity. `models_rename_exact` existentially constructs/pulls back valuations;
  no chosen model is a caller input. Private `originalName`/`original_image`
  are inverse-witness proof machinery and are not used by the executable entry.
- `run_source_rename` takes arbitrary env/roles/wf/awf/src/input. The well-formed
  registries and finite scalar/one-binder fragment are inherited cycle83
  boundaries. It proves equal Bool readiness, not dictionary observation or
  final rejected/pending/ambiguous classification.

Planned derivation: a future scoped source lowering must compute names and prove
its encoding injective on distinct identities (or justify intended sharing).
Spec §6.3 establishes associated equations and sibling conjunction, but does
not choose invocation identity. Existing Q1/Q2 and cycle23/24 remain pending.
The full global injectivity hypothesis in this module is a sufficient interface
condition, not the minimal finite-support condition and not a language limit.

Inspected declaration gap: `Roles.Impl.constraints : List Goal` contains core
where goals, without the receiver/output names and associated equations of
`CommonRoleAssociatedClauseExtraction.Clause`. `Roles.AssocImpl.assoc` contains
associated bodies, not those source annotations. No extraction from these fields
alone is claimed. Reuse an authoritative source carrier or establish its
preservation before connecting this entry to full Parent/Left/Right inference.
No new semantic decision or duplicated question note was introduced. I-13 total
coverage remains incomplete; inventory counts are not semantic audit counts.


## V. Cycle85 — computed finite renaming support

Module: `CommonRoleFiniteSourceRenaming`.

- `support src input` reads receiver/output names from existing finite source
  and every input assumption's name. No domain list is caller-supplied.
- `CollisionFree f src input`, its Decidable instance and `check` inspect only
  this support. `check_exact` and `check_fails` expose the condition and a
  concrete conflicting pair. The caller still chooses `f : Nat → Nat`; the
  executable checker no longer asks for global Function.Injective evidence.
- `derives_supported` has arbitrary env/roles/source/input/name/head and an
  independent derivation. `derives_original` and `derives_exact` take the
  finite CollisionFree proposition; the latter explicitly restricts the
  queried name to support. An unsupported query can collide from outside,
  so unrestricted evidence reflection is deliberately not claimed.
- `models_exact` existentially constructs a valuation using a private supported
  inverse witness (`originalName`/`original_image`); no model is an input.
  These private proof helpers are not in the executable checker.
- `run_source_exact` takes finite CollisionFree, env/roles/wf/awf and recomputes
  allocation/state. `renameChecked` computes safe source/input output or none.
  `rename_checked_exact` characterizes it; `checked_readiness` uses successful
  checking, not solver success, to preserve Bool readiness without a caller
  injectivity proof. The input map is required to be computable for execution.

Spec §6.3 governs associated equalities and where conjunction, not invocation
sharing. This cycle changes representation safety, not that unresolved policy.
Input-only names must participate because capture can create false evidence.
The check is conservative (including irrelevant input/input collisions), not
a characterization of every map whose readiness result happens to agree.
Extraction of source/input/f from real declarations remains future work. No
new semantic decision. Existing Q1/Q2 and cycle23/24 remain pending. All five
B4 bridges and the total I-13 semantic audit remain incomplete.


## W. Cycle86 — source-derived canonical allocation

Module: `CommonRoleComputedSourceAllocation`.

- `encode src input name` and `allocate src input` take only the existing finite
  source/input carriers. The name map and capacity come from the first index
  in `support src input`; the caller supplies no domain, map or injectivity.
- `encode_bound`, `decode_encode`, `encode_safe`, `checked_allocation` and
  `allocated_name_bound` certify finite capacity, exact decoding and acceptance.
  Capacity counts occurrences with repetitions, not distinct identities.
- `allocated_derives` takes arbitrary env/roles/src/input/name/head. Unlike the
  generic finite renaming theorem, no query-support hypothesis is needed:
  unused names encode to capacity and cannot alias any supported name.
- `allocated_models` constructs model witnesses inside the inherited proof.
  `allocated_readiness` takes arbitrary env/roles/wf/awf/src/input, recomputing
  checking, allocation and saturation. No old state, chosen package, model,
  fuel or successful solver result is passed from outside.
- `support_rename` holds for every name map. `encode_rename` and `allocate_rename`
  take a map collision-free on the original computed support. This is a
  representation-comparison hypothesis, not an input to `allocate`.
  `allocate_idempotent` has no map or collision premise. Canonicality is for
  preserved occurrence order and multiplicity, not arbitrary source permutations.
- Private list-index, name-list, composition and pointwise-congruence lemmas
  are proof machinery with explicit finite membership hypotheses.

Actual source/assumption extraction is still external. Spec 6.3 does not choose
invocation sharing, and Roles.Impl.constraints does not retain grouped source
annotations. This encoding result neither reconstructs those annotations nor
settles existing Q1/Q2 or cycle23/24. All five B4 bridges remain open. The total
I-13 semantic audit remains incomplete; inventory reachability is not coverage.


## X. Cycle87 — checked annotated-literal inputs

Module: `CommonRoleAnnotatedLiteralInputs`.

- `Binding` takes a scope-resolved name, existing `Inference.Expr`, and an
  explicit scalar annotation. Name and grouped-source resolution remain outside.
  `Valid` checks that each expression is its annotated scalar literal. This is
  an implementation fragment boundary, not a language prohibition on other terms.
- `BindingMeaning` uses existing `Core.PresenceGeneration.Typing Common.model`
  and the annotation upper bound. `binding_meaning_exact` needs checked literal
  syntax and arbitrary common value type. `literal_check_exact` quantifies all
  literal/annotation pairs and existentially constructs or rules out a value
  model. `literal_does_not_force_scalar` exhibits a wider literal typing, so a
  bare expression lower bound cannot be silently converted to an equality.
- `lower` computes ordered named facts from annotations, retaining duplicates.
  `Seed` independently reads original bindings and checked syntax. `lower_exact`
  requires the whole-list Valid condition, not solver success.
- `Derives` closes original Seeds under source equations. `derives_exact` and
  `models_exact` connect them to the previous entry under Valid. `Models` keeps
  the inherited source-only name domain; unrelated input names are not globally
  constrained. `models_bindings` explicitly needs source-domain membership and
  a valuation satisfying independent facts. It proves actual literal/annotation
  meaning for each such binding; the valuation is not an executable input.
- `run` takes env/roles/wf/src/bindings and computes validation, facts, canonical
  names, package/state and readiness. `run_exact` adds awf for soundness and
  completeness. It has no caller atoms, map, fuel, model or success hypothesis.

Spec 3.1 supplies literals; spec 4.2 specifies value-annotation checking and
published type, while effects pass through. The literal fragment is pure; no
annotation rule for fixing effect rows is introduced. Spec 6.3 supplies the
existing role equations. Caller annotations are genuine source syntax in this
interface, not invented ordinary constraints. Parser lowering, source identity,
nonliteral inference and invocation sharing remain unproved. Existing questions
and all five B4 bridges remain open. Total I-13 coverage remains incomplete.

## Y. Cycle88 — checked scalar expression inputs

Module: `CommonRoleScalarExpressionInputs`.

- `infer` takes a finite scalar context and an existing `Inference.Expr`; the
  public binding checker always uses the empty context. Only literal, variable
  and let are supported. `infer_exact` matches independent `Evaluates` rules,
  including lookup failure and the evaluated RHS of every let. De Bruijn names
  inside expressions are already resolved by the existing Expr carrier.
- `LowerEnv` is a proof interface, not a runtime input: every typed lookup of a
  scalar context entry has its scalar lower bound. `evaluates_lower` quantifies
  arbitrary existing environments and typings satisfying this relation, and
  covers both existing let rules. `evaluates_typed` uses a computed canonical
  monomorphic environment and constructs typing at every scalar supertype.
- `annotation_exact` takes independent support `Evaluates [] e head`, not checker
  success; it is complete only for this fragment. `meaning_exact` connects a
  checked scalar annotation to the existing typing and annotation upper bound.
  The upper bound is explicit source syntax, not inferred from a literal alone.
- `Binding` reuses the prior carrier: scope-resolved name, Expr and explicit
  scalar annotation. `Valid` is executable. `valid_exact` removes its computation
  from the independent final statement. `Seed` requires original expression
  evaluation; `Derives` adds only original grouped source equations.
- `lower_exact`, `derives_exact` and `models_exact` take whole-list Valid.
  `models_bindings` also takes source-name membership and a valuation satisfying
  independent facts. It proves existing expression/annotation meaning there.
- `run_exact` takes env/roles/wf/awf/src/bindings. Its right side requires original
  evaluation for each input, valid source, an independent model and independent
  discharge. Atoms, map, model and success are not executable inputs. Name
  resolution and grouped clauses, annotations and registry well-formedness remain.

Spec 3.1 supplies literals; 3.5 specifies let RHS then body evaluation (including
unused RHS); 4.2 specifies annotation bounds. The module uses existing lexical
Expr/Typing, not a new resolution rule. It does not settle invocation sharing,
nonlinear heads, role-variable scope, generic/effectful input inference or parser
lowering. Unsupported input is not language rejection. Existing questions and
all five B4 bridges remain. I-13 full semantic coverage is still incomplete.


## Z. Cycle89 — actual recursive where-declaration closure

Module: `CommonRoleGeneratedWhereClosure`.

- `children`, `Unique`, `Edge`, `Reach`, `Missing` take a finite first-order
  `List Roles.Impl` and goals. Declarations carry role/head/where/key. `Edge`
  quantifies an arbitrary substitution matching the original head and a real
  child occurrence, rather than reading executable closure or solver success.
  The use of `Unique` follows spec 6.2; it does not infer scalar information.
- `closure`, `classify`, `registerOne`, `runOne` and `runSource` also take existing
  `WellFormed impls`. Recursion derives strict measure decrease from that actual
  declaration check at every call. No caller visit sequence, fuel, graph or child
  list survives. `checkedClassify` removes this proof input by invoking existing
  `CheckedRoles.checkDatabase`; `checked_exact` has no WF premise.
- `registerOne` retains the source receiver owner, not a newly invented identity
  for declaration binders or invocation instances. `registered_exact` proves a
  root owner and an independent reachable goal for every registered element.
  The list preserves repeated children; membership exactness alone does not
  identify occurrence positions or decide revisitation sharing.
- `runSource` retains role signatures, grouped source and a scalar name/head
  function. These are the same boundary inputs as the existing source entry;
  `run_source_agrees` and `run_source_exact` state literal agreement and the
  original independent discharge judgment. It is not connected to source
  expression inference here; cycle88's expression entry remains unchanged.
- `closure_resolves`, `registered_resolves` and `edge_resolves` explicitly take
  the respective root success/evidence when deriving descendant success. The
  closure construction and membership theorem themselves require no success.
- `resolve_unique_closure`, `ambiguous_exact` and `noImpl_exact` quantify all
  finite checked first-order registries and arbitrary goals. They are complete
  for that carrier, not the state-dependent Common interval system. Missing and
  overlapping siblings are both retained; ambiguity is only the final priority.

Spec 6.2/6.3 governs unique heads, all-child conjunction and Paterson descent.
Parser/name lowering, semantic-normalization adequacy and associated-where
annotations absent from `Roles.Impl.constraints` remain unproved. This work does
not settle pending invocation, nonlinear Common head or where-variable questions.
Five B4 bridges and incomplete I-13 semantic coverage remain explicit.


## AA. Cycle90: CommonRoleIntervalWorkClosure

- Inputs to `compute`: `registry : List Declaration`, `root : Goal`. The existing
  declaration checker is computed internally. Visible registry and root endpoint
  syntax still require source/ordinary lowering (spec 6.2, 6.3). There is no
  supplied work list, stopping witness, finite source domain, or source-owner map.
- `closure` / `domain` additionally take `Checked registry` only as internal
  helpers. `compute_reach_exact` moves this check to the result side, not an
  unchecked caller assumption.
- `Edge` has original declaration, captured bindings and requirement membership,
  with independent `Accepts`. `Reach` is an independent finite-path judgment.
  These are proof-side derivations; executable closure computes both children and
  termination from actual scans and the declaration check.
- `prepared_child_closed` quantifies arbitrary slots, old demands, bindingSource,
  actual returned candidate, and child membership. These remain the underlying
  prepare entry's inputs, as documented in A4. They are not inputs to `compute`.
  The theorem does not manufacture source keys or prove interval-state adequacy.
- `domain_allocation` quantifies arbitrary graph, role and visible heads and proves
  snapshot preservation. It does not prove graph/ordinary correspondence.
- Endpoints are fixed syntax. `CommonRoleWhereSourceModels.run` computes its scan
  from declaration and goal, not from old ordinary demands. State updates can
  change future materialized goals; this closure does not cover them without a
  separate refinement/replay theorem. Potential branches must retain guards when
  incorporated into a solver; never conjoin all registry candidates.
- `boundaries` retains scanner `none` at every reachable node. Nonlinear/join
  heads remain outside the implementation fragment, not language errors. This
  uses the existing boundary; no new meaning for pending/ambiguous is chosen.

Spec 6.3 supports finite checked where descent and shared source variables.
Invocation lifetime questions and full I-13 semantic coverage remain open. The
source-domain name iff does not imply finite structural work without Paterson.

## AB. CommonRoleGuardedIntervalPlans (cycle91)

- `registry : List Declaration`, `goal : Goal`: supplied elaborated fixed Form endpoints and visibility; parser/scope/annotation adequacy remains bridge 1. `run` computes the actual declaration check, and compile termination is derived from it.
- `slots : Nat → α`: original ambient endpoint slot assignment; unchanged boundary from WhereSourceModels. Not computed from source in this module.
- `Sources := Goal → Declaration → Nat → Nat`: supplied invocation-local binder to source key map. Equal goal/declaration/binder tuples necessarily alias, so this adapter cannot independently name repeated identical occurrences. No fresh invocation identity or general source allocator is proved. The existing invocation-lifetime question remains open; spec 6.3 supports shared logical variables but does not derive this tuple keying.
- `old : List (Demand α)`: original ordinary demand history, retained with every alternative. `assignment` and `values` are universally quantified model/semantic inputs; `run_models_exact` existentially chooses a single `values` outside the full recursive judgment. They are not preselected witnesses.
- `compile_exact` and `ordinary_exact` require Checked; public `run_models_exact` computes it and places it on the result side. No caller fuel, visit sequence, closure proof, child success or model existence.
- Fixed syntax only. `run` preserves unsupported scans in its second component via `run_boundaries_exact`; the plan list itself omits them, and is not a final rejection/selection classifier. Separate declaration choices are disjoined; child plans are conjoined with cross-sibling constraints. General state-dependent materialization and dictionary equivalence remain open.

## AC. CommonRoleGuardedIntervalFrontier (cycle92)

- `run` inputs are registry, slots, Sources and fixed goal, exactly the AB
  boundaries. It computes the declaration check and all child trees. No child
  success proof, finite work domain, fuel, or source valuation is supplied.
- `Sources` still identifies equal goal/declaration/binder tuples. This is not
  a derived source-occurrence allocator or a resolution of invocation lifetime.
- `ordinary` also receives old demands; `run_models_exact` quantifies arbitrary
  assignments and existentially obtains one global source valuation.
- `Tree` is public data, so arbitrary caller-constructed trees need not be valid.
  Model/retention theorems explicitly concern actual `build`/`run` outputs.
- Accepted parent branches retain their exact full recursive children regardless
  of success. Per-node outside and rigid rejects are separate, but no final
  language classification is assigned. Spec 6.3 supplies the all-child and
  delayed-classification requirements, not a general state-materialization map.
- Source lowering, state-dependent revisits, K2 and dictionary observations remain
  the same open boundaries. Global flattened outside-list equality is not proved.

## AD. CommonRoleFrontierReachability (cycle93)

- `nodes`, `goals`, `boundaries`, `failures` read an arbitrary public Tree. Their
  semantic theorems only concern actual `build`/`run` outputs, never forged trees.
- Inputs are exactly the registry/slots/Sources/fixed Goal boundary of AC. No new
  source identity or state update policy is chosen. The full tree traversal is
  proved equal to independently generated closure, preserving list multiplicity.
- The AC global flattened outside-list gap is closed by `build_boundaries`.
  `run_boundaries_exact` and `run_failures_exact` put the computed Checked registry
  condition on the RHS and expose independent Reach + local scan judgments.
- Failures are local declaration rejections, not a failure classification of the
  goal. Empty registry, no plans, and unsupported scans remain distinct.
- No fuel, visit list, child success, model existence, or external stopping proof
  is supplied. Fixed syntax remains the scope; state rematerialization, K2,
  source lowering, invocation lifetime and dictionary observations remain open.

## AE. CommonRoleFrontierGraphs (cycle94)

- Public inputs: registry : List Declaration, slots : Nat -> Fin n, Sources,
  existing : List (Atom (Fin n)), old : Plan (Fin n), goal : Goal. Registry,
  fixed syntax, source aliasing and ambient slots have exactly the AB-AD
  boundary. Old ordinary atoms are arbitrary, not a supplied consistency proof.
- Graphs are actually computed by CommonPresenceConstraintGraph.compile. Their
  independent Models semantics does not consult origin metadata. Original input
  injection and literal readback are proved; every original row is retained.
- `run_models_exact` derives Checked on the result side and quantifies every
  assignment with one shared source valuation. No fuel, model, child success,
  finite visit sequence, or caller grammar certificate is assumed.
- `advance_exact` takes arbitrary fresh atoms; it proves only model restriction
  on the fixed tree. `advance_replays` returns an earlier graph model with the
  same original readback, not identical allocated graph nodes. It is not state
  materialization, an ordinary decision procedure, or a saturation theorem.
- Graphs exist even for inconsistent complete plans. Unsupported and missing
  child diagnostics remain in the unchanged tree, whether or not any graph
  exists. Spec 6.3 motivates conjunction within plans and delayed diagnostics.
  Invocation identity and all five major B4 bridges remain open.

## AF. CommonRoleStateMaterializedFrontier (cycle95)

- Inputs: registry : List Declaration, original : Goal, slots : Nat -> Fin n,
  Sources, atoms : List (Atom (Fin n)), old : Plan (Fin n). Registry, original
  source Form, ambient slots, invocation map and old demands remain caller
  boundaries from AB-AE. Spec 6.3 supports constraint-driven narrowing; this
  module does not derive any of those inputs from parser/scope/annotations.
- materialize uses the actual ordinary detector, replacing a variable only
  when its first detected scalar is int. Other bases and absent evidence keep
  the original source name. Consistency is not assumed by computation or finite
  containment. Conflicting scalar pairs can make its syntax order-dependent;
  arbitrary states are still covered by the finite domain.
- materialize_meaning quantifies every actual state model. detected_int_persists
  and rematerialize_fusion require atom inclusion and a later model, with the
  same slots map. These are explicit mathematical premises, not a model oracle
  supplied to execution. No general entailment or interval solver is claimed.
- goalVariants and workDomain compute a finite overapproximation from the
  original template and checked declarations. Independent occurrence choices
  include impossible sharing combinations. Public run/workDomain require no
  supplied fuel, finite visit list, check proof, successful child or finite bound.
- run_models_exact has Derives at the materialized goal, not original-goal
  derivability. Sources takes Goal as part of its key, so regeneration can change
  aliases even with the same function. Invocation lifetime and its source
  derivation remain the existing open semantic questions, not decided here.
- All actual tree nodes, including unsupported/incomplete children, fit the
  state-independent List Goal. The theorem does not bound internal graph nodes.
  Full generated_work_closed, saturation, stable classification and dictionary
  equivalence remain open; all five major B4 bridges are still incomplete.


## AG. CommonRoleMaterializationProgress (cycle96)

- Fixed original Goal and slots are the AF source-template boundary. The measure
  is computed from variable occurrences in both endpoints, not caller fuel/rank.
  It overcounts repeated names and aliased slots without requiring injectivity.
- changes consumes arbitrary finite lists of actual ordinary atoms. Chain is an
  explicit theorem premise: adjacent atom membership inclusion and existence of
  a later model. No model/proof is passed to computation. A supplied trace is not
  claimed to be a solver-generated trace or a derived saturation execution.
- Materialization count cannot increase; equal count means identical syntax.
  Fusion yields strict decrease for every changed Goal under Extension, hence
  changes plus final potential is bounded by the first materialized potential.
  The latter is at most the original syntax count, independently of trace length.
- run_tree_equal/strict/plateau concern the entire Tree projection of actual
  public graph runs, including unfinished descendants and all diagnostics.
  Old demands may differ; ordinary graphs and their models need not be equal.
- A plateau is not a stop signal; later evidence can cause another change. No
  bound on all updates/visits, new templates, graph nodes, runtime or ordinary
  solving follows. Contradictory inclusive states or noninclusive consistent
  states can undo materialization, so both Chain premises are necessary.
- All results are auxiliary progress facts for the existing explicit-int
  implementation fragment, not a spec rejection policy or B4 completion. Source
  identity, all five major B4 bridges and X13-X16 outer acceptance remain open.
