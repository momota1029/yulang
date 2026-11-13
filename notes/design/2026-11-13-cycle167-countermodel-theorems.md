# Cycle 167: countermodel 公開定理索引

対象は以下の三つの新規モジュールの **全公開 theorem**。private theorem と def/abbrev は定理数に含めない。各項目には日本語の量化・前提・結論と、証明本体を除いた実際の Lean 宣言を併記する。`{...}` の暗黙引数も全称量化として読む。

## 共通記号と適用範囲

- 名前空間接頭辞は `Yulang.`。各見出しはその後の完全な名前空間を示す。
- 具体的項目の `roles` は `GeneralDeclarationExamples.roles`。`{roles : Roles.RoleDecls}` または `{rs : Roles.RoleDecls}` を明記した項目だけが任意の role 宣言に量化する。
- `packet`、`producer`、`consumer`、`source`、`registry`、`lo`、`hi`、`target` は既存 captured-input fixture の固定値。`candidate` はその固定 producer packet。`observed` は実際の producer installation と scalar refresh 後の `GeneralDictionarySharedCapturedResumption.observed`。
- `oldModel` は既存の string-tail novelty model。新 `model` はその target だけを int に上書きした assignment。source 2 は str のまま。`tower 0` は str、`tower (n+1)` はその nominal 包装。InputCountermodel の model は AliasCountermodel の model の別名。
- `Models`、`Trusted`、`ReadyAt` は宣言中の名前空間を優先する。全 journal の Models と SharedSupport の slice Models は混同しない。
- 一般定理は既存定義の任意の対象についての補題。具体的反例は固定 fixture / 固定 observed に限る。将来のすべての拡張状態の不可能性、非停止、論理的不整合、一般 V5 完了は主張しない。

## GeneralDictionaryCapturedSettlementBoundary

### alias_eq_of_empty

分類: **一般**。任意の role 宣言、状態、二つの識別子について、alias 辺一覧が空で Alias 導出が存在すれば、両識別子は等しい。

```lean
theorem alias_eq_of_empty {roles : Roles.RoleDecls} {state : State roles} (empty : state.aliases = [])
    {first last : Nat} (same : Alias state first last) : first = last
```

### discharged_identity

分類: **一般**。任意の role 宣言、状態、occurrence について、alias 辺一覧が空で occurrence が Discharged なら、その識別子を持つ記録済み packet が存在する。

```lean
theorem discharged_identity {roles : Roles.RoleDecls} {state : State roles} (empty : state.aliases = [])
    {occurrence : GeneralSourceDictionaries.Occurrence roles}
    (done : Discharged state occurrence) :
    ∃ p ∈ state.packets, p.site.occurrence.identity = occurrence.identity
```

### trusted_output_settled

分類: **一般**。任意の role 宣言、Tracked 状態、facts、readbacks、packet、support について、Trusted 導出とその出力 fact の所属を仮定すると、その packet は現在状態で PacketSettled。

```lean
theorem trusted_output_settled {roles : Roles.RoleDecls} {state : Tracked roles} {facts : List (Fact roles)}
    {readbacks : GeneralNominalSharedSupport.Readbacks}
    (trusted : GeneralNominalSharedSupport.Trusted state facts readbacks)
    {p : Packet roles} {support : List (GeneralSourceDictionaries.Occurrence roles)}
    (member : Fact.outputs p support ∈ facts) :
    GeneralNominalSettledSupport.PacketSettled state.current p
```

### consumer_not_discharged

分類: **具体的反例補助**。追加仮定なし。固定した observed 現在状態では固定 consumer は Discharged でない。

```lean
theorem consumer_not_discharged : ¬ Discharged observed.current consumer
```

### parent_not_trusted

分類: **具体的反例**。任意の facts、readbacks、support について、固定 observed で Trusted な slice には固定親 packet の出力 fact が所属しない。

```lean
theorem parent_not_trusted {facts : List (Fact roles)}
    {readbacks : GeneralNominalSharedSupport.Readbacks}
    (trusted : GeneralNominalSharedSupport.Trusted observed facts readbacks)
    (support : List (GeneralSourceDictionaries.Occurrence roles)) :
    Fact.outputs packet support ∉ facts
```

## GeneralDictionaryCapturedAliasCountermodel

### target_above

分類: **具体的補助**。追加仮定なし。固定 producer 出力 target は 2 より大きい。

```lean
theorem target_above : 2 < target
```

### old_value

分類: **具体的補助**。任意の自然数 i について i ≤ 2 なら、新反例 model は oldModel と i で一致する。

```lean
theorem old_value (i : Nat) (bounded : i ≤ 2) : model i = oldModel i
```

### source_models

分類: **具体的補助**。追加仮定なし。固定 source の制約は、この名前空間の固定反例 model で成立する。

```lean
theorem source_models : GeneralNominalState.Models source model
```

### output_models

分類: **具体的補助**。追加仮定なし。固定 producer candidate の Outputs は反例 model で成立する。

```lean
theorem output_models : GeneralNominalPacketSupport.Outputs candidate model
```

### slice_models

分類: **具体的補助**。任意の support 一覧について、source と producer 出力 fact 一個からなる固定 observed の slice は反例 model で成立する。この slice が Trusted とは主張しない。

```lean
theorem slice_models (support : List (GeneralSourceDictionaries.Occurrence roles)) :
    GeneralNominalSharedSupport.Models observed [Fact.outputs candidate support] model
```

### captured_not_int

分類: **具体的反例補助**。追加仮定なし。反例 model の source 2 は int と Equivalent でない。

```lean
theorem captured_not_int : ¬ Equivalent (model 2).1 (.base .int)
```

### alias_not_entailed

分類: **具体的反例**。任意の support について、source と producer 出力一個だけを満たすすべての assignment が target と source 2 の同値性を満たす、という命題は偽。この singleton slice の Trusted 性は仮定も結論にもない。

```lean
theorem alias_not_entailed (support : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ (∀ m, GeneralNominalSharedSupport.Models observed [Fact.outputs candidate support] m →
      Equivalent (m target).1 (m 2).1)
```

### source_slice_trusted

分類: **具体的補助**。追加仮定なし。固定 observed の空 facts・空 readbacks は Trusted。

```lean
theorem source_slice_trusted : GeneralNominalSharedSupport.Trusted observed [] []
```

### source_scalar_not_entailed

分類: **具体的反例**。追加仮定なし。固定 observed の空 facts を満たすすべての assignment で source 2 が int と同値になる、という命題は偽。

```lean
theorem source_scalar_not_entailed :
    ¬ (∀ m, GeneralNominalSharedSupport.Models observed [] m →
      Equivalent (m 2).1 (.base .int))
```

## GeneralDictionaryCapturedInputCountermodel

### model_old

分類: **具体的補助**。任意の自然数 i について i ≤ 2 なら、反例 model の値は固定 string-tail finiteModel の値と一致する。

```lean
theorem model_old (i : Nat) (h : i ≤ 2) : model i = finiteModel i
```

### model_lo

分類: **具体的補助**。追加仮定なし。固定 lo での反例 model の型成分は tower 1。

```lean
theorem model_lo : (model lo).1 = tower 1
```

### model_hi

分類: **具体的補助**。追加仮定なし。固定 hi での反例 model の型成分は tower 1。

```lean
theorem model_hi : (model hi).1 = tower 1
```

### source_models

分類: **具体的補助**。追加仮定なし。固定 source の制約は、この名前空間の固定反例 model で成立する。

```lean
theorem source_models : GeneralNominalState.Models source model
```

### mid_seen

分類: **具体的補助**。追加仮定なし。固定 origin mid から反例 model で tower 1 を観測できる。

```lean
theorem mid_seen : Observes model mid (tower 1)
```

### captured_seen

分類: **具体的補助**。追加仮定なし。固定 captured origin から反例 model で tower 0 を観測できる。

```lean
theorem captured_seen : Observes model origin (tower 0)
```

### mid_same

分類: **具体的補助**。任意の型 t について、固定 model の mid から t を観測したなら t は tower 1 と同値。

```lean
theorem mid_same (t : Ty) (seen : Observes model mid t) : Equivalent t (tower 1)
```

### captured_same

分類: **具体的補助**。任意の型 t について、固定 model の captured origin から t を観測したなら t は tower 0 と同値。

```lean
theorem captured_same (t : Ty) (seen : Observes model origin t) : Equivalent t (tower 0)
```

### private_models

分類: **具体的補助**。追加仮定なし。固定親 packet の privateContext.state は反例 model で成立する。出力事実を含む全 journal の成立とは別。

```lean
theorem private_models : GeneralNominalState.Models packet.privateContext.state model
```

### projections

分類: **具体的補助**。追加仮定なし。固定 source に対する親 packet の report は反例 model で ProjectionModels を満たす。

```lean
theorem projections : ProjectionModels source (GeneralNominalPacketSupport.report packet) model
```

### lo_seen

分類: **具体的補助**。追加仮定なし。lo の nominal 第 0 引数を反例 model で観測すると tower 0 が得られる。

```lean
theorem lo_seen : Observes model (.nominal (.source lo) 0 0) (tower 0)
```

### hi_seen

分類: **具体的補助**。追加仮定なし。hi の nominal 第 0 引数を反例 model で観測すると tower 0 が得られる。

```lean
theorem hi_seen : Observes model (.nominal (.source hi) 0 0) (tower 0)
```

### use_values

分類: **具体的補助**。任意の Use entry が固定親 inputSchema.variables に属するなら、名前は 0、mode は actual、観測値が存在し、任意の観測値は tower 0 と同値。

```lean
theorem use_values (entry : GeneralNominalMaterialization.Use)
    (member : entry ∈ (GeneralNominalPacketSupport.inputSchema packet).variables) :
    entry.name = 0 ∧ entry.mode = .actual ∧
    (∃ actual, Observes model entry.origin actual) ∧
    ∀ actual, Observes model entry.origin actual → Equivalent actual (tower 0)
```

### parent_materialized

分類: **具体的補助**。追加仮定なし。固定親の context、declaration、capture、report に対する inputSchema の Materialization.Models が反例 model で成立する。namedSchema 全体ではない。

```lean
theorem parent_materialized : GeneralNominalMaterialization.Models packet.context.state
    packet.declaration (GeneralNominalPacketSupport.capture packet)
    (GeneralNominalPacketSupport.report packet) (GeneralNominalPacketSupport.inputSchema packet) model
```

### parent_inputs

分類: **具体的補助**。追加仮定なし。固定親 packet の Inputs が反例 model で成立する。

```lean
theorem parent_inputs : GeneralNominalPacketSupport.Inputs packet model
```

### Producer.allocated_value

分類: **具体的補助**。任意の自然数 purpose、owner、position について、固定 producer の allocation origin から生成される source 識別子における反例 model の型成分は tower 0。

```lean
theorem allocated_value (purpose owner position : Nat) :
    (model (GeneralNominalAllocation.source snapshot registry producer.identity
      (GeneralNominalAllocation.origin producer.identity declaration.id purpose owner position))).1 =
      tower 0
```

### Producer.ordinary

分類: **具体的補助**。追加仮定なし。固定 producer candidate の互換性、merge 等式、self checks を含む Ordinary が反例 model で成立する。

```lean
theorem ordinary : GeneralNominalPacketSupport.Ordinary candidate model
```

### Producer.projections

分類: **具体的補助**。追加仮定なし。固定刷新 snapshot に対する producer candidate の report は反例 model で ProjectionModels を満たす。

```lean
theorem projections : ProjectionModels snapshot (GeneralNominalPacketSupport.report candidate) model
```

### Producer.inputs

分類: **具体的補助**。追加仮定なし。固定 producer candidate の Inputs が反例 model で成立する。

```lean
theorem inputs : GeneralNominalPacketSupport.Inputs candidate model
```

### trusted_member_recorded

分類: **一般**。任意の role 宣言 rs、Tracked 状態、facts、readbacks、fact について、Trusted 導出と fact の slice 所属を仮定すれば、fact は状態の記録済み facts に属する。

```lean
theorem trusted_member_recorded {rs : Roles.RoleDecls} {state : Tracked rs}
    {facts : List (Fact rs)} {readbacks : GeneralNominalSharedSupport.Readbacks}
    (trusted : GeneralNominalSharedSupport.Trusted state facts readbacks)
    {fact : Fact rs} (member : fact ∈ facts) : fact ∈ state.facts
```

### recorded_except_parent

分類: **具体的補助**。任意の fact について、固定 observed.facts への所属と、どの support に対しても親出力 fact ではないことを仮定すれば、その fact は反例 model で成立する。

```lean
theorem recorded_except_parent {fact : Fact roles} (member : fact ∈ observed.facts)
    (notParent : ∀ support, fact ≠ Fact.outputs packet support) : fact.Holds model
```

### every_trusted_slice

分類: **具体的反例の一般量化部分**。任意の facts、readbacks について、固定 observed における Trusted 導出を仮定すると、同一の固定反例 model がその slice の Models を満たす。全 support alternatives と全 Trusted slice に量化するが、状態は固定。

```lean
theorem every_trusted_slice {facts : List (Fact roles)}
    {readbacks : GeneralNominalSharedSupport.Readbacks}
    (trusted : GeneralNominalSharedSupport.Trusted observed facts readbacks) :
    GeneralNominalSharedSupport.Models observed facts model
```

### no_trusted_scalar_entailment

分類: **具体的反例**。任意の facts、readbacks と固定 observed の Trusted 導出について、その slice の全 Models が source 2 = int の同値性を満たす、という命題は偽。

```lean
theorem no_trusted_scalar_entailment {facts : List (Fact roles)}
    {readbacks : GeneralNominalSharedSupport.Readbacks}
    (trusted : GeneralNominalSharedSupport.Trusted observed facts readbacks) :
    ¬ (∀ m, GeneralNominalSharedSupport.Models observed facts m →
      Equivalent (m 2).1 (.base .int))
```

### current_head_scalar

分類: **具体的補助**。任意の identity、test、observation について、固定 observed の現在状態に Head があり identity = 2 なら test は scalar int。

```lean
theorem current_head_scalar {identity : Nat} {test : Test} {observation : GeneralCanonicalObservations.Observation}
    (head : Head observed.current.context.state identity test observation)
    (equal : identity = 2) : test = .scalar .int
```

### scalar_head_holds

分類: **一般**。任意の snapshot、identity、scalar base、observation、assignment m について、対応する scalar Head と observation.Holds m を仮定すれば、m の identity の型成分はその base 型と同値。

```lean
theorem scalar_head_holds {snapshot : GeneralNominalState.State} {identity : Nat}
    {base : Inference.Base} {observation : GeneralCanonicalObservations.Observation}
    {m : GeneralNominalCommonBridge.Assignment}
    (head : Head snapshot identity (.scalar base) observation)
    (holds : observation.Holds m) : Equivalent (m identity).1 (.base base)
```

### consumer_input_not_ready

分類: **具体的反例・主要結論**。追加仮定なし。固定 observed の source 2 は SharedSupport.ReadyAt を満たさない。全 Trusted slice・説明 snapshot・観測 witness に対する否定である。

```lean
theorem consumer_input_not_ready : ¬ GeneralNominalSharedSupport.ReadyAt observed 2
```

### consumer_decision_guard_absent

分類: **具体的反例・主要結論**。追加仮定なし。固定 registry、observed、consumer に対する SharedSupport.DecisionGuard は存在しない。

```lean
theorem consumer_decision_guard_absent :
    ¬ GeneralNominalSharedSupport.DecisionGuard registry observed consumer
```

### raw_ready_not_trusted

分類: **具体的反例・主要結論**。追加仮定なし。固定 consumer の raw RootPending は偽であり、同時に source 2 の SharedSupport.ReadyAt も偽。raw readiness と Trusted readiness の乖離を一つの状態で示す。

```lean
theorem raw_ready_not_trusted :
    ¬ GeneralNominalState.RootPending observed.current.context.state consumer.demand ∧
    ¬ GeneralNominalSharedSupport.ReadyAt observed 2
```

## 網羅性と検証

公開 theorem は計 **42 件**。各三モジュールの行頭 `theorem` を列挙し、入れ子 `Producer` の4件を別名空間として含めた。private helper は除外。各モジュールの focused `--trust=0` コンパイルと専用 audit は成功済みで、主要結論の公理依存は propext / Classical.choice / Quot.sound のみ。既存の意味論・guard を変更せずに証明している。
