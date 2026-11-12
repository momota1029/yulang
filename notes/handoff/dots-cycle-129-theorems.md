# Cycle129: 全公開定理の型と意味

新規18 modules、公開125定理。一般B4 V3は12/12未充填。
型はLeanの`#check @定理名`の出力をそのまま載せ、前提や量化子を削らない。
全てI-18項目5の補助・健全性/順序保存。一般完全性・主型性の完成ではない。

## GeneralDictionaryNominalCandidateOrder

固定Context・共通catalogue・checked registryの許された可視順/where順変更について、実report・lookup・bindings・computed Framesとraw再構成/準備のOption全体を保持する。候補選択や異なる最終stateの同値ではない。

### `Yulang.GeneralDictionaryNominalCandidateOrder.report_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrder.report_reorders : ∀ (context : Yulang.GeneralNominalCandidates.Context)
  (first last : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
      Yulang.GeneralNominalCandidates.report context first bounds =
        Yulang.GeneralNominalCandidates.report context last bounds
```

### `Yulang.GeneralDictionaryNominalCandidateOrder.declaration_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrder.declaration_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last } →
    Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
        { constructors := constructors, roles := roles, declarations := last } →
      ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
        (selected : Yulang.GeneralDeclarations.Declaration),
        Yulang.GeneralDictionaryNominalCandidateReadback.declaration
              { constructors := constructors, roles := roles, declarations := first } root key =
            some selected →
          ∃ other,
            Yulang.GeneralDictionaryNominalCandidateReadback.declaration
                  { constructors := constructors, roles := roles, declarations := last } root key =
                some other ∧
              Yulang.GeneralRegistryReordering.DeclarationReorders selected other
```

### `Yulang.GeneralDictionaryNominalCandidateOrder.declaration_none_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrder.declaration_none_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat),
      Yulang.GeneralDictionaryNominalCandidateReadback.declaration
            { constructors := constructors, roles := roles, declarations := first } root key =
          none →
        Yulang.GeneralDictionaryNominalCandidateReadback.declaration
            { constructors := constructors, roles := roles, declarations := last } root key =
          none
```

### `Yulang.GeneralDictionaryNominalCandidateOrder.bindings_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrder.bindings_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last } →
    Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
        { constructors := constructors, roles := roles, declarations := last } →
      ∀ (context : Yulang.GeneralNominalCandidates.Context) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
        (key : Nat),
        Yulang.GeneralDictionaryNominalCandidateReadback.bindings
            { constructors := constructors, roles := roles, declarations := first } context root key =
          Yulang.GeneralDictionaryNominalCandidateReadback.bindings
            { constructors := constructors, roles := roles, declarations := last } context root key
```

### `Yulang.GeneralDictionaryNominalCandidateOrder.frame_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrder.frame_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last } →
    Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
        { constructors := constructors, roles := roles, declarations := last } →
      ∀ (context : Yulang.GeneralNominalCandidates.Context) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Yulang.GeneralDictionaryNominalCandidateReadback.frame
            { constructors := constructors, roles := roles, declarations := first } context root =
          Yulang.GeneralDictionaryNominalCandidateReadback.frame
            { constructors := constructors, roles := roles, declarations := last } context root
```

### `Yulang.GeneralDictionaryNominalCandidateOrder.frames_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrder.frames_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last } →
    Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
        { constructors := constructors, roles := roles, declarations := last } →
      ∀ (context : Yulang.GeneralNominalCandidates.Context),
        Yulang.GeneralDictionaryNominalCandidateReadback.frames
            { constructors := constructors, roles := roles, declarations := first } context =
          Yulang.GeneralDictionaryNominalCandidateReadback.frames
            { constructors := constructors, roles := roles, declarations := last } context
```

### `Yulang.GeneralDictionaryNominalCandidateOrder.reconstruct_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrder.reconstruct_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (context : Yulang.GeneralNominalCandidates.Context) (payload : Yulang.GeneralDictionaryReadback.Payload)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct
          { constructors := constructors, roles := roles, declarations := first } one context payload root =
        Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct
          { constructors := constructors, roles := roles, declarations := last } two context payload root
```

### `Yulang.GeneralDictionaryNominalCandidateOrder.prepare_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrder.prepare_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (context : Yulang.GeneralNominalCandidates.Context) (payload : Yulang.GeneralDictionaryReadback.Payload)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralDictionaryNominalCandidateEvidence.prepare
          { constructors := constructors, roles := roles, declarations := first } one context payload root =
        Yulang.GeneralDictionaryNominalCandidateEvidence.prepare
          { constructors := constructors, roles := roles, declarations := last } two context payload root
```

## GeneralDictionaryNominalSlotTransport

明示的な旧slot埋込み、型/rowの別source map、ordinary/head/interval/nominal descriptorの正確な構文像、global atomsの一致を前提に、任意full nominal assignmentのModelsを双方向に保持する。対象stateの生成や正規化view同値は結論しない。

### `Yulang.GeneralDictionaryNominalSlotTransport.parameter_kind`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalSlotTransport.parameter_kind : ∀ {n m : Nat} (embed : Fin n → Fin m)
  (value : Yulang.GeneralNominalState.Parameter n),
  (Yulang.GeneralDictionaryNominalSlotTransport.parameter embed value).kind = value.kind
```

### `Yulang.GeneralDictionaryNominalSlotTransport.embed_injective`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalSlotTransport.embed_injective : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after), Function.Injective transport.embed
```

### `Yulang.GeneralDictionaryNominalSlotTransport.assignment_embed`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalSlotTransport.assignment_embed : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalCommonBridge.assignment after.base model ∘ transport.embed =
    Yulang.GeneralNominalCommonBridge.assignment before.base model
```

### `Yulang.GeneralDictionaryNominalSlotTransport.term_eval`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalSlotTransport.term_eval : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (term : Yulang.Core.PresenceGeneration.TyTerm (Fin before.base.slots)),
  Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model
      (Yulang.GeneralNominalCommonBridge.assignment after.base model)
      (Yulang.Core.PresenceGeneration.TyTerm.rename transport.embed term) =
    Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model
      (Yulang.GeneralNominalCommonBridge.assignment before.base model) term
```

### `Yulang.GeneralDictionaryNominalSlotTransport.fits_parameter`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalSlotTransport.fits_parameter : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (bounds : Yulang.GeneralNominalState.Parameter before.base.slots) (value : Yulang.CommonNominalFullCarrier.Argument),
  Yulang.GeneralNominalState.Fits after.base model
      (Yulang.GeneralDictionaryNominalSlotTransport.parameter transport.embed bounds) value ↔
    Yulang.GeneralNominalState.Fits before.base model bounds value
```

### `Yulang.GeneralDictionaryNominalSlotTransport.fitsAll_parameters`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalSlotTransport.fitsAll_parameters : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (bounds : List (Yulang.GeneralNominalState.Parameter before.base.slots))
  (values : List Yulang.CommonNominalFullCarrier.Argument),
  Yulang.GeneralNominalState.FitsAll after.base model
      (List.map (Yulang.GeneralDictionaryNominalSlotTransport.parameter transport.embed) bounds) values ↔
    Yulang.GeneralNominalState.FitsAll before.base model bounds values
```

### `Yulang.GeneralDictionaryNominalSlotTransport.denotes_descriptor`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalSlotTransport.denotes_descriptor : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (slot : Fin before.base.slots)
  (value : Yulang.GeneralNominalState.Descriptor before.base.slots),
  Yulang.GeneralNominalState.Denotes after.base model (transport.embed slot)
      (Yulang.GeneralDictionaryNominalSlotTransport.descriptor transport.embed value) ↔
    Yulang.GeneralNominalState.Denotes before.base model slot value
```

### `Yulang.GeneralDictionaryNominalSlotTransport.base_models`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalSlotTransport.base_models : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalCommonBridge.Models after.base model ↔ Yulang.GeneralNominalCommonBridge.Models before.base model
```

### `Yulang.GeneralDictionaryNominalSlotTransport.models`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalSlotTransport.models : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models after model ↔ Yulang.GeneralNominalState.Models before model
```

### `Yulang.GeneralDictionaryNominalSlotTransport.source_identity`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalSlotTransport.source_identity : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (first last : Fin before.base.slots),
  after.base.source (transport.embed first) = after.base.source (transport.embed last) ↔ first = last
```

## GeneralDictionaryTypeCoverage

実type source slotの有限coverageを定義し、全需要のlower/upper/output出現を残した列に対するcoverageと位置探索成功、欠けたIDと探索失敗を正確に同値にする。

### `Yulang.GeneralDictionaryTypeCoverage.demand_coverage_iff`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryTypeCoverage.demand_coverage_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralSourceState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralDictionaryTypeCoverage.Covers state (Yulang.GeneralDictionaryTypeCoverage.demandTypeIDs demand) ↔
    Yulang.GeneralDictionaryHeadlessLocations.Available state demand
```

### `Yulang.GeneralDictionaryTypeCoverage.available_of_coverage`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryTypeCoverage.available_of_coverage : ∀ {roles : Yulang.Roles.RoleDecls}
  {neededTypeIDs : List Nat} (state : Yulang.GeneralSourceState.State)
  (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralDictionaryTypeCoverage.Covers state neededTypeIDs →
    (∀ (source : Nat), source ∈ Yulang.GeneralDictionaryTypeCoverage.demandTypeIDs demand → source ∈ neededTypeIDs) →
      Yulang.GeneralDictionaryHeadlessLocations.Available state demand
```

### `Yulang.GeneralDictionaryTypeCoverage.locate_of_coverage`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryTypeCoverage.locate_of_coverage : ∀ {roles : Yulang.Roles.RoleDecls} {neededTypeIDs : List Nat}
  (state : Yulang.GeneralSourceState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralDictionaryTypeCoverage.Covers state neededTypeIDs →
    (∀ (source : Nat), source ∈ Yulang.GeneralDictionaryTypeCoverage.demandTypeIDs demand → source ∈ neededTypeIDs) →
      ∃ inputs, Yulang.GeneralDictionaryHeadlessLocations.locate state demand = some inputs
```

### `Yulang.GeneralDictionaryTypeCoverage.locate_success_coverage_iff`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryTypeCoverage.locate_success_coverage_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralSourceState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  (∃ inputs, Yulang.GeneralDictionaryHeadlessLocations.locate state demand = some inputs) ↔
    Yulang.GeneralDictionaryTypeCoverage.Covers state (Yulang.GeneralDictionaryTypeCoverage.demandTypeIDs demand)
```

### `Yulang.GeneralDictionaryTypeCoverage.locate_none_missing_iff`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryTypeCoverage.locate_none_missing_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralSourceState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralDictionaryHeadlessLocations.locate state demand = none ↔
    ∃ source,
      source ∈ Yulang.GeneralDictionaryTypeCoverage.demandTypeIDs demand ∧
        ∀ (slot : Fin state.slots), state.source slot ≠ source
```

### `Yulang.GeneralDictionaryTypeCoverage.locateTerm_variable_iff`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryTypeCoverage.locateTerm_variable_iff : ∀ (state : Yulang.GeneralSourceState.State)
  (source : Nat),
  (∃ term,
      Yulang.GeneralDictionaryBinderLocations.locateTerm state (Yulang.Core.PresenceGeneration.TyTerm.var source) =
        some term) ↔
    Yulang.GeneralDictionaryTypeCoverage.Covers state [source]
```

## GeneralDictionaryTypeCoverageExamples

type10/row42/reserved77の旧snapshotとtype77を持つ提供済み新snapshotで、予約だけでは失敗し、実slotがあれば全6出現を保持して成功する。row42をtype slotと扱わない。

### `Yulang.GeneralDictionaryTypeCoverageExamples.reserved_linked`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryTypeCoverageExamples.reserved_linked : Yulang.GeneralNominalState.Linked
  Yulang.GeneralDictionaryTypeCoverageExamples.before Yulang.GeneralDictionaryTypeCoverageExamples.demand
```

### `Yulang.GeneralDictionaryTypeCoverageExamples.reserved_unavailable`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryTypeCoverageExamples.reserved_unavailable : Yulang.GeneralDictionaryHeadlessLocations.locate
    Yulang.GeneralDictionaryTypeCoverageExamples.before.base Yulang.GeneralDictionaryTypeCoverageExamples.demand =
  none
```

### `Yulang.GeneralDictionaryTypeCoverageExamples.after_coverage`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryTypeCoverageExamples.after_coverage : Yulang.GeneralDictionaryTypeCoverage.Covers
  Yulang.GeneralDictionaryTypeCoverageExamples.afterBase [77]
```

### `Yulang.GeneralDictionaryTypeCoverageExamples.after_located`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryTypeCoverageExamples.after_located : Yulang.GeneralDictionaryHeadlessLocations.locate
    Yulang.GeneralDictionaryTypeCoverageExamples.afterBase Yulang.GeneralDictionaryTypeCoverageExamples.demand =
  some Yulang.GeneralDictionaryTypeCoverageExamples.afterInputs
```

### `Yulang.GeneralDictionaryTypeCoverageExamples.repeated_occurrences`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryTypeCoverageExamples.repeated_occurrences : Yulang.GeneralDictionaryTypeCoverage.demandTypeIDs
      Yulang.GeneralDictionaryTypeCoverageExamples.demand =
    [77, 77, 77, 77, 77, 77] ∧
  List.ofFn Yulang.GeneralDictionaryTypeCoverageExamples.afterInputs.lower = [1, 1] ∧
    List.ofFn Yulang.GeneralDictionaryTypeCoverageExamples.afterInputs.upper = [1, 1] ∧
      List.ofFn Yulang.GeneralDictionaryTypeCoverageExamples.afterInputs.target = [1, 1]
```

### `Yulang.GeneralDictionaryTypeCoverageExamples.row_only_not_covered`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryTypeCoverageExamples.row_only_not_covered : Yulang.GeneralDictionaryTypeCoverageExamples.afterBase.rowSource
      0 =
    42 ∧
  ¬Yulang.GeneralDictionaryTypeCoverage.Covers Yulang.GeneralDictionaryTypeCoverageExamples.afterBase [42]
```

### `Yulang.GeneralDictionaryTypeCoverageExamples.variable_before_after`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryTypeCoverageExamples.variable_before_after : Yulang.GeneralDictionaryBinderLocations.locateTerm
      Yulang.GeneralDictionaryTypeCoverageExamples.before.base (Yulang.Core.PresenceGeneration.TyTerm.var 77) =
    none ∧
  Yulang.GeneralDictionaryBinderLocations.locateTerm Yulang.GeneralDictionaryTypeCoverageExamples.afterBase
        (Yulang.Core.PresenceGeneration.TyTerm.var 77) =
      some (Yulang.Core.PresenceGeneration.TyTerm.var 1) ∧
    Yulang.GeneralDictionaryBinderLocations.locateTerm Yulang.GeneralDictionaryTypeCoverageExamples.afterBase
        (Yulang.Core.PresenceGeneration.TyTerm.var 42) =
      none
```

## GeneralDictionaryNominalCandidateOrderExamples

実visible宣言リストの非自明な反転、子欠落/不在key、およびchecked宣言の二つのwhere clauseの交換を検証する。where交換は型に示す証拠を入力とする一般例であり、具体的な複数where nominal fixtureとは主張しない。

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_reversed`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_reversed : Yulang.GeneralRegistryReordering.Reorders
  Yulang.GeneralNominalExamples.registry Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_checked`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_order_changes`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.visible_order_changes : Yulang.GeneralNominalExamples.registry.declarations ≠
  Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed.declarations
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.computed_frames_preserved`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.computed_frames_preserved : Yulang.GeneralDictionaryNominalCandidateReadback.frames
    Yulang.GeneralNominalExamples.registry (Yulang.GeneralNominalExamples.context true) =
  Yulang.GeneralDictionaryNominalCandidateReadback.frames Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed
    (Yulang.GeneralNominalExamples.context true)
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_tree_reconstructed`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_tree_reconstructed : Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct
    Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed
    Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_checked (Yulang.GeneralNominalExamples.context true)
    Yulang.GeneralDictionaryNominalCandidateReadbackExamples.payload Yulang.GeneralNominalExamples.displayRoot =
  some Yulang.GeneralDictionaryNominalCandidateReadbackExamples.sourceTree
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_child_defers`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_child_defers : Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct
    Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed
    Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_checked (Yulang.GeneralNominalExamples.context true)
    (Yulang.CommonRoleOutermostResolver.Dictionary.node 1 []) Yulang.GeneralNominalExamples.displayRoot =
  none
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_key_preserved`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_key_preserved : Yulang.GeneralDictionaryNominalCandidateReadback.declaration
      Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.displayRoot 99 =
    none ∧
  Yulang.GeneralDictionaryNominalCandidateReadback.declaration
      Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed Yulang.GeneralNominalExamples.displayRoot 99 =
    none
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_bindings_preserved`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.absent_bindings_preserved : Yulang.GeneralDictionaryNominalCandidateReadback.bindings
      Yulang.GeneralNominalExamples.registry (Yulang.GeneralNominalExamples.context true)
      Yulang.GeneralNominalExamples.displayRoot 99 =
    [] ∧
  Yulang.GeneralDictionaryNominalCandidateReadback.bindings
      Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed (Yulang.GeneralNominalExamples.context true)
      Yulang.GeneralNominalExamples.displayRoot 99 =
    []
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.preparation_preserved`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.preparation_preserved : Yulang.GeneralDictionaryNominalCandidateEvidence.prepare
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.registry_checked
    (Yulang.GeneralNominalExamples.context true) Yulang.GeneralDictionaryNominalCandidateReadbackExamples.payload
    Yulang.GeneralNominalExamples.displayRoot =
  Yulang.GeneralDictionaryNominalCandidateEvidence.prepare
    Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed
    Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_checked (Yulang.GeneralNominalExamples.context true)
    Yulang.GeneralDictionaryNominalCandidateReadbackExamples.payload Yulang.GeneralNominalExamples.displayRoot
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_preparation_defers`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_omitted_preparation_defers : Yulang.GeneralDictionaryNominalCandidateEvidence.prepare
    Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed
    Yulang.GeneralDictionaryNominalCandidateOrderExamples.reversed_checked (Yulang.GeneralNominalExamples.context true)
    (Yulang.CommonRoleOutermostResolver.Dictionary.node 1 []) Yulang.GeneralNominalExamples.displayRoot =
  none
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_reorders`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_reorders : ∀
  (declaration : Yulang.GeneralDeclarations.Declaration) (left right : Yulang.GeneralDeclarations.Clause)
  (rest : List Yulang.GeneralDeclarations.Clause),
  declaration.requirements = left :: right :: rest →
    Yulang.GeneralRegistryReordering.Reorders
      { constructors := Yulang.GeneralDeclarationExamples.constructors,
        roles := Yulang.GeneralDeclarationExamples.roles, declarations := [declaration] }
      { constructors := Yulang.GeneralDeclarationExamples.constructors,
        roles := Yulang.GeneralDeclarationExamples.roles,
        declarations :=
          [{ id := declaration.id, role := declaration.role, head := declaration.head,
              requirements := right :: left :: rest, associated := declaration.associated,
              outputBinders := declaration.outputBinders }] }
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_computed_frames`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_computed_frames : ∀
  (declaration : Yulang.GeneralDeclarations.Declaration) (left right : Yulang.GeneralDeclarations.Clause)
  (rest : List Yulang.GeneralDeclarations.Clause),
  declaration.requirements = left :: right :: rest →
    Yulang.GeneralDeclarations.Checked
        { constructors := Yulang.GeneralDeclarationExamples.constructors,
          roles := Yulang.GeneralDeclarationExamples.roles, declarations := [declaration] } →
      ∀ (fixed : Yulang.GeneralNominalCandidates.Context),
        Yulang.GeneralDictionaryNominalCandidateReadback.frames
            { constructors := Yulang.GeneralDeclarationExamples.constructors,
              roles := Yulang.GeneralDeclarationExamples.roles, declarations := [declaration] }
            fixed =
          Yulang.GeneralDictionaryNominalCandidateReadback.frames
            { constructors := Yulang.GeneralDeclarationExamples.constructors,
              roles := Yulang.GeneralDeclarationExamples.roles,
              declarations :=
                [{ id := declaration.id, role := declaration.role, head := declaration.head,
                    requirements := right :: left :: rest, associated := declaration.associated,
                    outputBinders := declaration.outputBinders }] }
            fixed
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_changes`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_changes : ∀
  (declaration : Yulang.GeneralDeclarations.Declaration) (left right : Yulang.GeneralDeclarations.Clause)
  (rest : List Yulang.GeneralDeclarations.Clause),
  declaration.requirements = left :: right :: rest →
    left ≠ right →
      declaration ≠
        { id := declaration.id, role := declaration.role, head := declaration.head,
          requirements := right :: left :: rest, associated := declaration.associated,
          outputBinders := declaration.outputBinders }
```

### `Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_executors`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalCandidateOrderExamples.where_swap_executors : ∀
  (declaration : Yulang.GeneralDeclarations.Declaration) (left right : Yulang.GeneralDeclarations.Clause)
  (rest : List Yulang.GeneralDeclarations.Clause) (clauses : declaration.requirements = left :: right :: rest)
  (checked :
    Yulang.GeneralDeclarations.Checked
      { constructors := Yulang.GeneralDeclarationExamples.constructors,
        roles := Yulang.GeneralDeclarationExamples.roles, declarations := [declaration] })
  (fixed : Yulang.GeneralNominalCandidates.Context) (raw : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  let moved :=
    { constructors := Yulang.GeneralDeclarationExamples.constructors, roles := Yulang.GeneralDeclarationExamples.roles,
      declarations :=
        [{ id := declaration.id, role := declaration.role, head := declaration.head,
            requirements := right :: left :: rest, associated := declaration.associated,
            outputBinders := declaration.outputBinders }] };
  have movedChecked := ⋯;
  Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct
        { constructors := Yulang.GeneralDeclarationExamples.constructors,
          roles := Yulang.GeneralDeclarationExamples.roles, declarations := [declaration] }
        checked fixed raw root =
      Yulang.GeneralDictionaryNominalCandidateReadback.reconstruct moved movedChecked fixed raw root ∧
    Yulang.GeneralDictionaryNominalCandidateEvidence.prepare
        { constructors := Yulang.GeneralDeclarationExamples.constructors,
          roles := Yulang.GeneralDeclarationExamples.roles, declarations := [declaration] }
        checked fixed raw root =
      Yulang.GeneralDictionaryNominalCandidateEvidence.prepare moved movedChecked fixed raw root
```

## GeneralDictionaryNominalBatchTransport

同じ需要と局所head/outputの正確なrenameを使い、有限dictionary batchの記録前後のfull nominal model集合を同じassignmentで一致させる。重複と順序を維持し、target stateや辞書を選ばない。

### `Yulang.GeneralDictionaryNominalBatchTransport.liftType_eval`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalBatchTransport.liftType_eval : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (term : Yulang.Core.PresenceGeneration.TyTerm (Fin before.base.slots))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralDictionaryStateEquations.liftType after.base
        (Yulang.Core.PresenceGeneration.TyTerm.rename transport.embed term)) =
    Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralDictionaryStateEquations.liftType before.base term)
```

### `Yulang.GeneralDictionaryNominalBatchTransport.located_holds`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalBatchTransport.located_holds : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (old : Yulang.GeneralDictionaryStateEquations.Located before.base demand)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralDictionaryNominalEquations.Holds
      (Yulang.GeneralDictionaryNominalBatchTransport.located transport old).equations model ↔
    Yulang.GeneralDictionaryNominalEquations.Holds old.equations model
```

### `Yulang.GeneralDictionaryNominalBatchTransport.located_recorded`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalBatchTransport.located_recorded : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (old : Yulang.GeneralDictionaryStateEquations.Located before.base demand),
  Yulang.GeneralDictionaryStateEquations.Recorded old →
    Yulang.GeneralDictionaryStateEquations.Recorded
      (Yulang.GeneralDictionaryNominalBatchTransport.located transport old)
```

### `Yulang.GeneralDictionaryNominalBatchTransport.record_models`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalBatchTransport.record_models : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (old : List (Yulang.GeneralDictionaryBatchRecording.Item roles before.base))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models
      (Yulang.GeneralDictionaryNominalRecording.record after
        (Yulang.GeneralDictionaryNominalBatchTransport.items transport old))
      model ↔
    Yulang.GeneralNominalState.Models (Yulang.GeneralDictionaryNominalRecording.record before old) model
```

### `Yulang.GeneralDictionaryNominalBatchTransport.record_satisfiable`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalBatchTransport.record_satisfiable : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (old : List (Yulang.GeneralDictionaryBatchRecording.Item roles before.base)),
  (∃ model,
      Yulang.GeneralNominalState.Models
        (Yulang.GeneralDictionaryNominalRecording.record after
          (Yulang.GeneralDictionaryNominalBatchTransport.items transport old))
        model) ↔
    ∃ model, Yulang.GeneralNominalState.Models (Yulang.GeneralDictionaryNominalRecording.record before old) model
```

### `Yulang.GeneralDictionaryNominalBatchTransport.demands_preserved`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalBatchTransport.demands_preserved : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (old : List (Yulang.GeneralDictionaryBatchRecording.Item roles before.base)),
  List.map Yulang.GeneralDictionaryBatchRecording.Item.demand
      (Yulang.GeneralDictionaryNominalBatchTransport.items transport old) =
    List.map Yulang.GeneralDictionaryBatchRecording.Item.demand old
```

## GeneralDictionaryNominalBatchTransportExamples

同じpackageを二回、同じoutputを二回保持する非空batchと具体joint modelを検証する。arrow termの型source77とrowSource43を混同しない。

### `Yulang.GeneralDictionaryNominalBatchTransportExamples.lifted_arrow_separate`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalBatchTransportExamples.lifted_arrow_separate : Yulang.GeneralDictionaryStateEquations.liftType
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter.base
    (Yulang.Core.PresenceGeneration.TyTerm.rename
      Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedTransport.embed
      ((Yulang.Core.PresenceGeneration.TyTerm.var 1).arrow (Yulang.Core.PresenceGeneration.RowTerm.var 1)
        (Yulang.Core.PresenceGeneration.TyTerm.var 1) (Yulang.Core.PresenceGeneration.RowTerm.var 1))) =
  (Yulang.Core.PresenceGeneration.TyTerm.var 77).arrow (Yulang.Core.PresenceGeneration.RowTerm.var 43)
    (Yulang.Core.PresenceGeneration.TyTerm.var 77) (Yulang.Core.PresenceGeneration.RowTerm.var 43)
```

### `Yulang.GeneralDictionaryNominalBatchTransportExamples.old_item_holds`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalBatchTransportExamples.old_item_holds : Yulang.GeneralDictionaryNominalEquations.Holds
  Yulang.GeneralDictionaryNominalBatchTransportExamples.oldLocated.equations
  Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment
```

### `Yulang.GeneralDictionaryNominalBatchTransportExamples.repeated_batch_joint`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalBatchTransportExamples.repeated_batch_joint : Yulang.GeneralNominalState.Models
    (Yulang.GeneralDictionaryNominalRecording.record Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore
      Yulang.GeneralDictionaryNominalBatchTransportExamples.batch)
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment ∧
  Yulang.GeneralNominalState.Models
    (Yulang.GeneralDictionaryNominalRecording.record Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter
      (Yulang.GeneralDictionaryNominalBatchTransport.items
        Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedTransport
        Yulang.GeneralDictionaryNominalBatchTransportExamples.batch))
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment
```

### `Yulang.GeneralDictionaryNominalBatchTransportExamples.repeated_batch_not_collapsed`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalBatchTransportExamples.repeated_batch_not_collapsed : (Yulang.GeneralDictionaryNominalBatchTransport.items
        Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedTransport
        Yulang.GeneralDictionaryNominalBatchTransportExamples.batch).length =
    2 ∧
  List.map (fun item => item.demand.outputs.length)
      (Yulang.GeneralDictionaryNominalBatchTransport.items
        Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedTransport
        Yulang.GeneralDictionaryNominalBatchTransportExamples.batch) =
    [2, 2]
```

### `Yulang.GeneralDictionaryNominalBatchTransportExamples.all_assignment_recording_exact`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalBatchTransportExamples.all_assignment_recording_exact : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models
      (Yulang.GeneralDictionaryNominalRecording.record Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter
        (Yulang.GeneralDictionaryNominalBatchTransport.items
          Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedTransport
          Yulang.GeneralDictionaryNominalBatchTransportExamples.batch))
      model ↔
    Yulang.GeneralNominalState.Models
      (Yulang.GeneralDictionaryNominalRecording.record Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore
        Yulang.GeneralDictionaryNominalBatchTransportExamples.batch)
      model
```

## GeneralDictionaryNominalSemanticOrder

任意full nominal assignmentの独立Instance/Evidenceを、同じbinder値・完全canonical子・global Framesのままregistry順変更へ移す。固定Contextではcomputed Framesも内部で等しくなる。

### `Yulang.GeneralDictionaryNominalSemanticOrder.realizes_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionaryNominalSemanticOrder.realizes_reorders : ∀
  {first last : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (capture : Yulang.GeneralDeclarationDemands.Capture) (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
      (binderValues : Nat → Yulang.CommonNominalFullCarrier.Ty),
      Yulang.GeneralDictionaryNominalSourceEvidence.Realizes first capture assignment binderValues ↔
        Yulang.GeneralDictionaryNominalSourceEvidence.Realizes last capture assignment binderValues
```

### `Yulang.GeneralDictionaryNominalSemanticOrder.instance_reorders_forward`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSemanticOrder.instance_reorders_forward : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles)
      (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralDictionaryNominalSourceEvidence.Instance
          { constructors := constructors, roles := roles, declarations := first } one frames assignment root key
          children →
        Yulang.GeneralDictionaryNominalSourceEvidence.Instance
          { constructors := constructors, roles := roles, declarations := last } two frames assignment root key children
```

### `Yulang.GeneralDictionaryNominalSemanticOrder.instance_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSemanticOrder.instance_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles)
      (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralDictionaryNominalSourceEvidence.Instance
          { constructors := constructors, roles := roles, declarations := first } one frames assignment root key
          children ↔
        Yulang.GeneralDictionaryNominalSourceEvidence.Instance
          { constructors := constructors, roles := roles, declarations := last } two frames assignment root key children
```

### `Yulang.GeneralDictionaryNominalSemanticOrder.evidence_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSemanticOrder.evidence_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (frames : Yulang.GeneralDictionaryTransactions.Frames roles)
      (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
      (dictionary : Yulang.GeneralSourceDictionaries.Dictionary roles),
      Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryNominalSourceEvidence.Instance
            { constructors := constructors, roles := roles, declarations := first } one frames assignment)
          dictionary ↔
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryNominalSourceEvidence.Instance
            { constructors := constructors, roles := roles, declarations := last } two frames assignment)
          dictionary
```

### `Yulang.GeneralDictionaryNominalSemanticOrder.computed_instance_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSemanticOrder.computed_instance_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (context : Yulang.GeneralNominalCandidates.Context) (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralDictionaryNominalSourceEvidence.Instance
          { constructors := constructors, roles := roles, declarations := first } one
          (Yulang.GeneralDictionaryNominalCandidateReadback.frames
            { constructors := constructors, roles := roles, declarations := first } context)
          assignment root key children ↔
        Yulang.GeneralDictionaryNominalSourceEvidence.Instance
          { constructors := constructors, roles := roles, declarations := last } two
          (Yulang.GeneralDictionaryNominalCandidateReadback.frames
            { constructors := constructors, roles := roles, declarations := last } context)
          assignment root key children
```

### `Yulang.GeneralDictionaryNominalSemanticOrder.computed_evidence_reorders`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSemanticOrder.computed_evidence_reorders : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (roles : Yulang.Roles.RoleDecls)
  (first last : List Yulang.GeneralDeclarations.Declaration)
  (one : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := first })
  (two : Yulang.GeneralDeclarations.Checked { constructors := constructors, roles := roles, declarations := last }),
  Yulang.GeneralRegistryReordering.Reorders { constructors := constructors, roles := roles, declarations := first }
      { constructors := constructors, roles := roles, declarations := last } →
    ∀ (context : Yulang.GeneralNominalCandidates.Context) (assignment : Yulang.GeneralNominalCommonBridge.Assignment)
      (dictionary : Yulang.GeneralSourceDictionaries.Dictionary roles),
      Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryNominalSourceEvidence.Instance
            { constructors := constructors, roles := roles, declarations := first } one
            (Yulang.GeneralDictionaryNominalCandidateReadback.frames
              { constructors := constructors, roles := roles, declarations := first } context)
            assignment)
          dictionary ↔
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryNominalSourceEvidence.Instance
            { constructors := constructors, roles := roles, declarations := last } two
            (Yulang.GeneralDictionaryNominalCandidateReadback.frames
              { constructors := constructors, roles := roles, declarations := last } context)
            assignment)
          dictionary
```

## GeneralDictionaryNominalSlotTransportExamples

1→2/2→3の実slot増加で構文Transportを構成する。後者はtype77/row43の両parameterを持つ非空nominal descriptorを保存し、具体nominal assignmentが前後Modelsを同時に満たす。

### `Yulang.GeneralDictionaryNominalSlotTransportExamples.models_exact`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSlotTransportExamples.models_exact : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryNominalSlotTransportExamples.after model ↔
    Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryTypeCoverageExamples.before model
```

### `Yulang.GeneralDictionaryNominalSlotTransportExamples.every_assignment_models`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSlotTransportExamples.every_assignment_models : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryTypeCoverageExamples.before model ∧
    Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryNominalSlotTransportExamples.after model
```

### `Yulang.GeneralDictionaryNominalSlotTransportExamples.nominal_nonvacuous`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSlotTransportExamples.nominal_nonvacuous : Yulang.GeneralNominalState.Models
    Yulang.GeneralDictionaryTypeCoverageExamples.before
    Yulang.GeneralDictionaryNominalSlotTransportExamples.nominalAssignment ∧
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryNominalSlotTransportExamples.after
    Yulang.GeneralDictionaryNominalSlotTransportExamples.nominalAssignment
```

### `Yulang.GeneralDictionaryNominalSlotTransportExamples.old_coordinates_preserved`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSlotTransportExamples.old_coordinates_preserved : Yulang.GeneralDictionaryNominalSlotTransportExamples.after.base.source
      (Yulang.GeneralDictionaryNominalSlotTransportExamples.transport.embed 0) =
    10 ∧
  Yulang.GeneralDictionaryNominalSlotTransportExamples.after.base.rowSource
      (Yulang.GeneralDictionaryNominalSlotTransportExamples.transport.embed 0) =
    42
```

### `Yulang.GeneralDictionaryNominalSlotTransportExamples.strict_extension_localizes`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSlotTransportExamples.strict_extension_localizes : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralDictionaryTypeCoverageExamples.before.base.slots <
      Yulang.GeneralDictionaryNominalSlotTransportExamples.after.base.slots ∧
    (∀ (old : Fin Yulang.GeneralDictionaryTypeCoverageExamples.before.base.slots),
        Yulang.GeneralDictionaryNominalSlotTransportExamples.transport.embed old ≠ 1) ∧
      Yulang.GeneralDictionaryHeadlessLocations.locate Yulang.GeneralDictionaryTypeCoverageExamples.before.base
            Yulang.GeneralDictionaryTypeCoverageExamples.demand =
          none ∧
        Yulang.GeneralDictionaryHeadlessLocations.locate Yulang.GeneralDictionaryNominalSlotTransportExamples.after.base
              Yulang.GeneralDictionaryTypeCoverageExamples.demand =
            some Yulang.GeneralDictionaryTypeCoverageExamples.afterInputs ∧
          (Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryNominalSlotTransportExamples.after model ↔
            Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryTypeCoverageExamples.before model)
```

### `Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_models_exact`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_models_exact : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter model ↔
    Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore model
```

### `Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_bounds_preserved`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_bounds_preserved : (Yulang.GeneralDictionaryNominalSlotTransport.descriptor
        Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedEmbed
        Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedDescriptor).arguments =
    [Yulang.GeneralNominalState.Parameter.type (1, 1), Yulang.GeneralNominalState.Parameter.row (1, 1)] ∧
  Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter.base.source
        (Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedEmbed 1) =
      77 ∧
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter.base.rowSource
        (Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedEmbed 1) =
      43
```

### `Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_nominal_nonvacuous`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryNominalSlotTransportExamples.mixed_nominal_nonvacuous : Yulang.GeneralNominalState.Models
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment ∧
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment
```

## GeneralDictionarySlotLocalizationTransport

構文Transportと旧探索成功を前提に、source slot・変数RHS・変数head・全endpoint/target位置の成功が正確なrename結果として残る。失敗保存は述べない。

### `Yulang.GeneralDictionarySlotLocalizationTransport.sourceSlot_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotLocalizationTransport.sourceSlot_success : ∀
  {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after) (source : Nat)
  (slot : Fin before.base.slots),
  Yulang.GeneralDictionaryBinderLocations.sourceSlot before.base source = some slot →
    Yulang.GeneralDictionaryBinderLocations.sourceSlot after.base source = some (transport.embed slot)
```

### `Yulang.GeneralDictionarySlotLocalizationTransport.locateTerm_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotLocalizationTransport.locateTerm_success : ∀
  {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (source : Yulang.Core.PresenceGeneration.TyTerm Nat)
  (term : Yulang.Core.PresenceGeneration.TyTerm (Fin before.base.slots)),
  Yulang.GeneralDictionaryBinderLocations.locateTerm before.base source = some term →
    Yulang.GeneralDictionaryBinderLocations.locateTerm after.base source =
      some (Yulang.Core.PresenceGeneration.TyTerm.rename transport.embed term)
```

### `Yulang.GeneralDictionarySlotLocalizationTransport.binder_compile_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotLocalizationTransport.binder_compile_success : ∀
  {before after : Yulang.GeneralNominalState.State} {roles : Yulang.Roles.RoleDecls}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm (Fin before.base.slots)),
  Yulang.GeneralDictionaryBinderLocations.compile before.base roles declaration capture name = some term →
    Yulang.GeneralDictionaryBinderLocations.compile after.base roles declaration capture name =
      some (Yulang.Core.PresenceGeneration.TyTerm.rename transport.embed term)
```

### `Yulang.GeneralDictionarySlotLocalizationTransport.variable_compile_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotLocalizationTransport.variable_compile_success : ∀
  {before after : Yulang.GeneralNominalState.State} {roles : Yulang.Roles.RoleDecls}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm (Fin before.base.slots)),
  Yulang.GeneralDictionaryVariableTerms.compile before.base roles declaration capture name = some term →
    Yulang.GeneralDictionaryVariableTerms.compile after.base roles declaration capture name =
      some (Yulang.Core.PresenceGeneration.TyTerm.rename transport.embed term)
```

### `Yulang.GeneralDictionarySlotLocalizationTransport.headless_locate`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotLocalizationTransport.headless_locate : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (demand : Yulang.GeneralSourceState.Demand roles)
  (inputs : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs before.base demand),
  Yulang.GeneralDictionaryHeadlessLocations.locate after.base demand =
    some (Yulang.GeneralDictionarySlotLocalizationTransport.headlessInputs transport inputs)
```

### `Yulang.GeneralDictionarySlotLocalizationTransport.available`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotLocalizationTransport.available : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralDictionaryHeadlessLocations.Available before.base demand →
    Yulang.GeneralDictionaryHeadlessLocations.Available after.base demand
```

### `Yulang.GeneralDictionarySlotLocalizationTransport.head_denotesAt`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotLocalizationTransport.head_denotesAt : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (index : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm (Fin before.base.slots)),
  Yulang.GeneralDictionaryVariableHeads.DenotesAt before.base declaration capture index term →
    Yulang.GeneralDictionaryVariableHeads.DenotesAt after.base declaration capture index
      (Yulang.Core.PresenceGeneration.TyTerm.rename transport.embed term)
```

### `Yulang.GeneralDictionarySlotLocalizationTransport.head_compile_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotLocalizationTransport.head_compile_success : ∀
  {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (index : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm (Fin before.base.slots)),
  Yulang.GeneralDictionaryVariableHeads.compileAt before.base declaration capture index = some term →
    Yulang.GeneralDictionaryVariableHeads.compileAt after.base declaration capture index =
      some (Yulang.Core.PresenceGeneration.TyTerm.rename transport.embed term)
```

## GeneralDictionarySlotMaterializationTransport

同registry・capture・global frameで旧head/output materializationとPlanが成功するなら、全local termとslotを埋込みでrenameした正確な結果が新snapshotで成功する。

### `Yulang.GeneralDictionarySlotMaterializationTransport.head_denotes`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotMaterializationTransport.head_denotes : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (demand : Yulang.GeneralSourceState.Demand roles)
  (head : Fin (roles demand.role).arity → Yulang.Core.PresenceGeneration.TyTerm (Fin before.base.slots)),
  Yulang.GeneralDictionaryVariableHeads.HeadDenotes declaration capture demand head →
    Yulang.GeneralDictionaryVariableHeads.HeadDenotes declaration capture demand fun index =>
      Yulang.Core.PresenceGeneration.TyTerm.rename transport.embed (head index)
```

### `Yulang.GeneralDictionarySlotMaterializationTransport.head_build_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotMaterializationTransport.head_build_success : ∀
  {before after : Yulang.GeneralNominalState.State} {roles : Yulang.Roles.RoleDecls}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (demand : Yulang.GeneralSourceState.Demand roles) (sameRole : declaration.role = demand.role)
  (capture : Yulang.GeneralDeclarationDemands.Capture)
  (old : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs before.base demand)
  (result : Yulang.GeneralDictionaryBinderLocations.Inputs before.base demand),
  Yulang.GeneralDictionaryVariableHeads.build declaration checked sameRole capture old = some result →
    Yulang.GeneralDictionaryVariableHeads.build declaration checked sameRole capture
        (Yulang.GeneralDictionarySlotLocalizationTransport.headlessInputs transport old) =
      some (Yulang.GeneralDictionarySlotMaterializationTransport.inputs transport result)
```

### `Yulang.GeneralDictionarySlotMaterializationTransport.materializes`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotMaterializationTransport.materializes : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (old : Yulang.GeneralDictionaryBinderLocations.Inputs before.base demand)
  (result : Yulang.GeneralDictionaryStateEquations.Located before.base demand),
  Yulang.GeneralDictionaryVariableMaterialization.Materializes declaration capture old result →
    Yulang.GeneralDictionaryVariableMaterialization.Materializes declaration capture
      (Yulang.GeneralDictionarySlotMaterializationTransport.inputs transport old)
      (Yulang.GeneralDictionarySlotMaterializationTransport.located transport result)
```

### `Yulang.GeneralDictionarySlotMaterializationTransport.variable_build_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotMaterializationTransport.variable_build_success : ∀
  {before after : Yulang.GeneralNominalState.State} {roles : Yulang.Roles.RoleDecls}
  {demand : Yulang.GeneralSourceState.Demand roles}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  (List.map Yulang.GeneralDeclarations.Equation.name declaration.associated).Nodup →
    ∀ (old : Yulang.GeneralDictionaryBinderLocations.Inputs before.base demand)
      (result : Yulang.GeneralDictionaryStateEquations.Located before.base demand),
      Yulang.GeneralDictionaryVariableTerms.build declaration capture old = some result →
        Yulang.GeneralDictionaryVariableTerms.build declaration capture
            (Yulang.GeneralDictionarySlotMaterializationTransport.inputs transport old) =
          some (Yulang.GeneralDictionarySlotMaterializationTransport.located transport result)
```

### `Yulang.GeneralDictionarySlotMaterializationTransport.plan_lookup_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotMaterializationTransport.plan_lookup_success : ∀
  {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (old : Yulang.GeneralDictionaryBinderLocations.Inputs before.base root.demand)
  (result : Yulang.GeneralDictionaryVariablePlans.Result before.base root),
  Yulang.GeneralDictionaryVariablePlans.lookup registry checked frame root key old = some result →
    Yulang.GeneralDictionaryVariablePlans.lookup registry checked frame root key
        (Yulang.GeneralDictionarySlotMaterializationTransport.inputs transport old) =
      some (Yulang.GeneralDictionarySlotMaterializationTransport.planResult transport result)
```

### `Yulang.GeneralDictionarySlotMaterializationTransport.headless_lookup_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotMaterializationTransport.headless_lookup_success : ∀
  {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (old : Yulang.GeneralDictionaryVariableHeads.HeadlessInputs before.base root.demand)
  (result : Yulang.GeneralDictionaryHeadlessPlans.Result before.base root),
  Yulang.GeneralDictionaryHeadlessPlans.lookup registry checked frame root key old = some result →
    Yulang.GeneralDictionaryHeadlessPlans.lookup registry checked frame root key
        (Yulang.GeneralDictionarySlotLocalizationTransport.headlessInputs transport old) =
      some (Yulang.GeneralDictionarySlotMaterializationTransport.headlessResult transport result)
```

## GeneralDictionarySlotPreparationTransport

同checked registry・固定global Frames・同raw payloadに対し、全有限子木を含む準備成功を移し、返却source dictionary全体を不変に保つ。Contextを変えたcomputedFrames同値ではない。

### `Yulang.GeneralDictionarySlotPreparationTransport.prepared_root`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotPreparationTransport.prepared_root : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared roles before.base),
  (Yulang.GeneralDictionarySlotPreparationTransport.prepared transport tree).root = tree.root
```

### `Yulang.GeneralDictionarySlotPreparationTransport.prepared_dictionary`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotPreparationTransport.prepared_dictionary : ∀
  {before after : Yulang.GeneralNominalState.State} {roles : Yulang.Roles.RoleDecls}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared roles before.base),
  (Yulang.GeneralDictionarySlotPreparationTransport.prepared transport tree).dictionary = tree.dictionary
```

### `Yulang.GeneralDictionarySlotPreparationTransport.headless_prepare_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotPreparationTransport.headless_prepare_success : ∀
  {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (old : Yulang.GeneralDictionaryHeadlessPreparation.Recipe registry.roles before.base)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles before.base),
  Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames old = some tree →
    Yulang.GeneralDictionaryHeadlessPreparation.prepare registry checked frames
        (Yulang.GeneralDictionarySlotPreparationTransport.recipe transport old) =
      some (Yulang.GeneralDictionarySlotPreparationTransport.prepared transport tree)
```

### `Yulang.GeneralDictionarySlotPreparationTransport.source_localize_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotPreparationTransport.source_localize_success : ∀
  {before after : Yulang.GeneralNominalState.State} {roles : Yulang.Roles.RoleDecls}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (source : Yulang.GeneralDictionarySourceRecipe.Recipe roles)
  (old : Yulang.GeneralDictionaryHeadlessPreparation.Recipe roles before.base),
  Yulang.GeneralDictionarySourceRecipe.localize before.base source = some old →
    Yulang.GeneralDictionarySourceRecipe.localize after.base source =
      some (Yulang.GeneralDictionarySlotPreparationTransport.recipe transport old)
```

### `Yulang.GeneralDictionarySlotPreparationTransport.source_prepare_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotPreparationTransport.source_prepare_success : ∀
  {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (source : Yulang.GeneralDictionarySourceRecipe.Recipe registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles before.base),
  Yulang.GeneralDictionarySourceRecipe.prepare registry checked before.base frames source = some tree →
    Yulang.GeneralDictionarySourceRecipe.prepare registry checked after.base frames source =
      some (Yulang.GeneralDictionarySlotPreparationTransport.prepared transport tree)
```

### `Yulang.GeneralDictionarySlotPreparationTransport.payload_prepare_success`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotPreparationTransport.payload_prepare_success : ∀
  {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles) (raw : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles before.base),
  Yulang.GeneralDictionaryPayloadPreparation.prepare registry checked before.base frames raw root = some tree →
    Yulang.GeneralDictionaryPayloadPreparation.prepare registry checked after.base frames raw root =
      some (Yulang.GeneralDictionarySlotPreparationTransport.prepared transport tree)
```

## GeneralDictionarySlotEvidenceTransport

準備木の全item列が正確にmapされることから、記録後のfull nominal Modelsを同値にし、同じ一つのReadbackが全target transaction modelで元/新Modelsと独立source Evidenceを持つ。

### `Yulang.GeneralDictionarySlotEvidenceTransport.prepared_items`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotEvidenceTransport.prepared_items : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared roles before.base),
  (Yulang.GeneralDictionarySlotPreparationTransport.prepared transport tree).items =
    Yulang.GeneralDictionaryNominalBatchTransport.items transport tree.items
```

### `Yulang.GeneralDictionarySlotEvidenceTransport.recorded_models`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotEvidenceTransport.recorded_models : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared roles before.base)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models
      (Yulang.GeneralDictionaryNominalRecording.record after
        (Yulang.GeneralDictionarySlotPreparationTransport.prepared transport tree).items)
      model ↔
    Yulang.GeneralNominalState.Models (Yulang.GeneralDictionaryNominalRecording.record before tree.items) model
```

### `Yulang.GeneralDictionarySlotEvidenceTransport.source_evidence`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotEvidenceTransport.source_evidence : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry) (state : Yulang.GeneralNominalState.State)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles) (raw : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state.base),
  Yulang.GeneralDictionaryPayloadPreparation.prepare registry checked state.base frames raw root = some tree →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models (Yulang.GeneralDictionaryNominalRecording.record state tree.items) model →
        Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryNominalSourceEvidence.Instance registry checked frames model) tree.dictionary
```

### `Yulang.GeneralDictionarySlotEvidenceTransport.prepare_uniform_transport`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotEvidenceTransport.prepare_uniform_transport : ∀
  {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles) (raw : Yulang.GeneralDictionaryReadback.Payload)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles before.base),
  Yulang.GeneralDictionaryPayloadPreparation.prepare registry checked before.base frames raw root = some tree →
    Yulang.GeneralDictionaryPayloadPreparation.prepare registry checked after.base frames raw root =
        some (Yulang.GeneralDictionarySlotPreparationTransport.prepared transport tree) ∧
      (Yulang.GeneralDictionarySlotPreparationTransport.prepared transport tree).dictionary = tree.dictionary ∧
        ∃ witness,
          Yulang.GeneralSourceDictionaries.Readback root raw witness ∧
            witness = tree.dictionary ∧
              ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                Yulang.GeneralNominalState.Models
                    (Yulang.GeneralDictionaryNominalRecording.record after
                      (Yulang.GeneralDictionarySlotPreparationTransport.prepared transport tree).items)
                    model →
                  Yulang.GeneralNominalState.Models before model ∧
                    Yulang.GeneralNominalState.Models after model ∧
                      Yulang.GeneralSourceDictionaries.Evidence
                        (Yulang.GeneralDictionaryNominalSourceEvidence.Instance registry checked frames model) witness
```

## GeneralDictionarySlotPreparationTransportExamples

非空nominal descriptorと二重のexplicit outputを持つ2→3増加fixtureで、実raw準備の前後成功・同一辞書・同一nominal joint model・source意味証拠が同時に成立する。candidate Survivorはこの例の結論ではない。

### `Yulang.GeneralDictionarySlotPreparationTransportExamples.preparation_success`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotPreparationTransportExamples.preparation_success : Yulang.GeneralDictionaryPayloadPreparation.prepare
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore.base
    Yulang.GeneralDictionarySlotPreparationTransportExamples.frames
    Yulang.GeneralDictionarySlotPreparationTransportExamples.payload
    Yulang.GeneralDictionarySlotPreparationTransportExamples.root =
  some Yulang.GeneralDictionarySlotPreparationTransportExamples.tree
```

### `Yulang.GeneralDictionarySlotPreparationTransportExamples.moved_preparation_success`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotPreparationTransportExamples.moved_preparation_success : Yulang.GeneralDictionaryPayloadPreparation.prepare
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter.base
    Yulang.GeneralDictionarySlotPreparationTransportExamples.frames
    Yulang.GeneralDictionarySlotPreparationTransportExamples.payload
    Yulang.GeneralDictionarySlotPreparationTransportExamples.root =
  some Yulang.GeneralDictionarySlotPreparationTransportExamples.movedTree
```

### `Yulang.GeneralDictionarySlotPreparationTransportExamples.exact_shared_dictionary`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotPreparationTransportExamples.exact_shared_dictionary : Yulang.GeneralDictionarySlotPreparationTransportExamples.tree.dictionary =
    Yulang.GeneralDictionarySlotPreparationTransportExamples.sourceTree ∧
  Yulang.GeneralDictionarySlotPreparationTransportExamples.movedTree.dictionary =
    Yulang.GeneralDictionarySlotPreparationTransportExamples.sourceTree
```

### `Yulang.GeneralDictionarySlotPreparationTransportExamples.nonempty_obligations`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotPreparationTransportExamples.nonempty_obligations : Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore.nominals
      0 =
    some Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedDescriptor ∧
  Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedDescriptor.arguments.length = 2 ∧
    Yulang.GeneralDictionarySlotPreparationTransportExamples.demand.outputs.length = 2 ∧
      Yulang.GeneralDictionarySlotPreparationTransportExamples.tree.items.length = 1 ∧
        Yulang.GeneralDictionaryBatchRecording.batchAtoms
            Yulang.GeneralDictionarySlotPreparationTransportExamples.tree.items ≠
          []
```

### `Yulang.GeneralDictionarySlotPreparationTransportExamples.recorded_model`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotPreparationTransportExamples.recorded_model : Yulang.GeneralNominalState.Models
  (Yulang.GeneralDictionaryNominalRecording.record Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore
    Yulang.GeneralDictionarySlotPreparationTransportExamples.tree.items)
  Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment
```

### `Yulang.GeneralDictionarySlotPreparationTransportExamples.moved_recorded_model`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotPreparationTransportExamples.moved_recorded_model : Yulang.GeneralNominalState.Models
  (Yulang.GeneralDictionaryNominalRecording.record Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter
    Yulang.GeneralDictionarySlotPreparationTransportExamples.movedTree.items)
  Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment
```

### `Yulang.GeneralDictionarySlotPreparationTransportExamples.shared_source_evidence`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotPreparationTransportExamples.shared_source_evidence : Yulang.GeneralSourceDictionaries.Evidence
  (Yulang.GeneralDictionaryNominalSourceEvidence.Instance Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    Yulang.GeneralDictionarySlotPreparationTransportExamples.frames
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment)
  Yulang.GeneralDictionarySlotPreparationTransportExamples.sourceTree
```

### `Yulang.GeneralDictionarySlotPreparationTransportExamples.strict_preparation_joint`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotPreparationTransportExamples.strict_preparation_joint : Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore.base.slots <
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter.base.slots ∧
  Yulang.GeneralDictionaryPayloadPreparation.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
        Yulang.GeneralDictionaryHeadlessFixture.registry_checked
        Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore.base
        Yulang.GeneralDictionarySlotPreparationTransportExamples.frames
        Yulang.GeneralDictionarySlotPreparationTransportExamples.payload
        Yulang.GeneralDictionarySlotPreparationTransportExamples.root =
      some Yulang.GeneralDictionarySlotPreparationTransportExamples.tree ∧
    Yulang.GeneralDictionaryPayloadPreparation.prepare Yulang.GeneralDictionaryHeadlessFixture.registry
          Yulang.GeneralDictionaryHeadlessFixture.registry_checked
          Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter.base
          Yulang.GeneralDictionarySlotPreparationTransportExamples.frames
          Yulang.GeneralDictionarySlotPreparationTransportExamples.payload
          Yulang.GeneralDictionarySlotPreparationTransportExamples.root =
        some Yulang.GeneralDictionarySlotPreparationTransportExamples.movedTree ∧
      Yulang.GeneralNominalState.Models
          (Yulang.GeneralDictionaryNominalRecording.record
            Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore
            Yulang.GeneralDictionarySlotPreparationTransportExamples.tree.items)
          Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment ∧
        Yulang.GeneralNominalState.Models
            (Yulang.GeneralDictionaryNominalRecording.record
              Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter
              Yulang.GeneralDictionarySlotPreparationTransportExamples.movedTree.items)
            Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment ∧
          Yulang.GeneralSourceDictionaries.Readback Yulang.GeneralDictionarySlotPreparationTransportExamples.root
              Yulang.GeneralDictionarySlotPreparationTransportExamples.payload
              Yulang.GeneralDictionarySlotPreparationTransportExamples.sourceTree ∧
            Yulang.GeneralDictionarySlotPreparationTransportExamples.tree.dictionary =
                Yulang.GeneralDictionarySlotPreparationTransportExamples.sourceTree ∧
              Yulang.GeneralDictionarySlotPreparationTransportExamples.movedTree.dictionary =
                  Yulang.GeneralDictionarySlotPreparationTransportExamples.sourceTree ∧
                Yulang.GeneralSourceDictionaries.Evidence
                  (Yulang.GeneralDictionaryNominalSourceEvidence.Instance
                    Yulang.GeneralDictionaryHeadlessFixture.registry
                    Yulang.GeneralDictionaryHeadlessFixture.registry_checked
                    Yulang.GeneralDictionarySlotPreparationTransportExamples.frames
                    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment)
                  Yulang.GeneralDictionarySlotPreparationTransportExamples.sourceTree
```

## GeneralDictionarySlotFreshnessTransport

旧source所属または旧seed以下という追加の座標条件のもとで、実allocationのidentityと衝突guard Freshを保存する。新sourceの型付き起源の権限やtarget構成は結論しない。

### `Yulang.GeneralDictionarySlotFreshnessTransport.sources_preserved`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotFreshnessTransport.sources_preserved : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after) (identity : Nat),
  identity ∈ Yulang.GeneralNominalState.sources before → identity ∈ Yulang.GeneralNominalState.sources after
```

### `Yulang.GeneralDictionarySlotFreshnessTransport.sources_bounded`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotFreshnessTransport.sources_bounded : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after),
  Yulang.GeneralDictionarySlotFreshnessTransport.CoordinatesBound before after →
    ∀ (identity : Nat),
      identity ∈ Yulang.GeneralNominalState.sources after →
        identity ∈ Yulang.GeneralNominalState.sources before ∨ identity ≤ before.seed
```

### `Yulang.GeneralDictionarySlotFreshnessTransport.allocation_source`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotFreshnessTransport.allocation_source : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after)
  (registry : Yulang.GeneralDeclarations.Registry) (root : Nat) (key : Yulang.GeneralNominalAllocation.Origin),
  Yulang.GeneralNominalAllocation.source after registry root key =
    Yulang.GeneralNominalAllocation.source before registry root key
```

### `Yulang.GeneralDictionarySlotFreshnessTransport.generated_member_iff`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotFreshnessTransport.generated_member_iff : ∀
  {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after),
  Yulang.GeneralDictionarySlotFreshnessTransport.CoordinatesBound before after →
    ∀ (registry : Yulang.GeneralDeclarations.Registry) (root : Nat) (key : Yulang.GeneralNominalAllocation.Origin),
      Yulang.GeneralNominalAllocation.source after registry root key ∈ Yulang.GeneralNominalState.sources after ↔
        Yulang.GeneralNominalAllocation.source before registry root key ∈ Yulang.GeneralNominalState.sources before
```

### `Yulang.GeneralDictionarySlotFreshnessTransport.fresh_iff`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotFreshnessTransport.fresh_iff : ∀ {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after),
  Yulang.GeneralDictionarySlotFreshnessTransport.CoordinatesBound before after →
    ∀ (registry : Yulang.GeneralDeclarations.Registry) (root : Nat),
      Yulang.GeneralNominalAllocation.Fresh after registry root ↔
        Yulang.GeneralNominalAllocation.Fresh before registry root
```

### `Yulang.GeneralDictionarySlotFreshnessTransport.unowned_generated_absent`

役割: 補助／健全性・完全な局所対応または順序保存。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
@Yulang.GeneralDictionarySlotFreshnessTransport.unowned_generated_absent : ∀
  {before after : Yulang.GeneralNominalState.State}
  (transport : Yulang.GeneralDictionaryNominalSlotTransport.Transport before after),
  Yulang.GeneralDictionarySlotFreshnessTransport.CoordinatesBound before after →
    ∀ (registry : Yulang.GeneralDeclarations.Registry) (root : Nat),
      Yulang.GeneralNominalAllocation.Fresh before registry root →
        ∀ (key : Yulang.GeneralNominalAllocation.Origin),
          key ∈ Yulang.GeneralNominalAllocation.keys registry root →
            ¬key ∈ before.allocated →
              ¬Yulang.GeneralNominalAllocation.source after registry root key ∈ Yulang.GeneralNominalState.sources after
```

## GeneralDictionarySlotFreshnessTransportExamples

2→3のmixed fixtureで座標条件を実証し、reserved88/seed以下のrow44を根拠としてFreshと未所有source不在を保存する。一般新source生成器ではない。

### `Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_coordinates_bounded`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_coordinates_bounded : Yulang.GeneralDictionarySlotFreshnessTransport.CoordinatesBound
  Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore
  Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter
```

### `Yulang.GeneralDictionarySlotFreshnessTransportExamples.new_coordinates_justified`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotFreshnessTransportExamples.new_coordinates_justified : Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter.base.source
      2 =
    88 ∧
  88 ∈ Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore.reserved ∧
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter.base.rowSource 2 = 44 ∧
      44 ≤ Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore.seed
```

### `Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_sources_preserved`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_sources_preserved : ∀ (identity : Nat),
  identity ∈ Yulang.GeneralNominalState.sources Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore →
    identity ∈ Yulang.GeneralNominalState.sources Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter
```

### `Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_fresh_iff`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_fresh_iff : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (root : Nat),
  Yulang.GeneralNominalAllocation.Fresh Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter registry root ↔
    Yulang.GeneralNominalAllocation.Fresh Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore registry root
```

### `Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_unowned_absent`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotFreshnessTransportExamples.mixed_unowned_absent : ∀
  (registry : Yulang.GeneralDeclarations.Registry) (root : Nat),
  Yulang.GeneralNominalAllocation.Fresh Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore registry root →
    ∀ (key : Yulang.GeneralNominalAllocation.Origin),
      key ∈ Yulang.GeneralNominalAllocation.keys registry root →
        ¬key ∈ Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore.allocated →
          ¬Yulang.GeneralNominalAllocation.source Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter
                registry root key ∈
              Yulang.GeneralNominalState.sources Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter
```

## GeneralDictionarySlotViewBoundaryExamples

実full nominal modelを持つ前後snapshotでidentity Transportが成立しても、normalized viewだけを変えるとKnownとRootPendingが変わる反例。モデル同値からreadiness同値へ進めないことを明示する。

### `Yulang.GeneralDictionarySlotViewBoundaryExamples.models_exact`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotViewBoundaryExamples.models_exact : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionarySlotViewBoundaryExamples.forgotten assignment ↔
    Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state true) assignment
```

### `Yulang.GeneralDictionarySlotViewBoundaryExamples.known_before`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotViewBoundaryExamples.known_before : Yulang.GeneralNominalState.Known
  (Yulang.GeneralNominalExamples.state true) 1
```

### `Yulang.GeneralDictionarySlotViewBoundaryExamples.not_known_after`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotViewBoundaryExamples.not_known_after : ¬Yulang.GeneralNominalState.Known
    Yulang.GeneralDictionarySlotViewBoundaryExamples.forgotten 1
```

### `Yulang.GeneralDictionarySlotViewBoundaryExamples.not_pending_before`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotViewBoundaryExamples.not_pending_before : ¬Yulang.GeneralNominalState.RootPending
    (Yulang.GeneralNominalExamples.state true) Yulang.GeneralDictionarySlotViewBoundaryExamples.demand
```

### `Yulang.GeneralDictionarySlotViewBoundaryExamples.pending_after`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotViewBoundaryExamples.pending_after : Yulang.GeneralNominalState.RootPending
  Yulang.GeneralDictionarySlotViewBoundaryExamples.forgotten Yulang.GeneralDictionarySlotViewBoundaryExamples.demand
```

### `Yulang.GeneralDictionarySlotViewBoundaryExamples.nonvacuous_view_boundary`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionarySlotViewBoundaryExamples.nonvacuous_view_boundary : Yulang.GeneralNominalState.Models
    (Yulang.GeneralNominalExamples.state true) Yulang.GeneralNominalExamples.model ∧
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionarySlotViewBoundaryExamples.forgotten
      Yulang.GeneralNominalExamples.model ∧
    Yulang.GeneralNominalState.Known (Yulang.GeneralNominalExamples.state true) 1 ∧
      ¬Yulang.GeneralNominalState.Known Yulang.GeneralDictionarySlotViewBoundaryExamples.forgotten 1 ∧
        ¬Yulang.GeneralNominalState.RootPending (Yulang.GeneralNominalExamples.state true)
              Yulang.GeneralDictionarySlotViewBoundaryExamples.demand ∧
          Yulang.GeneralNominalState.RootPending Yulang.GeneralDictionarySlotViewBoundaryExamples.forgotten
            Yulang.GeneralDictionarySlotViewBoundaryExamples.demand
```

## GeneralDictionaryFreshSlotPreparationExamples

予約済み新type88を実際に使用するraw payloadで、旧noneから新成功へ変わること、二重output、full nominal joint model、独立source Evidenceを示す。新rootはなおPendingであり、候補選択/Survivorではない。

### `Yulang.GeneralDictionaryFreshSlotPreparationExamples.preparation_success`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryFreshSlotPreparationExamples.preparation_success : Yulang.GeneralDictionaryPayloadPreparation.prepare
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter.base
    Yulang.GeneralDictionaryFreshSlotPreparationExamples.frames
    Yulang.GeneralDictionaryFreshSlotPreparationExamples.payload
    Yulang.GeneralDictionaryFreshSlotPreparationExamples.root =
  some Yulang.GeneralDictionaryFreshSlotPreparationExamples.tree
```

### `Yulang.GeneralDictionaryFreshSlotPreparationExamples.before_preparation_defers`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryFreshSlotPreparationExamples.before_preparation_defers : Yulang.GeneralDictionaryPayloadPreparation.prepare
    Yulang.GeneralDictionaryHeadlessFixture.registry Yulang.GeneralDictionaryHeadlessFixture.registry_checked
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore.base
    Yulang.GeneralDictionaryFreshSlotPreparationExamples.frames
    Yulang.GeneralDictionaryFreshSlotPreparationExamples.payload
    Yulang.GeneralDictionaryFreshSlotPreparationExamples.root =
  none
```

### `Yulang.GeneralDictionaryFreshSlotPreparationExamples.new_reserved_slot`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryFreshSlotPreparationExamples.new_reserved_slot : 88 ∈
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore.reserved ∧
  Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter.base.source 2 = 88 ∧
    ∀ (slot : Fin Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore.base.slots),
      Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedBefore.base.source slot ≠ 88
```

### `Yulang.GeneralDictionaryFreshSlotPreparationExamples.recorded_model`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryFreshSlotPreparationExamples.recorded_model : Yulang.GeneralNominalState.Models
  (Yulang.GeneralDictionaryNominalRecording.record Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter
    Yulang.GeneralDictionaryFreshSlotPreparationExamples.tree.items)
  Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment
```

### `Yulang.GeneralDictionaryFreshSlotPreparationExamples.fresh_source_evidence`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryFreshSlotPreparationExamples.fresh_source_evidence : Yulang.GeneralSourceDictionaries.Evidence
  (Yulang.GeneralDictionaryNominalSourceEvidence.Instance Yulang.GeneralDictionaryHeadlessFixture.registry
    Yulang.GeneralDictionaryHeadlessFixture.registry_checked Yulang.GeneralDictionaryFreshSlotPreparationExamples.frames
    Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAssignment)
  Yulang.GeneralDictionaryFreshSlotPreparationExamples.sourceTree
```

### `Yulang.GeneralDictionaryFreshSlotPreparationExamples.still_pending`

役割: 補助（回帰・非空性）。上記moduleの範囲と、以下の全前提のもとでの主張。

```lean
Yulang.GeneralDictionaryFreshSlotPreparationExamples.still_pending : Yulang.GeneralNominalState.RootPending
  Yulang.GeneralDictionaryNominalSlotTransportExamples.mixedAfter
  Yulang.GeneralDictionaryFreshSlotPreparationExamples.demand
```
