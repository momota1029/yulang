# Cycle150 final initial-source addition

8new theorems; final99theorem audit and type print exit0. Full17module scoped gate not completed.

## Focused build
```text
✔ [692/692] Built Yulang.GeneralDictionaryTreeInitialExample (1.1s)
Build completed successfully (692 jobs).

```

## Exact types for initial-source addition
```text
Yulang.GeneralDictionaryTreeInitialExample.metadata : Yulang.GeneralNominalRecursiveCandidates.Metadata
  Yulang.GeneralNominalTreeExample.registry Yulang.GeneralNominalTreeExample.context
Yulang.GeneralDictionaryTreeInitialExample.linked : Yulang.GeneralNominalState.Linked
  Yulang.GeneralNominalTreeExample.state Yulang.GeneralNominalTreeExample.root.demand
Yulang.GeneralDictionaryTreeInitialExample.initial_source : Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralNominalTreeExample.registry Yulang.GeneralNominalTreeExample.context
  Yulang.GeneralNominalTreeExample.root
Yulang.GeneralDictionaryTreeInitialExample.initial_models : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDictionaryTreeInitialExample.start.current Yulang.GeneralNominalTreeExample.model
Yulang.GeneralDictionaryTreeInitialExample.actual_reachable : Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralNominalTreeExample.registry Yulang.GeneralNominalTreeExample.root
  Yulang.GeneralDictionaryTreeInitialExample.start
Yulang.GeneralDictionaryTreeInitialExample.actual_instance : Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralNominalTreeExample.registry Yulang.GeneralNominalTreeExample.context
  Yulang.GeneralNominalTreeExample.model Yulang.GeneralNominalTreeExample.root
  Yulang.GeneralNominalTreeExample.declaration.id []
Yulang.GeneralDictionaryTreeInitialExample.evidence : Yulang.GeneralDictionaryRecursiveEvidence.Evidence
  Yulang.GeneralNominalTreeExample.registry Yulang.GeneralNominalTreeExample.context
  Yulang.GeneralNominalTreeExample.model Yulang.GeneralNominalTreeExample.root
  (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralNominalTreeExample.declaration.id [])
Yulang.GeneralDictionaryTreeInitialExample.reachable_inhabited_evidence : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalTreeExample.registry Yulang.GeneralNominalTreeExample.root
    Yulang.GeneralDictionaryTreeInitialExample.start ∧
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryTreeInitialExample.start.current
      Yulang.GeneralNominalTreeExample.model ∧
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralNominalTreeExample.registry
      Yulang.GeneralDictionaryTreeInitialExample.start.current.context Yulang.GeneralNominalTreeExample.model
      Yulang.GeneralNominalTreeExample.root
      (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralNominalTreeExample.declaration.id [])
@Yulang.GeneralDictionaryTreeLeaf.branch_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (shape : Yulang.GeneralDictionaryTreeLeaf.TreeLeafShape context root declaration)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models context.state model →
    Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked
      [(shape.slot, shape.slot)] model
@Yulang.GeneralDictionaryTreeLeaf.ready : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (shape : Yulang.GeneralDictionaryTreeLeaf.TreeLeafShape context root declaration),
  Yulang.GeneralNominalRecursiveCandidates.RequestReady registry context root declaration checked
    [(shape.slot, shape.slot)]
@Yulang.GeneralDictionaryTreeLeaf.instance_of_shape : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  declaration ∈ registry.declarations →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
      ∀ (shape : Yulang.GeneralDictionaryTreeLeaf.TreeLeafShape context root declaration),
        Yulang.GeneralNominalRecursiveCandidates.Metadata registry context →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models context.state model →
              Yulang.GeneralDictionaryRecursiveEvidence.Instance registry context model root declaration.id []
@Yulang.GeneralDictionaryTreeLeaf.selected_leaf : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  declaration ∈ registry.declarations →
    Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
      ∀ (shape : Yulang.GeneralDictionaryTreeLeaf.TreeLeafShape state.context root declaration) (key : Nat)
        (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        Yulang.GeneralNominalFeedbackK2.Local registry state root
            (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models state.context.state model →
              declaration.id = key ∧
                children = [] ∧
                  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.context model root key [] ∧
                    Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root
                      (Yulang.CommonRoleOutermostResolver.Dictionary.node key [])
@Yulang.GeneralDictionaryTreeLeaf.selected_of_coverage : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralDictionaryTreeLeaf.HasTreeLeaf registry state.context root →
    ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralNominalFeedbackK2.Local registry state root
          (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalState.Models state.context.state model →
            children = [] ∧
              Yulang.GeneralDictionaryRecursiveEvidence.Instance registry state.context model root key [] ∧
                Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root
                  (Yulang.CommonRoleOutermostResolver.Dictionary.node key [])
@Yulang.GeneralDictionaryTreeLeaf.spine_covered : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralDictionarySpineLeaf.HasSpineLeaf registry context root →
    Yulang.GeneralDictionaryTreeLeaf.HasTreeLeaf registry context root
@Yulang.GeneralDictionaryTreeLeaf.branch_covered : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralDictionaryBranchLeaf.HasBranchLeaf registry context root →
    Yulang.GeneralDictionaryTreeLeaf.HasTreeLeaf registry context root
Yulang.GeneralNominalBranchExample.state_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralNominalBranchExample.state Yulang.GeneralNominalBranchExample.model
Yulang.GeneralNominalBranchExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalBranchExample.declaration
Yulang.GeneralNominalBranchExample.actual_branch : Yulang.GeneralNominalRecursiveCandidates.BranchModels
  Yulang.GeneralNominalBranchExample.registry Yulang.GeneralNominalBranchExample.context
  Yulang.GeneralNominalBranchExample.root Yulang.GeneralNominalBranchExample.declaration
  Yulang.GeneralNominalBranchExample.checked [(0, 0)] Yulang.GeneralNominalBranchExample.model
@Yulang.GeneralNominalBranchExample.not_unary_spine : ∀ {n : Nat} (names : Fin n → Nat)
  (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalBranchExample.state)
  (spine : Yulang.GeneralNominalSpineFacts.Spine Yulang.GeneralNominalBranchExample.state names bounds 0),
  spine.query ≠ Yulang.GeneralNominalBranchExample.fork.query
Yulang.GeneralNominalBranchExample.inhabited_branch : Yulang.GeneralNominalState.Models
    Yulang.GeneralNominalBranchExample.state Yulang.GeneralNominalBranchExample.model ∧
  Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralNominalBranchExample.registry
    Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.root
    Yulang.GeneralNominalBranchExample.declaration Yulang.GeneralNominalBranchExample.checked [(0, 0)]
    Yulang.GeneralNominalBranchExample.model
Yulang.GeneralNominalBranchFacts.report_exact : ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (declaration : Yulang.GeneralDeclarations.Declaration) {n m : Nat} {names : Fin (n + m) → Nat}
  {bounds : Fin (n + m) → Yulang.GeneralNominalInspection.Bounds context.state} {slot : Fin context.state.base.slots}
  (fork : Yulang.GeneralNominalBranchFacts.Fork context.state n m names bounds slot),
  Yulang.GeneralNominalInspection.queries context.state context.interpretation declaration = [fork.query] →
    Yulang.GeneralNominalRecursiveCandidates.report context declaration [(slot, slot)] =
      have __src := Yulang.GeneralNominalRecursiveInspection.inspect context.state fork.query (slot, slot) none;
      { captures := __src.captures, inspected := __src.inspected,
        checked :=
          (slot, slot) ::
            (Yulang.GeneralNominalRecursiveInspection.inspect context.state fork.query (slot, slot) none).checked,
        blocked := __src.blocked, conflicts := __src.conflicts, arity := __src.arity, anchors := __src.anchors,
        tests := __src.tests }
@Yulang.GeneralNominalBranchFacts.private_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  {n m : Nat} (names : Fin (n + m) → Nat),
  Function.Injective names →
    declaration.inputNames = List.ofFn names →
      ∀ (bounds : Fin (n + m) → Yulang.GeneralNominalInspection.Bounds context.state)
        {slot : Fin context.state.base.slots}
        (fork : Yulang.GeneralNominalBranchFacts.Fork context.state n m names bounds slot),
        Yulang.GeneralNominalInspection.queries context.state context.interpretation declaration = [fork.query] →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models context.state model →
              Yulang.GeneralNominalState.Models
                  (Yulang.GeneralNominalRecursiveCandidates.privateState registry context root declaration
                    [(slot, slot)])
                  model ∧
                Yulang.GeneralNominalRecursiveInspection.ProjectionModels context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report context declaration [(slot, slot)]) model
Yulang.GeneralNominalBranchProjection.point_argument_matches : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (slot child : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals slot = some descriptor →
        ∀ (index : Nat),
          descriptor.arguments[index]? = some (Yulang.GeneralNominalState.Parameter.type (child, child)) →
            ∀ (origin : Yulang.GeneralNominalRecursiveInspection.Origin),
              Yulang.GeneralNominalSpineFacts.Matches state model slot origin →
                Yulang.GeneralNominalSpineFacts.Matches state model child
                  (origin.nominal descriptor.declaration.name index)
Yulang.GeneralNominalBranchProjection.append_projection : ∀ (state : Yulang.GeneralNominalState.State)
  (left right : Yulang.GeneralNominalRecursiveInspection.Report state)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveInspection.ProjectionModels state left model →
    Yulang.GeneralNominalRecursiveInspection.ProjectionModels state right model →
      (∀ (a : Yulang.GeneralNominalRecursiveInspection.Capture state),
          a ∈ left.captures →
            ∀ (b : Yulang.GeneralNominalRecursiveInspection.Capture state), b ∈ right.captures → a.name ≠ b.name) →
        Yulang.GeneralNominalRecursiveInspection.ProjectionModels state (left.append right) model
Yulang.GeneralNominalBranchProjection.spine_capture_name : ∀ (state : Yulang.GeneralNominalState.State) {n : Nat}
  (names : Fin n → Nat) (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state) {slot : Fin state.base.slots}
  (spine : Yulang.GeneralNominalSpineFacts.Spine state names bounds slot)
  (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin)
  (capture : Yulang.GeneralNominalRecursiveInspection.Capture state),
  capture ∈ (Yulang.GeneralNominalRecursiveInspection.inspect state spine.query (slot, slot) origin).captures →
    ∃ i, capture.name = names i
Yulang.GeneralNominalBranchProjection.inspect_fork : ∀ (state : Yulang.GeneralNominalState.State)
  (slot left right : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals slot = some descriptor →
    descriptor.arguments =
        [Yulang.GeneralNominalState.Parameter.type (left, left),
          Yulang.GeneralNominalState.Parameter.type (right, right)] →
      ∀ (one two : Yulang.GeneralNominalInspection.Query)
        (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
        Yulang.GeneralNominalRecursiveInspection.inspect state
            (Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name [one, two]) (slot, slot) origin =
          Yulang.GeneralNominalRecursiveInspection.Report.visit (slot, slot) origin
            (Yulang.GeneralNominalRecursiveInspection.Test.nominal descriptor.declaration.name 2)
            ((Yulang.GeneralNominalRecursiveInspection.inspect state one (left, left)
                  (some
                    ((origin.getD
                          (Yulang.GeneralNominalRecursiveInspection.Origin.source (state.base.source slot))).nominal
                      descriptor.declaration.name 0))).append
              (Yulang.GeneralNominalRecursiveInspection.inspect state two (right, right)
                (some
                  ((origin.getD
                        (Yulang.GeneralNominalRecursiveInspection.Origin.source (state.base.source slot))).nominal
                    descriptor.declaration.name 1))))
Yulang.GeneralNominalBranchProjection.fork_projection : ∀ (state : Yulang.GeneralNominalState.State) {n m : Nat}
  (names : Fin n → Nat) (other : Fin m → Nat),
  Function.Injective names →
    Function.Injective other →
      (∀ (i : Fin n) (j : Fin m), names i ≠ other j) →
        ∀ (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state)
          (otherBounds : Fin m → Yulang.GeneralNominalInspection.Bounds state) (slot left right : Fin state.base.slots)
          (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
          state.nominals slot = some descriptor →
            descriptor.arguments =
                [Yulang.GeneralNominalState.Parameter.type (left, left),
                  Yulang.GeneralNominalState.Parameter.type (right, right)] →
              ∀ (one : Yulang.GeneralNominalSpineFacts.Spine state names bounds left)
                (two : Yulang.GeneralNominalSpineFacts.Spine state other otherBounds right)
                (model : Yulang.GeneralNominalCommonBridge.Assignment),
                Yulang.GeneralNominalState.Models state model →
                  ∀ (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
                    (∀ (o : Yulang.GeneralNominalRecursiveInspection.Origin),
                        origin = some o → Yulang.GeneralNominalSpineFacts.Matches state model slot o) →
                      Yulang.GeneralNominalRecursiveInspection.ProjectionModels state
                        (Yulang.GeneralNominalRecursiveInspection.inspect state
                          (Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                            [one.query, two.query])
                          (slot, slot) origin)
                        model
Yulang.GeneralNominalBranchProjection.fork_finished : ∀ (state : Yulang.GeneralNominalState.State) {n m : Nat}
  (names : Fin n → Nat) (other : Fin m → Nat) (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state)
  (otherBounds : Fin m → Yulang.GeneralNominalInspection.Bounds state) (slot left right : Fin state.base.slots)
  (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals slot = some descriptor →
    descriptor.arguments =
        [Yulang.GeneralNominalState.Parameter.type (left, left),
          Yulang.GeneralNominalState.Parameter.type (right, right)] →
      ∀ (one : Yulang.GeneralNominalSpineFacts.Spine state names bounds left)
        (two : Yulang.GeneralNominalSpineFacts.Spine state other otherBounds right)
        (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
        Yulang.GeneralNominalRecursiveInspection.Finished
          (Yulang.GeneralNominalRecursiveInspection.inspect state
            (Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name [one.query, two.query])
            (slot, slot) origin)
Yulang.GeneralNominalBranchProjection.fork_bindings : ∀ (state : Yulang.GeneralNominalState.State) {n m : Nat}
  (names : Fin (n + m) → Nat) (bounds : Fin (n + m) → Yulang.GeneralNominalInspection.Bounds state)
  (slot left right : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals slot = some descriptor →
    descriptor.arguments =
        [Yulang.GeneralNominalState.Parameter.type (left, left),
          Yulang.GeneralNominalState.Parameter.type (right, right)] →
      ∀
        (one :
          Yulang.GeneralNominalSpineFacts.Spine state (fun i => names (Fin.castAdd m i))
            (fun i => bounds (Fin.castAdd m i)) left)
        (two :
          Yulang.GeneralNominalSpineFacts.Spine state (fun i => names (Fin.natAdd n i))
            (fun i => bounds (Fin.natAdd n i)) right)
        (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
        Yulang.GeneralNominalRecursiveInspection.bindings state
            (Yulang.GeneralNominalRecursiveInspection.inspect state
              (Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name [one.query, two.query])
              (slot, slot) origin) =
          List.ofFn fun i => (names i, state.base.source (bounds i).fst, state.base.source (bounds i).snd)
Yulang.GeneralNominalBranchProjection.fork_checked : ∀ (state : Yulang.GeneralNominalState.State) {n m : Nat}
  (names : Fin n → Nat) (other : Fin m → Nat) (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state)
  (otherBounds : Fin m → Yulang.GeneralNominalInspection.Bounds state) (slot left right : Fin state.base.slots)
  (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals slot = some descriptor →
    descriptor.arguments =
        [Yulang.GeneralNominalState.Parameter.type (left, left),
          Yulang.GeneralNominalState.Parameter.type (right, right)] →
      ∀ (one : Yulang.GeneralNominalSpineFacts.Spine state names bounds left)
        (two : Yulang.GeneralNominalSpineFacts.Spine state other otherBounds right)
        (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalState.Models state model →
          ∀ (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin)
            (pair : Yulang.GeneralNominalInspection.Bounds state),
            pair ∈
                (Yulang.GeneralNominalRecursiveInspection.inspect state
                    (Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name [one.query, two.query])
                    (slot, slot) origin).checked →
              Yulang.CommonNominalFullCarrier.Subtype (model (state.base.source pair.fst)).fst
                (model (state.base.source pair.snd)).fst
Yulang.GeneralNominalTreeExample.state_models : Yulang.GeneralNominalState.Models Yulang.GeneralNominalTreeExample.state
  Yulang.GeneralNominalTreeExample.model
Yulang.GeneralNominalTreeExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalTreeExample.declaration
Yulang.GeneralNominalTreeExample.actual_branch : Yulang.GeneralNominalRecursiveCandidates.BranchModels
  Yulang.GeneralNominalTreeExample.registry Yulang.GeneralNominalTreeExample.context
  Yulang.GeneralNominalTreeExample.root Yulang.GeneralNominalTreeExample.declaration
  Yulang.GeneralNominalTreeExample.checked [(0, 0)] Yulang.GeneralNominalTreeExample.model
@Yulang.GeneralNominalTreeExample.inner_not_spine : ∀ {n : Nat} (names : Fin n → Nat)
  (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalTreeExample.state)
  (spine : Yulang.GeneralNominalSpineFacts.Spine Yulang.GeneralNominalTreeExample.state names bounds 1),
  spine.query ≠ Yulang.GeneralNominalTreeExample.innerTree.query
@Yulang.GeneralNominalTreeExample.not_single_fork : ∀ {n m : Nat} (names : Fin (n + m) → Nat)
  (bounds : Fin (n + m) → Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalTreeExample.state)
  (fork : Yulang.GeneralNominalBranchFacts.Fork Yulang.GeneralNominalTreeExample.state n m names bounds 0),
  fork.query ≠ Yulang.GeneralNominalTreeExample.tree.query
Yulang.GeneralNominalTreeExample.inhabited_tree_branch : Yulang.GeneralNominalState.Models
    Yulang.GeneralNominalTreeExample.state Yulang.GeneralNominalTreeExample.model ∧
  Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralNominalTreeExample.registry
    Yulang.GeneralNominalTreeExample.context Yulang.GeneralNominalTreeExample.root
    Yulang.GeneralNominalTreeExample.declaration Yulang.GeneralNominalTreeExample.checked [(0, 0)]
    Yulang.GeneralNominalTreeExample.model
Yulang.GeneralNominalTreeFacts.capture_name : ∀ (state : Yulang.GeneralNominalState.State) {n : Nat}
  {names : Fin n → Nat} {bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state} {slot : Fin state.base.slots}
  (tree : Yulang.GeneralNominalTreeFacts.Tree state names bounds slot)
  (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin)
  (capture : Yulang.GeneralNominalRecursiveInspection.Capture state),
  capture ∈ (Yulang.GeneralNominalRecursiveInspection.inspect state tree.query (slot, slot) origin).captures →
    ∃ i, capture.name = names i
Yulang.GeneralNominalTreeFacts.tree_projection : ∀ (state : Yulang.GeneralNominalState.State) {n : Nat}
  {names : Fin n → Nat} {bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state} {slot : Fin state.base.slots}
  (tree : Yulang.GeneralNominalTreeFacts.Tree state names bounds slot),
  Function.Injective names →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models state model →
        ∀ (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
          (∀ (o : Yulang.GeneralNominalRecursiveInspection.Origin),
              origin = some o → Yulang.GeneralNominalSpineFacts.Matches state model slot o) →
            Yulang.GeneralNominalRecursiveInspection.ProjectionModels state
              (Yulang.GeneralNominalRecursiveInspection.inspect state tree.query (slot, slot) origin) model
Yulang.GeneralNominalTreeFacts.tree_bindings : ∀ (state : Yulang.GeneralNominalState.State) {n : Nat}
  {names : Fin n → Nat} {bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state} {slot : Fin state.base.slots}
  (tree : Yulang.GeneralNominalTreeFacts.Tree state names bounds slot)
  (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
  Yulang.GeneralNominalRecursiveInspection.bindings state
      (Yulang.GeneralNominalRecursiveInspection.inspect state tree.query (slot, slot) origin) =
    List.ofFn fun i => (names i, state.base.source (bounds i).fst, state.base.source (bounds i).snd)
Yulang.GeneralNominalTreeFacts.tree_finished : ∀ (state : Yulang.GeneralNominalState.State) {n : Nat}
  {names : Fin n → Nat} {bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state} {slot : Fin state.base.slots}
  (tree : Yulang.GeneralNominalTreeFacts.Tree state names bounds slot)
  (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
  Yulang.GeneralNominalRecursiveInspection.Finished
    (Yulang.GeneralNominalRecursiveInspection.inspect state tree.query (slot, slot) origin)
Yulang.GeneralNominalTreeFacts.tree_bounds : ∀ (state : Yulang.GeneralNominalState.State) {n : Nat}
  {names : Fin n → Nat} {bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state} {slot : Fin state.base.slots}
  (tree : Yulang.GeneralNominalTreeFacts.Tree state names bounds slot)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (i : Fin n),
      Yulang.CommonNominalFullCarrier.Subtype (model (state.base.source (bounds i).fst)).fst
        (model (state.base.source (bounds i).snd)).fst
Yulang.GeneralNominalTreeFacts.tree_checked : ∀ (state : Yulang.GeneralNominalState.State) {n : Nat}
  {names : Fin n → Nat} {bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state} {slot : Fin state.base.slots}
  (tree : Yulang.GeneralNominalTreeFacts.Tree state names bounds slot)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin)
      (pair : Yulang.GeneralNominalInspection.Bounds state),
      pair ∈ (Yulang.GeneralNominalRecursiveInspection.inspect state tree.query (slot, slot) origin).checked →
        Yulang.CommonNominalFullCarrier.Subtype (model (state.base.source pair.fst)).fst
          (model (state.base.source pair.snd)).fst
Yulang.GeneralNominalTreeFacts.report_exact : ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (declaration : Yulang.GeneralDeclarations.Declaration) {n : Nat} {names : Fin n → Nat}
  {bounds : Fin n → Yulang.GeneralNominalInspection.Bounds context.state} {slot : Fin context.state.base.slots}
  (tree : Yulang.GeneralNominalTreeFacts.Tree context.state names bounds slot),
  Yulang.GeneralNominalInspection.queries context.state context.interpretation declaration = [tree.query] →
    Yulang.GeneralNominalRecursiveCandidates.report context declaration [(slot, slot)] =
      have __src := Yulang.GeneralNominalRecursiveInspection.inspect context.state tree.query (slot, slot) none;
      { captures := __src.captures, inspected := __src.inspected,
        checked :=
          (slot, slot) ::
            (Yulang.GeneralNominalRecursiveInspection.inspect context.state tree.query (slot, slot) none).checked,
        blocked := __src.blocked, conflicts := __src.conflicts, arity := __src.arity, anchors := __src.anchors,
        tests := __src.tests }
@Yulang.GeneralNominalTreeFacts.private_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  {n : Nat} (names : Fin n → Nat),
  Function.Injective names →
    declaration.inputNames = List.ofFn names →
      ∀ (bounds : Fin n → Yulang.GeneralNominalInspection.Bounds context.state) {slot : Fin context.state.base.slots}
        (tree : Yulang.GeneralNominalTreeFacts.Tree context.state names bounds slot),
        Yulang.GeneralNominalInspection.queries context.state context.interpretation declaration = [tree.query] →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models context.state model →
              Yulang.GeneralNominalState.Models
                  (Yulang.GeneralNominalRecursiveCandidates.privateState registry context root declaration
                    [(slot, slot)])
                  model ∧
                Yulang.GeneralNominalRecursiveInspection.ProjectionModels context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report context declaration [(slot, slot)]) model
@Yulang.GeneralNominalTreeFacts.ofSpine_query : ∀ {state : Yulang.GeneralNominalState.State} {n : Nat}
  {names : Fin n → Nat} {bounds : Fin n → Yulang.GeneralNominalInspection.Bounds state} {slot : Fin state.base.slots}
  (spine : Yulang.GeneralNominalSpineFacts.Spine state names bounds slot),
  (Yulang.GeneralNominalTreeFacts.ofSpine spine).query = spine.query
@Yulang.GeneralNominalTreeFacts.ofFork_query : ∀ {state : Yulang.GeneralNominalState.State} {n m : Nat}
  {names : Fin (n + m) → Nat} {bounds : Fin (n + m) → Yulang.GeneralNominalInspection.Bounds state}
  {slot : Fin state.base.slots} (fork : Yulang.GeneralNominalBranchFacts.Fork state n m names bounds slot),
  (Yulang.GeneralNominalTreeFacts.ofFork fork).query = fork.query

```

## Final99theorem axiom output
```text
'Yulang.GeneralDictionaryFiniteJournalJointExample.alias_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJointExample.root_locality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJointExample.root_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJointExample.actual_stable_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.coverage_from_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.dictionary_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.forget_growth' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.covered_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.recursive_fixture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.at_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.steps_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.at_aliases' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.at_named' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.initial_invariants' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.alias_eq' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.related_locality' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.initial_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocalityExample.root_named' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNamedLocalityExample.child_named' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNamedLocalityExample.actual_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocalityExample.every_model_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryAliasMixedLocality.leaf_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryAliasMixedLocality.covered_of_recorded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryAliasMixedLocality.covered_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryAliasMixedLocality.early_ordinary_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryAliasRecordedLocality.covered_of_locality' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryAliasRecordedLocality.related_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryAliasRecordedLocality.covered_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryAliasRecordedLocality.early_ordinary_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchLeaf.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchLeaf.ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBranchLeaf.instance_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchLeaf.selected_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchLeaf.selected_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalBranchExample.state_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchExample.checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchExample.actual_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalBranchExample.not_unary_spine' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchExample.inhabited_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalBranchFacts.report_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchFacts.private_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalBranchProjection.point_argument_matches' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.append_projection' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.spine_capture_name' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.inspect_fork' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.fork_projection' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.fork_finished' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.fork_bindings' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.fork_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.selected_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.dictionary_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.dictionaries_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.of_spine' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.recursive_fixture' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.of_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.initial_dictionary_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryAliasTreeLocality.leaf_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryAliasTreeLocality.covered_of_recorded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryAliasTreeLocality.covered_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryAliasTreeLocality.early_ordinary_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryAliasTreeLocality.covered_of_mixed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.selected_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.dictionary_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.dictionaries_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.of_branch' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.recursive_fixture' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.of_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.initial_dictionary_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.instance_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.selected_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.selected_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.spine_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.branch_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeExample.state_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeExample.checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeExample.actual_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalTreeExample.inner_not_spine' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeExample.not_single_fork' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeExample.inhabited_tree_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalTreeFacts.capture_name' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.tree_projection' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.tree_bindings' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.tree_finished' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.tree_bounds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.tree_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.report_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.private_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalTreeFacts.ofSpine_query' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.ofFork_query' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeInitialExample.metadata' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeInitialExample.linked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeInitialExample.initial_source' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeInitialExample.initial_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeInitialExample.actual_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeInitialExample.actual_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeInitialExample.evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeInitialExample.reachable_inhabited_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```
