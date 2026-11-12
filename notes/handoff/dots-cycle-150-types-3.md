# Cycle150 exact theorem types, part3/3

Lean4.35.0 `#check @name`, exit0.

```text
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
