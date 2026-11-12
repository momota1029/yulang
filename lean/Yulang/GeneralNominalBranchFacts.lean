import Yulang.GeneralNominalBranchProjection

namespace Yulang.GeneralNominalBranchFacts
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates GeneralNominalSpineFacts GeneralNominalBranchProjection
open CommonNominalFullCarrier

structure Fork (state : GeneralNominalState.State) (n m : Nat)
    (names : Fin (n+m) → Nat) (bounds : Fin (n+m) → GeneralNominalInspection.Bounds state)
    (slot : Fin state.base.slots) where
  left : Fin state.base.slots
  right : Fin state.base.slots
  descriptor : GeneralNominalState.Descriptor state.base.slots
  recorded : state.nominals slot = some descriptor
  parameters : descriptor.arguments = [.type (left,left),.type (right,right)]
  one : Spine state (fun i : Fin n => names (i.castAdd m)) (fun i => bounds (i.castAdd m)) left
  two : Spine state (fun i : Fin m => names (i.natAdd n)) (fun i => bounds (i.natAdd n)) right

def Fork.query {state n m names bounds slot} (fork : Fork state n m names bounds slot) : GeneralNominalInspection.Query :=
  .nominal fork.descriptor.declaration.name [fork.one.query,fork.two.query]

theorem report_exact (context : Context) (declaration : Declaration) {n m names bounds slot}
    (fork : Fork context.state n m names bounds slot)
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration = [fork.query]) :
    report context declaration [(slot,slot)] =
      { inspect context.state fork.query (slot,slot) none with
        checked := (slot,slot) :: (inspect context.state fork.query (slot,slot) none).checked } := by
  simp [report,query,inspectMany,append_empty]

theorem private_models (context : Context) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) {n m : Nat} (names : Fin (n+m) → Nat) (distinct : Function.Injective names)
    (inputs : declaration.inputNames = List.ofFn names) (bounds) {slot}
    (fork : Fork context.state n m names bounds slot)
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration = [fork.query])
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    GeneralNominalState.Models (privateState registry context root declaration [(slot,slot)]) model ∧
      ProjectionModels context.state (report context declaration [(slot,slot)]) model := by
  have computed := report_exact context declaration fork query
  have captured : bindings context.state (report context declaration [(slot,slot)]) =
      List.ofFn fun i => (names i,context.state.base.source (bounds i).1,context.state.base.source (bounds i).2) := by
    rw [computed]
    exact fork_bindings context.state names bounds slot fork.left fork.right fork.descriptor fork.recorded fork.parameters fork.one fork.two none
  constructor
  · unfold privateState
    rw [captured]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · apply GeneralNominalLinearCaptureFacts.propagated_models context.state registry root.identity declaration names distinct inputs bounds model valid
      intro i
      refine Fin.addCases ?_ ?_ i
      · intro j
        exact spine_bounds context.state _ _ fork.one model valid j
      · intro j
        exact spine_bounds context.state _ _ fork.two model valid j
    · intro atom member
      obtain ⟨pair,present,rfl⟩ := List.mem_map.mp member
      rw [computed] at present
      rcases List.mem_cons.mp present with rfl | tail
      · exact subtype_refl _
      · exact fork_checked context.state _ _ _ _ slot fork.left fork.right fork.descriptor fork.recorded fork.parameters fork.one fork.two model valid none pair tail
  · rw [computed]
    have leftDistinct : Function.Injective (fun i : Fin n => names (i.castAdd m)) := by
      intro i j h
      have eq := congrArg Fin.val (distinct h)
      exact Fin.ext eq
    have rightDistinct : Function.Injective (fun i : Fin m => names (i.natAdd n)) := by
      intro i j h
      apply Fin.ext
      have eq := congrArg Fin.val (distinct h)
      simp only [Fin.val_natAdd] at eq
      omega
    have separate : ∀ (i : Fin n) (j : Fin m), names (i.castAdd m) ≠ names (j.natAdd n) := by
      intro i j h
      have eq := congrArg Fin.val (distinct h)
      simp only [Fin.val_castAdd,Fin.val_natAdd] at eq
      omega
    exact fork_projection context.state _ _ leftDistinct rightDistinct separate _ _ slot fork.left fork.right fork.descriptor fork.recorded fork.parameters fork.one fork.two model valid none (by intro o eq; cases eq)
end Yulang.GeneralNominalBranchFacts
