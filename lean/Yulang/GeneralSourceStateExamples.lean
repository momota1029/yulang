import Yulang.GeneralSourceState
import Yulang.CommonRoleRecordGraphBridge

/-!
# Source snapshot examples and a normalization falsifier

The Index example uses the multiargument demand and the shared ordinary state.
The recursive example has an actual Common regular model. The last example
shows why raw graph cycles cannot yet define the language's root K2 rule.
No implementation registry or independent fragment classifier is introduced.
-/
namespace Yulang.GeneralSourceStateExamples

open GeneralSourceState
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (All)

abbrev indexRole : Roles.RoleDecl :=
  ⟨2, fun name => if name = 0 then some none else none, by
    intro name rhs impossible
    split at impossible <;> cases impossible⟩

abbrev unaryRole : Roles.RoleDecl := ⟨1, fun _ => none, by intros; contradiction⟩
abbrev roles : Roles.RoleDecls := fun role => if role = 0 then indexRole else unaryRole

abbrev indexHeads : Fin 3 → Head (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Shape 3) :=
  fun slot => if slot = 0 then .scalar .str else .unresolved

abbrev indexState : State where
  slots := 3
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := equationAtoms 0 (.base .str)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := indexHeads
  intervals := [(0, 0), (1, 1)]
  heads_sound := by
    intro assignment models slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have same : (.base .str : TyTerm (Fin 3)) = term := by
        simpa [indexHeads, Head.equation] using recorded
      subst term
      exact (equationAtoms_exact _ _ assignment).mp models
    · simp [indexHeads, zero, Head.equation] at recorded
  intervals_sound := by
    intro assignment _ pair member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact Common.subtype_refl _

abbrev indexDemand : Demand roles where
  role := 0
  arguments := fun i => if i.val = 0 then (0, 0) else (1, 1)
  outputs := [⟨0, 2⟩]
  declared := by
    intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact ⟨none, rfl⟩

abbrev indexNeeded : Needed indexDemand := fun i => i.val = 0 ∨ i.val = 1

private theorem index_linked : Linked indexState indexDemand := by
  constructor
  · intro argument
    by_cases zero : argument.val = 0
    · exact ⟨(0, 0), by simp [indexState], by simp [zero]⟩
    · exact ⟨(1, 1), by simp [indexState], by simp [zero]⟩
  · intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact ⟨2, rfl⟩

abbrev indexModel (key : Common.Ty) : Assignment :=
  fun name => (if name = 0 then .base .str else key, Common.rowEmpty)

/-- Every Common key type is still possible; a future singleton registry has
no place to impose an equation in this state. -/
private theorem index_models (key : Common.Ty) : Models indexState (indexModel key) := by
  apply (models_ordinary _ _).mpr
  apply (equationAtoms_exact _ _ _).mpr
  exact Common.equivalent_refl _

private theorem index_pending : RootPending indexState indexDemand indexNeeded := by
  apply (pending_graph_iff indexState indexDemand index_linked indexNeeded).mpr
  exact ⟨⟨1, by simp [roles, indexRole]⟩, 1, Or.inr rfl, rfl, rfl⟩

abbrev indexAfterHeads : Fin 3 → Head (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Shape 3) :=
  fun slot => if slot = 0 then .scalar .str else if slot = 1 then .scalar .int else .unresolved

abbrev indexAfter : State where
  slots := 3
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := equationAtoms 0 (.base .str) ++ equationAtoms 1 (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := indexAfterHeads
  intervals := [(0, 0), (1, 1)]
  heads_sound := by
    intro assignment models slot term recorded
    have both := (PresenceNormalForm.all_append _ _ _ _).mp models
    by_cases zero : slot = 0
    · subst slot
      have same : (.base .str : TyTerm (Fin 3)) = term := by
        simpa [indexAfterHeads, Head.equation] using recorded
      subst term
      exact (equationAtoms_exact _ _ assignment).mp both.1
    · by_cases one : slot = 1
      · subst slot
        have same : (.base .int : TyTerm (Fin 3)) = term := by
          simpa [indexAfterHeads, Head.equation] using recorded
        subst term
        exact (equationAtoms_exact _ _ assignment).mp both.2
      · simp [indexAfterHeads, zero, one, Head.equation] at recorded
  intervals_sound := by
    intro assignment models
    exact indexState.intervals_sound assignment ((PresenceNormalForm.all_append _ _ _ _).mp models).1

private def index_refines : Refines indexState indexAfter where
  embed := id
  source := fun _ => rfl
  rowSource := fun _ => rfl
  ordinary := by
    intro atom member
    simp only [indexState, equationAtoms, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [indexAfter, equationAtoms, PresenceNormalForm.Atom.rename, TyTerm.rename]
  known := by
    intro slot known
    by_cases zero : slot = 0
    · simp [State.graph, indexAfter, indexAfterHeads, zero, Head.node]
    · exact False.elim (known (by simp [State.graph, indexState, indexHeads, zero, Head.node]))
  intervals := by intro pair member; cases pair; exact member

private theorem index_after_ready : ¬ RootPending indexAfter indexDemand indexNeeded := by
  rintro ⟨argument, required, unknown⟩
  rcases required with zero | one
  · exact unknown ⟨0, by simp [zero],
      by simp [State.graph, indexAfter, indexAfterHeads, Head.node]⟩
  · exact unknown ⟨1, by simp [one],
      by simp [State.graph, indexAfter, indexAfterHeads, Head.node]⟩

theorem index_example :
    Linked indexState indexDemand ∧ (∀ key, Models indexState (indexModel key)) ∧
      RootPending indexState indexDemand indexNeeded ∧
      Nonempty (Refines indexState indexAfter) ∧
      ¬ RootPending indexAfter indexDemand indexNeeded :=
  ⟨index_linked, index_models, index_pending, ⟨index_refines⟩, index_after_ready⟩

abbrev loopSource : CommonRoleRecordGraphBridge.RecordGraph 1 := fun _ => (7, 0)
abbrev loopType : Common.Ty := CommonRoleRecordGraphBridge.common loopSource 0

abbrev loopShapes : Fin 1 → Shape 1 := fun _ => .required 7
abbrev loopHeads : Fin 1 → Head loopShapes := fun _ => .structural 0 (fun _ => 0)

abbrev loopState : State where
  slots := 1
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := equationAtoms 0 (.required 7 (.var 0))
  kinds := 1
  shapes := loopShapes
  shapes_injective := by intro a b _; apply Fin.ext; omega
  heads := loopHeads
  intervals := [(0, 0)]
  heads_sound := by
    intro assignment models slot term recorded
    have zero : slot = 0 := by apply Fin.ext; omega
    subst slot
    have same : (.required 7 (.var 0) : TyTerm (Fin 1)) = term := by
      simpa [loopHeads, Head.equation, loopShapes, Shape.term] using recorded
    subst term
    exact (equationAtoms_exact _ _ assignment).mp models
  intervals_sound := by
    intro assignment _ pair member
    have same := List.mem_singleton.mp member
    subst pair
    exact Common.subtype_refl _

abbrev loopDemand : Demand roles where
  role := 1
  arguments := fun _ => (0, 0)
  outputs := []
  declared := by intro output member; cases member

abbrev loopNeeded : Needed loopDemand := fun i => i.val = 0
abbrev loopModel : Assignment := fun _ => (loopType, Common.rowEmpty)

private theorem loop_linked : Linked loopState loopDemand :=
  ⟨fun _ => ⟨(0, 0), by simp [loopState], rfl⟩, fun _ member => nomatch member⟩

private theorem loop_models : Models loopState loopModel := by
  apply (models_ordinary _ _).mpr
  apply (equationAtoms_exact _ _ _).mpr
  exact CommonRoleRecordGraphBridge.common_unfold loopSource 0

private theorem loop_ready : ¬ RootPending loopState loopDemand loopNeeded := by
  rintro ⟨argument, _, unknown⟩
  exact unknown ⟨0, rfl, by simp [State.graph, loopState, Head.node]⟩

/-- The loop example has a real regular Common model, not merely a graph flag. -/
private theorem loop_observedK2 : ObservedRootK2 loopState loopDemand loopNeeded := by
  refine ⟨loop_ready, ⟨0, by simp [roles, unaryRole]⟩, 0, rfl, Or.inl ?_⟩
  refine ⟨0, [0], rfl, 0, by simp, ?_⟩
  exact FiniteWorklist.Path.nil _

private theorem loop_unfolds : Common.Equivalent loopType (Common.required 7 loopType) :=
  CommonRoleRecordGraphBridge.common_unfold loopSource 0

theorem recursive_example :
    Linked loopState loopDemand ∧ Models loopState loopModel ∧
      ObservedRootK2 loopState loopDemand loopNeeded ∧
      ¬ RootPending loopState loopDemand loopNeeded ∧
      Common.Equivalent loopType (Common.required 7 loopType) :=
  ⟨loop_linked, loop_models, loop_observedK2, loop_ready, loop_unfolds⟩

/-- A finite type also solves a raw self-tail equation. Such an equation is
insufficient to certify normalized source recursion. -/
private theorem finite_self_tail (label : Nat) (payload : Common.Ty) :
    Common.Equivalent (Common.required label payload)
      (Common.record label payload (Common.required label payload)) :=
  Common.equivalent_symm (Common.common_shadowed_head_equivalent label payload payload .emptyRecord)

abbrev shadowShapes : Fin 1 → Shape 2 := fun _ => .record 7
abbrev shadowChildren : Fin (shadowShapes 0).arity → Fin 2 := fun i => if i.val = 0 then 1 else 0
abbrev shadowHeads : Fin 2 → Head shadowShapes := fun slot =>
  if slot = 0 then .structural 0 shadowChildren else .scalar .int

/-- The raw tail is still present. This is deliberately not a normalized view. -/
abbrev shadowState : State where
  slots := 2
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := equationAtoms 0 (.record 7 (.var 1) (.var 0)) ++ equationAtoms 1 (.base .int)
  kinds := 1
  shapes := shadowShapes
  shapes_injective := by intro a b _; apply Fin.ext; omega
  heads := shadowHeads
  intervals := [(0, 0)]
  heads_sound := by
    intro assignment models slot term recorded
    have both := (PresenceNormalForm.all_append _ _ _ _).mp models
    by_cases zero : slot = 0
    · subst slot
      have same : (.record 7 (.var 1) (.var 0) : TyTerm (Fin 2)) = term := by
        simpa [shadowHeads, Head.equation, Shape.term, shadowChildren] using recorded
      subst term
      exact (equationAtoms_exact _ _ assignment).mp both.1
    · have one : slot = 1 := by apply Fin.ext; have := slot.isLt; omega
      subst slot
      have same : (.base .int : TyTerm (Fin 2)) = term := by
        simpa [shadowHeads, Head.equation] using recorded
      subst term
      exact (equationAtoms_exact _ _ assignment).mp both.2
  intervals_sound := by
    intro assignment _ pair member
    have same := List.mem_singleton.mp member
    subst pair
    exact Common.subtype_refl _

abbrev shadowModel : Assignment := fun source =>
  (if source = 0 then Common.required 7 (.base .int) else .base .int, Common.rowEmpty)

/-- A model-inhabited checked snapshot with a raw cycle and a finite lower
type. This prevents promoting ObservedRootK2 to the normalized source rule. -/
theorem shadow_cycle_counterexample :
    Linked shadowState loopDemand ∧ Models shadowState shadowModel ∧
      ObservedRootK2 shadowState loopDemand loopNeeded ∧
      (shadowModel 0).1 = Common.required 7 (.base .int) := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · exact ⟨fun _ => ⟨(0, 0), by simp [shadowState], rfl⟩,
      fun _ member => nomatch member⟩
  · apply (models_ordinary _ _).mpr
    apply (PresenceNormalForm.all_append _ _ _ _).mpr
    constructor
    · apply (equationAtoms_exact _ _ _).mpr
      exact finite_self_tail 7 (.base .int)
    · apply (equationAtoms_exact _ _ _).mpr
      exact Common.equivalent_refl _
  · constructor
    · rintro ⟨argument, _, unknown⟩
      exact unknown ⟨0, rfl, by simp [State.graph, shadowState, shadowHeads, Head.node]⟩
    · refine ⟨⟨0, by simp [roles, unaryRole]⟩, 0, rfl, Or.inl ?_⟩
      refine ⟨0, [1, 0], rfl, 0, by simp, ?_⟩
      exact FiniteWorklist.Path.nil _

end Yulang.GeneralSourceStateExamples
