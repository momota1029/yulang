import Yulang.GeneralNominalCycleEdges
import Yulang.GeneralNominalProgressObstruction

/-! An outer list node is off-cycle while its record argument is cyclic.
This is distinct from the older record/list example where both nodes lie on
the same cycle. The model and the graph use the full nominal carrier. -/
namespace Yulang.GeneralNominalCycleWrapper

open GeneralDeclarationExamples (roles constructors)
open GeneralSourceState (equationAtoms equationAtoms_exact)
open CommonNominalFullCarrier
open Core.PresenceGeneration (TyTerm)

abbrev shapes : Fin 1 → GeneralSourceState.Shape 2 := fun _ => .required 7
abbrev heads : Fin 2 → GeneralSourceState.Head shapes :=
  fun slot => if slot = 0 then .structural 0 (fun _ => 0) else .unresolved

abbrev base : GeneralSourceState.State where
  slots := 2
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := equationAtoms 0 (.required 7 (.var 0))
  kinds := 1
  shapes := shapes
  shapes_injective := by intro i j _; exact Subsingleton.elim _ _
  heads := heads
  intervals := [(0,0),(1,1)]
  heads_sound := by
    intro assignment valid slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have same : (.required 7 (.var 0) : TyTerm (Fin 2)) = term := by
        simpa [heads,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term] using recorded
      subst term; exact (equationAtoms_exact ..).mp valid
    · simp [heads,zero,GeneralSourceState.Head.equation] at recorded
  intervals_sound := by
    intro assignment _ pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact Common.subtype_refl _

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 1
  shapes := fun _ => .record [7]
  shapes_injective := by intro i j _; exact Subsingleton.elim _ _
  canonical := by intro i; simp [GeneralNormalizedObservation.Shape.Canonical]
  heads := fun slot => if slot = 0 then .structural 0 (fun _ => 0) else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have same : (.record 7 (.var 0) .emptyRecord : TyTerm (Fin 2)) = term := by
        simpa [GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Shape.term,
          GeneralNormalizedObservation.recordTerm,List.ofFn_succ] using recorded
      subst term; exact .trans (.head rfl) .required
    · simp [zero,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded

abbrev descriptor : GeneralNominalState.Descriptor 2 := ⟨0,⟨[.type],0⟩,[.type (0,0)],rfl⟩
abbrev state : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => if slot = 1 then some descriptor else none
  catalogue := by
    intro slot d recorded
    split at recorded
    · have same := Option.some.inj recorded; subst d; rfl
    · cases recorded
  bodies_opaque := by
    intro slot d recorded
    by_cases one : slot = 1
    · subst slot; rfl
    · simp [one] at recorded

abbrev body : CommonNominalFullGuardedClosure.Body 2 0 := fun index =>
  if index = 0 then .record 7 (.inl 0) .emptyRecord else .nominal 0 [.inl (.inl 0)]
abbrev value := CommonNominalFullGuardedClosure.instantiate body Fin.elim0
abbrev model : GeneralNominalCommonBridge.Assignment := fun identity =>
  (if identity = 0 then value 0 else value 1,Common.rowEmpty)
abbrev context : GeneralNominalCandidates.Context := ⟨state,GeneralNominalExamples.interpretation⟩

theorem record_equation : Equivalent (value 0) (required 7 (value 0)) := by
  have equation := CommonNominalFullGuardedClosure.all_parameter_sound body Fin.elim0 (0 : Fin 2)
  simpa [CommonNominalFullGuardedClosure.equation,CommonNominalFullGuardedClosure.valueReference,
    CommonNominalSyntax.Layer.map,body,required,record] using equation

theorem list_equation : Equivalent (value 1) (nominal 0 [.inl (value 0)]) := by
  have equation := CommonNominalFullGuardedClosure.all_parameter_sound body Fin.elim0 (1 : Fin 2)
  simpa [CommonNominalFullGuardedClosure.equation,CommonNominalFullGuardedClosure.valueReference,
    CommonNominalSyntax.Layer.map,body,nominal] using equation

theorem state_models : GeneralNominalState.Models state model := by
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro atom member
    change atom ∈ equationAtoms (0 : Fin 2) (.required 7 (.var 0)) at member
    simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact record_equation.1
    · exact record_equation.2
  · intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have same : (.required 7 (.var 0) : TyTerm (Fin 2)) = term := by
        simpa [heads,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term] using recorded
      subst term; exact record_equation
    · simp [heads,zero,GeneralSourceState.Head.equation] at recorded
  · intro pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact subtype_refl _
  · intro slot d recorded
    by_cases one : slot = 1
    · subst slot
      have same := Option.some.inj recorded; subst d
      exact ⟨[.inl (value 0)],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,list_equation⟩
    · simp [state,one] at recorded

private theorem distinct_heads : ¬ Equivalent (value 0) (value 1) := by
  intro equal
  have below : Subtype (required 7 (value 0)) (nominal 0 [.inl (value 0)]) :=
    subtype_trans record_equation.2 (subtype_trans equal.1 list_equation.1)
  have probe := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead 0 1) (by exact ⟨rfl,rfl⟩)
  exact probe

theorem edge_target_zero (first last : Fin 2) (edge : GeneralNominalCycleK2.Edge state first last) : last = 0 := by
  rcases edge with structural | argument
  · obtain ⟨kind,children,head,index,equal⟩ := structural
    by_cases zero : first = 0
    · subst first
      have same := GeneralNormalizedObservation.Head.structural.inj head
      have targets : children = (fun _ => (0 : Fin 2)) := by cases same.1; exact eq_of_heq same.2.symm
      rw [targets] at equal; exact equal.symm
    · simp [view,zero] at head
  · obtain ⟨d,recorded,index,observes⟩ := argument
    have one : first = 1 := by
      by_cases same : first = 1
      · exact same
      · simp [state,same] at recorded
    subst first
    have same := Option.some.inj recorded; subst d
    obtain ⟨actual,seen,equal⟩ := observes model state_models
    cases seen with
    | argument source nominal found =>
      cases source
      have invariant := (nominal_regular_invariant_exact _ _ _ _).mp
        (subtype_trans list_equation.2 nominal.1)
      have size := invariant.2.1
      have indexZero : index = 0 := by
        obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
        simp only [List.length_cons,List.length_nil] at size
        omega
      subst index
      have actualEq := invariant.2.2 0 (.inl (value 0)) (.inl actual) rfl found
      by_cases zero : last = 0
      · exact zero
      · have lastOne : last = 1 := by apply Fin.ext; have h := last.isLt; have hn : last.val ≠ 0 := fun e => zero (Fin.ext e); omega
        subst last
        exact False.elim (distinct_heads ⟨subtype_trans actualEq.1 equal.1,subtype_trans equal.2 actualEq.2⟩)

theorem list_off_cycle : ¬ GeneralNominalCycleK2.Cycle state 1 := by
  rintro ⟨child,edge,path⟩
  have target := edge_target_zero 1 child edge; subst child
  have zero : ∀ (a b : Fin state.base.slots), GeneralNominalMixedRecurrence.Path state a b → a = 0 → b = 0 := by
    intro a b path
    induction path with
    | nil => exact id
    | cons edge path ih => exact fun _ => ih (edge_target_zero _ _ edge)
  have impossible := zero 0 1 path rfl
  contradiction

end Yulang.GeneralNominalCycleWrapper
