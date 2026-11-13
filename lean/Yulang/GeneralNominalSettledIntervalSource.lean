import Yulang.GeneralNominalSettledIntervalDeclarations
import Yulang.GeneralNominalSettledSteps

/-! A finite source with a strict structural interval. The two unused slots
also permit a separate leaf-output request on this same source carrier. -/
namespace Yulang.GeneralNominalSettledIntervalSource
open GeneralNominalSettledIntervalDeclarations
open GeneralSourceDictionaries GeneralDeclarations GeneralNominalSaturationState
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier

abbrev equations : List (PresenceNormalForm.Atom (Fin 9)) :=
  GeneralSourceState.equationAtoms 0 (.variant 0 (.var 1)) ++
  GeneralSourceState.equationAtoms 1 (.variant 0 (.var 2)) ++
  GeneralSourceState.equationAtoms 3 (.variant 0 (.var 4)) ++
  GeneralSourceState.equationAtoms 5 (.variant 0 (.var 6)) ++
  GeneralSourceState.equationAtoms 4 .bottom ++
  GeneralSourceState.equationAtoms 6 .top ++ [.tyLe (.var 3) (.var 5)]

abbrev base : GeneralSourceState.State where
  slots := 9
  source := Fin.val
  source_injective := fun _ _ equal => Fin.ext equal
  rowSource := Fin.val
  ordinary := equations
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := fun _ => .unresolved
  intervals := []
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev views (slot : Fin 9) : GeneralNormalizedObservation.Head (fun _ : Fin 1 => .variant 0) 9 :=
  if slot = 0 then .structural 0 (fun _ => 1)
  else if slot = 1 then .structural 0 (fun _ => 2)
  else if slot = 3 then .structural 0 (fun _ => 4)
  else if slot = 5 then .structural 0 (fun _ => 6)
  else .deferred .unresolved

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 1
  shapes := fun _ => .variant 0
  shapes_injective := fun a b _ => Subsingleton.elim a b
  canonical := by intro _; trivial
  heads := views
  checked := by
    intro slot term seen
    unfold views at seen
    repeat first
      | split at seen
      | (rename_i same; subst slot; cases Option.some.inj seen
         exact .ordinary (by simp [base,equations,GeneralSourceState.equationAtoms,GeneralNormalizedObservation.Shape.term])
           (by simp [base,equations,GeneralSourceState.equationAtoms,GeneralNormalizedObservation.Shape.term]))
      | cases seen

abbrev source : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun _ => none
  catalogue := by intro _ _ impossible; cases impossible
  bodies_opaque := by intro _ _ impossible; cases impossible
  seed := 8

abbrev interpretation : GeneralNominalInspection.Interpretation :=
  ⟨fun _ => none,fun _ => false,by intro _ impossible; cases impossible⟩
abbrev context : GeneralNominalCandidates.Context := ⟨source,interpretation⟩
abbrev root : Occurrence roles :=
  ⟨9,⟨0,fun index => if index.val = 0 then (0,0) else (3,5),[],by intro _ impossible; cases impossible⟩⟩
abbrev start := GeneralNominalSupport.initial context root
abbrev V (a : Ty) := variant 0 a

def model (a z u : Ty) : GeneralNominalCommonBridge.Assignment := fun identity =>
  (match identity with
   | 0 => V (V a) | 1 => V a | 2 => a
   | 3 => V .bottom | 4 => .bottom | 5 => V .top | 6 => .top
   | 7 => z | 8 => u | _ => .base .int,Common.rowEmpty)

theorem interval_order : Subtype (V .bottom) (V .top) :=
  (CommonNominalFullModelMap.subtype_exact (Common.variant 0 .bottom) (Common.variant 0 .top)).mpr
    ((Common.common_variant_iff 0 _ _).mpr (CommonBoundCoalescing.bottom_le _))

theorem source_models (a z u : Ty) : GeneralNominalState.Models source (model a z u) := by
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro atom member
    simp only [base,equations,GeneralSourceState.equationAtoms,
      List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact subtype_refl _ | exact interval_order
  · intro _ _ impossible; cases impossible
  · intro _ impossible; cases impossible
  · intro _ _ impossible; cases impossible

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
  have member (slot : Fin 9) : slot.val ∈ GeneralNominalState.sources source :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))
  refine ⟨rfl,⟨rfl,by intro _ _ impossible; cases impossible⟩,?_,?_,?_,rfl⟩
  · constructor
    · intro index
      change (if index.val = 0 then (0,0) else (3,5)).1 ∈ _ ∧
        (if index.val = 0 then (0,0) else (3,5)).2 ∈ _
      split
      · exact ⟨member 0,member 0⟩
      · exact ⟨member 3,member 5⟩
    · intro _ impossible; cases impossible
  · intro assignment valid index
    change Subtype (assignment (if index.val = 0 then (0,0) else (3,5)).1).1
      (assignment (if index.val = 0 then (0,0) else (3,5)).2).1
    split
    · exact subtype_refl _
    · exact valid.1.1 (.tyLe (.var 3) (.var 5)) (by simp [base,equations])
  · intro identity present
    change identity ≤ 8
    simp only [GeneralNominalState.sources,source,List.mem_append,List.not_mem_nil,List.flatMap_nil,or_false] at present
    rcases present with first | last
    all_goals obtain ⟨slot,equal⟩ := List.mem_ofFn.mp ‹_›
    all_goals have bound := slot.isLt
    all_goals change slot.val < 9 at bound
    all_goals change slot.val = identity at equal
    all_goals omega

theorem formed : GeneralNominalSettledSteps.SourceFormed registry root start :=
  .initial context initial_source

theorem initial_models (a z u : Ty) : Models start.current (model a z u) :=
  (GeneralNominalSaturationState.initial_models ..).mpr (source_models a z u)

end Yulang.GeneralNominalSettledIntervalSource
