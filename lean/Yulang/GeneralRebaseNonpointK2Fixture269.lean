import Yulang.GeneralRebaseRawBoundedK2269
import Yulang.GeneralNominalProgressObstruction

namespace Yulang.GeneralRebaseNonpointK2Fixture269
open CommonNominalFullCarrier
open GeneralDeclarationExamples (constructors)
open GeneralNominalProgressObstruction (model value equation)

abbrev base : GeneralSourceState.State where
 slots := 2
 source := Fin.val
 source_injective := fun _ _ h => Fin.ext h
 rowSource := Fin.val
 ordinary := [.tyLe (.var 0) (.var 1),.tyLe (.var 1) (.var 0)]
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 heads := fun _ => .unresolved
 intervals := []
 heads_sound := by intro _ _ _ _ known; cases known
 intervals_sound := by intro _ _ _ listed; cases listed

abbrev snapshot : GeneralNormalizedObservation.Snapshot base where
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := by intro i; exact Fin.elim0 i
 canonical := by intro i; exact Fin.elim0 i
 heads := fun _ => .deferred .unresolved
 checked := by intro _ _ known; cases known

abbrev descriptor : GeneralNominalState.Descriptor 2 :=
 ⟨0,⟨[.type],0⟩,[.type (0,1)],rfl⟩

abbrev source : GeneralNominalState.State where
 base := base
 view := snapshot
 constructors := constructors
 nominals := fun _ => some descriptor
 catalogue := by intro _ d known; cases Option.some.inj known; rfl
 bodies_opaque := by intros; rfl

theorem witnessed : GeneralNominalState.Models source model := by
 refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
 · intro atom listed
   change atom ∈ ([.tyLe (.var 0) (.var 1),.tyLe (.var 1) (.var 0)] : List (PresenceNormalForm.Atom (Fin 2))) at listed
   simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
   rcases listed with rfl | rfl <;> exact subtype_refl _
 · intro _ _ known; cases known
 · intro _ listed; cases listed
 · intro _ d known
   cases Option.some.inj known
   exact ⟨[.inl value],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,equation⟩

theorem no_direct : GeneralRebaseDirectCycles268.cycle source 0 = false := by decide +kernel

theorem independent_oneway :
 GeneralRebaseSlotInequalities269.prove source 1 0 = true := by decide +kernel

theorem computed_nominal :
 GeneralRebaseRawBoundedK2269.nominal source (fun _ _ => none) 0 0 = some true := by decide +kernel

theorem computed_recurs :
 GeneralRebaseRawBoundedK2269.recurs source (fun _ _ => none) (some true) 0 = some true := by decide +kernel

/-- The old K2 predicate accepts this non-point actual argument cycle.
The finite calculation did not use the direct graph or any preassigned
edge answer. This is a checked source snapshot, not a reachable program. -/
theorem true_nondirect : GeneralNominalCycleK2.RecursAt source 0 ∧
 ¬ GeneralNominalCycleK2.DirectCycle source 0 := by
 have yes := GeneralRebaseRawBoundedK2269.recurs_sound source (fun _ _ => none) (fun _ _ => True.intro)
   (some true) ⟨model,witnessed⟩ 0
 rw [computed_recurs] at yes
 exact ⟨yes,fun direct => Bool.noConfusion
   (no_direct.symm.trans ((GeneralRebaseDirectCycles268.cycle_exact ..).mpr direct))⟩

end Yulang.GeneralRebaseNonpointK2Fixture269
