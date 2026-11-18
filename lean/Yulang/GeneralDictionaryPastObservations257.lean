import Yulang.GeneralDictionaryPastRaw257
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryPastObservations257
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryLooseIterationBook240 (context packet)
open GeneralDictionaryLooseFamilyNames240 (lower)
open GeneralDictionaryLooseLoopSource240 (F P)
open GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

theorem observed (assignment : Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot assignment)
 (index : Nat) (small : index < 2) : Observes assignment (.nominal (.source 3) 5 index) F := by
 have root := GeneralDictionaryLooseLoopInitial240.root_fixed assignment source
 apply Observes.nominal (.source 3) root
 have cases : index=0 ∨ index=1 := by omega
 rcases cases with rfl | rfl <;> rfl

theorem observed_value (assignment : Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot assignment)
 (index : Nat) (small : index < 2) (value : Ty)
 (seen : Observes assignment (.nominal (.source 3) 5 index) value) : Equivalent value F :=
 nominal_observation_unique assignment (.argument (.source 3) 5 index) value F seen
   (observed assignment source index small)

theorem endpoint_fit (n index : Nat) (before : index ≤ n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) (value : Ty)
 (same : Equivalent value F) : GeneralNominalCaptureMerges.Fits assignment (lower index,4) value := by
 have source := GeneralDictionaryHistoricalValues257.raw_initial n assignment valid
 have lo := GeneralDictionaryHistoricalValues257.lower_same n index before assignment valid
 have two := GeneralDictionaryLooseLoopInitial240.foo_fixed assignment source
 have four := GeneralDictionaryLooseLoopInitial240.foo4_fixed assignment source
 exact ⟨subtype_trans lo.1 (subtype_trans two.1 same.2),subtype_trans same.1 four.2⟩

theorem projection (n index : Nat) (before : index ≤ n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment) :
 ProjectionModels (context index).state (GeneralNominalPacketSupport.report (packet index)) assignment := by
 have source := GeneralDictionaryHistoricalValues257.raw_initial n assignment valid
 rw [show GeneralNominalPacketSupport.report (packet index) =
   GeneralDictionaryLooseFamilyPacket240.calculated index
     (GeneralDictionaryLooseIterationBook240.allocations index)
     (GeneralDictionaryLooseIterationBook240.reservations index)
     (GeneralDictionaryLooseIterationBook240.atoms index) from GeneralDictionaryLooseFamilyPacket240.report_exact ..]
 have fit (i : Nat) (small : i < 2) (value : Ty)
   (seen : Observes assignment (.nominal (.source 3) 5 i) value) :
   Fits (context index).state assignment (GeneralDictionaryLooseFamilyBase240.anchor index,GeneralDictionaryLooseFamilyBase240.original index 4) value := by
   change GeneralNominalCaptureMerges.Fits assignment
     (GeneralDictionaryLooseFamilyBase240.source index (GeneralDictionaryLooseFamilyBase240.anchor index),
      GeneralDictionaryLooseFamilyBase240.source index (GeneralDictionaryLooseFamilyBase240.original index 4)) value
   rw [GeneralDictionaryLooseFamilyBase240.source_anchor,GeneralDictionaryLooseFamilyBase240.source_original]
   exact endpoint_fit n index before assignment valid value (observed_value assignment source i small value seen)
 refine ⟨?_,?_,?_,?_⟩
 · intro anchor member
   rcases List.mem_cons.mp member with rfl | member
   · exact ⟨⟨F,observed assignment source 0 (by decide)⟩,fun value seen => fit 0 (by decide) value seen⟩
   · cases List.mem_singleton.mp member
     exact ⟨⟨F,observed assignment source 1 (by decide)⟩,fun value seen => fit 1 (by decide) value seen⟩
 · intro test member; cases member
 · intro first one last two _ origin located value seen
   rcases List.mem_cons.mp one with rfl | one
   all_goals first | cases List.mem_singleton.mp one | skip
   all_goals cases Option.some.inj located
   all_goals rcases List.mem_cons.mp two with rfl | two
   all_goals first | cases List.mem_singleton.mp two | skip
   all_goals first | exact fit 0 (by decide) value seen | exact fit 1 (by decide) value seen
 · intro first one last two _ a b firstOrigin lastOrigin x y seenX seenY
   rcases List.mem_cons.mp one with rfl | one
   all_goals first | cases List.mem_singleton.mp one | skip
   all_goals cases Option.some.inj firstOrigin
   all_goals rcases List.mem_cons.mp two with rfl | two
   all_goals first | cases List.mem_singleton.mp two | skip
   all_goals cases Option.some.inj lastOrigin
   all_goals
     have ex : Equivalent x F := by first | exact observed_value assignment source 0 (by decide) x seenX | exact observed_value assignment source 1 (by decide) x seenX
     have ey : Equivalent y F := by first | exact observed_value assignment source 0 (by decide) y seenY | exact observed_value assignment source 1 (by decide) y seenY
     exact ⟨subtype_trans ex.1 ey.2,subtype_trans ey.1 ex.2⟩
end Yulang.GeneralDictionaryPastObservations257
