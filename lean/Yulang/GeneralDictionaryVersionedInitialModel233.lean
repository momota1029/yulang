import Yulang.GeneralDictionaryVersionedGuarded232
import Yulang.GeneralNominalVersionedCache232
import Yulang.GeneralDictionaryDefaultPacketSupport213
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! First versioned installation model over the actual original source.
Only fresh aggregate names are changed; legacy packet support and all source
names remain intact. No old operational prefix is used. -/
namespace Yulang.GeneralDictionaryVersionedInitialModel233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229
open GeneralNominalCenters
open GeneralNominalAggregateVersion231
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)

abbrev bindings := GeneralDictionaryVersionedNames231.oldBindings
abbrev names (index : Fin 2) := slot snapshot.seed root.identity declaration.id index.val 0 bindings
abbrev values (index : Fin 2) : Ty := if index.val = 0 then GeneralDictionaryOptionalOutput229.value else .emptyRecord
noncomputable def extended : Assignment := GeneralNominalCenteredModelExtension.assign model names values
abbrev pool := [0,1,2,3,4,lo,hi,actual]

theorem fresh_outside (index : Fin 2) : names index ∉ pool := by
  intro present
  have high : 4 < names index := above_seed _ _ _ _ _ _
  have separate (purpose : Nat) : names index ≠ fresh snapshot.seed root.identity declaration.id purpose 0 0 :=
    not_legacy_slot _ _ _ _ _ _ _ _ _ _
  simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with h | h | h | h | h | h | h | h
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact separate 0 h
  · exact separate 1 h
  · exact separate 8 h

theorem fresh_value (index : Fin 2) : (extended (names index)).1 = values index := by
  apply GeneralNominalCenteredModelExtension.assign_value
  intro first last equal
  have same : first.val = last.val := by
    exact Classical.byContradiction (fun different => distinct_purpose _ _ _ _ _ _ bindings bindings different equal)
  exact congrArg values (Fin.ext same)

theorem old_value (name : Nat) (present : name ∈ pool) : extended name = model name :=
  GeneralNominalCenteredModelExtension.assign_outside model names values
    (fun index same => fresh_outside index (same ▸ present))

theorem packet_support : GeneralDictionaryDefaultPacketSupport213.packetSources plan ⊆ pool := by decide +kernel

theorem old_packet : GeneralNominalCenteredHeadMatStepPackets.Holds plan extended :=
  (GeneralDictionaryDefaultPacketSupport213.packet_iff plan
    (fun name member => (old_value name (packet_support member)).symm)).mp packet_holds

theorem source_model : GeneralNominalState.Models snapshot extended := old_packet.1

theorem initial_model : GeneralNominalVersionedJournal232.Models
    (GeneralNominalVersionedJournal232.initial context root) extended :=
  (GeneralNominalVersionedJournal232.initial_models context root extended).mpr
    ⟨source_model,GeneralNominalCenters.point_root_holds _ _ root_point _⟩

theorem new_merges : PresenceNormalForm.All CommonNominalFullCarrier.model extended
    (GeneralNominalVersionedAllocation231.merges snapshot registry root.identity declaration packet.bindings) := by
  rw [bindings_exact]
  have pair : PresenceNormalForm.All CommonNominalFullCarrier.model extended
      (GeneralNominalAllocation.equations (names 0) (.union (.var 4) (.var 4)) ++
        GeneralNominalAllocation.equations (names 1) (.inter (.var 2) (.var 2))) := by
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact]
    change Equivalent (extended (names 0)).1 (.union (extended 4).1 (extended 4).1) ∧
      Equivalent (extended (names 1)).1 (.inter (extended 2).1 (extended 2).1)
    rw [fresh_value 0,fresh_value 1,old_value 4 (by simp [pool]),old_value 2 (by simp [pool])]
    change Equivalent GeneralDictionaryOptionalOutput229.value
      (.union GeneralDictionaryOptionalOutput229.value GeneralDictionaryOptionalOutput229.value) ∧
      Equivalent emptyRecord (.inter emptyRecord emptyRecord)
    exact ⟨⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
      (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩,
      ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
      (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩⟩
  change PresenceNormalForm.All CommonNominalFullCarrier.model extended (_ ++ _)
  exact (PresenceNormalForm.all_append ..).mpr ⟨pair,pair⟩

end Yulang.GeneralDictionaryVersionedInitialModel233
