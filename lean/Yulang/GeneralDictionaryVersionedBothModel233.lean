import Yulang.GeneralDictionaryVersionedInitialModel233
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryVersionedBothModel233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229
open GeneralNominalCenters GeneralNominalAggregateVersion231
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
abbrev bindings := GeneralDictionaryVersionedInitialModel233.bindings
abbrev names := GeneralDictionaryVersionedInitialModel233.names
abbrev values := GeneralDictionaryVersionedInitialModel233.values
abbrev pool := GeneralDictionaryVersionedInitialModel233.pool
abbrev nextNames := GeneralDictionaryVersionedNames231.names
noncomputable def extended : Assignment := GeneralNominalCenteredModelExtension.assign
  GeneralDictionaryVersionedInitialModel233.extended nextNames (fun _ => .emptyRecord)

theorem versions_distinct (first last : Fin 2) : nextNames first ≠ names last := by
  by_cases same : first.val = last.val
  · have equal : first = last := Fin.ext same
    subst last
    exact Ne.symm (GeneralDictionaryVersionedNames231.version_changed first.val)
  · exact distinct_purpose _ _ _ _ _ _ _ _ same

theorem fresh_value (index : Fin 2) : (extended (names index)).1 = values index := by
  rw [show extended (names index) = GeneralDictionaryVersionedInitialModel233.extended (names index) from
    GeneralNominalCenteredModelExtension.assign_outside _ _ _ (fun other => versions_distinct other index)]
  exact GeneralDictionaryVersionedInitialModel233.fresh_value index

theorem next_value (index : Fin 2) : (extended (nextNames index)).1 = .emptyRecord :=
  GeneralNominalCenteredModelExtension.assign_value _ _ _ (by intro _ _ _; rfl) index

theorem old_value (name : Nat) (present : name ∈ pool) : extended name = model name := by
  rw [show extended name = GeneralDictionaryVersionedInitialModel233.extended name from
    GeneralNominalCenteredModelExtension.assign_outside _ _ _ (fun index same =>
      GeneralDictionaryVersionedNames231.fresh_outside index.val (by
        change GeneralDictionaryVersionedNames231.freshName index.val = name at same
        rw [same]
        simpa only [pool,GeneralDictionaryVersionedInitialModel233.pool,GeneralDictionaryVersionedSupport231.pool] using present))]
  exact GeneralDictionaryVersionedInitialModel233.old_value name present

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

end Yulang.GeneralDictionaryVersionedBothModel233
