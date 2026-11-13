import Yulang.GeneralDictionaryMixedCapturedReplay
import Yulang.GeneralDictionaryReservedNominalRefresh

/-! An actual carrier extension exposes the closed output of the mixed packet. -/
namespace Yulang.GeneralDictionaryMixedCarrierRefresh
open GeneralDictionaryMixedCatalogExample
open GeneralDictionaryMixedCatalogReachable (installed reachable installed_model recorded)
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalExamples (interpretation displayRoot model)
open GeneralNominalSaturationState CommonNominalFullCarrier
open Core.PresenceGeneration (TyTerm)
open GeneralSourceState (equationAtoms)
abbrev embed : Fin 2 → Fin 3 := fun i => ⟨i.val,by omega⟩
private theorem cases2 (i : Fin 2) : i = 0 ∨ i = 1 := by
  have := i.isLt
  apply Or.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  omega
private theorem cases3 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by have := i.isLt; omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))
theorem target_fresh : 1 < target 10 := by
  have h := GeneralNominalIdentities.source_above_invocation (GeneralNominalExamples.state true).seed
    (GeneralNominalAllocation.origin 100 1 5 30 0)
  change 100 < target 10 at h
  omega
abbrev source : Fin 3 → Nat := fun i => if i = 2 then target 10 else i.val
abbrev rowSource : Fin 3 → Nat := fun i => if i = 2 then 0 else i.val
abbrev heads : Fin 3 → GeneralSourceState.Head
    (fun i : Fin 0 => Fin.elim0 i : Fin 0 → GeneralSourceState.Shape 3) :=
  fun i => if i = 0 then .unresolved else .scalar .int
abbrev base : GeneralSourceState.State where
  slots := 3
  source := source
  source_injective := by
    intro a b same
    rcases cases3 a with rfl | rfl | rfl <;> rcases cases3 b with rfl | rfl | rfl
    all_goals simp [source] at same ⊢
    all_goals have := target_fresh; omega
  rowSource := rowSource
  ordinary := equationAtoms 1 (.base .int) ++ equationAtoms 2 (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := heads
  intervals := [(0,0),(1,1)]
  heads_sound := by
    intro m valid slot term recorded
    rcases cases3 slot with rfl | rfl | rfl
    · cases recorded
    · cases Option.some.inj recorded
      exact (GeneralSourceState.equationAtoms_exact ..).mp (by rw [PresenceNormalForm.all_append] at valid; exact valid.1)
    · cases Option.some.inj recorded
      exact (GeneralSourceState.equationAtoms_exact ..).mp (by rw [PresenceNormalForm.all_append] at valid; exact valid.2)
  intervals_sound := by
    intro m _ pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact Common.subtype_refl _
abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun i => if i = 0 then .deferred .unresolved else .scalar .int
  checked := by
    intro slot term recorded
    rcases cases3 slot with rfl | rfl | rfl
    · cases recorded
    · cases Option.some.inj recorded; exact .head rfl
    · cases Option.some.inj recorded; exact .head rfl
abbrev descriptor : GeneralNominalState.Descriptor 3 := ⟨0,⟨[.type],0⟩,[.type (1,1)],rfl⟩
noncomputable abbrev snapshot : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun i => if i = 0 then some descriptor else none
  catalogue := by
    intro i d known
    split at known
    · cases Option.some.inj known; rfl
    · cases known
  bodies_opaque := by
    intro i d known
    by_cases zero : i = 0
    · subst i; rfl
    · simp [zero] at known
  seed := installed.current.context.state.seed
  allocated := installed.current.context.state.allocated
  reserved := installed.current.context.state.reserved
  ordinary := installed.current.context.state.ordinary
noncomputable abbrev refreshedContext : GeneralNominalCandidates.Context := ⟨snapshot,interpretation⟩
noncomputable abbrev refreshed : GeneralNominalSupport.Tracked roles :=
  { installed with current := regenerate installed.current refreshedContext }

noncomputable def refines : GeneralNominalRefinements.Refines installed.current.context.state snapshot := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · refine ⟨embed,?_,?_,?_,?_,?_⟩
    · intro i; rcases cases2 i with rfl | rfl <;> rfl
    · intro i; rcases cases2 i with rfl | rfl <;> rfl
    · intro atom member
      change atom ∈ equationAtoms (1 : Fin 2) (.base .int) at member
      apply List.mem_append_left
      rcases List.mem_cons.mp member with eq | member
      · rw [eq]; exact List.mem_cons_self ..
      · rw [List.mem_singleton.mp member]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · intro i known
      rcases cases2 i with rfl | rfl
      · exact False.elim (known rfl)
      · decide +kernel
    · intro pair member
      change pair ∈ ([(0,0),(1,1)] : List (Fin 2 × Fin 2)) at member
      rcases List.mem_cons.mp member with eq | member
      · rw [eq]; exact List.mem_cons_self ..
      · rw [List.mem_singleton.mp member]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · intro i term recorded
    rcases cases2 i with rfl | rfl
    · cases recorded
    · cases Option.some.inj recorded; exact .head rfl
  · intro i d recorded
    rcases cases2 i with rfl | rfl
    · cases Option.some.inj recorded; rfl
    · cases recorded
  · intro atom member; exact member
  · rintro id ⟨i,same,known⟩
    refine ⟨embed i,?_,?_⟩
    · rcases cases2 i with rfl | rfl <;> exact same
    · rcases cases2 i with rfl | rfl
      · exact Or.inr ⟨descriptor,rfl⟩
      · exact Or.inl (by decide +kernel)
  · intro id member; exact member
  · intro id member; exact member

theorem output_int (m : GeneralNominalCommonBridge.Assignment) (valid : Models installed.current m) :
    Equivalent (m (target 10)).1 (.base .int) := by
  have out := (valid.2.1 packet recorded).2.2
  change GeneralNominalMaterialization.Models _ declaration _ _ (GeneralNominalPacketSupport.namedSchema packet) m at out
  rw [generated_exact] at out
  exact (out.1 _ List.mem_cons_self).2 _ (.source _)

theorem snapshot_models (m : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current m) : GeneralNominalState.Models snapshot m := by
  have scalar := valid.1.1.2.1 (1 : Fin 2) (.base .int) rfl
  have output := output_int m valid
  refine ⟨⟨?_,?_,?_⟩,?_,valid.1.2.2⟩
  · rw [PresenceNormalForm.all_append]
    constructor
    · intro atom member
      rcases List.mem_cons.mp member with eq | member
      · rw [eq]; exact scalar.1
      · rw [List.mem_singleton.mp member]; exact scalar.2
    · intro atom member
      rcases List.mem_cons.mp member with eq | member
      · rw [eq]; exact output.1
      · rw [List.mem_singleton.mp member]; exact output.2
  · intro slot term recorded
    rcases cases3 slot with rfl | rfl | rfl
    · cases recorded
    · cases Option.some.inj recorded; exact scalar
    · cases Option.some.inj recorded; exact output
  · intro pair member
    rcases List.mem_cons.mp member with eq | member
    · rw [eq]; exact subtype_refl _
    · rw [List.mem_singleton.mp member]; exact subtype_refl _
  · intro slot d recorded
    rcases cases3 slot with rfl | rfl | rfl
    · cases Option.some.inj recorded
      obtain ⟨args,fits,equal⟩ := valid.1.2.1 (0 : Fin 2) GeneralNominalExamples.listDescriptor rfl
      refine ⟨args,?_,equal⟩
      change GeneralNominalState.FitsAll installed.current.context.state.base m [.type ((1 : Fin 2),(1 : Fin 2))] args at fits
      cases fits with
      | cons fit tail =>
        cases tail
        rename_i value
        cases value with
        | inl ty => exact .cons fit .nil
        | inr row => exact False.elim fit
    · cases recorded
    · cases recorded

theorem target_reserved : target 10 ∈ installed.current.context.state.reserved := by
  change target 10 ∈ [] ++ GeneralNominalAllocation.reserved (GeneralNominalExamples.state true) registry 100 ++ []
  simp only [List.nil_append,List.append_nil]
  apply List.mem_map.mpr
  refine ⟨GeneralNominalAllocation.origin 100 1 5 30 0,?_,rfl⟩
  simp [GeneralNominalAllocation.keys,GeneralNominalAllocation.declarationKeys,
    declaration,firstClause,secondClause,GeneralDeclarations.Declaration.inputNames,
    GeneralDeclarations.Declaration.outputNames]

theorem output_member : target 10 ∈ GeneralNominalState.sources installed.current.context.state :=
  List.mem_append_left _ (List.mem_append_right _ target_reserved)

noncomputable def certificate : GeneralNominalCycleSteps.Refresh installed.current refreshedContext where
  refines := refines
  interpretation := rfl
  exact := snapshot_models
  support := by
    intro id member
    simp only [GeneralNominalState.sources,List.mem_append] at member ⊢
    rcases member with ((type | row) | reserved) | ordinary
    · obtain ⟨slot,same⟩ := List.mem_ofFn.mp type
      rcases cases3 slot with rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(0 : Fin 2),same⟩)))
      · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(1 : Fin 2),same⟩)))
      · subst id; exact Or.inl (Or.inr target_reserved)
    · obtain ⟨slot,same⟩ := List.mem_ofFn.mp row
      rcases cases3 slot with rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨(0 : Fin 2),same⟩)))
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨(1 : Fin 2),same⟩)))
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨(0 : Fin 2),same⟩)))
    · exact Or.inl (Or.inr reserved)
    · exact Or.inr ordinary

theorem output_not_known : ¬ GeneralNominalState.Known installed.current.context.state (target 10) := by
  rintro ⟨slot,equal,_⟩
  have bound := slot.isLt
  change slot.val = target 10 at equal
  change slot.val < 2 at bound
  have := target_fresh
  omega

theorem output_known : GeneralNominalState.Known snapshot (target 10) :=
  ⟨(2 : Fin 3),rfl,Or.inl (by decide +kernel)⟩

theorem refresh_step : GeneralNominalValueSteps.Step registry displayRoot installed refreshed :=
  ⟨displayRoot,.root,.administrative displayRoot _ (.refresh displayRoot refreshedContext certificate
    (target 10) output_member output_not_known output_known)⟩

theorem refreshed_models (m : GeneralNominalCommonBridge.Assignment) :
    Models refreshed.current m ↔ Models installed.current m := GeneralNominalCycleSteps.refresh_models certificate m

theorem refreshed_reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles)
    registry displayRoot refreshed := by
  obtain ⟨start,initial,path⟩ := reachable
  exact ⟨start,initial,.tail path refresh_step⟩

theorem refreshed_inhabited : Models refreshed.current model := (refreshed_models model).mpr installed_model

noncomputable abbrev currentReport := GeneralNominalRecursiveCandidates.report refreshedContext declaration [(0,0)]
noncomputable abbrev currentCapture := GeneralNominalAllocation.capture snapshot registry displayRoot.identity declaration.id
  (GeneralNominalRecursiveInspection.bindings snapshot currentReport)

theorem report_current : currentReport = GeneralNominalUnaryCaptureFacts.captured snapshot 0 0 0 (1,1) :=
  GeneralNominalUnaryCaptureFacts.report_exact refreshedContext declaration 0 descriptor rfl 0 (1,1) rfl
    GeneralDictionaryMixedCatalogInhabited.query

theorem bindings_exact : GeneralNominalRecursiveInspection.bindings snapshot currentReport = packet.bindings := by
  unfold GeneralNominalSaturationState.Packet.bindings
  rw [report_current,GeneralNominalUnaryCaptureFacts.report_exact (GeneralNominalExamples.context true)
    declaration 0 GeneralNominalExamples.listDescriptor rfl 0 (1,1) rfl GeneralDictionaryMixedCatalogInhabited.query]
  rfl

theorem origins : GeneralDictionaryBindingSchemaReplay.Origins packet currentReport := by
  intro entry member captured present same actual origin known
  rw [report_current] at present
  have eq := List.mem_singleton.mp present
  subst captured
  rw [GeneralDictionaryMixedCapturedReplay.report_old]
  exact ⟨_,List.mem_cons_self,rfl,known⟩

theorem packet_recorded : packet ∈ refreshed.current.packets := recorded

theorem replay (m : GeneralNominalCommonBridge.Assignment) (valid : Models refreshed.current m) :
    GeneralNominalMaterialization.Models snapshot declaration currentCapture currentReport
      (GeneralNominalRecursiveCandidates.generated registry refreshedContext displayRoot declaration checked [(0,0)]) m :=
  GeneralDictionaryBindingSchemaReplay.replay registry displayRoot refreshed refreshed_reachable packet packet_recorded
    [((0 : Fin 3),(0 : Fin 3))] bindings_exact origins m valid

theorem carrier_changed : installed.current.context.state.base.slots = 2 ∧ snapshot.base.slots = 3 := ⟨rfl,rfl⟩

theorem nonvacuous_replay : Models refreshed.current model ∧
    (GeneralNominalPacketSupport.namedSchema packet).variables ≠ [] ∧
    GeneralNominalMaterialization.Models snapshot declaration currentCapture currentReport
      (GeneralNominalRecursiveCandidates.generated registry refreshedContext displayRoot declaration checked [(0,0)]) model :=
  ⟨refreshed_inhabited,mixed,replay model refreshed_inhabited⟩
end Yulang.GeneralDictionaryMixedCarrierRefresh
