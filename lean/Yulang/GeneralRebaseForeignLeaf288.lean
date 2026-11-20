import Yulang.GeneralRebaseRowLedgerNames288

/-! Closed counterexample to a shortcut on arbitrary ledgers: adding a
foreign plan that is valid under every full model can manufacture
settlement of an actually pending child. No rule of the actual kernel
is replaced or asserted to reach this malformed data. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28600
set_option maxHeartbeats 18000000
namespace Yulang.GeneralRebaseForeignLeaf288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (plan child sole_child)
open GeneralRebaseRowParentFrame287 (after after_model)
open GeneralRebaseRowLeafSlice288 (prior finalFacts prior_trusted class_readback same_models)
open GeneralRebaseRowLeafWitness288 (no_leaf source_exact)
open GeneralRebaseLeafLedger288 (record growth)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedSupport233 (Discharged Trusted PacketSettled)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralNominalVersionedEvidence231 (Evidence Frame)

noncomputable abbrev foreignPlan := GeneralRebaseRowWholeChild287.plan
noncomputable abbrev unscoped : State roles := record (after false) foreignPlan

theorem same_occurrence : child true = child false := rfl

theorem foreign_holds_on_source (m : Assignment)
    (src : GeneralRebaseInertLeaf288.SourceSlice (after false) m) :
    GeneralNominalVersionedPlans231.Holds foreignPlan m :=
  GeneralRebaseRowLeafWitness288.leaf.sourcePacket m ((source_exact true m).mpr ((source_exact false m).mp src))

theorem models_eq (m : Assignment) : Models unscoped m ↔ Models (after false) m := by
  constructor
  · intro valid
    exact ⟨valid.1,fun p present => valid.2.1 p (List.mem_cons_of_mem _ present),valid.2.2⟩
  · intro valid
    refine ⟨valid.1,?_,valid.2.2⟩
    intro p present
    rcases List.mem_cons.mp present with rfl | other
    · exact foreign_holds_on_source m (GeneralNominalVersionedSupport233.trusted_models .source valid)
    · exact valid.2.1 p other

theorem syntactically_discharged : Discharged unscoped (child false) := by
  rw [← same_occurrence]
  change Discharged unscoped foreignPlan.packet.site.occurrence
  refine .packet foreignPlan List.mem_cons_self ?_
  intro o seen
  rw [GeneralRebaseRowWholeChild287.no_children] at seen
  cases seen

theorem parent_settled : PacketSettled unscoped (plan false) := by
  refine ⟨List.mem_cons_of_mem _ (List.mem_singleton_self _),?_⟩
  intro o seen
  rw [sole_child false] at seen
  cases List.mem_singleton.mp seen
  exact syntactically_discharged

theorem no_correct_frame (key : Nat) (p : GeneralNominalCenters.Plan roles) :
    ¬ Frame (registry false) unscoped.core (child false) key p := by
  intro f
  have ready := f.prepared
  rw [GeneralRebaseRowLocal287.child_at_role false _ f.visible f.role_eq] at ready
  exact GeneralRebaseRowGeneratedChild287.not_prepared ready

theorem still_no_dictionary (m : Assignment) (value : Payload) :
    ¬ Evidence (registry false) unscoped.core m (child false) value :=
  GeneralRebaseRowGeneratedChild287.no_child_evidence m value

theorem old_slice_accepts_foreign : Trusted unscoped (finalFacts false) := by
  have lift := growth (after false) foreignPlan
  refine .output (GeneralRebaseRowParentFrame287.effect false)
    (GeneralNominalVersionedSupportGrowth233.trusted lift (prior_trusted false))
    (List.mem_singleton_self _) parent_settled.1 (List.mem_singleton_self _)
    (GeneralNominalVersionedSupportGrowth233.class_readback lift (class_readback false)) parent_settled

theorem semantic_shortcut_counterexample :
    (∀ m, Models unscoped m ↔ Models (after false) m) ∧
    Discharged unscoped (child false) ∧
    Trusted unscoped (finalFacts false) ∧
    (∀ m payload, ¬ Evidence (registry false) unscoped.core m (child false) payload) :=
  ⟨models_eq,syntactically_discharged,old_slice_accepts_foreign,still_no_dictionary⟩

theorem no_raw_path :
    ¬ B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step (registry false) root) before unscoped := by
  intro path
  have count := GeneralRebaseRowActualPaths287.one_or_zero false unscoped path
  rcases count with prior | stopped
  · have size := congrArg (fun s : State roles => s.plans.length) prior
    change (2 : Nat) = 0 at size
    cases size
  · have size := congrArg (fun s : State roles => s.plans.length) stopped
    change (2 : Nat) = 1 at size
    cases size

theorem no_discharge_to_evidence_without_invariant :
    ¬ (∀ (reg : GeneralDeclarations.Registry) (s : State roles)
      (occ : GeneralSourceDictionaries.Occurrence roles) (m : Assignment),
      GeneralDeclarations.Checked reg → Models s m → Discharged s occ →
      ∃ payload, Evidence reg s.core m occ payload) := by
  intro claims
  have valid := (models_eq (model Common.rowEmpty)).mpr (after_model false Common.rowEmpty)
  obtain ⟨payload,ev⟩ := claims (registry false) unscoped (child false) _
    (checked false) valid syntactically_discharged
  exact still_no_dictionary _ payload ev

end Yulang.GeneralRebaseForeignLeaf288
