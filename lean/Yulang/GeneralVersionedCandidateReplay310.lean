import Yulang.GeneralVersionedOrdinaryFrame310

set_option backward.isDefEq.respectTransparency false
/-! Ordinary, support-preserving and model-implied equations preserve exactly
which checked heads survive. This does not say they preserve Local: class
administration/history can change even when candidate data do not. -/
namespace Yulang.GeneralVersionedCandidateReplay310
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates (Context arguments report Metadata)
open GeneralNominalVersionedCandidates231 (inputs Prepared Survivor Unique HeadModels)
open GeneralNominalVersionedTransport231 (extendedPacket)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedOrdinaryFrame310 (Supported Atoms)
open GeneralDictionaryOrdinaryTransport (extend)
open GeneralNominalState (sources Linked)
open GeneralNominalRecursiveInspection (bindings Finished)

variable {roles : Roles.RoleDecls} (ctx : Context) (atoms : Atoms)

abbrev next := extend ctx [] atoms []

def Implied : Prop := ∀ m, GeneralNominalState.Models ctx.state m →
  PresenceNormalForm.All CommonNominalFullCarrier.model m atoms

theorem source_subset (safe : Supported ctx.state atoms) : sources (next ctx atoms).state ⊆ sources ctx.state :=
  GeneralNominalAllocationSupport.extend_sources ctx.state [] atoms (List.Subset.refl _)
    (by intro _ absent; cases absent) safe

theorem linked_iff (safe : Supported ctx.state atoms) (d : Occurrence roles) :
    Linked (next ctx atoms).state d.demand ↔ Linked ctx.state d.demand := by
  constructor
  · rintro ⟨arguments,outputs⟩
    exact ⟨fun i => ⟨source_subset ctx atoms safe (arguments i).1,source_subset ctx atoms safe (arguments i).2⟩,
      fun target member => source_subset ctx atoms safe (outputs target member)⟩
  · exact GeneralNominalVersionedPreparedTransport231.linked_forward [] atoms [] ctx d

theorem packet_head {registry : Registry} {d : Occurrence roles} {declaration : Declaration}
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds ctx.state)) (m : Assignment)
    (implied : Implied ctx atoms) :
    HeadModels registry (next ctx atoms) d declaration bounds m ↔
      HeadModels registry ctx d declaration bounds m := by
  let packet : GeneralNominalSaturationState.Packet roles :=
    ⟨registry,ctx,GeneralNominalDemandMerging.pointSite (inputs d),declaration,checked,bounds⟩
  change GeneralNominalVersionedPlans231.HeadModels (extendedPacket [] atoms [] packet) m ↔
    GeneralNominalVersionedPlans231.HeadModels packet m
  unfold GeneralNominalVersionedPlans231.HeadModels
  rw [GeneralNominalVersionedPlans231.private_models_iff,GeneralNominalVersionedPlans231.private_models_iff,
    GeneralNominalVersionedTransport231.ordinary_iff,GeneralNominalVersionedTransport231.projection_iff]
  change ((GeneralNominalState.Models (next ctx atoms).state m ∧ _) ∧ _) ↔
    (GeneralNominalState.Models ctx.state m ∧ _) ∧ _
  rw [GeneralDictionaryOrdinaryTransport.models_extended]
  exact ⟨fun h => ⟨⟨h.1.1.1,h.1.2⟩,h.2⟩,
    fun h => ⟨⟨⟨h.1.1,implied m h.1.1⟩,h.1.2⟩,h.2⟩⟩

theorem same_fresh {registry : Registry} {d : Occurrence roles} {declaration : Declaration}
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds ctx.state)) (safe : Supported ctx.state atoms) :
    GeneralNominalVersionedAllocation231.Fresh (next ctx atoms).state registry d.identity
       (bindings (next ctx atoms).state (report (next ctx atoms) declaration bounds)) ↔
       GeneralNominalVersionedAllocation231.Fresh ctx.state registry d.identity
       (bindings ctx.state (report ctx declaration bounds)) := by
  unfold next
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,GeneralDictionaryOrdinaryTransport.bindings_report]
  constructor
  · intro new origin member used
    have subset := GeneralNominalRefinements.sources
      (GeneralNominalRefinements.extended ctx.state [] atoms)
    have held := new origin member (subset _ used)
    simpa only [extend,GeneralDictionaryOrdinaryTransport.extendState,List.append_nil] using held
  · intro old
    let packet : GeneralNominalSaturationState.Packet roles :=
      ⟨registry,ctx,GeneralNominalDemandMerging.pointSite d,declaration,checked,bounds⟩
    exact GeneralVersionedOrdinaryFrame310.fresh packet atoms old safe

theorem prepared {registry : Registry} {d : Occurrence roles} {declaration : Declaration}
    (checked : DeclarationChecked registry.constructors roles declaration)
    (safe : Supported ctx.state atoms) (implied : Implied ctx atoms) :
    Prepared registry (next ctx atoms) d declaration ↔ Prepared registry ctx d declaration := by
  change (_ ∧ Linked (next ctx atoms).state (inputs d).demand ∧ _) ↔ _
  rw [linked_iff ctx atoms safe (inputs d)]
  constructor
  · rintro ⟨metadata,input,bounds,located,fresh,finished,m,head⟩
    exact ⟨metadata,input,bounds,located,(same_fresh ctx atoms (d := d) checked bounds safe).mp fresh,
      (GeneralNominalVersionedPreparedTransport231.finished_iff [] atoms [] ctx declaration bounds).mp finished,
      m,(packet_head ctx atoms (d := d) checked bounds m implied).mp head⟩
  · rintro ⟨metadata,input,bounds,located,fresh,finished,m,head⟩
    exact ⟨metadata,input,bounds,located,(same_fresh ctx atoms (d := d) checked bounds safe).mpr fresh,
      (GeneralNominalVersionedPreparedTransport231.finished_iff [] atoms [] ctx declaration bounds).mpr finished,
      m,(packet_head ctx atoms (d := d) checked bounds m implied).mpr head⟩

theorem emitted (registry : Registry) (d : Occurrence roles) (decl : Declaration)
    (checked : DeclarationChecked registry.constructors roles decl)
    (bounds : List (GeneralNominalInspection.Bounds ctx.state)) :
    GeneralNominalVersionedCandidates231.children registry (next ctx atoms) d decl checked bounds =
      GeneralNominalVersionedCandidates231.children registry ctx d decl checked bounds := by
  apply GeneralNominalVersionedTransport231.children_eq [] atoms []
    (⟨registry,ctx,GeneralNominalDemandMerging.pointSite (inputs d),decl,checked,bounds⟩ :
      GeneralNominalSaturationState.Packet roles)

theorem survivor (registry : Registry) (d : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (safe : Supported ctx.state atoms) (implied : Implied ctx atoms) :
    Survivor registry (next ctx atoms) d key children ↔ Survivor registry ctx d key children := by
  constructor
  · rintro ⟨known,decl,visible,checked,keyEq,role,bounds,located,ready,child⟩
    refine ⟨known,decl,visible,checked,keyEq,role,bounds,located,(prepared ctx atoms checked safe implied).mp ready,?_⟩
    exact child.trans (emitted ctx atoms registry d decl checked bounds)
  · rintro ⟨known,decl,visible,checked,keyEq,role,bounds,located,ready,child⟩
    refine ⟨known,decl,visible,checked,keyEq,role,bounds,located,(prepared ctx atoms checked safe implied).mpr ready,?_⟩
    exact child.trans (emitted ctx atoms registry d decl checked bounds).symm

end Yulang.GeneralVersionedCandidateReplay310
