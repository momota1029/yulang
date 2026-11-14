import Yulang.GeneralNominalModeFrame181
import Yulang.GeneralNominalRawFrame179

/-! A complete centered journal frame with mode-sensitive schema support.
Endpoint-only schema entries no longer freeze a separate centered binder.
Capture bounds, actual uses, child sites and the raw journal remain preserved. -/
namespace Yulang.GeneralNominalModeLedger181
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree siteSources site_iff captureSources capture_mem)
open GeneralNominalModeFrame181 (schemaSources schema_iff)
variable {first last : Assignment}

 def childSources (plan : Plan roles) : List Nat :=
  plan.packet.declaration.requirements.attach.flatMap fun clause =>
    let valid := plan.packet.checked.signature.2.2.2 clause.val clause.property
    siteSources (plan.childSite clause.val valid) ++ schemaSources plan (plan.schema (plan.childRequests clause.val valid))

 def equationSources (plan : Plan roles) : List Nat :=
  siteSources plan.input ++ captureSources plan ++ schemaSources plan plan.headSchema ++
    schemaSources plan (GeneralNominalPacketSupport.inputSchema plan.packet) ++
    schemaSources plan (GeneralNominalPacketSupport.namedSchema plan.packet) ++ childSources plan

 theorem equations_iff (plan : Plan roles) (same : Agree (equationSources plan) first last) :
    plan.Equations first ↔ plan.Equations last := by
  have input := site_iff plan.input (fun name member => same name (by simp [equationSources,member]))
  have head := schema_iff plan plan.headSchema (fun name member => same name (by simp [equationSources,member]))
  have ins := schema_iff plan (GeneralNominalPacketSupport.inputSchema plan.packet)
    (fun name member => same name (by simp [equationSources,member]))
  have named := schema_iff plan (GeneralNominalPacketSupport.namedSchema plan.packet)
    (fun name member => same name (by simp [equationSources,member]))
  have captures : Agree (captureSources plan) first last :=
    fun name member => same name (by simp [equationSources,member])
  unfold Plan.Equations
  apply and_congr input
  apply and_congr
  · apply forall_congr'; intro name
    apply forall_congr'; intro needed
    have mem := (capture_mem plan name).mpr needed
    have one := captures (((GeneralNominalPacketSupport.capture plan.packet).inputs name).1)
      (List.mem_flatMap.mpr ⟨name,mem,by simp⟩)
    have two := captures (((GeneralNominalPacketSupport.capture plan.packet).inputs name).2)
      (List.mem_flatMap.mpr ⟨name,mem,by simp⟩)
    have center := captures (plan.binder name)
      (List.mem_flatMap.mpr ⟨name,mem,by simp⟩)
    simp only [GeneralNominalCaptureMerges.Fits,one,two,center]
  apply and_congr head
  apply and_congr ins
  apply and_congr named
  apply forall_congr'; intro clause
  apply forall_congr'; intro member
  apply forall_congr'; intro valid
  have children : Agree (siteSources (plan.childSite clause valid) ++
      schemaSources plan (plan.schema (plan.childRequests clause valid))) first last := by
    intro name present
    apply same
    have item : name ∈ childSources plan := List.mem_flatMap.mpr ⟨⟨clause,member⟩,by simp,present⟩
    simp [equationSources,item]
  exact and_congr (site_iff _ (fun name member => children name (List.mem_append_left _ member)))
    (schema_iff _ _ (fun name member => children name (List.mem_append_right _ member)))

/-- Actual finite ledger footprint, excluding the independent raw journal. -/
def ledgerSources (state : GeneralNominalCenteredSteps.State roles) : List Nat :=
  state.sites.flatMap siteSources ++ state.plans.flatMap equationSources

 theorem ledger_frame (state : GeneralNominalCenteredSteps.State roles)
    (same : Agree (ledgerSources state) first last)
    (valid : GeneralNominalCenteredSteps.Models state first)
    (raw : GeneralNominalSaturationState.Models state.erased.current last) :
    GeneralNominalCenteredSteps.Models state last := by
  refine ⟨raw,?_,?_⟩
  · intro site member
    apply (site_iff site ?_).mp (valid.2.1 site member)
    intro name present
    exact same name (List.mem_append_left _ (List.mem_flatMap.mpr ⟨site,member,present⟩))
  · intro plan member
    apply (equations_iff plan ?_).mp (valid.2.2 plan member)
    intro name present
    exact same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨plan,member,present⟩))


 def fullSources (state : GeneralNominalCenteredSteps.State roles) : List Nat :=
  GeneralNominalRawFrame179.rawSources state.erased.current ++ ledgerSources state

 theorem centered_models_frame (state : GeneralNominalCenteredSteps.State roles)
    (same : Agree (fullSources state) first last)
    (valid : GeneralNominalCenteredSteps.Models state first) :
    GeneralNominalCenteredSteps.Models state last :=
  ledger_frame state (fun name member => same name (List.mem_append_right _ member)) valid
    (GeneralNominalRawFrame179.raw_models_frame state.erased.current
      (fun name member => same name (List.mem_append_left _ member)) valid.1)

 theorem centered_models_iff (state : GeneralNominalCenteredSteps.State roles)
    (same : Agree (fullSources state) first last) :
    GeneralNominalCenteredSteps.Models state first ↔ GeneralNominalCenteredSteps.Models state last :=
  ⟨centered_models_frame state same,
    centered_models_frame state (fun name member => (same name member).symm)⟩

end Yulang.GeneralNominalModeLedger181
