import Yulang.GeneralStoppedLower335
import Yulang.GeneralStoppedOrdinarySite335
import Yulang.GeneralRebaseDisplayExecutor276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralStoppedDisplayProjection335
open GeneralRebaseDisplayFrame276 (before after after_models)
open GeneralRebaseDisplayExecutor276 (raw Phase)
open GeneralNominalExamples (registry state displayRoot displayChild interpretation)
open GeneralDeclarationExamples (roles)
open GeneralNominalNonleafPlan193 (centerSite)
open GeneralNominalCenters (rootSite)
open GeneralStoppedLower335 (lower normal original exact_models)
open GeneralStoppedOrdinarySite335 (demand occurrence)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported from_source restriction)
open GeneralNominalCommonBridge (Assignment)

/-- Closed form of the actual normalized source rows, with the
opaque body retained as one invariant constructor equation. -/
abbrev scalarRow : Equation := ⟨1,.primitive (.scalar .int) []⟩
abbrev listRow : Equation := ⟨0,.nominal 0 [.variable 1]⟩
abbrev initialOrdinary : State := ⟨normal (state true),[listRow,scalarRow]⟩

noncomputable abbrev ordinary : State :=
  ⟨normal after.core.erased.current.context.state,[listRow,scalarRow]⟩

abbrev diagonal : List (PresenceNormalForm.Atom Nat) :=
  [.tyLe (.var 1) (.var 1),.tyLe (.var 0) (.var 0),.tyLe (.var 0) (.var 0),.tyLe (.var 1) (.var 1)]

theorem terminal_atoms :
    ordinary.normal.ordinary = initialOrdinary.normal.ordinary ++ diagonal := by decide +kernel

theorem initial_read : lower before.core.erased.current.context.state = some initialOrdinary := rfl

theorem stopped_read : lower after.core.erased.current.context.state = some ordinary := rfl

theorem actual_model (m : Assignment) :
    Models ordinary m ↔ GeneralNominalVersionedJournal232.Models after m :=
  by
  have same : Models ordinary m ↔ Models initialOrdinary m := by
    unfold Models GeneralDeclarativeWhere319.Models
    rw [terminal_atoms,PresenceNormalForm.all_append]
    constructor
    · rintro ⟨⟨⟨origin,_⟩,intervals⟩,rows⟩
      exact ⟨⟨origin,intervals⟩,rows⟩
    · rintro ⟨⟨origin,intervals⟩,rows⟩
      refine ⟨⟨⟨origin,?_⟩,intervals⟩,rows⟩
      intro atom seen
      simp only [diagonal,List.mem_cons,List.not_mem_nil,or_false] at seen
      rcases seen with h|h|h|h <;> cases ‹_› <;> exact CommonNominalFullCarrier.subtype_refl _
  exact same.trans ((exact_models (state true) m initial_read).trans (after_models m).symm)

noncomputable def supported (done : Nat → Prop) : Supported ordinary done :=
  original initialOrdinary ordinary (fun _ held => held) done

theorem list_allowed (done : Nat → Prop) :
    listRow ∈ (restriction (supported done)).equations :=
  from_source _ ⟨List.mem_cons_self,rfl⟩

theorem int_allowed (done : Nat → Prop) :
    scalarRow ∈ (restriction (supported done)).equations :=
  from_source _ ⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩

abbrev parentDemand : Demand := ⟨0,[⟨0,0,0⟩],[]⟩
abbrev childDemand : Demand := ⟨0,[⟨1,1,1⟩],[]⟩

theorem exact_parent :
    occurrence (rootSite (state true).seed displayRoot) = (displayRoot.identity,parentDemand) := rfl

theorem exact_child : occurrence centerSite = (displayChild.identity,childDemand) := rfl

theorem stopped_sites :
    after.core.sites.map occurrence = [(displayRoot.identity,parentDemand),(displayChild.identity,childDemand)] := by
  rw [GeneralRebaseDisplayEvidence276.center_sites]
  exact rfl

theorem reached :
    B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry displayRoot) before after :=
  .tail .refl GeneralRebaseDisplayStep276.actual_step

theorem halted : ∀ later, ¬ GeneralNominalVersionedMixedKernel234.Step registry displayRoot after later :=
  GeneralRebaseDisplayStable276.halted

end Yulang.GeneralStoppedDisplayProjection335
