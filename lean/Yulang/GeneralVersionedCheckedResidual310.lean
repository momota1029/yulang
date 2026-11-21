import Yulang.GeneralVersionedExplicitFromHolds310
import Yulang.GeneralVersionedRecursiveBridge310

set_option backward.isDefEq.respectTransparency false
/-! Two useful exact reductions of the still-open general bridges: a class
with no historical packet has no incompatible old choice; explicit output
classes with same-name local representatives need no separate live witnesses. -/
namespace Yulang.GeneralVersionedCheckedResidual310
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedExplicitFromHolds310 (Explicit live_from_represented)
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralNominalSaturationState (Alias)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state : State roles} {focus : Occurrence roles} {m : Assignment}

def UnrecordedClass (state : State roles) (focus : Occurrence roles) : Prop :=
  ∀ prior ∈ state.core.erased.current.packets,
    ¬ Alias state.core.erased.current focus.identity prior.site.occurrence.identity

theorem choice_fresh (effect : Effect roles)
    (unrecorded : UnrecordedClass state effect.plan.packet.site.occurrence) :
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet :=
  fun prior present alias => False.elim (unrecorded prior present alias)

def Represented (state : State roles) (focus : Occurrence roles) : Prop :=
  ∀ output ∈ requests state.core focus,
    ∃ localReq ∈ focus.demand.outputs, localReq.name = output.name

theorem represented_of_same_requests
    (filter : ∀ output ∈ requests state.core focus, output ∈ focus.demand.outputs) :
    Represented state focus := by
  intro output member
  exact ⟨output,filter output member,rfl⟩

theorem equal_by_shared_target
    (shared : ∀ a ∈ requests state.core focus, ∀ b ∈ requests state.core focus,
      a.name = b.name → a.target = b.target) :
    EqualOutputs state.core focus m := by
  intro a ma b mb same
  rw [shared a ma b mb same]
  exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem installation (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (registered : effect.registry = Compiled registry)
    (snapshot : effect.snapshot = state.core)
    (explicit : Explicit effect.plan effect.plan.packet.site.occurrence.demand.outputs)
    (represented : Represented state effect.plan.packet.site.occurrence)
    (valid : Models state m) (held : Holds effect.plan m)
    (same : EqualOutputs state.core effect.plan.packet.site.occurrence m) :
    GeneralNominalVersionedInstall232.InstallationModels state effect m := by
  apply (GeneralNominalVersionedMixedCommon235.installation_models_iff checked path registered snapshot).mpr
  have frame : Frame (Compiled registry) state.core effect.plan.packet.site.occurrence effect.plan.packet.declaration.id effect.plan :=
    registered ▸ snapshot ▸ effect.frame
  exact ⟨valid,held,live_from_represented frame held explicit represented same⟩

/-- No independent live model is chosen: the same witness that realizes the
    input and emitted packet equations also realizes all class requests. This
    can be used on previously uninstalled selected frames. -/
theorem installable_of_explicit (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (effect : Effect roles) (registered : effect.registry = Compiled registry)
    (snapshot : effect.snapshot = state.core)
    (selected : Local registry state effect.plan.packet.site.occurrence (.selected key children))
    (unrecorded : UnrecordedClass state effect.plan.packet.site.occurrence)
    (explicit : Explicit effect.plan effect.plan.packet.site.occurrence.demand.outputs)
    (represented : Represented state effect.plan.packet.site.occurrence)
    (common : ∃ m, Models state m ∧ Holds effect.plan m ∧
      EqualOutputs state.core effect.plan.packet.site.occurrence m) :
    GeneralNominalVersionedMixedKernel234.Installable (Compiled registry) state effect := by
  apply (GeneralNominalVersionedMixedSelectedEffect235.source_installable_iff path selected registered snapshot).mpr
  obtain ⟨m,valid,held,same⟩ := common
  exact ⟨choice_fresh effect unrecorded,m,installation checked path effect registered snapshot explicit represented valid held same⟩

end Yulang.GeneralVersionedCheckedResidual310
