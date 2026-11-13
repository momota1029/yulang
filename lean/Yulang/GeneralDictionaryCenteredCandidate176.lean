import Yulang.GeneralNominalCenteredGroundBoundary
import Yulang.GeneralNominalCenteredInspection

/-! Selection constructs a registered current candidate, with its own branch
model. This does not identify that model with a model of the entire centered
journal, and does not discharge installation support or alias closure. -/
namespace Yulang.GeneralDictionaryCenteredCandidate176
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredBoundary (Local)
open GeneralNominalSaturationState (Packet Generated)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}

structure Candidate (registry : Registry) (state : State roles) (focus : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) (plan : Plan roles) : Prop where
  registry_eq : plan.packet.registry = registry
  context_eq : plan.packet.context = state.erased.current.context
  occurrence_eq : plan.packet.site.occurrence = focus
  key_eq : plan.packet.declaration.id = key
  children_eq : plan.packet.children = children
  raw_recorded : plan.packet.site ∈ state.erased.current.sites
  centered_recorded : plan.input ∈ state.sites
  visible : plan.packet.declaration ∈ registry.declarations
  role : plan.packet.declaration.role = focus.demand.role
  located : GeneralNominalRecursiveCandidates.arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds
  prepared : GeneralNominalRecursiveCandidates.Prepared plan.packet.registry plan.packet.context
    plan.packet.site.occurrence plan.packet.declaration plan.packet.checked
  branch : ∃ model, plan.packet.Holds model

theorem selected_candidate
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : Generated state.erased.current root focus)
    (selected : Local registry state focus (.selected key children)) :
    ∃ plan : Plan roles, Candidate registry state focus key children plan := by
  obtain ⟨raw,rawMember,rawSame⟩ := GeneralNominalCenteredTrace.generated_registered path generated
  obtain ⟨center,centerMember,centerSame⟩ := GeneralNominalCenteredTrace.raw_site_centered path raw rawMember
  cases selected with
  | selected safe unique =>
    obtain ⟨_,declaration,visible,checked,identity,role,bounds,located,prepared,kids⟩ := unique.1
    let packet : Packet roles := ⟨registry,state.erased.current.context,raw,declaration,checked,bounds⟩
    let plan : Plan roles := ⟨packet,center,centerSame⟩
    have branch : ∃ model, packet.Holds model := by
      obtain ⟨_,_,_,other,found,_,_,model,valid⟩ := prepared
      have equal : other = bounds := Option.some.inj (found.symm.trans located)
      subst other
      exact ⟨model,by simpa only [Packet.Holds,packet,rawSame] using valid⟩
    refine ⟨plan,⟨rfl,rfl,rawSame,identity,?_,rawMember,centerMember,visible,role,?_,?_,branch⟩⟩
    · change GeneralNominalAllocation.children _ registry raw.occurrence declaration checked _ = children
      rw [rawSame]
      exact kids.symm
    · simpa only [plan,packet,rawSame] using located
    · simpa only [plan,packet,rawSame] using prepared

theorem reachable_candidate
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
      registry root state)
    (reached : focus = root ∨ Generated state.erased.current root focus)
    (selected : Local registry state focus (.selected key children)) :
    ∃ plan : Plan roles, Candidate registry state focus key children plan := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  apply selected_candidate path _ selected
  rcases reached with rfl | generated
  · exact .root
  · exact generated

end Yulang.GeneralDictionaryCenteredCandidate176
