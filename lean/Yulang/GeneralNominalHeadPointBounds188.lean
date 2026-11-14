import Yulang.GeneralNominalHeadInitialCommon188
import Yulang.GeneralNominalPacketCaptureReadback

/-! Actual initial point-root frames locate equal endpoint slots and retain
exactly the source name at each center. The finite index default is unreachable. -/
namespace Yulang.GeneralNominalHeadPointBounds188
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs (Frame)
open GeneralNominalRecursiveInspection (Origin)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

 theorem initial_point_bounds (context : GeneralNominalCandidates.Context)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (candidate : Plan roles) (frame : Frame registry (initial context root).core root key candidate)
    (index : Nat) (interval : GeneralNominalInspection.Bounds candidate.packet.context.state)
    (found : candidate.packet.bounds[index]? = some interval) :
    interval.1 = interval.2 ∧
      some (Origin.source ((List.ofFn candidate.input.center)[index]?.getD 0)) =
        some (Origin.source (candidate.packet.context.state.base.source interval.1)) := by
  have mapped := GeneralNominalPacketCaptureReadback.locate_sources
    candidate.packet.context.state.base (List.ofFn root.demand.arguments) candidate.packet.bounds frame.located
  have length : candidate.packet.bounds.length = (roles root.demand.role).arity := by
    have lengths := congrArg List.length mapped
    simpa only [List.length_map,List.length_ofFn] using lengths
  have bound : index < (roles root.demand.role).arity := by
    obtain ⟨present,_⟩ := List.getElem?_eq_some_iff.mp found
    omega
  have atIndex := congrArg (fun xs => xs[index]?) mapped
  simp only [List.getElem?_map,found,Option.map_some,List.getElem?_ofFn,bound,↓reduceDIte] at atIndex
  have pair := Option.some.inj atIndex
  have lower := congrArg Prod.fst pair
  have upper := congrArg Prod.snd pair
  have same : interval.1 = interval.2 := candidate.packet.context.state.base.source_injective
    (lower.trans ((point ⟨index,bound⟩).trans upper.symm))
  have siteEq : candidate.input = rootSite context.state.seed root := List.mem_singleton.mp frame.center_recorded
  refine ⟨same,?_⟩
  rw [siteEq]
  simpa only [rootSite,List.getElem?_ofFn,bound,↓reduceDIte,Option.getD_some,point,↓reduceIte] using congrArg (fun name => some (Origin.source name)) lower.symm

 theorem boundary_initial_point_bounds (state : State roles)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (index : Nat) (interval : GeneralNominalInspection.Bounds candidate.packet.context.state)
    (found : candidate.packet.bounds[index]? = some interval) :
    interval.1 = interval.2 ∧
      some (Origin.source ((List.ofFn candidate.input.center)[index]?.getD 0)) =
        some (Origin.source (candidate.packet.context.state.base.source interval.1)) := by
  obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
  subst state
  exact initial_point_bounds context point candidate frame index interval found

end Yulang.GeneralNominalHeadPointBounds188
