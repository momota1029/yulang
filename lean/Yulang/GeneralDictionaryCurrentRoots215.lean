import Yulang.GeneralDictionaryRecursiveBounds215
import Yulang.GeneralDictionaryCurrentProjection215
import Yulang.GeneralNominalPacketCaptureReadback

namespace Yulang.GeneralDictionaryCurrentRoots215
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryStructuralProjection215 (Bounded)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
set_option backward.isDefEq.respectTransparency false

theorem root_bounds (candidate : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model)
    (index : Fin candidate.packet.bounds.length) :
    Bounded candidate.packet.context.state model candidate.packet.bounds[index]
      (.source ((List.ofFn candidate.input.center)[index.val]?.getD 0)) := by
  have mapped := GeneralNominalPacketCaptureReadback.locate_sources
    candidate.packet.context.state.base (List.ofFn focus.demand.arguments) candidate.packet.bounds frame.located
  have occurrence : candidate.input.occurrence = focus := candidate.input_exact.trans frame.occurrence_eq
  have held := valid.2.2.2.1 candidate.input frame.center_recorded
  have length : candidate.packet.bounds.length = (roles focus.demand.role).arity := by
    have lengths := congrArg List.length mapped
    simpa only [List.length_map,List.length_ofFn] using lengths
  have bounded : index.val < (roles focus.demand.role).arity := by omega
  have pair := congrArg (fun xs => xs[index.val]?) mapped
  simp only [List.getElem?_map,List.getElem?_eq_getElem,index.isLt,Option.map_some,
    List.getElem?_ofFn,bounded,↓reduceDIte] at pair
  have pairEq := Option.some.inj pair
  generalize siteEq : candidate.input = site at *
  cases site with
  | mk input centers =>
    simp only at occurrence held ⊢
    subst input
    simp only [List.getElem?_ofFn,bounded,↓reduceDIte,Option.getD_some]
    refine ⟨⟨_,.source _⟩,?_⟩
    intro value seen
    cases seen
    have fit := held ⟨index.val,bounded⟩
    change CommonNominalFullCarrier.Subtype _ _ ∧ CommonNominalFullCarrier.Subtype _ _
    rw [← pairEq] at fit
    exact fit

theorem projection (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (registered : historical ∈ state.core.plans)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model) :
    ProjectionModels candidate.packet.context.state (headInspection candidate) model := by
  apply GeneralDictionaryCurrentProjection215.projection_of_anchors checked path historical candidate
    registered frame identity declaration model valid
  apply GeneralDictionaryRecursiveBounds215.many_bounds
  · rw [frame.context_eq]
    exact valid.1
  · intro index
    simpa only [Nat.zero_add] using root_bounds candidate frame model valid index
  · exact GeneralDictionaryDefaultRevisit214.candidate_tests checked path historical candidate registered
      frame identity declaration model valid

end Yulang.GeneralDictionaryCurrentRoots215
