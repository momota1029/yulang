import Yulang.GeneralDictionaryCountedInspection216
import Yulang.GeneralDictionaryCurrentRoots215
import Yulang.GeneralDictionaryDefaultAncestry208
import Yulang.GeneralDictionaryDefaultAliasProjection215
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCountedCandidate216
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCountedObservation216 (Labelled)
open GeneralNominalOriginTerms (Head)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem tests_of_finished
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles)
    (current : candidate.packet.context = state.core.erased.current.context)
    (registered : candidate.input ∈ state.core.sites)
    (located : GeneralNominalRecursiveCandidates.arguments candidate.packet.context
      (GeneralNominalCenteredHeadCandidates.inputs candidate.input.occurrence) = some candidate.packet.bounds)
    (finished : Finished (headInspection candidate))
    (model : Assignment) (valid : Models state model) :
    ∀ test ∈ candidate.headSchema.tests, Head model test.1 test.2 := by
  obtain ⟨depth,labels,ancestry,inputs,bound⟩ :=
    GeneralDictionaryDefaultAncestry208.sites_bounded GeneralDictionaryDefaultAncestry208.head_readback
      source point ground coverage path model valid candidate.input registered
  have mapped := GeneralNominalPacketCaptureReadback.locate_sources
    candidate.packet.context.state.base (List.ofFn candidate.input.occurrence.demand.arguments) candidate.packet.bounds located
  have length : candidate.packet.bounds.length = (roles candidate.input.occurrence.demand.role).arity := by
    have lengths := congrArg List.length mapped
    simpa only [List.length_map,List.length_ofFn] using lengths
  apply GeneralDictionaryCountedInspection216.many_tests candidate.packet.context.state model
    (constructors := registry.constructors) (interpretation := context.interpretation)
  · rw [current]; exact valid.1
  · intro index
    have within : index.val < (roles candidate.input.occurrence.demand.role).arity := by rw [← length]; exact index.isLt
    have counted := inputs.2 ⟨index.val,within⟩
    have labelled := GeneralDictionaryCountedObservation216.counted_source counted
    simpa only [Nat.zero_add,List.getElem?_ofFn,within,↓reduceDIte,Option.getD_some] using labelled
  · intro index
    simpa only [Nat.zero_add,GeneralDictionaryStructuralProjection215.Bounded,GeneralDictionaryDefaultNominalProjection215.Bounded] using GeneralDictionaryDefaultAliasProjection215.root_bounds candidate registered located model valid index
  · exact finished


theorem tests
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model) :
    ∀ test ∈ candidate.headSchema.tests, Head model test.1 test.2 := by
  obtain ⟨depth,labels,ancestry,inputs,bound⟩ :=
    GeneralDictionaryDefaultAncestry208.sites_bounded GeneralDictionaryDefaultAncestry208.head_readback
      source point ground coverage path model valid candidate.input frame.center_recorded
  have located := GeneralNominalPacketCaptureReadback.locate_sources
    candidate.packet.context.state.base (List.ofFn focus.demand.arguments) candidate.packet.bounds frame.located
  have occurrence : candidate.input.occurrence = focus := candidate.input_exact.trans frame.occurrence_eq
  have length : candidate.packet.bounds.length = (roles candidate.input.occurrence.demand.role).arity := by
    have lengths := congrArg List.length located
    rw [occurrence]
    simpa only [List.length_map,List.length_ofFn] using lengths
  apply GeneralDictionaryCountedInspection216.many_tests candidate.packet.context.state model
    (constructors := registry.constructors) (interpretation := context.interpretation)
  · rw [frame.context_eq]; exact valid.1
  · intro index
    have within : index.val < (roles candidate.input.occurrence.demand.role).arity := by rw [← length]; exact index.isLt
    have counted := inputs.2 ⟨index.val,within⟩
    have labelled := GeneralDictionaryCountedObservation216.counted_source counted
    simpa only [Nat.zero_add,List.getElem?_ofFn,within,↓reduceDIte,Option.getD_some] using labelled
  · intro index
    simpa only [Nat.zero_add] using GeneralDictionaryCurrentRoots215.root_bounds candidate frame model valid index
  · exact GeneralDictionaryDefaultRevisit214.frame_finished frame

end Yulang.GeneralDictionaryCountedCandidate216
