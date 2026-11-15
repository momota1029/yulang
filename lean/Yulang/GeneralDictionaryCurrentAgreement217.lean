import Yulang.GeneralDictionaryCountedProjection216
import Yulang.GeneralDictionaryDefaultBinderCollisions214
import Yulang.GeneralDictionaryDefaultProjectionBounds215

namespace Yulang.GeneralDictionaryCurrentAgreement217
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms (Same)
open CommonNominalFullCarrier
open GeneralDictionaryCountedProjection216 (Agreement)
open GeneralDictionaryDefaultHeadEquationExtension214 (uses uses_mem Compatible)
open GeneralDictionaryDefaultRevisit214 (BoundsFit)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
set_option backward.isDefEq.respectTransparency false

theorem use_same (candidate : Plan roles) {model : Assignment}
    (finished : Finished (headInspection candidate))
    (agreement : Agreement candidate model)
    (first last : Use) (one : first ∈ candidate.headSchema.variables)
    (two : last ∈ candidate.headSchema.variables) (names : first.name = last.name) :
    Same model first.origin last.origin := by
  obtain ⟨a,ha,na,oa⟩ := GeneralNominalSchemaCapture187.schemas_capture
    candidate.packet.context.state _ candidate.packet.bounds _ 0 finished first one
  obtain ⟨b,hb,nb,ob⟩ := GeneralNominalSchemaCapture187.schemas_capture
    candidate.packet.context.state _ candidate.packet.bounds _ 0 finished last two
  exact agreement a ha b hb (na.trans (names.trans nb.symm)) first.origin last.origin oa ob

theorem coherent
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : GeneralDictionaryDefaultDepth208.InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (agreement : Agreement candidate model) (fits : BoundsFit candidate model) :
    ∀ i j first last, candidate.binder (uses candidate i).name = candidate.binder (uses candidate j).name →
      Observes model (uses candidate i).origin first → Observes model (uses candidate j).origin last →
      Equivalent first last := by
  intro i j a b same seenA seenB
  have oneInput := GeneralNominalHeadSchemaNames186.head_not_output candidate _ (uses_mem candidate i)
  have twoInput := GeneralNominalHeadSchemaNames186.head_not_output candidate _ (uses_mem candidate j)
  by_cases pointA : ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate i).name).1 =
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate i).name).2
  · by_cases pointB : ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate j).name).1 =
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate j).name).2
    · have left := GeneralDictionaryDefaultBinderCollisions214.point_fits candidate _ oneInput pointA model a (fits i a seenA)
      have right := GeneralDictionaryDefaultBinderCollisions214.point_fits candidate _ twoInput pointB model b (fits j b seenB)
      rw [same] at left
      exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩
    · exact False.elim ((GeneralDictionaryDefaultConservative214.nonpoint_binder_endpoints_separate
        source bound path candidate frame.context_eq _ twoInput pointB _).1
        (same.symm.trans (GeneralDictionaryDefaultBinderCollisions214.point_binder candidate _ oneInput pointA)))
  · by_cases pointB : ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate j).name).1 =
        ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate j).name).2
    · exact False.elim ((GeneralDictionaryDefaultConservative214.nonpoint_binder_endpoints_separate
        source bound path candidate frame.context_eq _ oneInput pointA _).1
        (same.trans (GeneralDictionaryDefaultBinderCollisions214.point_binder candidate _ twoInput pointB)))
    · have names := GeneralDictionaryDefaultBinderCollisions214.nonpoint_name candidate _ _ oneInput twoInput pointA pointB same
      exact (use_same candidate (GeneralDictionaryDefaultRevisit214.frame_finished frame) agreement
        _ _ (uses_mem candidate i) (uses_mem candidate j) names).2.2 a b seenA seenB

theorem compatible
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model) (agreement : Agreement candidate model)
    (fits : BoundsFit candidate model) : Compatible candidate model := by
  have tests := GeneralDictionaryCountedCandidate216.tests source point ground coverage path candidate frame model valid
  have projection := (GeneralDictionaryCountedProjection216.projection_iff source point ground coverage path candidate frame model valid).mpr agreement
  have finished := GeneralDictionaryDefaultRevisit214.frame_finished frame
  refine ⟨tests,?_,fits,coherent source (GeneralDictionaryDefaultAncestry208.ground_depth_bound source point ground coverage)
    path candidate frame model agreement fits⟩
  intro i
  obtain ⟨captured,present,_,origin⟩ := GeneralNominalSchemaCapture187.schemas_capture
    candidate.packet.context.state _ candidate.packet.bounds _ 0 finished (uses candidate i) (uses_mem candidate i)
  exact (projection.1 _ (GeneralNominalCaptureAnchors.many_anchored
    candidate.packet.context.state _ candidate.packet.bounds _ 0 captured present (uses candidate i).origin origin)).1


theorem agreement_of_compatible (candidate : Plan roles) (model : Assignment)
    (compatible : Compatible candidate model) : Agreement candidate model := by
  intro a one b two names first last atFirst atLast
  obtain ⟨x,atX,usedX⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    candidate.packet.context.state _ candidate.packet.bounds _ 0 a one
  obtain ⟨y,atY,usedY⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    candidate.packet.context.state _ candidate.packet.bounds _ 0 b two
  cases Option.some.inj (atX.symm.trans atFirst)
  cases Option.some.inj (atY.symm.trans atLast)
  obtain ⟨i,equalI⟩ := GeneralDictionaryDefaultHeadEquationExtension214.uses_cover candidate _ usedX
  obtain ⟨j,equalJ⟩ := GeneralDictionaryDefaultHeadEquationExtension214.uses_cover candidate _ usedY
  have inhabitedI := compatible.2.1 i
  have inhabitedJ := compatible.2.1 j
  rw [equalI] at inhabitedI
  rw [equalJ] at inhabitedJ
  refine ⟨inhabitedI,inhabitedJ,?_⟩
  intro u v seenU seenV
  have coherent := compatible.2.2.2 i j u v
  simp only [equalI,equalJ,names] at coherent
  exact coherent True.intro seenU seenV

theorem compatible_iff
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model) :
    Compatible candidate model ↔ Agreement candidate model ∧ BoundsFit candidate model := by
  constructor
  · exact fun given => ⟨agreement_of_compatible candidate model given,given.2.2.1⟩
  · exact fun given => compatible source point ground coverage path candidate frame model valid given.1 given.2

end Yulang.GeneralDictionaryCurrentAgreement217
