import Yulang.GeneralNominalEvidenceOutput254
import Yulang.GeneralNominalSourceOwnerCandidates252
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalSourceReadback254
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatSemanticLabels (Inputs)
open GeneralNominalPatersonLineage (mass)
open GeneralNominalEvidenceOutput254 (FiniteOutputs)
variable {roles : Roles.RoleDecls} {state : State roles} {model : GeneralNominalCommonBridge.Assignment}

/-- This bridges local plan-label mass to the original root-label mass along
the actual mixed source trace, including plans with leaf declarations. -/
theorem input_bound
 (source : GeneralNominalSourceFormation.InitialSource registry context root)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (valid : Models state model)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (name : Nat) (input : name ∈ plan.packet.declaration.inputNames) :
 ∃ pattern : Pattern,
 GeneralNominalCenteredHeadMatSchemaMass.Part
   (algebra registry.constructors context.interpretation) plan model name pattern ∧
 pattern.encode.size ≤ mass rootLabels := by
 obtain ⟨ancestry,labels,_,known,bounded⟩ :=
   GeneralNominalVersionedMixedAncestry237.sites_bounded source point ground coverage path model valid plan.input frame.center_recorded
 have interpretation : state.core.erased.current.context.interpretation = context.interpretation :=
   (GeneralNominalVersionedMixedAncestry237.configuration_trace path).2.2
 have localInputs : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels := by
   simpa only [frame.registry_eq,frame.context_eq,interpretation] using known
 obtain ⟨pattern,part,small⟩ := GeneralNominalInputReadback254.input_part frame branch localInputs name input
 exact ⟨pattern,by simpa only [frame.registry_eq,frame.context_eq,interpretation] using part,by omega⟩

/-- A source-derived finite-input provider discharges the evidence theorem's
site premise. Evidence remains an explicit supplied certificate; this theorem
does not claim every selected plan already has evidence. -/
theorem evidence_outputs
 (source : GeneralNominalSourceFormation.InitialSource registry context root)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (valid : Models state model)
 (evidence : GeneralNominalVersionedEvidence231.Evidence registry state.core model focus payload) :
 FiniteOutputs (algebra registry.constructors context.interpretation) model focus := by
 have interpretation : state.core.erased.current.context.interpretation = context.interpretation :=
   (GeneralNominalVersionedMixedAncestry237.configuration_trace path).2.2
 have result := GeneralNominalEvidenceOutput254.payload_outputs evidence (by
   intro plan occurrence key frame
   obtain ⟨ancestry,labels,_,known,_⟩ :=
     GeneralNominalVersionedMixedAncestry237.sites_bounded source point ground coverage path model valid plan.input frame.center_recorded
   exact ⟨labels,by simpa only [frame.registry_eq,frame.context_eq,interpretation] using known⟩)
 simpa only [interpretation] using result

theorem mixed_source_outputs
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start)
 (path : B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start state)
 (valid : Models state model)
 (evidence : GeneralNominalVersionedEvidence231.Evidence
   (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) state.core model focus payload) :
 FiniteOutputs
   (algebra (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry).constructors
     state.core.erased.current.context.interpretation) model focus := by
 have compiled := GeneralNominalVersionedMixedSourceBoundary234.initial_compiled source
 obtain ⟨legacy,⟨context,labels,formed,point,ground,coverage,rfl⟩,rfl⟩ := compiled
 have result := evidence_outputs formed point ground coverage path valid evidence
 have interpretation : state.core.erased.current.context.interpretation = context.interpretation :=
   (GeneralNominalVersionedMixedAncestry237.configuration_trace path).2.2
 simpa only [interpretation] using result

theorem point_source_outputs
 (source : (GeneralNominalPointSourceBoundary240.boundary roles).Initial sourceRegistry root start)
 (path : B4Target.Steps ((GeneralNominalPointSourceBoundary240.boundary roles).Step sourceRegistry root) start state)
 (valid : Models state model)
 (evidence : GeneralNominalVersionedEvidence231.Evidence
   (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) state.core model focus payload) :
 FiniteOutputs
   (algebra (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry).constructors
     state.core.erased.current.context.interpretation) model focus :=
 mixed_source_outputs source (GeneralNominalPointErasure240.steps_old path) valid evidence
end Yulang.GeneralNominalSourceReadback254
