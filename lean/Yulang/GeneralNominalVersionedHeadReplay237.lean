import Yulang.GeneralNominalVersionedCurrentHead237
set_option backward.isDefEq.respectTransparency false
/-! Actual heads do not depend on observation versions. Historical nonpoint
binders replay, and current point binders are recovered from actual projections.
The unresolved old-point/current-nonpoint case is explicitly excluded. -/
namespace Yulang.GeneralNominalVersionedHeadReplay237
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedFrame231 (binder capture)
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls}

theorem schema_eq (first last : Plan roles)
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (centers : List.ofFn first.input.center = List.ofFn last.input.center) : first.headSchema = last.headSchema := by
  simp only [Plan.headSchema,GeneralNominalInspection.queries,declaration,constructors,interpretation,centers]

def NoPointLoss (old current : Plan roles) : Prop :=
  ∀ name ∈ current.packet.declaration.inputNames,
    ((capture current.packet).inputs name).1 = ((capture current.packet).inputs name).2 ∨
    ((capture old.packet).inputs name).1 ≠ ((capture old.packet).inputs name).2

theorem nonpoint_binder (plan : Plan roles) (name : Nat)
    (notOutput : name ∉ plan.packet.declaration.outputNames)
    (nonpoint : ((capture plan.packet).inputs name).1 ≠ ((capture plan.packet).inputs name).2) :
    binder plan name = fresh plan.packet.context.state.seed plan.packet.site.occurrence.identity plan.packet.declaration.id 8 name 0 := by
  simp only [binder,notOutput,ite_false,nonpoint]

theorem schema_replay (state : State roles) (old current : Plan roles) (model : Assignment)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key current)
    (valid : Models state model) (head : HeadModels current.packet model)
    (sameSchema : old.headSchema = current.headSchema)
    (seed : old.packet.context.state.seed = current.packet.context.state.seed)
    (identity : old.packet.site.occurrence.identity = current.packet.site.occurrence.identity)
    (declaration : old.packet.declaration = current.packet.declaration)
    (phase : NoPointLoss old current)
    (prior : SchemaHolds old old.headSchema model) : SchemaHolds current current.headSchema model := by
  have tests : ∀ test ∈ current.headSchema.tests, Head model test.1 test.2 := by
    rw [← sameSchema]; exact prior.1
  have shared : GeneralDictionaryHeadSharing220.Holds current model := by
    have previous := GeneralNominalVersionedHeadSharing232.schema_holds old model prior
    simpa only [GeneralDictionaryHeadSharing220.Holds,GeneralDictionaryHeadSharing220.equations,sameSchema] using previous
  have projection := (GeneralNominalVersionedCurrentProjection237.projection_iff current frame model valid tests).mpr
    (GeneralDictionaryHeadSharing220.agreement_of_holds current model shared)
  have finished := GeneralNominalVersionedCurrentProjection237.frame_finished current frame
  have merges := ((private_models_iff ..).mp head.1).2.2.1
  refine ⟨tests,?_⟩
  intro entry member
  have actual := GeneralNominalHeadSchemaNames186.head_actual current entry member
  have named := GeneralNominalHeadSchemaNames186.head_input current entry member
  have oldMember : entry ∈ old.headSchema.variables := sameSchema.symm ▸ member
  have notOutput := GeneralNominalHeadSchemaNames186.head_not_output current entry member
  have oldNotOutput := GeneralNominalHeadSchemaNames186.head_not_output old entry oldMember
  have previous : Same model entry.origin (.source (binder old entry.name)) := by
    simpa only [actual,ite_true] using prior.2 entry oldMember
  simp only [actual,ite_true]
  rcases phase entry.name named with point | nonpoint
  · have centered : binder current entry.name = ((capture current.packet).inputs entry.name).1 := by
      simp only [binder,notOutput,ite_false,point,ite_true]
    refine ⟨previous.1,⟨_,.source _⟩,?_⟩
    intro value target seen atTarget
    cases atTarget
    have fit := GeneralNominalVersionedProjectionBounds237.head_use current model finished projection merges entry member value seen
    rw [centered]
    exact ⟨by simpa only [← point] using fit.2,fit.1⟩
  · by_cases currentPoint : ((capture current.packet).inputs entry.name).1 = ((capture current.packet).inputs entry.name).2
    · have centered : binder current entry.name = ((capture current.packet).inputs entry.name).1 := by
        simp only [binder,notOutput,ite_false,currentPoint,ite_true]
      refine ⟨previous.1,⟨_,.source _⟩,?_⟩
      intro value target seen atTarget
      cases atTarget
      have fit := GeneralNominalVersionedProjectionBounds237.head_use current model finished projection merges entry member value seen
      rw [centered]
      exact ⟨by simpa only [← currentPoint] using fit.2,fit.1⟩
    · have binders : binder old entry.name = binder current entry.name := by
        rw [nonpoint_binder old entry.name oldNotOutput nonpoint,
          nonpoint_binder current entry.name notOutput currentPoint,seed,identity,declaration]
      rwa [← binders]

theorem recorded_replay (state : State roles) (old current : Plan roles) (model : Assignment)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key current)
    (valid : Models state model) (recorded : old ∈ state.plans) (head : HeadModels current.packet model)
    (sameSchema : old.headSchema = current.headSchema)
    (seed : old.packet.context.state.seed = current.packet.context.state.seed)
    (identity : old.packet.site.occurrence.identity = current.packet.site.occurrence.identity)
    (declaration : old.packet.declaration = current.packet.declaration) (phase : NoPointLoss old current) :
    SchemaHolds current current.headSchema model :=
  schema_replay state old current model frame valid head sameSchema seed identity declaration phase
    (valid.2.1 old recorded).2.1.2.2.2.2.1
end Yulang.GeneralNominalVersionedHeadReplay237
