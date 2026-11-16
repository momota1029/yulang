import Yulang.GeneralDictionarySharingObstruction217
import Yulang.GeneralDictionaryDefaultKernel208
import Yulang.GeneralNominalCenteredHeadMatPermutationPlans

/-! A finite list of equalities between actual head positions bearing the same
name. The existing total head equations already imply these constraints. This
module exposes them explicitly without changing endpoint candidate matching. -/
namespace Yulang.GeneralDictionaryHeadSharing220
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalOriginTerms
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryCountedProjection216 (Agreement)
variable {roles : Roles.RoleDecls}

def equations (plan : Plan roles) : List (Origin × Origin) :=
  plan.headSchema.variables.flatMap fun first =>
    (plan.headSchema.variables.filter fun last => first.name == last.name).map
      fun last => (first.origin,last.origin)

def Holds (plan : Plan roles) (model : Assignment) : Prop :=
  ∀ equation ∈ equations plan, Same model equation.1 equation.2

theorem equations_mem_iff (plan : Plan roles) (equation : Origin × Origin) :
    equation ∈ equations plan ↔
    ∃ first ∈ plan.headSchema.variables, ∃ last ∈ plan.headSchema.variables,
      first.name = last.name ∧ equation = (first.origin,last.origin) := by
  simp only [equations,List.mem_flatMap,List.mem_map,List.mem_filter,beq_iff_eq]
  constructor
  · rintro ⟨first,one,last,⟨two,names⟩,eq⟩
    exact ⟨first,one,last,two,names,eq.symm⟩
  · rintro ⟨first,one,last,two,names,eq⟩
    exact ⟨first,one,last,⟨two,names⟩,eq.symm⟩

theorem holds_iff (plan : Plan roles) (model : Assignment) : Holds plan model ↔
    ∀ first ∈ plan.headSchema.variables, ∀ last ∈ plan.headSchema.variables,
      first.name = last.name → Same model first.origin last.origin := by
  constructor
  · intro held first one last two names
    exact held (first.origin,last.origin) ((equations_mem_iff ..).mpr ⟨first,one,last,two,names,rfl⟩)
  · intro held equation present
    obtain ⟨first,one,last,two,names,rfl⟩ := (equations_mem_iff ..).mp present
    exact held first one last two names

theorem agreement_of_holds (plan : Plan roles) (model : Assignment)
    (held : Holds plan model) : Agreement plan model := by
  intro a one b two names first last atFirst atLast
  obtain ⟨x,atX,usedX⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 a one
  obtain ⟨y,atY,usedY⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 b two
  cases Option.some.inj (atX.symm.trans atFirst)
  cases Option.some.inj (atY.symm.trans atLast)
  exact (holds_iff plan model).mp held _ usedX _ usedY names

theorem holds_of_agreement (plan : Plan roles) (model : Assignment)
    (finished : Finished (GeneralNominalQueryProvenance183.headInspection plan))
    (agreement : Agreement plan model) : Holds plan model :=
  (holds_iff plan model).mpr (fun first one last two names =>
    GeneralDictionaryCurrentAgreement217.use_same plan finished agreement first last one two names)

theorem holds_iff_agreement (plan : Plan roles) (model : Assignment)
    (finished : Finished (GeneralNominalQueryProvenance183.headInspection plan)) :
    Holds plan model ↔ Agreement plan model :=
  ⟨agreement_of_holds plan model,holds_of_agreement plan model finished⟩

theorem schema_holds (plan : Plan roles) (model : Assignment)
    (held : plan.SchemaHolds plan.headSchema model) : Holds plan model := by
  apply (holds_iff plan model).mpr
  intro first one last two names
  have actualFirst := GeneralNominalHeadSchemaNames186.head_actual plan first one
  have actualLast := GeneralNominalHeadSchemaNames186.head_actual plan last two
  have a : Same model first.origin (.source (plan.binder first.name)) := by
    simpa only [actualFirst,ite_true] using held.2 first one
  have b : Same model last.origin (.source (plan.binder last.name)) := by
    simpa only [actualLast,ite_true] using held.2 last two
  rw [names] at a
  exact same_trans a (same_symm b)

theorem head_holds (plan : Plan roles) (model : Assignment)
    (held : GeneralNominalCenteredHeadOutputs.HeadEquations plan model) : Holds plan model :=
  schema_holds plan model held.2.2

theorem packet_holds (plan : Plan roles) (model : Assignment)
    (held : GeneralNominalCenteredHeadMatStepPackets.Holds plan model) : Holds plan model :=
  head_holds plan model (GeneralNominalCenteredHeadMatStepPackets.head_equations held)

theorem effect_holds (effect : Effect roles) (model : Assignment)
    (held : effect.Holds model) : Holds effect.plan model := head_holds effect.plan model held.1

theorem committed_holds (state : State roles) (plan : Plan roles) (model : Assignment)
    (committed : GeneralDictionaryDefaultKernel208.Committed state plan)
    (valid : Models state model) : Holds plan model :=
  packet_holds plan model (committed.1.1 model valid)

theorem packet_with_sharing_iff (plan : Plan roles) (model : Assignment) :
    (GeneralNominalCenteredHeadMatStepPackets.Holds plan model ∧ Holds plan model) ↔
      GeneralNominalCenteredHeadMatStepPackets.Holds plan model :=
  ⟨And.left,fun held => ⟨held,packet_holds plan model held⟩⟩

theorem effect_with_sharing_iff (effect : Effect roles) (model : Assignment) :
    (effect.Holds model ∧ Holds effect.plan model) ↔ effect.Holds model :=
  ⟨And.left,fun held => ⟨held,effect_holds effect model held⟩⟩

theorem committed_with_sharing_iff (state : State roles) (plan : Plan roles) :
    (GeneralDictionaryDefaultKernel208.Committed state plan ∧
      ∀ model, Models state model → Holds plan model) ↔
    GeneralDictionaryDefaultKernel208.Committed state plan :=
  ⟨And.left,fun held => ⟨held,fun model valid => committed_holds state plan model held valid⟩⟩

theorem head_schema_pair {first last : Plan roles}
    (pair : GeneralNominalCenteredHeadMatPermutationPlans.Pair first last) :
    first.headSchema = last.headSchema := by
  obtain ⟨allocated,reserved,contextEq,_,_⟩ := pair.contexts.replace_form
  have headEq := pair.matched.declaration.head
  have centers := congrArg (fun site : Site roles => List.ofFn site.center) pair.matched.input
  simp only [Plan.headSchema,GeneralNominalInspection.queries,Declaration.normalHead,
    contextEq,GeneralNominalJournalPermutation.Metadata.replace,
    GeneralNominalMetadataEquivalence.replace,headEq,centers]

theorem holds_pair {first last : Plan roles}
    (pair : GeneralNominalCenteredHeadMatPermutationPlans.Pair first last) (model : Assignment) :
    Holds first model ↔ Holds last model := by
  simp only [Holds,equations,head_schema_pair pair]

theorem holds_rebase (plan : Plan roles)
    (order : GeneralRegistryReordering.Reorders plan.packet.registry registry)
    (pair : GeneralRegistryReordering.DeclarationReorders plan.packet.declaration declaration)
    (allocated reserved) (model : Assignment) :
    Holds (GeneralNominalCenteredPermutationCounterparts.rebase plan order pair allocated reserved) model ↔
      Holds plan model := by
  simp only [Holds,equations,GeneralNominalCenteredPermutationCounterparts.rebase,
    GeneralNominalCenteredPermutationPlans.head_schema,
    GeneralNominalCenteredPlanReordering.head_schema]

end Yulang.GeneralDictionaryHeadSharing220
