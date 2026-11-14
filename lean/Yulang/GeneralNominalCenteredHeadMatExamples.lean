import Yulang.GeneralNominalCenteredHeadMatPlans
import Yulang.GeneralNominalCenteredHeadMatExtension
import Yulang.GeneralNominalCenteredHeadWFJoinSource

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadMatExamples
open GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredHeadWFSource
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Observes)
open CommonNominalFullCarrier

theorem row_emission_complete :
    (GeneralNominalCenteredHeadMatPlans.emittedSchema GeneralNominalCenteredHeadWFJoinSource.plan).unknown = false :=
  GeneralNominalCenteredHeadMatPlans.emitted_complete
    (GeneralNominalCenteredHeadWFJoinSource.coverage.1 _ (List.mem_singleton_self _))

theorem row_translation : translate GeneralDeclarationExamples.constructors GeneralNominalExamples.interpretation
    (.join (.variant 0 (.app 2 [])) (.variant 1 (.app 2 []))) =
    some (.join (.variant 0 (.primitive (.scalar .int) [])) (.variant 1 (.primitive (.scalar .int) []))) := rfl

theorem open_record_translation (catalogue interpretation label payload tail) :
    translate catalogue interpretation (.record label (.var payload) (.var tail)) =
      some (.record label (.variable payload) (.variable tail)) := rfl

theorem record_shadow (variables mode label first last tail) :
    Equivalent (value variables mode (.record label first (.record label last tail)))
      (value variables mode (.record label first tail)) :=
  GeneralNominalCommonBridge.shadow _ _ _ _

theorem duplicate_tag_value (variables mode tag first last) :
    Equivalent (value variables mode (.join (.variant tag first) (.variant tag last)))
      (value variables mode (.variant tag (.join first last))) :=
  GeneralNominalCommonBridge.variant_merge _ _ _

namespace Rows
open GeneralNominalCenteredHeadWFJoinSource
open GeneralNominalCenteredHeadMatExtension

abbrev target := GeneralNominalAllocation.source snapshot registry root.identity
  (GeneralNominalAllocation.origin root.identity declaration.id 5 43 0)

theorem schema_exact : GeneralNominalCenteredHeadMatPlans.emittedSchema plan =
    ⟨[⟨target,.actual,.join (.variant 0 (.primitive (.scalar .int) []))
      (.variant 1 (.primitive (.scalar .int) []))⟩],false⟩ := by
  unfold GeneralNominalCenteredHeadMatPlans.emittedSchema GeneralNominalCenteredHeadMatSchemas.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canonical_declaration]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalCenteredHeadMatSchemas.emissionRequests,List.ofFn_zero,
    GeneralNominalCenteredHeadMatSchemas.generated,GeneralNominalCenteredHeadMatSchemas.materialize,
    GeneralNominalCenteredHeadMatSchemas.Schema.append,row_translation,
    GeneralDeclarationDemands.outputTarget,normalized_row,GeneralNominalAllocation.allocation,target,
    GeneralNominalDemandMerging.pointSite]

theorem source_extension : ∃ after : Assignment,
    GeneralNominalState.Models snapshot after ∧
      (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds
        (sources (fun _ name => name) after) after ∧
      ∀ identity ∈ GeneralNominalState.sources snapshot, after identity = model identity := by
  apply source_model_extension source_model
  · rw [schema_exact]
    simp
  · rw [schema_exact]
    intro equation member
    cases List.mem_singleton.mp member
    intro mode name used
    cases used
  · rw [schema_exact]
    intro equation member
    cases List.mem_singleton.mp member
    intro present
    exact GeneralNominalAllocation.source_initial_fresh snapshot registry root.identity _ _
      (source.below_seed target present) rfl

end Rows

namespace Defaults
open GeneralNominalCenteredHeadStepDefaults
open GeneralNominalCenteredHeadDefaultSchemas.Example (examplePlan request_eq)

theorem ready : Ready start.core root examplePlan := by
  apply ready_of_wf GeneralNominalCenteredHeadWFFixtures.defaults_coverage (List.mem_singleton_self _) rfl
  intro output member
  cases request_eq member
  exact ⟨some (.var 0),rfl⟩

theorem effects : ClassEffects start.core root examplePlan GeneralNominalExamples.model := by
  constructor
  · intro output member body found
    cases request_eq member
    have equal : body = .default 0 0 (.var 0) := (Option.some.inj found).symm
    subst body
    exact (positional_default examplePlan GeneralNominalExamples.model (0 : Fin 1)).mpr
      ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two _
    cases request_eq one
    cases request_eq two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem inhabited : GeneralNominalCenteredHeadStepEffects.Models start GeneralNominalExamples.model ∧
    ClassEffects start.core root examplePlan GeneralNominalExamples.model :=
  ⟨GeneralNominalCenteredHeadStepDefaults.inhabited,effects⟩

end Defaults

/-! The old payload query equates captures; it cannot be retained as the
semantics of an output union. This is a model-level comparison, not a trace. -/
def legacySchema (catalogue : Constructors) (interpretation : GeneralNominalInspection.Interpretation)
    (target tag first last : Nat) : GeneralNominalMaterialization.Schema :=
  GeneralNominalMaterialization.schema
    (GeneralNominalInspection.translate catalogue interpretation (.variant tag (.join (.var first) (.var last))))
    (.source target) .actual

theorem legacy_requires_equal (plan : Plan roles) (model : Assignment)
    (valid : plan.SchemaHolds (legacySchema catalogue interpretation target tag first last) model) :
    Equivalent (model (plan.binder first)).1 (model (plan.binder last)).1 := by
  let origin := Origin.structural (.source target) (.variant tag) 0
  have one : GeneralNominalOriginTerms.Same model origin (.source (plan.binder first)) := by
    apply valid.2 ⟨first,origin,.actual⟩
    simp [legacySchema,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,
      GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,GeneralCandidateInspection.plainNames,origin]
  have two : GeneralNominalOriginTerms.Same model origin (.source (plan.binder last)) := by
    apply valid.2 ⟨last,origin,.actual⟩
    simp [legacySchema,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,
      GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,GeneralCandidateInspection.plainNames,origin]
  have equal := GeneralNominalOriginTerms.same_trans (GeneralNominalOriginTerms.same_symm one) two
  exact equal.2.2 _ _ (.source _) (.source _)

def distinctModel : Assignment := fun identity =>
  (if identity = 0 then .base .int else if identity = 1 then .base .bool
   else variant 7 (.union (.base .int) (.base .bool)),Common.rowEmpty)

theorem distinct_inputs : ¬ Equivalent (distinctModel 0).1 (distinctModel 1).1 := by
  intro equal
  have impossible := equal.1 0
  change CommonNominalFullDemand.ProducerLe Common.rowLe
    (.base .int) (.base .bool) at impossible
  have different := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp impossible 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.base .bool) rfl
  cases different

theorem union_equation_inhabited :
    (GeneralNominalCenteredHeadMatSchemas.materialize GeneralDeclarationExamples.constructors GeneralNominalExamples.interpretation
      ⟨.variant 7 (.join (.var 0) (.var 1)),2,.actual⟩).Holds
        (fun _ name => (distinctModel name).1) distinctModel := by
  intro equation member
  have equal : equation = ⟨2,.actual,.variant 7 (.join (.variable 0) (.variable 1))⟩ := by
    exact List.mem_singleton.mp member
  subst equation
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem union_does_not_require_equal :
    ∃ model : Assignment,
      (GeneralNominalCenteredHeadMatSchemas.materialize GeneralDeclarationExamples.constructors GeneralNominalExamples.interpretation
        ⟨.variant 7 (.join (.var 0) (.var 1)),2,.actual⟩).Holds (fun _ name => (model name).1) model ∧
      ¬ Equivalent (model 0).1 (model 1).1 :=
  ⟨distinctModel,union_equation_inhabited,distinct_inputs⟩

end Yulang.GeneralNominalCenteredHeadMatExamples
