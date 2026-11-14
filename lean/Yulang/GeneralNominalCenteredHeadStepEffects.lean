import Yulang.GeneralNominalCenteredHeadOutputs
import Yulang.GeneralNominalCenteredTrace

set_option backward.isDefEq.respectTransparency false

/-! Recorded class equations have both their installation snapshot and a live
alias-class view. Enlarging a class retains its equations and named requests. -/
namespace Yulang.GeneralNominalCenteredHeadStepEffects
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

structure Effect (roles : Roles.RoleDecls) where
  registry : Registry
  snapshot : GeneralNominalCenteredSteps.State roles
  plan : Plan roles
  frame : Frame registry snapshot plan.packet.site.occurrence plan.packet.declaration.id plan
  unique : GeneralNominalCenteredHeadCandidates.Unique registry snapshot.erased.current.context
    plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children
  ready : EffectsReady snapshot plan.packet.site.occurrence plan

def Effect.Holds (effect : Effect roles) (model : Assignment) : Prop :=
  HeadEquations effect.plan model ∧
    OutputEquations effect.snapshot effect.plan.packet.site.occurrence effect.plan model

def Effect.Live (effect : Effect roles) (state : GeneralNominalCenteredSteps.State roles) (model : Assignment) : Prop :=
  OutputEquations state effect.plan.packet.site.occurrence effect.plan model

theorem Effect.chosen (effect : Effect roles) (valid : effect.Holds model) :
    ChosenClassEffects effect.registry effect.snapshot effect.plan.packet.site.occurrence
      effect.plan.packet.declaration.id model :=
  ⟨⟨_,effect.unique⟩,effect.plan,effect.frame,effect.ready,valid⟩

structure State (roles : Roles.RoleDecls) where
  core : GeneralNominalCenteredSteps.State roles
  effects : List (Effect roles) := []

def Models (state : State roles) (model : Assignment) : Prop :=
  GeneralNominalCenteredSteps.Models state.core model ∧
    ∀ effect ∈ state.effects, effect.Holds model ∧ effect.Live state.core model

/-- A separate interpretation obligation when later merging exposes requests
outside the explicit, supported schemas certified at installation. -/
def LiveEffectsReady (state : State roles) : Prop :=
  ∀ effect ∈ state.effects,
    EffectsReady state.core effect.plan.packet.site.occurrence effect.plan

def initial (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : State roles :=
  ⟨GeneralNominalCenteredSteps.initial context root,[]⟩

theorem initial_models : Models (initial context root) model ↔
    GeneralNominalCenteredSteps.Models (GeneralNominalCenteredSteps.initial context root) model := by
  simp [Models,initial]

theorem head_of_plan (valid : plan.Holds model) : HeadEquations plan model :=
  ⟨valid.2.1,fun name member => valid.2.2.1 name (Or.inl member),valid.2.2.2.1⟩

theorem requests_mono
    (growth : GeneralNominalSaturationSteps.Extends before.erased.current after.erased.current) :
    requests before root ⊆ requests after root := by
  intro output member
  obtain ⟨site,registered,alias,within⟩ := mem_requests_iff.mp member
  exact mem_requests_iff.mpr ⟨site,growth.sites site registered,
    GeneralNominalSaturationSteps.alias_monotone growth alias,within⟩

theorem requests_subset_of_sites_aliases
    (sites : before.erased.current.sites ⊆ after.erased.current.sites)
    (aliases : before.erased.current.aliases ⊆ after.erased.current.aliases) :
    requests before root ⊆ requests after root := by
  intro output member
  obtain ⟨site,present,related,within⟩ := mem_requests_iff.mp member
  have transport : ∀ first last, GeneralNominalSaturationState.Alias before.erased.current first last →
      GeneralNominalSaturationState.Alias after.erased.current first last := by
    intro first last related
    induction related with
    | refl => exact .refl _
    | edge member => exact .edge (aliases member)
    | symm _ ih => exact .symm ih
    | trans _ _ one two => exact .trans one two
  exact mem_requests_iff.mpr ⟨site,sites present,transport _ _ related,within⟩

private theorem generated_tests (snapshot : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (items : List GeneralNominalMaterialization.Request) :
    (GeneralNominalMaterialization.generated snapshot interpretation items).tests =
      items.flatMap (fun item => (GeneralNominalMaterialization.schema
        (GeneralNominalInspection.translate snapshot.constructors interpretation (GeneralDeclarationPatterns.normalize item.pattern))
        (.source item.target) item.mode).tests) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      change _ ++ (GeneralNominalMaterialization.generated snapshot interpretation rest).tests = _ ++ _
      rw [ih]
      rfl

private theorem generated_variables (snapshot : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (items : List GeneralNominalMaterialization.Request) :
    (GeneralNominalMaterialization.generated snapshot interpretation items).variables =
      items.flatMap (fun item => (GeneralNominalMaterialization.schema
        (GeneralNominalInspection.translate snapshot.constructors interpretation (GeneralDeclarationPatterns.normalize item.pattern))
        (.source item.target) item.mode).variables) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      change _ ++ (GeneralNominalMaterialization.generated snapshot interpretation rest).variables = _ ++ _
      rw [ih]
      rfl

private theorem flatMap_subset {first last : List α} (included : first ⊆ last) (f : α → List β) : first.flatMap f ⊆ last.flatMap f := by
  intro element member
  obtain ⟨item,present,within⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨item,included present,within⟩

theorem output_equations_restrict (included : requests before root ⊆ requests after root)
    (valid : OutputEquations after root plan model) : OutputEquations before root plan model := by
  refine ⟨?_,fun first one last two same => valid.2 first (included one) last (included two) same⟩
  have materialized := flatMap_subset included (fun output =>
    ((plan.packet.declaration.associated.find? fun equation => equation.name == output.name).toList).map fun equation =>
      (⟨equation.rhs,output.target,.actual⟩ : GeneralNominalMaterialization.Request))
  have tests := flatMap_subset materialized (fun item => (GeneralNominalMaterialization.schema
    (GeneralNominalInspection.translate plan.packet.context.state.constructors plan.packet.context.interpretation
      (GeneralDeclarationPatterns.normalize item.pattern)) (.source item.target) item.mode).tests)
  have variables := flatMap_subset materialized (fun item => (GeneralNominalMaterialization.schema
    (GeneralNominalInspection.translate plan.packet.context.state.constructors plan.packet.context.interpretation
      (GeneralDeclarationPatterns.normalize item.pattern)) (.source item.target) item.mode).variables)
  refine ⟨fun entry member => valid.1.1 entry ?_,fun entry member => valid.1.2 entry ?_⟩
  · simpa only [outputSchema,Plan.schema,generated_tests] using
      tests (by simpa only [outputSchema,Plan.schema,generated_tests] using member)
  · simpa only [outputSchema,Plan.schema,generated_variables] using
      variables (by simpa only [outputSchema,Plan.schema,generated_variables] using member)

theorem live_restrict (effect : Effect roles)
    (growth : GeneralNominalSaturationSteps.Extends before.erased.current after.erased.current)
    (valid : effect.Live after model) : effect.Live before model :=
  output_equations_restrict (requests_mono growth) valid

theorem recorded_effects (recorded : effect ∈ state.effects) (valid : Models state model) :
    ChosenClassEffects effect.registry effect.snapshot effect.plan.packet.site.occurrence
      effect.plan.packet.declaration.id model := effect.chosen (valid.2 effect recorded).1

theorem live_equal_outputs (recorded : effect ∈ state.effects) (valid : Models state model) :
    EqualOutputs state.core effect.plan.packet.site.occurrence model := (valid.2 effect recorded).2.2

end Yulang.GeneralNominalCenteredHeadStepEffects
