import Yulang.GeneralNominalCenteredHeadCandidates

set_option backward.isDefEq.respectTransparency false

/-! Alias classes retain the union of named requests, including one-sided
requests. Complete explicit output schemas are checked after head choice.
Missing schema coverage is distinct from an inconsistent output equation. -/
namespace Yulang.GeneralNominalCenteredHeadOutputs
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredHeadCandidates
open GeneralNominalSaturationState (Alias)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

noncomputable def requests (state : State roles) (root : Occurrence roles) : List GeneralSourceState.Output := by
  classical
  exact (state.erased.current.sites.filter fun site =>
    Alias state.erased.current root.identity site.occurrence.identity).flatMap fun site => site.occurrence.demand.outputs

theorem mem_requests_iff : output ∈ requests state root ↔
    ∃ site ∈ state.erased.current.sites, Alias state.erased.current root.identity site.occurrence.identity ∧
      output ∈ site.occurrence.demand.outputs := by
  classical
  simp only [requests,List.mem_flatMap,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨site,⟨member,alias⟩,within⟩; exact ⟨site,member,alias,within⟩
  · rintro ⟨site,member,alias,within⟩; exact ⟨site,⟨member,alias⟩,within⟩

theorem request_retained (site : GeneralNominalDemandMerging.Site roles)
    (member : site ∈ state.erased.current.sites)
    (alias : Alias state.erased.current root.identity site.occurrence.identity)
    (within : output ∈ site.occurrence.demand.outputs) : output ∈ requests state root :=
  mem_requests_iff.mpr ⟨site,member,alias,within⟩

theorem same_class_requests (alias : Alias state.erased.current first.identity last.identity) :
    output ∈ requests state first ↔ output ∈ requests state last := by
  simp only [mem_requests_iff]
  constructor
  · rintro ⟨site,member,related,within⟩
    exact ⟨site,member,.trans (.symm alias) related,within⟩
  · rintro ⟨site,member,related,within⟩
    exact ⟨site,member,.trans alias related,within⟩

theorem one_sided_request (state : State roles) (first last : Site roles)
    (_empty : first.occurrence.demand.outputs = [])
    (member : last.observed ∈ state.erased.current.sites)
    (within : output ∈ last.occurrence.demand.outputs) (support) :
    output ∈ requests (merge state first last support) first.occurrence :=
  request_retained last.observed member (.edge (List.mem_cons_self ..)) within

structure Frame (registry : Registry) (state : State roles) (root : Occurrence roles)
    (key : Nat) (plan : Plan roles) : Prop where
  registry_eq : plan.packet.registry = registry
  context_eq : plan.packet.context = state.erased.current.context
  occurrence_eq : plan.packet.site.occurrence = root
  key_eq : plan.packet.declaration.id = key
  raw_recorded : plan.packet.site ∈ state.erased.current.sites
  center_recorded : plan.input ∈ state.sites
  visible : plan.packet.declaration ∈ registry.declarations
  role_eq : plan.packet.declaration.role = root.demand.role
  located : GeneralNominalRecursiveCandidates.arguments plan.packet.context (inputs root) = some plan.packet.bounds
  prepared : Prepared registry state.erased.current.context root plan.packet.declaration

noncomputable def outputSchema (state : State roles) (root : Occurrence roles) (plan : Plan roles) :
    GeneralNominalMaterialization.Schema :=
  plan.schema ((requests state root).flatMap fun output =>
    ((plan.packet.declaration.associated.find? fun equation => equation.name == output.name).toList).map fun equation =>
      ⟨equation.rhs,output.target,.actual⟩)

/-- Coverage is separate from head applicability. Role-default evaluation and
unsupported translations must be supplied before this explicit-schema API can
certify their output conflicts. -/
def EffectsReady (state : State roles) (root : Occurrence roles) (plan : Plan roles) : Prop :=
  (∀ output ∈ requests state root, ∃ equation ∈ plan.packet.declaration.associated, equation.name = output.name) ∧
    (outputSchema state root plan).unknown = false

def HeadEquations (plan : Plan roles) (model : Assignment) : Prop :=
  plan.input.Holds model ∧
    (∀ name ∈ plan.packet.declaration.inputNames, GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name) (model (plan.binder name)).1) ∧
    plan.SchemaHolds plan.headSchema model

def EqualOutputs (state : State roles) (root : Occurrence roles) (model : Assignment) : Prop :=
  ∀ first ∈ requests state root, ∀ last ∈ requests state root, first.name = last.name →
    CommonNominalFullCarrier.Equivalent (model first.target).1 (model last.target).1

def OutputEquations (state : State roles) (root : Occurrence roles) (plan : Plan roles) (model : Assignment) : Prop :=
  plan.SchemaHolds (outputSchema state root plan) model ∧ EqualOutputs state root model

def ChosenHead (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat)
    (model : Assignment) : Prop :=
  (∃ children, Unique registry state.erased.current.context root key children) ∧
    ∃ plan, Frame registry state root key plan ∧ EffectsReady state root plan ∧ HeadEquations plan model

def ChosenClassEffects (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat)
    (model : Assignment) : Prop :=
  (∃ children, Unique registry state.erased.current.context root key children) ∧
    ∃ plan, Frame registry state root key plan ∧ EffectsReady state root plan ∧
      HeadEquations plan model ∧ OutputEquations state root plan model

def PreexistingInconsistency (state : State roles) : Prop := ¬ ∃ model, Models state model

/-- The baseline contains a feasible chosen head; only its output extension
fails. Unsatisfiability ranges over every eligible frame, not one arbitrary
representative. No historical installation is required. -/
def OutputConflict (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  (∃ model, Models state model ∧ ChosenHead registry state root key model) ∧
    ¬ ∃ model, Models state model ∧ ChosenClassEffects registry state root key model

theorem effects_head (effects : ChosenClassEffects registry state root key model) :
    ChosenHead registry state root key model := by
  obtain ⟨unique,plan,frame,ready,head,_⟩ := effects
  exact ⟨unique,plan,frame,ready,head⟩

theorem conflict_inhabited (conflict : OutputConflict registry state root key) : ∃ model, Models state model := by
  obtain ⟨model,valid,_⟩ := conflict.1
  exact ⟨model,valid⟩

theorem conflict_not_preexisting (conflict : OutputConflict registry state root key) : ¬ PreexistingInconsistency state :=
  fun absent => absent (conflict_inhabited conflict)

theorem conflict_unique (conflict : OutputConflict registry state root key) :
    ∃ children, Unique registry state.erased.current.context root key children := by
  obtain ⟨_,_,unique,_⟩ := conflict.1
  exact unique

theorem conflict_excludes_ambiguity (conflict : OutputConflict registry state root key)
    (one : Survivor registry state.erased.current.context root a xs)
    (two : Survivor registry state.erased.current.context root b ys) (different : a ≠ b) : False := by
  obtain ⟨children,unique⟩ := conflict_unique conflict
  exact unique_excludes_two unique one two different

theorem effects_equal_outputs (effects : ChosenClassEffects registry state root key model) : EqualOutputs state root model := by
  obtain ⟨_,_,_,_,_,outputs⟩ := effects
  exact outputs.2

theorem no_conflict_iff_effects
    (baseline : ∃ model, Models state model ∧ ChosenHead registry state root key model) :
    ¬ OutputConflict registry state root key ↔
      ∃ model, Models state model ∧ ChosenClassEffects registry state root key model := by
  classical
  constructor
  · intro clear
    by_cases effects : ∃ model, Models state model ∧ ChosenClassEffects registry state root key model
    · exact effects
    · exact False.elim (clear ⟨baseline,effects⟩)
  · exact fun effects conflict => conflict.2 effects

theorem empty_outputs_no_conflict (empty : requests state root = []) : ¬ OutputConflict registry state root key := by
  rintro ⟨⟨model,valid,unique,plan,frame,ready,head⟩,impossible⟩
  apply impossible
  refine ⟨model,valid,unique,plan,frame,ready,head,?_,?_⟩
  · simp [outputSchema,empty,Plan.schema,GeneralNominalMaterialization.generated,Plan.SchemaHolds]
  · intro first member; simp [empty] at member

/-- A later installation bridge must establish universal coverage, not merely
existence of a compatible prospective assignment. -/
def OutputEffectCoverage (registry : Registry) (before after : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  ∀ model, Models after model → ChosenClassEffects registry before root key model

end Yulang.GeneralNominalCenteredHeadOutputs
