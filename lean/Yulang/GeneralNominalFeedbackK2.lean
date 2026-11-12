import Yulang.GeneralNominalFeedbackSites
import Yulang.GeneralNominalCycleBoundary

/-! A journal-normalized observation graph over finite source identities.
Structural edges come from the checked normalized view. Nominal edges observe
actual explicit arguments in every journal model; bodies supply no edges.
Equality transports edge endpoints but never constitutes an edge by itself.
A model witness prevents vacuous entailment from manufacturing a new cycle. -/
namespace Yulang.GeneralNominalFeedbackK2

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open CommonNominalFullCarrier
open GeneralNominalProjections (Observes)

abbrev Equal (state : State roles) (first last : Nat) :=
  GeneralNominalFeedbackSites.EndpointEqual state (first,last)

def Argument (state : State roles) (first last : Nat) : Prop :=
  ∃ name index, ∀ model, Models state model →
    ∃ actual, Observes model (.argument (.source first) name index) (.inl actual) ∧
      Equivalent actual (model last).1

def Structural (state : State roles) (first last : Nat) : Prop :=
  ∃ parent child, GeneralSourceK2.Child state.context.state.view parent child ∧
    Equal state first (state.context.state.base.source parent) ∧
    Equal state (state.context.state.base.source child) last

def Edge (state : State roles) (first last : Nat) : Prop :=
  first ∈ GeneralNominalState.sources state.context.state ∧
    last ∈ GeneralNominalState.sources state.context.state ∧
    (Structural state first last ∨ Argument state first last)

inductive Path (state : State roles) : Nat → Nat → Prop
  | nil (source) : Path state source source
  | cons : Edge state first middle → Path state middle last → Path state first last

def Cycle (state : State roles) (source : Nat) : Prop :=
  ∃ next, Edge state source next ∧ Path state next source

def RecursAt (state : State roles) (source : Nat) : Prop :=
  Cycle state source ∧ ∃ model, Models state model

def RootK2 (state : State roles) (root : Occurrence roles) : Prop :=
  GeneralNominalCycleK2.RootK2 state.context.state root.demand ∨
    (GeneralNominalState.Linked state.context.state root.demand ∧
      ¬ GeneralNominalState.RootPending state.context.state root.demand ∧
      ∃ index, RecursAt state (root.demand.arguments index).1)

def CandidateK2 (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  GeneralNominalCycleK2.CandidateK2 registry state.context root ∨
    (¬ GeneralNominalState.RootPending state.context.state root.demand ∧
      ∃ declaration ∈ registry.declarations,
        ∃ _checked : DeclarationChecked registry.constructors roles declaration,
          declaration.role = root.demand.role ∧
          GeneralNominalRecursiveCandidates.HeadReady registry state.context root declaration ∧
          ∃ bounds, GeneralNominalRecursiveCandidates.arguments state.context root = some bounds ∧
            ∃ visited ∈ (GeneralNominalRecursiveCandidates.report state.context declaration bounds).inspected,
              RecursAt state (state.context.state.base.source visited.1))

def fields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (GeneralNominalCycleBoundary.vocabulary roles) :=
  { GeneralNominalCycleBoundary.localFields roles with
    RootK2 := fun _ state => RootK2 state
    CandidateK2 := CandidateK2 }

abbrev Local {roles : Roles.RoleDecls} (registry : Registry) (state : State roles) :=
  GeneralNominalLocalBoundary.Local (fields roles) registry state

theorem root_ready (rejected : RootK2 state root) :
    ¬ GeneralNominalState.RootPending state.context.state root.demand := by
  rcases rejected with old | current
  · exact old.2.1
  · exact current.2.1

theorem candidate_ready (rejected : CandidateK2 registry state root) :
    ¬ GeneralNominalState.RootPending state.context.state root.demand := by
  rcases rejected with old | current
  · exact old.1
  · exact current.1

theorem root_rejected (registry : Registry) (state : State roles) (root : Occurrence roles)
    (cycle : RootK2 state root) : Local registry state root .rejected :=
  .rejected ⟨root_ready cycle,Or.inl cycle⟩

theorem candidate_rejected (registry : Registry) (state : State roles) (root : Occurrence roles)
    (cycle : CandidateK2 registry state root) : Local registry state root .rejected :=
  .rejected ⟨candidate_ready cycle,Or.inr (Or.inl cycle)⟩

theorem selected_legacy (selected : Local registry state root (.selected key children)) :
    GeneralNominalCycleK2.Local registry state.context root (.selected key children) := by
  cases selected with
  | selected safe unique =>
      exact .selected ⟨safe.1,fun old => safe.2.1 (Or.inl old),
        fun old => safe.2.2.1 (Or.inl old),safe.2.2.2⟩ unique

theorem local_total (registry : Registry) (checked : Checked registry) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier :=
  GeneralNominalLocalBoundary.local_total
    (fun key first last one two => GeneralNominalRecursiveCandidates.survivor_children_functional registry checked
      state.context root key first last one two)

theorem local_functional (one : Local registry state root first) (two : Local registry state root last) : first = last :=
  GeneralNominalLocalBoundary.local_functional one two

theorem equal_refl (state : State roles) (source : Nat) : Equal state source source :=
  fun _ _ => ⟨subtype_refl _,subtype_refl _⟩

theorem equal_trans (one : Equal state first middle) (two : Equal state middle last) : Equal state first last := by
  intro model valid
  exact ⟨subtype_trans (one model valid).1 (two model valid).1,
    subtype_trans (two model valid).2 (one model valid).2⟩

theorem actual_argument (state : State roles) (parent child : Fin state.context.state.base.slots)
    (old : GeneralNominalMixedRecurrence.ActualArgument state.context.state parent child) :
    Argument state (state.context.state.base.source parent) (state.context.state.base.source child) := by
  obtain ⟨descriptor,_,index,observed⟩ := old
  exact ⟨descriptor.declaration.name,index,fun model valid => observed model valid.1⟩

theorem argument_equal_target (argument : Argument state first middle) (equal : Equal state middle last) :
    Argument state first last := by
  obtain ⟨name,index,observed⟩ := argument
  refine ⟨name,index,?_⟩
  intro model valid
  obtain ⟨actual,seen,eq⟩ := observed model valid
  exact ⟨actual,seen,subtype_trans eq.1 (equal model valid).1,subtype_trans (equal model valid).2 eq.2⟩

theorem endpoint_argument (state : State roles) (parent lower upper : Fin state.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.context.state.base.slots)
    (recorded : state.context.state.nominals parent = some descriptor) (index : Nat)
    (parameter : descriptor.arguments[index]? = some (.type (lower,upper)))
    (equal : Equal state (state.context.state.base.source lower) (state.context.state.base.source upper)) :
    Argument state (state.context.state.base.source parent) (state.context.state.base.source lower) := by
  refine ⟨descriptor.declaration.name,index,?_⟩
  intro model valid
  obtain ⟨value,seen,fits⟩ := GeneralNominalProjections.parameter_binding_valid state.context.state model valid.1
    parent descriptor recorded index 0 (.type (lower,upper)) parameter
  cases value with
  | inr => cases fits
  | inl actual => exact ⟨actual,seen,subtype_trans fits.2 (equal model valid).2,fits.1⟩

theorem self_argument_cycle (state : State roles) (source : Nat)
    (supported : source ∈ GeneralNominalState.sources state.context.state)
    (argument : Argument state source source) (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models state model) : RecursAt state source :=
  ⟨⟨source,⟨supported,supported,Or.inr argument⟩,.nil source⟩,model,valid⟩

theorem root_self_argument (state : State roles) (root : Occurrence roles)
    (linked : GeneralNominalState.Linked state.context.state root.demand)
    (ready : ¬ GeneralNominalState.RootPending state.context.state root.demand)
    (index : Fin (roles root.demand.role).arity)
    (argument : Argument state (root.demand.arguments index).1 (root.demand.arguments index).1)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) : RootK2 state root :=
  Or.inr ⟨linked,ready,index,self_argument_cycle state _ (linked.1 index).1 argument model valid⟩

theorem argument_sound (argument : Argument state first last) (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models state model) : ∃ name index actual,
      Observes model (.argument (.source first) name index) (.inl actual) ∧ Equivalent actual (model last).1 := by
  obtain ⟨name,index,all⟩ := argument
  obtain ⟨actual,observed,equal⟩ := all model valid
  exact ⟨name,index,actual,observed,equal⟩

theorem argument_model_restriction {before after : State roles}
    (restriction : ∀ model, Models after model → Models before model)
    (argument : Argument before first last) : Argument after first last := by
  obtain ⟨name,index,all⟩ := argument
  exact ⟨name,index,fun model valid => all model (restriction model valid)⟩

end Yulang.GeneralNominalFeedbackK2
