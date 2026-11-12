import Yulang.GeneralNominalRecursiveBoundary

/-! Cycle-based K2 on normalized structural children and actual nominal
arguments. Nominal bodies never add an edge. The root need not be structural.
Structural children and point nominal arguments give direct graph certificates.
A model witness prevents vacuous semantic argument edges from creating additional
cycles. Recognized legacy recurrence observations without such a certificate
defer; general observation coverage is a separate obligation. -/
namespace Yulang.GeneralNominalCycleK2

open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates

abbrev Edge := GeneralNominalMixedRecurrence.Edge
abbrev Path := GeneralNominalMixedRecurrence.Path
abbrev Cycle := GeneralNominalMixedRecurrence.Cycle

/-- Point arguments are graph identities even when the ordinary store is
inconsistent. Only semantic, nonpoint edges need a model witness. -/
def DirectArgument (state : GeneralNominalState.State) (parent child : Fin state.base.slots) : Prop :=
  ∃ descriptor : GeneralNominalState.Descriptor state.base.slots, state.nominals parent = some descriptor ∧
    ∃ index : Nat, descriptor.arguments[index]? = some (GeneralNominalState.Parameter.type (child,child))

def DirectEdge (state : GeneralNominalState.State) (parent child : Fin state.base.slots) : Prop :=
  GeneralSourceK2.Child state.view parent child ∨ DirectArgument state parent child

inductive DirectPath (state : GeneralNominalState.State) : Fin state.base.slots → Fin state.base.slots → Prop
  | nil (root) : DirectPath state root root
  | cons : DirectEdge state first middle → DirectPath state middle last → DirectPath state first last

def DirectCycle (state : GeneralNominalState.State) (root : Fin state.base.slots) : Prop :=
  ∃ child, DirectEdge state root child ∧ DirectPath state child root

theorem direct_edge_sound (edge : DirectEdge state parent child) : Edge state parent child := by
  rcases edge with structural | ⟨descriptor,recorded,index,parameter⟩
  · exact Or.inl structural
  · exact Or.inr (GeneralNominalMixedRecurrence.point_argument_edge state parent child descriptor recorded index parameter)

theorem direct_path_sound (path : DirectPath state first last) : Path state first last := by
  induction path with
  | nil => exact .nil _
  | cons edge _ ih => exact .cons (direct_edge_sound edge) ih

theorem structural_path_direct {state : GeneralNominalState.State} {first last : Fin state.base.slots} (path : GeneralSourceK2.Path state.view first last) : DirectPath state first last := by
  induction path with
  | nil => exact .nil _
  | cons edge _ ih => exact .cons (Or.inl edge) ih

def RecursAt (state : GeneralNominalState.State) (root : Fin state.base.slots) : Prop :=
  DirectCycle state root ∨ (Cycle state root ∧ ∃ model, GeneralNominalState.Models state model)

def RootK2 (state : GeneralNominalState.State) (demand : GeneralSourceState.Demand roles) : Prop :=
  GeneralNominalState.Linked state demand ∧ ¬ GeneralNominalState.RootPending state demand ∧
    ∃ index slot, state.base.source slot = (demand.arguments index).1 ∧ RecursAt state slot

def CandidateK2 (registry : Registry) (context : Context) (root : Occurrence roles) : Prop :=
  ¬ GeneralNominalState.RootPending context.state root.demand ∧
    ∃ declaration ∈ registry.declarations, ∃ _checked : DeclarationChecked registry.constructors roles declaration,
      declaration.role = root.demand.role ∧ HeadReady registry context root declaration ∧
      ∃ bounds, arguments context root = some bounds ∧
        ∃ visited ∈ (report context declaration bounds).inspected, RecursAt context.state visited.1

/-- Prior structural equivalence coverage is retained as a deferred observation
until its quotient-cycle correspondence is available for the new graph. -/
def InspectionPending (registry : Registry) (context : Context) (root : Occurrence roles) : Prop :=
  GeneralNominalRecursiveCandidates.InspectionPending registry context root ∨
    (¬ GeneralNominalState.RootPending context.state root.demand ∧
      ((GeneralNominalMixedRecurrence.RootK2 context.state root.demand ∧ ¬ RootK2 context.state root.demand) ∨
       (GeneralNominalRecursiveCandidates.CandidateK2 registry context root ∧ ¬ CandidateK2 registry context root)))

def fields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (GeneralNominalCandidates.vocabulary roles) :=
  { GeneralNominalLocalBoundary.recursiveFields roles with
    RootK2 := fun _ context root => RootK2 context.state root.demand
    CandidateK2 := CandidateK2
    InspectionPending := InspectionPending }

abbrev Local {roles : Roles.RoleDecls} (registry : Registry) (context : Context) := GeneralNominalLocalBoundary.Local (fields roles) registry context

theorem cycle_rejects (state : GeneralNominalState.State) (demand : GeneralSourceState.Demand roles)
    (linked : GeneralNominalState.Linked state demand) (ready : ¬ GeneralNominalState.RootPending state demand)
    (index : Fin (roles demand.role).arity) (slot : Fin state.base.slots)
    (source : state.base.source slot = (demand.arguments index).1) (cycle : Cycle state slot)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model) : RootK2 state demand :=
  ⟨linked,ready,index,slot,source,Or.inr ⟨cycle,model,valid⟩⟩

theorem recurs_cycle (state : GeneralNominalState.State) (root : Fin state.base.slots)
    (cycle : RecursAt state root) : Cycle state root := by
  rcases cycle with ⟨next,edge,path⟩ | ⟨cycle,_⟩
  · exact ⟨next,direct_edge_sound edge,direct_path_sound path⟩
  · exact cycle

theorem recurs_iff_cycle (state : GeneralNominalState.State) (root : Fin state.base.slots)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model) :
    RecursAt state root ↔ Cycle state root :=
  ⟨recurs_cycle state root,fun cycle => Or.inr ⟨cycle,model,valid⟩⟩

theorem structural_cycle_rejects (state : GeneralNominalState.State) (demand : GeneralSourceState.Demand roles)
    (linked : GeneralNominalState.Linked state demand) (ready : ¬ GeneralNominalState.RootPending state demand)
    (index : Fin (roles demand.role).arity) (slot : Fin state.base.slots)
    (source : state.base.source slot = (demand.arguments index).1) (cycle : GeneralSourceK2.Cycle state.view slot) :
    RootK2 state demand := by
  obtain ⟨child,edge,path⟩ := cycle
  exact ⟨linked,ready,index,slot,source,Or.inl ⟨child,Or.inl edge,structural_path_direct path⟩⟩

theorem direct_cycle_rejects (state : GeneralNominalState.State) (demand : GeneralSourceState.Demand roles)
    (linked : GeneralNominalState.Linked state demand) (ready : ¬ GeneralNominalState.RootPending state demand)
    (index : Fin (roles demand.role).arity) (slot : Fin state.base.slots)
    (source : state.base.source slot = (demand.arguments index).1) (cycle : DirectCycle state slot) :
    RootK2 state demand := ⟨linked,ready,index,slot,source,Or.inl cycle⟩

theorem alias_observation_defers (registry : Registry) (context : Context) (root : Occurrence roles)
    (old : GeneralNominalMixedRecurrence.RootK2 context.state root.demand)
    (rootUnknown : ¬ RootK2 context.state root.demand) (candidateUnknown : ¬ CandidateK2 registry context root) :
    Local registry context root .pending :=
  .inspectionPending old.2.1 (Or.inr ⟨old.2.1,Or.inl ⟨old,rootUnknown⟩⟩) rootUnknown candidateUnknown

theorem pending_excludes_K2 (state : GeneralNominalState.State) (demand : GeneralSourceState.Demand roles)
    (pending : GeneralNominalState.RootPending state demand) : ¬ RootK2 state demand := fun rejected => rejected.2.1 pending

theorem candidateK2_not_pending (registry : Registry) (context : Context) (root : Occurrence roles)
    (rejected : CandidateK2 registry context root) : ¬ GeneralNominalState.RootPending context.state root.demand := rejected.1

theorem root_rejected (registry : Registry) (context : Context) (root : Occurrence roles)
    (cycle : RootK2 context.state root.demand) : Local registry context root .rejected :=
  .rejected ⟨cycle.2.1,Or.inl cycle⟩

theorem prepared_cycle (registry : Registry) (context : Context) (root : Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending context.state root.demand)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (role : declaration.role = root.demand.role) (prepared : Prepared registry context root declaration checked)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) (located : arguments context root = some bounds)
    (visited : GeneralNominalInspection.Bounds context.state) (member : visited ∈ (report context declaration bounds).inspected)
    (cycle : RecursAt context.state visited.1) : CandidateK2 registry context root := by
  refine ⟨ready,declaration,visible,checked,role,?_,bounds,located,visited,member,cycle⟩
  obtain ⟨metadata,linked,fresh,other,found,finished,_,model,models⟩ := prepared
  exact ⟨metadata,linked,fresh,other,found,finished,model,models.1,models.2.1⟩

theorem candidate_rejected (registry : Registry) (context : Context) (root : Occurrence roles)
    (cycle : CandidateK2 registry context root) : Local registry context root .rejected :=
  .rejected ⟨cycle.1,Or.inr (Or.inl cycle)⟩

theorem selected_not_K2 (selected : Local registry context (root : Occurrence roles) (.selected key children)) :
    ¬ RootK2 context.state root.demand ∧ ¬ CandidateK2 registry context root := by
  cases selected with | selected safe _ => exact ⟨safe.2.1,safe.2.2.1⟩

theorem local_total (registry : Registry) (checked : Checked registry) (context : Context) (root : Occurrence roles) :
    ∃ frontier, Local registry context root frontier :=
  GeneralNominalLocalBoundary.local_total
    (fun key first last one two => survivor_children_functional registry checked context root key first last one two)

theorem local_functional (first : Local registry context (root : Occurrence roles) a)
    (last : Local registry context root b) : a = b := GeneralNominalLocalBoundary.local_functional first last

theorem rejected_accessible (rejected : Local registry context (root : Occurrence roles) .rejected) :
    Acc (CommonRoleOutermostResolver.Child (Local registry context)) root := by
  refine Acc.intro root ?_
  rintro child ⟨key,children,selected,_⟩
  have impossible := local_functional rejected selected
  cases impossible

theorem rootK2_accessible (registry : Registry) (context : Context) (root : Occurrence roles)
    (cycle : RootK2 context.state root.demand) :
    Acc (CommonRoleOutermostResolver.Child (Local registry context)) root := rejected_accessible (root_rejected _ _ _ cycle)

end Yulang.GeneralNominalCycleK2
