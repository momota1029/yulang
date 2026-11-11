import Yulang.GeneralNominalInspection
import Yulang.GeneralCandidateBoundaryParts

/-! Candidate alternatives over the full nominal model and computed frames.
Consistency is an independent mathematical property of propagated ordinary
constraints, not a substitution enumeration or an executor result. An effective
complete full-carrier solver remains separate. Children are emitted, never
resolved here. Unsupported materialization requests remain pending. -/
namespace Yulang.GeneralNominalCandidates

open GeneralDeclarations
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalInspection

structure Context where
  state : GeneralNominalState.State
  interpretation : Interpretation

def arguments (context : Context) (root : Occurrence roles) :
    Option (List (Bounds context.state)) :=
  GeneralCandidateBoundaryParts.locate context.state.base (List.ofFn root.demand.arguments)

def report (context : Context) (declaration : Declaration) (bounds : List (Bounds context.state)) :
    Report context.state :=
  let result := inspectMany context.state (queries context.state context.interpretation declaration) bounds
  { result with inspected := bounds ++ result.inspected }

def privateState (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (bounds : List (Bounds context.state)) : GeneralNominalState.State :=
  GeneralNominalAllocation.propagate context.state registry root.identity declaration
    (bindings context.state (report context declaration bounds))

def Consistent (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (bounds : List (Bounds context.state)) : Prop :=
  ∃ model, GeneralNominalState.Models (privateState registry context root declaration bounds) model

def HeadReady (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) : Prop :=
  ∃ bounds, arguments context root = some bounds ∧ Finished (report context declaration bounds) ∧ Covered context.state (report context declaration bounds) ∧
    Consistent registry context root declaration bounds

def Metadata (registry : Registry) (context : Context) : Prop :=
  registry.constructors = context.state.constructors ∧
    GeneralCandidateInspection.PrimitivesCompatible registry.constructors context.interpretation.primitives

def EmissionsReady (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (Bounds context.state)) : Prop :=
  root.demand.outputs = [] ∧
  (∀ emission ∈ GeneralCanonicalChildOrder.canonicalEmit root.identity declaration checked
      (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
        (bindings context.state (report context declaration bounds)))
      (GeneralNominalAllocation.allocation context.state registry root.identity declaration.id),
    (∀ input ∈ emission.inputs, ∃ name,
      GeneralDeclarationPatterns.normalize input.pattern = .var name ∧
      name ∈ (bindings context.state (report context declaration bounds)).map Prod.fst) ∧
    (∀ output ∈ emission.outputs, ∃ name ∈ declaration.outputNames,
      GeneralDeclarationPatterns.normalize output.pattern = .var name)) ∧
  ∀ child ∈ GeneralNominalAllocation.children context.state registry root declaration checked
      (bindings context.state (report context declaration bounds)),
    GeneralNominalState.Linked (privateState registry context root declaration bounds) child.demand

def Prepared (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration) : Prop :=
  Metadata registry context ∧ GeneralNominalState.Linked context.state root.demand ∧
    GeneralNominalAllocation.Fresh context.state registry root.identity ∧
    ∃ bounds, arguments context root = some bounds ∧ Finished (report context declaration bounds) ∧ Covered context.state (report context declaration bounds) ∧
      Consistent registry context root declaration bounds ∧ EmissionsReady registry context root declaration checked bounds

def Survivor (registry : Registry) (context : Context) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) : Prop :=
  ¬ GeneralNominalState.RootPending context.state root.demand ∧
  ∃ declaration ∈ registry.declarations, ∃ checked : DeclarationChecked registry.constructors roles declaration,
    declaration.id = key ∧ declaration.role = root.demand.role ∧
    ∃ bounds, arguments context root = some bounds ∧ Prepared registry context root declaration checked ∧
      children = GeneralNominalAllocation.children context.state registry root declaration checked
        (bindings context.state (report context declaration bounds))

def Failed (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) : Prop :=
  GeneralNominalAllocation.Fresh context.state registry root.identity ∧
  Metadata registry context ∧ ∃ bounds, arguments context root = some bounds ∧
    (report context declaration bounds).blocked = [] ∧ (report context declaration bounds).arity = [] ∧
    Covered context.state (report context declaration bounds) ∧
    ((report context declaration bounds).conflicts ≠ [] ∨ ¬ Consistent registry context root declaration bounds)

def InspectionPending (registry : Registry) (context : Context) (root : Occurrence roles) : Prop :=
  ¬ GeneralNominalState.RootPending context.state root.demand ∧
  ∃ declaration ∈ registry.declarations, ∃ checked : DeclarationChecked registry.constructors roles declaration,
    declaration.role = root.demand.role ∧ ¬ Failed registry context root declaration ∧
      ¬ Prepared registry context root declaration checked

def CandidateK2 (registry : Registry) (context : Context) (root : Occurrence roles) : Prop :=
  ¬ GeneralNominalState.RootPending context.state root.demand ∧ Metadata registry context ∧
    GeneralNominalState.Linked context.state root.demand ∧
  ∃ declaration ∈ registry.declarations, ∃ _checked : DeclarationChecked registry.constructors roles declaration,
    declaration.role = root.demand.role ∧ HeadReady registry context root declaration ∧
    ∃ bounds, arguments context root = some bounds ∧ NeedsK2 context.state (report context declaration bounds)

theorem survivor_interval_sound (registry : Registry) (context : Context) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) (survivor : Survivor registry context root key children) :
    ∃ declaration ∈ registry.declarations, declaration.id = key ∧
      ∃ bounds, arguments context root = some bounds ∧
        ∀ model, GeneralNominalState.Models (privateState registry context root declaration bounds) model →
          GeneralNominalState.Models context.state model ∧
          GeneralNominalAllocation.Compatible (bindings context.state (report context declaration bounds)) model := by
  obtain ⟨_, declaration, visible, _, same, _, bounds, located, _, _⟩ := survivor
  exact ⟨declaration, visible, same, bounds, located, fun model valid =>
    ⟨((GeneralNominalAllocation.propagate_models ..).mp valid).1,
      ((GeneralNominalAllocation.propagate_models ..).mp valid).2.1⟩⟩

theorem survivor_children_functional (registry : Registry) (checked : Checked registry)
    (context : Context) (root : Occurrence roles) (key : Nat) (first last : List (Occurrence roles))
    (one : Survivor registry context root key first) (two : Survivor registry context root key last) : first = last := by
  obtain ⟨_, a, av, ac, ak, _, ab, al, _, ae⟩ := one
  obtain ⟨_, b, bv, bc, bk, _, bb, bl, _, be⟩ := two
  have same := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked a b av bv (ak.trans bk.symm)
  subst b
  have bounds := Option.some.inj (al.symm.trans bl)
  subst bb
  exact ae.trans be.symm

theorem pending_excludes_candidateK2 (registry : Registry) (context : Context) (root : Occurrence roles)
    (pending : GeneralNominalState.RootPending context.state root.demand) : ¬ CandidateK2 registry context root :=
  fun cycle => cycle.1 pending

theorem candidateK2_recurrence (registry : Registry) (context : Context) (root : Occurrence roles)
    (cycle : CandidateK2 registry context root) :
    ∃ declaration ∈ registry.declarations, ∃ bounds, arguments context root = some bounds ∧
      ∃ visited ∈ (report context declaration bounds).inspected,
        GeneralSourceK2.RecursAt context.state.view visited.1 := by
  obtain ⟨_, _, _, declaration, visible, _, _, _, bounds, located, recursive⟩ := cycle
  exact ⟨declaration, visible, bounds, located, inspected_recurrence _ _ recursive⟩

theorem conservative_deferral (registry : Registry) (context : Context) (root : Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending context.state root.demand)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (sameRole : declaration.role = root.demand.role) (failure : ¬ Failed registry context root declaration)
    (blocked : ¬ Prepared registry context root declaration checked) : InspectionPending registry context root :=
  ⟨ready, declaration, visible, checked, sameRole, failure, blocked⟩

theorem allocation_collision_defers (registry : Registry) (context : Context) (root : Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending context.state root.demand)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (sameRole : declaration.role = root.demand.role)
    (collision : ¬ GeneralNominalAllocation.Fresh context.state registry root.identity) :
    InspectionPending registry context root := by
  apply conservative_deferral registry context root ready declaration visible checked sameRole
  · exact fun failure => collision failure.1
  · exact fun prepared => collision prepared.2.2.1

theorem coverage_defers (registry : Registry) (context : Context) (root : Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending context.state root.demand)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (sameRole : declaration.role = root.demand.role) (bounds : List (Bounds context.state))
    (located : arguments context root = some bounds)
    (unsupported : ¬ Covered context.state (report context declaration bounds)) :
    InspectionPending registry context root := by
  apply conservative_deferral registry context root ready declaration visible checked sameRole
  · rintro ⟨_,_,other,found,_,_,covered,_⟩
    have same := Option.some.inj (located.symm.trans found)
    subst other
    exact unsupported covered
  · rintro ⟨_,_,_,other,found,_,covered,_⟩
    have same := Option.some.inj (located.symm.trans found)
    subst other
    exact unsupported covered

def vocabulary (roles : Roles.RoleDecls) : B4Target.Vocabulary where
  Registry := Registry
  State := Context
  Demand := Occurrence roles
  Model := GeneralNominalCommonBridge.Assignment

theorem local_total_of_extension (roles : Roles.RoleDecls)
    (boundary : B4Target.SourceBoundary (vocabulary roles)) (registry : Registry) (checked : Checked registry)
    (context : Context) (root : Occurrence roles)
    (same : ∀ key children, boundary.Survivor registry context root key children ↔ Survivor registry context root key children) :
    ∃ frontier, B4TargetV3.Local boundary registry context root frontier := by
  apply B4TargetV3.local_total
  intro key first last one two
  exact survivor_children_functional registry checked context root key first last
    ((same key first).mp one) ((same key last).mp two)

end Yulang.GeneralNominalCandidates
