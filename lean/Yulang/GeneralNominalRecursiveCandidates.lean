import Yulang.GeneralNominalMaterialization

/-! Candidate-private interval and projection propagation with deterministic
where emission. Children remain a conjunction outside applicability. This
interface also retains source equations for compound and named requests. -/
namespace Yulang.GeneralNominalRecursiveCandidates

open GeneralDeclarations
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalRecursiveInspection

abbrev Context := GeneralNominalCandidates.Context
abbrev arguments (context : Context) (root : Occurrence roles) := GeneralNominalCandidates.arguments context root
abbrev Metadata := GeneralNominalCandidates.Metadata

def report (context : Context) (declaration : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) : Report context.state :=
  let result := inspectMany context.state
    (GeneralNominalInspection.queries context.state context.interpretation declaration) bounds (fun _ => none) 0
  { result with checked := bounds ++ result.checked }

def privateState (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state)) : GeneralNominalState.State :=
  GeneralNominalState.extend
    (GeneralNominalAllocation.propagate context.state registry root.identity declaration
      (bindings context.state (report context declaration bounds))) []
    (selfChecks context.state (report context declaration bounds))

def generated (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) : GeneralNominalMaterialization.Schema :=
  GeneralNominalMaterialization.generated context.state context.interpretation
    (GeneralNominalMaterialization.requests context.state registry root declaration checked
      (bindings context.state (report context declaration bounds)))

def RequestReady (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) : Prop :=
  GeneralNominalMaterialization.RootDefined declaration root ∧
    (generated registry context root declaration checked bounds).unknown = false

def BranchModels (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  GeneralNominalState.Models (privateState registry context root declaration bounds) model ∧
    ProjectionModels context.state (report context declaration bounds) model ∧
    GeneralNominalMaterialization.Models context.state declaration
      (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
        (bindings context.state (report context declaration bounds)))
      (report context declaration bounds) (generated registry context root declaration checked bounds) model

def Consistent (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) : Prop :=
  ∃ model, BranchModels registry context root declaration checked bounds model

def Prepared (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration) : Prop :=
  Metadata registry context ∧ GeneralNominalState.Linked context.state root.demand ∧
    GeneralNominalAllocation.Fresh context.state registry root.identity ∧
    ∃ bounds, arguments context root = some bounds ∧ Finished (report context declaration bounds) ∧
      RequestReady registry context root declaration checked bounds ∧
      Consistent registry context root declaration checked bounds

def Survivor (registry : Registry) (context : Context) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) : Prop :=
  ¬ GeneralNominalState.RootPending context.state root.demand ∧
    ∃ declaration ∈ registry.declarations, ∃ checked : DeclarationChecked registry.constructors roles declaration,
      declaration.id = key ∧ declaration.role = root.demand.role ∧
      ∃ bounds, arguments context root = some bounds ∧ Prepared registry context root declaration checked ∧
        children = GeneralNominalAllocation.children context.state registry root declaration checked
          (bindings context.state (report context declaration bounds))

def Failed (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration) : Prop :=
  Metadata registry context ∧ GeneralNominalAllocation.Fresh context.state registry root.identity ∧
    ∃ bounds, arguments context root = some bounds ∧
      (report context declaration bounds).blocked = [] ∧
      (report context declaration bounds).arity = [] ∧
      ((report context declaration bounds).conflicts ≠ [] ∨
        (RequestReady registry context root declaration checked bounds ∧
          ¬ Consistent registry context root declaration checked bounds))

def InspectionPending (registry : Registry) (context : Context) (root : Occurrence roles) : Prop :=
  ¬ GeneralNominalState.RootPending context.state root.demand ∧
    ∃ declaration ∈ registry.declarations, ∃ checked : DeclarationChecked registry.constructors roles declaration,
      declaration.role = root.demand.role ∧ ¬ Failed registry context root declaration checked ∧
        ¬ Prepared registry context root declaration checked

def HeadReady (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) : Prop :=
  Metadata registry context ∧ GeneralNominalState.Linked context.state root.demand ∧
    GeneralNominalAllocation.Fresh context.state registry root.identity ∧
    ∃ bounds, arguments context root = some bounds ∧ Finished (report context declaration bounds) ∧
      ∃ model, GeneralNominalState.Models (privateState registry context root declaration bounds) model ∧
        ProjectionModels context.state (report context declaration bounds) model

def CandidateK2 (registry : Registry) (context : Context) (root : Occurrence roles) : Prop :=
  ¬ GeneralNominalState.RootPending context.state root.demand ∧
    ∃ declaration ∈ registry.declarations, ∃ _checked : DeclarationChecked registry.constructors roles declaration,
      declaration.role = root.demand.role ∧ HeadReady registry context root declaration ∧
      ∃ bounds, arguments context root = some bounds ∧
        ∃ visited ∈ (report context declaration bounds).inspected,
          GeneralNominalMixedRecurrence.RecursAt context.state visited.1

theorem branch_interval_sound (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : GeneralNominalCommonBridge.Assignment)
    (models : BranchModels registry context root declaration checked bounds model) :
    GeneralNominalState.Models context.state model ∧
      GeneralNominalAllocation.Compatible (bindings context.state (report context declaration bounds)) model ∧
      ProjectionModels context.state (report context declaration bounds) model := by
  have extended := (GeneralNominalState.extend_models ..).mp models.1
  have propagated := (GeneralNominalAllocation.propagate_models ..).mp extended.1
  exact ⟨propagated.1,propagated.2.1,models.2.1⟩

theorem branch_child_correspondence (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : GeneralNominalCommonBridge.Assignment)
    (models : BranchModels registry context root declaration checked bounds model)
    (name : Nat) (declared : name ∈ declaration.inputNames)
    (nonempty : GeneralNominalAllocation.occurrences (bindings context.state (report context declaration bounds)) name ≠ [])
    (actual : CommonNominalFullCarrier.Ty) (clause : Clause) (valid : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (pattern : GeneralDeclarationPatterns.normalize (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)) = .var name) :
    let captures := bindings context.state (report context declaration bounds)
    let child := GeneralDeclarationDemands.childDemand declaration clause valid
      (GeneralNominalAllocation.capture context.state registry root.identity declaration.id captures)
      (GeneralNominalAllocation.allocation context.state registry root.identity declaration.id clause)
    GeneralNominalCaptureMerges.Fits model (child.arguments index) actual ↔
      ∀ interval ∈ GeneralNominalAllocation.occurrences captures name, GeneralNominalCaptureMerges.Fits model interval actual :=
  GeneralNominalCaptureMerges.repeated_child_correspondence context.state registry root.identity declaration
    (bindings context.state (report context declaration bounds)) model
    ((GeneralNominalState.extend_models ..).mp models.1).1 name declared nonempty actual clause valid index pattern

theorem survivor_children_functional (registry : Registry) (checked : Checked registry)
    (context : Context) (root : Occurrence roles) (key : Nat) (first last : List (Occurrence roles))
    (one : Survivor registry context root key first) (two : Survivor registry context root key last) : first = last := by
  obtain ⟨_,a,av,ac,ak,_,ab,al,_,ae⟩ := one
  obtain ⟨_,b,bv,bc,bk,_,bb,bl,_,be⟩ := two
  have equal := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked a b av bv (ak.trans bk.symm)
  subst b
  have same := Option.some.inj (al.symm.trans bl)
  subst bb
  exact ae.trans be.symm

theorem blocked_defers (registry : Registry) (context : Context) (root : Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending context.state root.demand)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (sameRole : declaration.role = root.demand.role)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) (located : arguments context root = some bounds)
    (blocked : (report context declaration bounds).blocked ≠ []) : InspectionPending registry context root := by
  refine ⟨ready,declaration,visible,checked,sameRole,?_,?_⟩
  · rintro ⟨_,_,other,found,empty,_⟩
    have same := Option.some.inj (located.symm.trans found); subst other
    exact blocked empty
  · rintro ⟨_,_,_,other,found,finished,_⟩
    have same := Option.some.inj (located.symm.trans found); subst other
    exact blocked finished.1

theorem candidateK2_not_root_pending (registry : Registry) (context : Context) (root : Occurrence roles)
    (cycle : CandidateK2 registry context root) : ¬ GeneralNominalState.RootPending context.state root.demand := cycle.1

end Yulang.GeneralNominalRecursiveCandidates
