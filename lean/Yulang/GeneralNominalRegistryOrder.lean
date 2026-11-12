import Yulang.GeneralDictionaryRecursiveSemanticOrder
import Yulang.GeneralNominalFeedbackBoundary

/-! Registry enumeration does not change capture, canonical source children,
or per-model candidate constraints in a fixed context. Reservation lists may
change order; freshness uses their membership, not their enumeration. -/
namespace Yulang.GeneralNominalRegistryOrder

open GeneralDeclarations GeneralRegistryReordering GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates
open GeneralDictionaryRecursiveOrder (report_reorders)

variable {roles : Roles.RoleDecls} {first last : Registry} {a b : Declaration}

private theorem declaration_keys (root : Nat) (order : DeclarationReorders a b) :
    (GeneralNominalAllocation.declarationKeys root a).Perm
      (GeneralNominalAllocation.declarationKeys root b) := by
  rw [declarationReorders_update order]
  unfold GeneralNominalAllocation.declarationKeys
  dsimp only [Declaration.inputNames,Declaration.outputNames]
  exact (List.Perm.flatMap_right _ order.requirements).append_left _

theorem keys_membership (order : Reorders first last) (root key) :
    key ∈ GeneralNominalAllocation.keys first root ↔ key ∈ GeneralNominalAllocation.keys last root := by
  constructor
  · intro member
    obtain ⟨d,present,within⟩ := List.mem_flatMap.mp member
    obtain ⟨other,visible,pair⟩ := reorders_visible order d present
    exact List.mem_flatMap.mpr ⟨other,visible,(declaration_keys root pair).mem_iff.mp within⟩
  · intro member
    obtain ⟨d,present,within⟩ := List.mem_flatMap.mp member
    obtain ⟨other,visible,pair⟩ := reorders_visible_back order d present
    exact List.mem_flatMap.mpr ⟨other,visible,(declaration_keys root pair).mem_iff.mpr within⟩

theorem fresh (order : Reorders first last) (state : GeneralNominalState.State) (root : Nat) :
    GeneralNominalAllocation.Fresh state first root ↔ GeneralNominalAllocation.Fresh state last root :=
  ⟨fun valid key member collision => valid key ((keys_membership order root key).mpr member) collision,
    fun valid key member collision => valid key ((keys_membership order root key).mp member) collision⟩

theorem metadata (order : Reorders first last) (context : Context) :
    Metadata first context ↔ Metadata last context := by
  simp only [Metadata,GeneralNominalCandidates.Metadata,order.1]

theorem private_models (order : DeclarationReorders a b) (context : Context)
    (root : Occurrence roles) (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models (privateState first context root a bounds) model ↔
      GeneralNominalState.Models (privateState last context root b bounds) model := by
  simp only [privateState,GeneralNominalState.extend_models,GeneralNominalAllocation.propagate_models,
    report_reorders context a b order bounds,GeneralNominalAllocation.merges,
    Declaration.inputNames,order.head,order.id,GeneralNominalAllocation.capture,GeneralNominalAllocation.source]

theorem generated (order : Reorders first last) (roleEq : first.roles = roles)
    (pair : DeclarationReorders a b) (context : Context) (root : Occurrence roles)
    (ac : DeclarationChecked first.constructors roles a) (bc : DeclarationChecked last.constructors roles b)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    GeneralNominalRecursiveCandidates.generated first context root a ac bounds =
      GeneralNominalRecursiveCandidates.generated last context root b bc bounds := by
  rcases first with ⟨constructors,firstRoles,firstDecls⟩
  rcases last with ⟨otherConstructors,lastRoles,lastDecls⟩
  cases roleEq
  have sameConstructors := order.1
  have sameRoles := order.2.1
  dsimp only at sameConstructors sameRoles
  cases sameConstructors; cases sameRoles
  exact GeneralDictionaryRecursiveSemanticOrder.generated_reorders constructors firstRoles firstDecls lastDecls
    context root a b pair ac bc bounds

theorem branch_models (order : Reorders first last) (roleEq : first.roles = roles)
    (pair : DeclarationReorders a b) (context : Context) (root : Occurrence roles)
    (ac : DeclarationChecked first.constructors roles a) (bc : DeclarationChecked last.constructors roles b)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) (model : GeneralNominalCommonBridge.Assignment) :
    BranchModels first context root a ac bounds model ↔ BranchModels last context root b bc bounds model := by
  rcases first with ⟨constructors,firstRoles,firstDecls⟩
  rcases last with ⟨otherConstructors,lastRoles,lastDecls⟩
  cases roleEq
  have sameConstructors := order.1
  have sameRoles := order.2.1
  dsimp only at sameConstructors sameRoles
  cases sameConstructors; cases sameRoles
  exact GeneralDictionaryRecursiveSemanticOrder.branch_reorders constructors firstRoles firstDecls lastDecls
    context root a b pair ac bc bounds model

theorem request_ready (order : Reorders first last) (roleEq : first.roles = roles)
    (pair : DeclarationReorders a b) (context : Context) (root : Occurrence roles)
    (ac : DeclarationChecked first.constructors roles a) (bc : DeclarationChecked last.constructors roles b)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    RequestReady first context root a ac bounds ↔ RequestReady last context root b bc bounds := by
  simp only [RequestReady,GeneralNominalMaterialization.RootDefined,pair.associated,
    generated order roleEq pair context root ac bc bounds]

theorem children (order : Reorders first last) (pair : DeclarationReorders a b)
    (state : GeneralNominalState.State) (root : Occurrence roles)
    (ac : DeclarationChecked first.constructors roles a) (bc : DeclarationChecked last.constructors roles b)
    (bindings : GeneralNominalAllocation.Bindings) :
    GeneralNominalAllocation.children state first root a ac bindings =
      GeneralNominalAllocation.children state last root b bc bindings := by
  have bc' : DeclarationChecked first.constructors roles b := order.1.symm ▸ bc
  have sameFrame : GeneralNominalAllocation.frame (roles := roles) state first root.identity bindings =
      GeneralNominalAllocation.frame state last root.identity bindings := rfl
  unfold GeneralNominalAllocation.children
  rw [sameFrame]
  exact GeneralDictionaryEmissionPlans.children_reorders _ root pair ac bc'

theorem prepared (order : Reorders first last) (roleEq : first.roles = roles)
    (pair : DeclarationReorders a b) (context : Context) (root : Occurrence roles)
    (ac : DeclarationChecked first.constructors roles a) (bc : DeclarationChecked last.constructors roles b) :
    Prepared first context root a ac ↔ Prepared last context root b bc := by
  simp only [Prepared,metadata order context,fresh order context.state root.identity,
    report_reorders context a b pair,request_ready order roleEq pair context root ac bc,
    Consistent,branch_models order roleEq pair context root ac bc]

theorem failed (order : Reorders first last) (roleEq : first.roles = roles)
    (pair : DeclarationReorders a b) (context : Context) (root : Occurrence roles)
    (ac : DeclarationChecked first.constructors roles a) (bc : DeclarationChecked last.constructors roles b) :
    Failed first context root a ac ↔ Failed last context root b bc := by
  simp only [Failed,metadata order context,fresh order context.state root.identity,
    report_reorders context a b pair,request_ready order roleEq pair context root ac bc,
    Consistent,branch_models order roleEq pair context root ac bc]

theorem head_ready (order : Reorders first last) (pair : DeclarationReorders a b)
    (context : Context) (root : Occurrence roles) :
    HeadReady first context root a ↔ HeadReady last context root b := by
  simp only [HeadReady,metadata order context,fresh order context.state root.identity,
    private_models (first := first) (last := last) pair context root,
    report_reorders context a b pair]

end Yulang.GeneralNominalRegistryOrder
