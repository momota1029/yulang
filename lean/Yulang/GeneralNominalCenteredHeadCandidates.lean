import Yulang.GeneralNominalCenteredAdministrativeLocal

/-! Head applicability erases named requests before inspecting a demand.
Output equations are handled only after a unique implementation is known. -/
namespace Yulang.GeneralNominalCenteredHeadCandidates
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (Context arguments report privateState Metadata)

variable {roles : Roles.RoleDecls}

def inputs (root : Occurrence roles) : Occurrence roles :=
  ⟨root.identity,⟨root.demand.role,root.demand.arguments,[],by intro _ h; cases h⟩⟩

def HeadModels (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  GeneralNominalState.Models (privateState registry context (inputs root) declaration bounds) model ∧
    ProjectionModels context.state (report context declaration bounds) model

def Prepared (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) : Prop :=
  Metadata registry context ∧ GeneralNominalState.Linked context.state (inputs root).demand ∧
    GeneralNominalAllocation.Fresh context.state registry root.identity ∧
    ∃ bounds, arguments context (inputs root) = some bounds ∧ Finished (report context declaration bounds) ∧
      ∃ model, HeadModels registry context root declaration bounds model

def Survivor (registry : Registry) (context : Context) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) : Prop :=
  ¬ GeneralNominalState.RootPending context.state (inputs root).demand ∧
    ∃ declaration ∈ registry.declarations, ∃ checked : DeclarationChecked registry.constructors roles declaration,
      declaration.id = key ∧ declaration.role = root.demand.role ∧
      ∃ bounds, arguments context (inputs root) = some bounds ∧ Prepared registry context root declaration ∧
        children = GeneralNominalAllocation.children context.state registry (inputs root) declaration checked
          (bindings context.state (report context declaration bounds))

def Failed (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) : Prop :=
  Metadata registry context ∧ GeneralNominalAllocation.Fresh context.state registry root.identity ∧
    ∃ bounds, arguments context (inputs root) = some bounds ∧
      (report context declaration bounds).blocked = [] ∧ (report context declaration bounds).arity = [] ∧
      ((report context declaration bounds).conflicts ≠ [] ∨
        ¬ ∃ model, HeadModels registry context root declaration bounds model)

def InspectionPending (registry : Registry) (context : Context) (root : Occurrence roles) : Prop :=
  ¬ GeneralNominalState.RootPending context.state (inputs root).demand ∧
    ∃ declaration ∈ registry.declarations, declaration.role = root.demand.role ∧
      ¬ Failed registry context root declaration ∧ ¬ Prepared registry context root declaration

def Unique (registry : Registry) (context : Context) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) : Prop :=
  Survivor registry context root key children ∧
    ∀ other cs, Survivor registry context root other cs → other = key ∧ cs = children

theorem inputs_idempotent (root : Occurrence roles) : inputs (inputs root) = inputs root := rfl

theorem prepared_headReady : Prepared registry context root declaration ↔
    GeneralNominalRecursiveCandidates.HeadReady registry context (inputs root) declaration := Iff.rfl

theorem prepared_ignores_outputs (same : inputs first = inputs last) :
    Prepared registry context first declaration ↔ Prepared registry context last declaration := by
  rw [prepared_headReady,prepared_headReady,same]

theorem survivor_ignores_outputs (first last : Occurrence roles) (same : inputs first = inputs last) :
    Survivor registry context first key children ↔ Survivor registry context last key children := by
  have role := congrArg (fun root : Occurrence roles => root.demand.role) same
  simp only [Survivor,same,show first.demand.role = last.demand.role from role,
    prepared_ignores_outputs same]

theorem old_prepared_head
    (old : GeneralNominalRecursiveCandidates.Prepared registry context root declaration checked) :
    Prepared registry context root declaration := by
  obtain ⟨metadata,linked,fresh,bounds,located,finished,_,model,branch⟩ := old
  exact ⟨metadata,⟨linked.1,by intro _ h; cases h⟩,fresh,bounds,located,finished,model,branch.1,branch.2.1⟩

theorem old_survivor_head
    (old : GeneralNominalRecursiveCandidates.Survivor registry context root key children) :
    Survivor registry context root key children := by
  obtain ⟨known,declaration,visible,checked,identity,role,bounds,located,prepared,kids⟩ := old
  exact ⟨known,declaration,visible,checked,identity,role,bounds,located,old_prepared_head prepared,kids⟩

theorem survivor_children_functional (checked : Checked registry)
    (one : Survivor registry context root key first) (two : Survivor registry context root key last) : first = last := by
  obtain ⟨_,a,av,ac,ak,_,ab,al,_,ae⟩ := one
  obtain ⟨_,b,bv,bc,bk,_,bb,bl,_,be⟩ := two
  have equal := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked a b av bv (ak.trans bk.symm)
  subst b
  have same := Option.some.inj (al.symm.trans bl)
  subst bb
  exact ae.trans be.symm

theorem unique_excludes_two (unique : Unique registry context root key children)
    (one : Survivor registry context root a xs) (two : Survivor registry context root b ys)
    (different : a ≠ b) : False :=
  different ((unique.2 a xs one).1.trans (unique.2 b ys two).1.symm)

end Yulang.GeneralNominalCenteredHeadCandidates
