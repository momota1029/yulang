import Yulang.GeneralNominalCycleRegressions

/-! A joint applicability condition for one alias class. All named output
obligations participate in one model witness, including names requested by only
one occurrence. This condition is independent of a driver and preserves the
old survivor interface through projection. Producing the complete joint local
classifier and its updates remains a separate obligation. -/
namespace Yulang.GeneralNominalJointCandidates

open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalSaturationState
open GeneralNominalDemandMerging (Site)

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
variable {root : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}

def Related (state : State roles) (root : Occurrence roles) (site : Site roles) : Prop :=
  site ∈ state.sites ∧ Alias state root.identity site.occurrence.identity

def BranchAt (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat)
    (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  ∃ declaration ∈ registry.declarations, ∃ checked : DeclarationChecked registry.constructors roles declaration,
    declaration.id = key ∧ declaration.role = root.demand.role ∧
      GeneralNominalRecursiveCandidates.Prepared registry state.context root declaration checked ∧
      ∃ bounds, GeneralNominalRecursiveCandidates.arguments state.context root = some bounds ∧
        GeneralNominalRecursiveCandidates.BranchModels registry state.context root declaration checked bounds model

def Joint (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  (∀ packet ∈ state.packets, Alias state root.identity packet.site.occurrence.identity → packet.declaration.id = key) ∧
    ∃ model, Models state model ∧ BranchAt registry state root key model ∧
      ∀ site, Related state root site → BranchAt registry state site.occurrence key model

def Survivor (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat)
    (children : List (Occurrence roles)) : Prop :=
  GeneralNominalRecursiveCandidates.Survivor registry state.context root key children ∧ Joint registry state root key

theorem initial_joint (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration) (role : declaration.role = root.demand.role)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (located : GeneralNominalRecursiveCandidates.arguments context root = some bounds)
    (prepared : GeneralNominalRecursiveCandidates.Prepared registry context root declaration checked)
    (model : GeneralNominalCommonBridge.Assignment)
    (branch : GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked bounds model) :
    Joint registry (initial context root) root declaration.id := by
  have atRoot : BranchAt registry (initial context root) root declaration.id model :=
    ⟨declaration,visible,checked,rfl,role,prepared,bounds,located,branch⟩
  refine ⟨(by intro packet member; cases member),model,?_,atRoot,?_⟩
  · exact (initial_models context root model).mpr
      (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ branch).1
  · intro site related
    have same := List.mem_singleton.mp related.1
    subst site
    exact atRoot

theorem old_survivor (survivor : Survivor registry state (root : Occurrence roles) key children) :
    GeneralNominalRecursiveCandidates.Survivor registry state.context root key children := survivor.1

theorem all_alias_conditions (joint : Joint registry state (root : Occurrence roles) key) :
    ∃ model, Models state model ∧ BranchAt registry state root key model ∧
      ∀ site, Related state root site → BranchAt registry state site.occurrence key model := joint.2

theorem alias_outputs_not_dropped (joint : Joint registry state (root : Occurrence roles) key)
    (site : Site roles) (related : Related state root site) :
    ∃ model, Models state model ∧ ∃ declaration ∈ registry.declarations,
      ∃ checked : DeclarationChecked registry.constructors roles declaration,
        declaration.id = key ∧ ∃ bounds,
          GeneralNominalRecursiveCandidates.arguments state.context site.occurrence = some bounds ∧
          GeneralNominalMaterialization.Models state.context.state declaration
            (GeneralNominalAllocation.capture state.context.state registry site.occurrence.identity declaration.id
              (GeneralNominalRecursiveInspection.bindings state.context.state
                (GeneralNominalRecursiveCandidates.report state.context declaration bounds)))
            (GeneralNominalRecursiveCandidates.report state.context declaration bounds)
            (GeneralNominalRecursiveCandidates.generated registry state.context site.occurrence declaration checked bounds) model := by
  obtain ⟨model,valid,_,all⟩ := joint.2
  obtain ⟨declaration,visible,checked,identity,_,_,bounds,located,branch⟩ := all site related
  exact ⟨model,valid,declaration,visible,checked,identity,bounds,located,branch.2.2⟩

theorem conflicting_recorded_choices (state : State roles) (root : Occurrence roles)
    (first last : Packet roles) (one : first ∈ state.packets) (two : last ∈ state.packets)
    (a : Alias state root.identity first.site.occurrence.identity)
    (b : Alias state root.identity last.site.occurrence.identity)
    (different : first.declaration.id ≠ last.declaration.id) (registry : Registry) :
    ∀ key, ¬ Joint registry state root key := by
  intro key joint
  exact different ((joint.1 first one a).trans (joint.1 last two b).symm)

theorem joint_consistent_with_journal (joint : Joint registry state (root : Occurrence roles) key) :
    ∃ model, Models state model := by
  obtain ⟨model,valid,_⟩ := joint.2
  exact ⟨model,valid⟩

theorem conflicting_journal_eliminates (registry : Registry) (state : State roles) (root : Occurrence roles)
    (key : Nat) (conflict : ∀ model, Models state model → ¬ BranchAt registry state root key model) :
    ¬ Joint registry state root key := by
  rintro ⟨_,model,valid,branch,_⟩
  exact conflict model valid branch

theorem survivor_functional (registry : Registry) (checked : Checked registry) (state : State roles)
    (root : Occurrence roles) (key : Nat) (first last : List (Occurrence roles))
    (one : Survivor registry state root key first) (two : Survivor registry state root key last) : first = last :=
  GeneralNominalRecursiveCandidates.survivor_children_functional registry checked state.context root key first last one.1 two.1

end Yulang.GeneralNominalJointCandidates
