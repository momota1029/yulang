import Yulang.GeneralDictionarySettledProjection

/-! Exact selected-dictionary transfer when every selected where descendant has
an I26 explanation. The guard premise is structural, not semantic Evidence or
new classification. This does not infer explanations from stability. -/
namespace Yulang.GeneralDictionarySettledGuardedClassification
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open CommonRoleOutermostResolver GeneralDictionarySettledProjection
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}

/-- Check I26 explanations on the OLD selected-child graph, independently of
new classification. Includes the root and any finite selected-child path. -/
def GuardClosure (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ child, B4Target.Steps (fun parent child => Child
    (B4TargetV3.Local (old roles).toSourceBoundary registry state) child parent) root child →
    GeneralNominalSettledSupport.DecisionGuard registry state child

theorem guard_root {root : Occurrence roles} (guard : GuardClosure registry state root) :
    GeneralNominalSettledSupport.DecisionGuard registry state root := guard root .refl

theorem guard_child {root child : Occurrence roles} (guard : GuardClosure registry state root)
    (edge : Child (B4TargetV3.Local (old roles).toSourceBoundary registry state) child root) :
    GuardClosure registry state child := by
  intro descendant path
  apply guard descendant
  induction path with
  | refl => exact .tail .refl edge
  | tail _ next ih => exact .tail ih next

theorem selected_local_iff {root : Occurrence roles} {key : Nat} {children : List (Occurrence roles)} :
    B4TargetV3.Local (fresh roles).toSourceBoundary registry state root (.selected key children) ↔
    B4TargetV3.Local (old roles).toSourceBoundary registry state root (.selected key children) ∧
      GeneralNominalSettledSupport.DecisionGuard registry state root := by
  classical
  constructor
  · intro selected
    refine ⟨selected_local_old selected,?_⟩
    cases selected with
    | selected safe _ => exact Classical.byContradiction (fun absent => safe.2.2.2 (Or.inr absent))
  · rintro ⟨selected,guard⟩
    cases selected with
    | selected safe unique =>
      refine .selected ⟨safe.1,safe.2.1,safe.2.2.1,?_⟩ unique
      rintro (pending | pending)
      · exact safe.2.2.2 pending
      · exact pending guard

mutual
  theorem classified_of_guards (dictionary : Dictionary) (root : Occurrence roles)
      (guard : GuardClosure registry state root)
      (classified : B4TargetV3.Classify (old roles).toSourceBoundary registry state root (.selected dictionary)) :
      B4TargetV3.Classify (fresh roles).toSourceBoundary registry state root (.selected dictionary) := by
    match dictionary, classified with
    | .node key dictionaries, .selected safe unique all =>
      have localOld : B4TargetV3.Local (old roles).toSourceBoundary registry state root (.selected key _) := .selected safe unique
      have localNew := selected_local_iff.mpr ⟨localOld,guard_root guard⟩
      cases localNew with
      | selected newSafe newUnique =>
        exact .selected newSafe newUnique (children_of_guards dictionaries _ all
          (fun child member => guard_child guard ⟨key,_,localOld,member⟩))
  termination_by sizeOf dictionary

  theorem children_of_guards (dictionaries : List Dictionary) (roots : List (Occurrence roles))
      (classified : All₂ (fun root dictionary => B4TargetV3.Classify
        (old roles).toSourceBoundary registry state root (.selected dictionary)) roots dictionaries)
      (guards : ∀ child ∈ roots, GuardClosure registry state child) :
      All₂ (fun root dictionary => B4TargetV3.Classify
        (fresh roles).toSourceBoundary registry state root (.selected dictionary)) roots dictionaries := by
    cases classified with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (classified_of_guards _ _ (guards _ (by simp)) first)
        (children_of_guards _ _ rest (fun child member => guards child (by simp [member])))
  termination_by sizeOf dictionaries
end

theorem selected_iff_of_guards (root : Occurrence roles) (dictionary : Dictionary)
    (guard : GuardClosure registry state root) :
    B4TargetV3.Classify (fresh roles).toSourceBoundary registry state root (.selected dictionary) ↔
    B4TargetV3.Classify (old roles).toSourceBoundary registry state root (.selected dictionary) :=
  ⟨selected_classification_old dictionary root,classified_of_guards dictionary root guard⟩
end Yulang.GeneralDictionarySettledGuardedClassification
