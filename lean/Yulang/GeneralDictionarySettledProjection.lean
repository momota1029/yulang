import Yulang.GeneralNominalSettledBoundary

/-! One-way projection of the I26 boundary's selected dictionaries and actual
paths to the existing Value boundary. Semantic evidence is unchanged. This is
not a projection of Stable, nor a proof of evidenceNode or of all-model soundness. -/
namespace Yulang.GeneralDictionarySettledProjection
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}

abbrev fresh (roles : Roles.RoleDecls) := GeneralNominalSettledBoundary.boundary roles
abbrev old (roles : Roles.RoleDecls) := GeneralNominalValueBoundary.boundary roles

theorem safe_old {root : Occurrence roles}
    (safe : B4Target.SafeKnown (fresh roles).toSourceBoundary registry state root) :
    B4Target.SafeKnown (old roles).toSourceBoundary registry state root :=
  ⟨safe.1, safe.2.1, safe.2.2.1, fun pending => safe.2.2.2 (Or.inl pending)⟩

theorem selected_local_old {root : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}
    (selected : B4TargetV3.Local (fresh roles).toSourceBoundary registry state root (.selected key children)) :
    B4TargetV3.Local (old roles).toSourceBoundary registry state root (.selected key children) := by
  cases selected with
  | selected safe unique => exact .selected (safe_old safe) unique

mutual
  theorem selected_classification_old (dictionary : Dictionary) (root : Occurrence roles)
      (selected : B4TargetV3.Classify (fresh roles).toSourceBoundary registry state root (.selected dictionary)) :
      B4TargetV3.Classify (old roles).toSourceBoundary registry state root (.selected dictionary) := by
    match dictionary, selected with
    | .node key dictionaries, .selected safe unique children =>
      exact .selected (safe_old safe) unique (selected_children_old dictionaries _ children)
  termination_by sizeOf dictionary

  theorem selected_children_old (dictionaries : List Dictionary) (roots : List (Occurrence roles))
      (selected : All₂ (fun root dictionary => B4TargetV3.Classify
        (fresh roles).toSourceBoundary registry state root (.selected dictionary)) roots dictionaries) :
      All₂ (fun root dictionary => B4TargetV3.Classify
        (old roles).toSourceBoundary registry state root (.selected dictionary)) roots dictionaries := by
    cases selected with
    | nil => exact .nil
    | cons first rest => exact .cons (selected_classification_old _ _ first) (selected_children_old _ _ rest)
  termination_by sizeOf dictionaries
end

theorem completed_selected_old {root : Occurrence roles} {tree : Tree} {dictionary : Dictionary}
    (resolved : Resolves (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) root tree)
    (done : B4TargetV3.Completed tree (.selected dictionary)) :
    B4TargetV3.Classify (old roles).toSourceBoundary registry state root (.selected dictionary) :=
  selected_classification_old dictionary root (B4TargetV3.tree_classifies _ _ _ _ _ _ resolved done)

theorem steps_old {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps ((fresh roles).Step registry root) before after) :
    B4Target.Steps ((old roles).Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (GeneralNominalSettledSteps.step_old step)

theorem reachable_old {root : Occurrence roles}
    (reachable : B4TargetV5.Reachable (fresh roles) registry root state) :
    B4TargetV5.Reachable (old roles) registry root state := by
  obtain ⟨start,initial,path⟩ := reachable
  exact ⟨start,initial,steps_old path⟩

theorem evidence_iff (root : Occurrence roles) (model : GeneralNominalCommonBridge.Assignment)
    (dictionary : Dictionary) :
    (fresh roles).Evidence registry state model root dictionary ↔
      (old roles).Evidence registry state model root dictionary := Iff.rfl

theorem models_iff (model : GeneralNominalCommonBridge.Assignment) :
    (fresh roles).Models state model ↔ (old roles).Models state model := Iff.rfl

end Yulang.GeneralDictionarySettledProjection
