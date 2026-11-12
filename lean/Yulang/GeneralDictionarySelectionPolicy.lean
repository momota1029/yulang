import Yulang.B4TargetV3Functionality

/-! Policy guards for completed dictionaries and every selected source descendant.
The Evidence predicate and raw reconstruction do not enforce K2. The independent
V3 classification does, for whichever concrete K2 predicates the boundary supplies.
This module does not implement cycle detection or a new executor. -/
namespace Yulang.GeneralDictionarySelectionPolicy

open CommonRoleOutermostResolver
open B4Target (Vocabulary SourceBoundary SafeKnown Unique)
open B4TargetV3
universe u
variable {v : Vocabulary.{u}} {b : SourceBoundary v}

/-- A source occurrence reached along actually selected local edges. -/
inductive SelectedPath (b : SourceBoundary v) (r : v.Registry) (s : v.State) :
    v.Demand → v.Demand → Prop where
  | root : SelectedPath b r s root root
  | child : SelectedPath b r s root parent →
      Local b r s parent (.selected key children) → child ∈ children →
      SelectedPath b r s root child

theorem selected_safe (derived : Classify b r s root (.selected dictionary)) :
    SafeKnown b r s root := by
  cases derived with
  | selected safe _ _ => exact safe

theorem selected_not_rootK2 (derived : Classify b r s root (.selected dictionary)) :
    ¬ b.RootK2 r s root := (selected_safe derived).2.1

theorem selected_not_candidateK2 (derived : Classify b r s root (.selected dictionary)) :
    ¬ b.CandidateK2 r s root := (selected_safe derived).2.2.1

private theorem all_selected_member
    (given : All₂ (fun d dictionary => Classify b r s d (.selected dictionary)) children dictionaries)
    (member : child ∈ children) : ∃ dictionary, Classify b r s child (.selected dictionary) := by
  induction given with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, first⟩
      · exact ih later

/-- Every demand reached in the selected source tree has its own selected dictionary.
The explicit local edge is reconciled by functionality, not assumed to match by key. -/
theorem selected_path_classifies (path : SelectedPath b r s root child)
    (derived : Classify b r s root (.selected dictionary)) :
    ∃ childDictionary, Classify b r s child (.selected childDictionary) := by
  induction path with
  | root => exact ⟨_, derived⟩
  | @child parent key children child path localRule member ih =>
      obtain ⟨parentDictionary, parentDerived⟩ := ih
      cases parentDerived with
      | selected safe unique all =>
          have same := local_functional (.selected safe unique) localRule
          cases same
          exact all_selected_member all member

theorem selected_path_safe (path : SelectedPath b r s root child)
    (derived : Classify b r s root (.selected dictionary)) : SafeKnown b r s child := by
  obtain ⟨_, proof⟩ := selected_path_classifies path derived
  exact selected_safe proof

/-- Neither K2 rejection can occur anywhere in a completed selected source tree. -/
theorem selected_path_excludes_K2 (path : SelectedPath b r s root child)
    (derived : Classify b r s root (.selected dictionary)) :
    ¬ b.RootK2 r s child ∧ ¬ b.CandidateK2 r s child :=
  ⟨(selected_path_safe path derived).2.1, (selected_path_safe path derived).2.2.1⟩

/-- This is the lossless diagnostic-tree interface, with no exact-executor assumption. -/
theorem completed_tree_excludes_K2 (resolved : Resolves (Local b r s) root tree)
    (done : Completed tree (.selected dictionary)) :
    ¬ b.RootK2 r s root ∧ ¬ b.CandidateK2 r s root :=
  ⟨selected_not_rootK2 (tree_classifies b r s tree root _ resolved done),
    selected_not_candidateK2 (tree_classifies b r s tree root _ resolved done)⟩

/-- A source selected path and a K2 witness block completed dictionary extraction. -/
theorem K2_descendant_prevents_completed (resolved : Resolves (Local b r s) root tree)
    (path : SelectedPath b r s root child)
    (cycle : b.RootK2 r s child ∨ b.CandidateK2 r s child) :
    ¬ Completed tree (.selected dictionary) := by
  intro done
  have guarded := selected_path_excludes_K2 path (tree_classifies b r s tree root _ resolved done)
  exact cycle.elim guarded.1 guarded.2

/-- For an executor with the existing exactness bridge, the public returned tree
cannot yield a dictionary at a K2-rejected root. Exactness remains explicit. -/
theorem exact_executor_excludes_K2 (e : Executor v) (exact : Exact b e)
    (checked : b.Checked r)
    (done : Completed (e.run r s root).2 (.selected dictionary)) :
    ¬ b.RootK2 r (e.run r s root).1 root ∧
      ¬ b.CandidateK2 r (e.run r s root).1 root :=
  completed_tree_excludes_K2 ((exact r checked s root _).mp rfl) done

end Yulang.GeneralDictionarySelectionPolicy
