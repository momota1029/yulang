import Yulang.GeneralPresenceOrderedRebase247
import Yulang.GeneralPresenceOrderedCheck247

/-! A finite actual-syntax alias/lower/upper-shaped block rebase. Consumers
are arbitrary and may read private type targets. This is a compiled-block
regression, not a proof that these entries arise in a reachable source journal. -/
namespace Yulang.GeneralPresenceOrderedRebaseExample247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedRebase247

def old : List (Entry Nat) :=
  [(2,.var 0),(3,.union (.var 2) (.var 1)),(4,.inter (.var 3) (.var 0))]

def fresh : List (Entry Nat) :=
  [(2,.inter (.var 0) (.var 1)),(3,.var 2),(4,.union (.var 3) (.var 1))]

theorem old_checked : GeneralPresenceOrderedCheck247.check old = true := by decide

theorem fresh_checked : GeneralPresenceOrderedCheck247.check fresh = true := by decide

theorem old_safe : SafeOrder old := (GeneralPresenceOrderedCheck247.check_exact old).mp old_checked

theorem fresh_safe : SafeOrder fresh := (GeneralPresenceOrderedCheck247.check_exact fresh).mp fresh_checked

theorem targets_within : TargetsWithin fresh old := by
  intro entry member
  simp only [fresh,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨(2,.var 0),by simp [old],rfl⟩
  · exact ⟨(3,.union (.var 2) (.var 1)),by simp [old],rfl⟩
  · exact ⟨(4,.inter (.var 3) (.var 0)),by simp [old],rfl⟩

def sharedNames (name : Nat) : Prop := name ≠ 2 ∧ name ≠ 3 ∧ name ≠ 4

theorem private_targets : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name := by
  intro name outside entry member
  obtain ⟨two,three,four⟩ := outside
  simp only [old,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact Ne.symm two
  · exact Ne.symm three
  · exact Ne.symm four

theorem arbitrary_consumers_exact (consumers : List (Atom Nat))
    (boundary : Nat → Comp CommonNominalFullCarrier.model) :
    (∃ assignment, All CommonNominalFullCarrier.model assignment (consumers ++ block old) ∧
      Agrees CommonNominalFullCarrier.model sharedNames assignment boundary) ↔
    (∃ assignment, All CommonNominalFullCarrier.model assignment (rewrite old consumers ++ block fresh) ∧
      Agrees CommonNominalFullCarrier.model sharedNames assignment boundary) :=
  common_public_models_iff old fresh old_safe fresh_safe targets_within consumers sharedNames private_targets boundary

theorem old_lower_expanded : (mapping old 3).ty = .union (.var 0) (.var 1) := rfl

theorem old_upper_expanded : (mapping old 4).ty =
    .inter (.union (.var 0) (.var 1)) (.var 0) := rfl

theorem fresh_upper_expanded : (mapping fresh 4).ty =
    .union (.inter (.var 0) (.var 1)) (.var 1) := rfl

theorem private_query_rewritten : rewrite old (equations 7 (.var 4)) =
    equations 7 (.inter (.union (.var 0) (.var 1)) (.var 0)) := rfl

theorem private_row_unchanged : (mapping old 4).row = .var 4 := rfl

end Yulang.GeneralPresenceOrderedRebaseExample247
