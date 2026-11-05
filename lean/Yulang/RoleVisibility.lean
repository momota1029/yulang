import Yulang.RoleConstraints

/-!
# Caller-visible impl sets and resolution stability

Spec 6.2 (2026-11-05) selects impls at the instantiation site, including all
nested `where` requirements. The existing `Roles.resolve` already supplies the
same impl list to every recursive call. This module proves its exact behavior
when that visible set grows or its list representation changes.

A resolved goal remains resolved or becomes ambiguous; it never loses its
evidence. An ambiguous goal stays ambiguous. If both visible sets resolve the
goal, the selected head declaration is unchanged. These are local properties:
no global coherence or orphan condition is imposed. Terms in goals remain
rigid, as in `Roles`; solving unknown inference variables is a separate layer.
-/

namespace Yulang.RoleVisibility

open Roles

def Included (smaller larger : List Impl) : Prop :=
  ∀ implementation, implementation ∈ smaller → implementation ∈ larger

theorem candidates_included {smaller larger : List Impl} (included : Included smaller larger)
    (goal : Goal) {implementation : Impl} (member : implementation ∈ candidates smaller goal) :
    implementation ∈ candidates larger goal := by
  obtain ⟨visible, matching⟩ := mem_candidates.mp member
  exact mem_candidates.mpr ⟨included implementation visible, matching⟩

theorem derives_mono {smaller larger : List Impl} (included : Included smaller larger)
    {goal : Goal} (derived : Derives smaller goal) : Derives larger goal := by
  induction derived with
  | impl implementation substitution member role head children ih =>
      exact .impl implementation substitution (included implementation member) role head ih

theorem headOverlap_mono {smaller larger : List Impl} (included : Included smaller larger)
    {goal : Goal} (overlap : HeadOverlap smaller goal) : HeadOverlap larger goal := by
  obtain ⟨first, firstVisible, second, secondVisible, distinct, firstMatches, secondMatches⟩ :=
    (head_overlap_iff smaller goal).mp overlap
  exact (head_overlap_iff larger goal).mpr
    ⟨first, included first firstVisible, second, included second secondVisible,
      distinct, firstMatches, secondMatches⟩

/-- A previously visible unique candidate either stays unique or meets another
head. It cannot disappear when visibility grows. -/
theorem singleton_or_overlap {smaller larger : List Impl} (included : Included smaller larger)
    {goal : Goal} {implementation : Impl} (unique : candidates smaller goal = [implementation]) :
    candidates larger goal = [implementation] ∨ HeadOverlap larger goal := by
  have member : implementation ∈ candidates larger goal :=
    candidates_included included goal (unique ▸ List.mem_singleton_self implementation)
  cases candidatesLarger : candidates larger goal with
  | nil => simp [candidatesLarger] at member
  | cons first rest =>
      cases rest with
      | nil =>
          have same : implementation = first := by simpa [candidatesLarger] using member
          subst first
          exact Or.inl rfl
      | cons second rest => exact Or.inr (by simp [HeadOverlap, candidatesLarger])

/-- New overlap may stop a previously unique path earlier, but cannot remove
the ambiguity that path already exposed. -/
theorem reachesOverlap_mono {smaller larger : List Impl} (included : Included smaller larger)
    {goal : Goal} (overlap : ReachesOverlap smaller goal) : ReachesOverlap larger goal := by
  induction overlap with
  | here overlap => exact .here (headOverlap_mono included overlap)
  | descend unique constraint child ih =>
      rcases singleton_or_overlap included unique with unique | overlap
      · exact .descend unique constraint ih
      · exact .here overlap

theorem resolved_mono {smaller larger : List Impl} (included : Included smaller larger)
    (smallWellFormed : WellFormed smaller) (largeWellFormed : WellFormed larger) (goal : Goal)
    (resolved : resolve smaller smallWellFormed goal = .resolved) :
    resolve larger largeWellFormed goal = .resolved ∨
      resolve larger largeWellFormed goal = .ambiguous := by
  have derived := derives_mono included (resolve_sound smaller smallWellFormed goal resolved)
  by_cases overlap : ReachesOverlap larger goal
  · exact Or.inr ((resolve_ambiguous_iff larger largeWellFormed goal).mpr overlap)
  · exact Or.inl (resolve_complete larger largeWellFormed goal derived overlap)

theorem resolved_ne_noImpl {smaller larger : List Impl} (included : Included smaller larger)
    (smallWellFormed : WellFormed smaller) (largeWellFormed : WellFormed larger) (goal : Goal)
    (resolved : resolve smaller smallWellFormed goal = .resolved) :
    resolve larger largeWellFormed goal ≠ .noImpl := by
  intro missing
  rcases resolved_mono included smallWellFormed largeWellFormed goal resolved with success | ambiguous
  · rw [missing] at success
    cases success
  · rw [missing] at ambiguous
    cases ambiguous

theorem ambiguous_mono {smaller larger : List Impl} (included : Included smaller larger)
    (smallWellFormed : WellFormed smaller) (largeWellFormed : WellFormed larger) (goal : Goal)
    (ambiguous : resolve smaller smallWellFormed goal = .ambiguous) :
    resolve larger largeWellFormed goal = .ambiguous :=
  (resolve_ambiguous_iff larger largeWellFormed goal).mpr
    (reachesOverlap_mono included ((resolve_ambiguous_iff smaller smallWellFormed goal).mp ambiguous))

theorem unique_head_preserved {smaller larger : List Impl} (included : Included smaller larger)
    (goal : Goal) {first second : Impl}
    (smallUnique : candidates smaller goal = [first])
    (largeUnique : candidates larger goal = [second]) : first = second := by
  have member := candidates_included included goal (smallUnique ▸ List.mem_singleton_self first)
  simpa [largeUnique] using member

theorem derives_congr {left right : List Impl}
    (same : ∀ implementation, implementation ∈ left ↔ implementation ∈ right) (goal : Goal) :
    Derives left goal ↔ Derives right goal :=
  ⟨derives_mono (fun implementation => (same implementation).mp),
    derives_mono (fun implementation => (same implementation).mpr)⟩

theorem reachesOverlap_congr {left right : List Impl}
    (same : ∀ implementation, implementation ∈ left ↔ implementation ∈ right) (goal : Goal) :
    ReachesOverlap left goal ↔ ReachesOverlap right goal :=
  ⟨reachesOverlap_mono (fun implementation => (same implementation).mp),
    reachesOverlap_mono (fun implementation => (same implementation).mpr)⟩

/-- Candidate order and duplicate occurrences have no effect, including the
priority of ambiguity over a missing sibling constraint. -/
theorem resolve_congr {left right : List Impl}
    (same : ∀ implementation, implementation ∈ left ↔ implementation ∈ right)
    (leftWellFormed : WellFormed left) (rightWellFormed : WellFormed right) (goal : Goal) :
    resolve left leftWellFormed goal = resolve right rightWellFormed goal := by
  have success : resolve left leftWellFormed goal = .resolved ↔
      resolve right rightWellFormed goal = .resolved := by
    rw [RoleConstraints.resolve_exact, RoleConstraints.resolve_exact]
    exact and_congr (derives_congr same goal) (not_congr (reachesOverlap_congr same goal))
  have ambiguous : resolve left leftWellFormed goal = .ambiguous ↔
      resolve right rightWellFormed goal = .ambiguous := by
    rw [resolve_ambiguous_iff, resolve_ambiguous_iff]
    exact reachesOverlap_congr same goal
  cases leftResult : resolve left leftWellFormed goal <;>
    cases rightResult : resolve right rightWellFormed goal <;> simp_all

theorem resolve_perm {left right : List Impl} (permutation : left.Perm right)
    (leftWellFormed : WellFormed left) (rightWellFormed : WellFormed right) (goal : Goal) :
    resolve left leftWellFormed goal = resolve right rightWellFormed goal :=
  resolve_congr (fun _ => permutation.mem_iff) leftWellFormed rightWellFormed goal

theorem resolve_duplicate_list (impls : List Impl) (wellFormed : WellFormed impls)
    (duplicatedWellFormed : WellFormed (impls ++ impls)) (goal : Goal) :
    resolve (impls ++ impls) duplicatedWellFormed goal = resolve impls wellFormed goal :=
  resolve_congr (fun _ => by simp) duplicatedWellFormed wellFormed goal

namespace Examples

def value : Term := .app 20 []
def otherValue : Term := .app 21 []
def requirement : Goal := ⟨7, [value]⟩
def otherRequirement : Goal := ⟨7, [otherValue]⟩
def firstImpl : Impl := ⟨7, [value], [], 100⟩
def secondImpl : Impl := ⟨7, [value], [], 101⟩
def otherImpl : Impl := ⟨7, [otherValue], [], 102⟩

theorem first_wellFormed : WellFormed [firstImpl] := by
  simp [WellFormed, Impl.WellFormed, firstImpl]
theorem second_wellFormed : WellFormed [secondImpl] := by
  simp [WellFormed, Impl.WellFormed, secondImpl]
theorem both_wellFormed : WellFormed [firstImpl, secondImpl] := by
  simp [WellFormed, Impl.WellFormed, firstImpl, secondImpl]
theorem unrelated_wellFormed : WellFormed [firstImpl, secondImpl, otherImpl] := by
  simp [WellFormed, Impl.WellFormed, firstImpl, secondImpl, otherImpl]

theorem separate_callers_resolve :
    resolve [firstImpl] first_wellFormed requirement = .resolved ∧
      resolve [secondImpl] second_wellFormed requirement = .resolved := by
  constructor
  · rw [resolve_one [firstImpl] first_wellFormed requirement firstImpl (by decide)]
    rfl
  · rw [resolve_one [secondImpl] second_wellFormed requirement secondImpl (by decide)]
    rfl

theorem jointly_visible_is_ambiguous :
    resolve [firstImpl, secondImpl] both_wellFormed requirement = .ambiguous :=
  resolve_many [firstImpl, secondImpl] both_wellFormed requirement firstImpl secondImpl [] (by decide)

/-- Overlap elsewhere does not cause a global coherence rejection. -/
theorem unrelated_overlap_is_allowed :
    resolve [firstImpl, secondImpl, otherImpl] unrelated_wellFormed otherRequirement = .resolved := by
  rw [resolve_one [firstImpl, secondImpl, otherImpl] unrelated_wellFormed otherRequirement otherImpl (by decide)]
  rfl

end Examples

end Yulang.RoleVisibility
