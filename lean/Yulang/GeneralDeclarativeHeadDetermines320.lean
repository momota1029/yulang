import Yulang.GeneralDeclarativeNormalized320
import Yulang.GeneralNominalFiniteMeaning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12500
set_option maxHeartbeats 3300000
namespace Yulang.GeneralDeclarativeHeadDetermines320
open CommonNominalFullCarrier (Ty Equivalent)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalOriginTerms (Expr project)
open GeneralNominalFiniteMeaning (At denote project_value)
open GeneralNominalReadbackFunctionality (Canonical)
open GeneralNominalCenteredHeadMatPatternSemantics (Algebra eval evals eqv_refl eqv_symm eqv_trans
  record_congr variant_congr union_congr)
open GeneralDeclarationPatterns (Pattern normalize variablesArgs)
open GeneralNominalMatchedAssembly (Aligned)

theorem at_source (m : Assignment) (n : Nat) (e : Ty)
    (equal : Equivalent (m n).1 e) : At m .actual (.source n) e := by
  refine ⟨⟨_,.source n⟩,?_⟩
  intro actual observed
  cases observed
  exact equal

theorem same_readback {m : Assignment} {root : Origin} {a b : Ty}
    (first : At m .actual root a) (last : At m .actual root b) :
    Equivalent a b := by
  obtain ⟨x,h⟩ := first.1
  exact eqv_trans (eqv_symm (first.2 x h)) (last.2 x h)

/-- Any visible capture of a canonical finite constructor head is
semantically determined by that head. Repeated variable positions are
not given separate substitutions. -/
theorem visible_capture (term : Expr α) (canonical : Canonical term) (first last : α → Ty)
    (whole : Equivalent (denote first term) (denote last term)) :
    ∀ name ∈ term.leaves, Equivalent (first name) (last name) := by
  induction term with
  | leaf x =>
    intro name used
    cases List.mem_singleton.mp used
    exact whole
  | node test children ih =>
    intro name used
    simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn] at used
    obtain ⟨_,⟨i,rfl⟩,member⟩ := used
    let rootModel : Assignment := fun _ => (denote first (.node test children),Common.rowEmpty)
    have a := project_value test canonical.1 (fun i => denote first (children i))
      (at_source rootModel 0 _ (eqv_refl _)) i
    have b := project_value test canonical.1 (fun i => denote last (children i))
      (at_source rootModel 0 _ whole) i
    exact ih i (canonical.2 i) (same_readback a b) name member

mutual
 theorem pattern_congruent (algebra : Algebra) (pattern : Pattern) {first last : Nat → Ty}
    (captures : ∀ n ∈ pattern.variables, Equivalent (first n) (last n)) :
    Equivalent (eval algebra first pattern) (eval algebra last pattern) := by
  cases pattern with
  | var name => exact captures name List.mem_cons_self
  | app name args => exact algebra.congruent name (patterns_congruent algebra args captures)
  | record label payload tail =>
    exact record_congr label
      (pattern_congruent algebra payload (fun i used => captures i (List.mem_append_left _ used)))
      (pattern_congruent algebra tail (fun i used => captures i (List.mem_append_right _ used)))
  | variant tag payload => exact variant_congr tag (pattern_congruent algebra payload captures)
  | join a b =>
    exact union_congr
      (pattern_congruent algebra a (fun i used => captures i (List.mem_append_left _ used)))
      (pattern_congruent algebra b (fun i used => captures i (List.mem_append_right _ used)))
 termination_by sizeOf pattern
 theorem patterns_congruent (algebra : Algebra) (patterns : List Pattern) {first last : Nat → Ty}
    (captures : ∀ n ∈ variablesArgs patterns, Equivalent (first n) (last n)) :
    Aligned Equivalent (evals algebra first patterns) (evals algebra last patterns) := by
  cases patterns with
  | nil => exact .nil
  | cons head rest =>
    exact .cons (pattern_congruent algebra head (fun n used => captures n (List.mem_append_left _ used)))
      (patterns_congruent algebra rest (fun n used => captures n (List.mem_append_right _ used)))
 termination_by sizeOf patterns
end

/-- A normalized associated source expression using only visible head
variables is independent of which equivalent actual capture was used.
A variable supplied by a where child needs that child's separate evidence. -/
theorem normalized_output_determined (terms : List (Expr Nat)) (first last : Nat → Ty)
    (canonical : ∀ t ∈ terms, Canonical t)
    (equal : ∀ t ∈ terms, Equivalent (denote first t) (denote last t))
    (algebra : Algebra) (rhs : Pattern)
    (scope : ∀ n ∈ (normalize rhs).variables, n ∈ terms.flatMap Expr.leaves) :
    Equivalent (eval algebra first (normalize rhs)) (eval algebra last (normalize rhs)) := by
  apply pattern_congruent
  intro name used
  obtain ⟨term,listed,present⟩ := List.mem_flatMap.mp (scope name used)
  exact visible_capture term (canonical term listed) first last (equal term listed) name present

end Yulang.GeneralDeclarativeHeadDetermines320
