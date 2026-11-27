import Yulang.GeneralDeclarationPatterns

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CapturedNormalForm462
open GeneralDeclarationPatterns

private theorem hidden_names_commute (x y : Nat) : ∀ p : Pattern,
    hide x (hide y p) = hide y (hide x p)
  | .record label payload tail => by
    have ih := hidden_names_commute x y tail
    by_cases xEq : x = label <;> by_cases yEq : y = label <;>
      simp [hide,xEq,yEq] at * <;> try rw [ih]
  | .app _ _ | .variant _ _ | .join _ _ | .var _ => rfl

private theorem remove_written_shadow_before_capture (name : Nat)
    (cap : Nat → Pattern) : ∀ p : Pattern,
    hide name (normalize ((hide name p).subst cap)) =
      hide name (normalize (p.subst cap))
  | .record label payload tail => by
    have ih := remove_written_shadow_before_capture name cap tail
    by_cases same : name = label
    · subst label
      simpa [hide,Pattern.subst,normalize,hide_idempotent] using ih
    · simp only [hide,same,ite_false,Pattern.subst,normalize]
      rw [hidden_names_commute name label,hidden_names_commute name label,ih]
  | .app _ _ | .variant _ _ | .join _ _ | .var _ => rfl

/- A uniform *auxiliary* normalization certificate compiler. This retains
the caller's actual written source. It does not compile candidate visits,
read a graph, or decide additional source equivalences. -/
mutual
  def simplify : Pattern → Pattern
    | .var n => .var n
    | .app k args => .app k (simplifyArgs args)
    | .record l p t => .record l (simplify p) (hide l (simplify t))
    | .variant k p => .variant k (simplify p)
    | .join a b =>
      let x := simplify a
      let y := simplify b
      if x = y then x else .join x y

  def simplifyArgs : List Pattern → List Pattern
    | [] => []
    | h :: t => simplify h :: simplifyArgs t
end

mutual
  theorem same_captured_normal_form (cap : Nat → Pattern) :
      ∀ p, normalize ((simplify p).subst cap) = normalize (p.subst cap)
    | .var _ => rfl
    | .app k args => by
      simp only [simplify,Pattern.subst,normalize,same_captured_normal_args cap args]
    | .record label payload tail => by
      simp only [simplify,Pattern.subst,normalize,remove_written_shadow_before_capture,
        same_captured_normal_form cap payload,same_captured_normal_form cap tail]
    | .variant k p => by
      simp only [simplify,Pattern.subst,normalize,same_captured_normal_form cap p]
    | .join first last => by
      have left := same_captured_normal_form cap first
      have right := same_captured_normal_form cap last
      simp only [simplify]
      split
      · rename_i identical
        have after : normalize (first.subst cap) = normalize (last.subst cap) := by
          rw [← left,← right,identical]
        rw [left]
        simp [Pattern.subst,normalize,after,merge]
      · simp only [Pattern.subst,normalize,left,right]

  theorem same_captured_normal_args (cap : Nat → Pattern) :
      ∀ ps, normalizeArgs (substArgs cap (simplifyArgs ps)) = normalizeArgs (substArgs cap ps)
    | [] => rfl
    | p :: ps => by
      simp only [simplifyArgs,substArgs,normalizeArgs,same_captured_normal_form cap p,
        same_captured_normal_args cap ps]
end

theorem same_original_captured_counts (cap : Nat → Pattern) (ps : List Pattern) :
    counted (substArgs cap (simplifyArgs ps)) = counted (substArgs cap ps) :=
  congrArg encodeArgs (same_captured_normal_args cap ps)

end Yulang.GeneralDeclarativeI65.I72.CapturedNormalForm462
