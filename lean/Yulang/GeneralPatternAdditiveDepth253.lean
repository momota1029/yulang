import Yulang.GeneralDeclarationPatterns
namespace Yulang.GeneralPatternAdditiveDepth253
open GeneralDeclarationPatterns

mutual
 def depth : Pattern → Nat
 | .var _ => 0
 | .app _ args => 1 + depths args
 | .record _ payload tail => 1 + max (depth payload) (depth tail)
 | .variant _ payload => 1 + depth payload
 | .join first last => 1 + max (depth first) (depth last)
 def depths : List Pattern → Nat
 | [] => 0
 | first :: rest => max (depth first) (depths rest)
end

mutual
 theorem subst_depth (term : Pattern) (capture : Nat → Pattern) (bound : Nat)
 (held : ∀ name, depth (capture name) ≤ bound) :
 depth (term.subst capture) ≤ depth term + bound := by
 cases term with
 | var name => simpa only [Pattern.subst,depth,Nat.zero_add] using held name
 | app name args =>
   have lower := subst_depths args capture bound held
   simp only [Pattern.subst,depth]
   omega
 | record label payload tail =>
   have first := subst_depth payload capture bound held
   have last := subst_depth tail capture bound held
   simp only [Pattern.subst,depth]
   omega
 | variant tag payload =>
   have lower := subst_depth payload capture bound held
   simp only [Pattern.subst,depth]
   omega
 | join payload tail =>
   have first := subst_depth payload capture bound held
   have last := subst_depth tail capture bound held
   simp only [Pattern.subst,depth]
   omega
 theorem subst_depths (terms : List Pattern) (capture : Nat → Pattern) (bound : Nat)
 (held : ∀ name, depth (capture name) ≤ bound) :
 depths (substArgs capture terms) ≤ depths terms + bound := by
 cases terms with
 | nil => exact Nat.zero_le _
 | cons first rest =>
   have one := subst_depth first capture bound held
   have two := subst_depths rest capture bound held
   simp only [substArgs,depths]
   omega
end

mutual
 theorem rename_depth (term : Pattern) (names : Nat → Nat) :
 depth (term.subst (fun name => .var (names name))) = depth term := by
 cases term with
 | var => rfl
 | app => simp only [Pattern.subst,depth,rename_depths]
 | record => simp only [Pattern.subst,depth,rename_depth]
 | variant => simp only [Pattern.subst,depth,rename_depth]
 | join => simp only [Pattern.subst,depth,rename_depth]
 theorem rename_depths (terms : List Pattern) (names : Nat → Nat) :
 depths (substArgs (fun name => .var (names name)) terms) = depths terms := by
 cases terms with
 | nil => rfl
 | cons => simp only [substArgs,depths,rename_depth,rename_depths]
end

theorem member_depth (terms : List Pattern) (term : Pattern) (member : term ∈ terms) : depth term ≤ depths terms := by
 induction terms with
 | nil => cases member
 | cons first rest ih =>
   rcases List.mem_cons.mp member with rfl | member
   · exact Nat.le_max_left _ _
   · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

theorem substitution_from_pool (term : Pattern) (pool : List Pattern) (capture : Nat → Pattern)
 (closed : ∀ name, capture name ∈ pool) : depth (term.subst capture) ≤ depth term + depths pool :=
 subst_depth term capture (depths pool) (fun name => member_depth pool _ (closed name))

def tower : Nat → Pattern → Pattern
 | 0, term => term
 | n+1, term => .app 0 [tower n term]

theorem tower_depth (n : Nat) (term : Pattern) : depth (tower n term) = n + depth term := by
 induction n with
 | zero => simp [tower]
 | succ n ih => simp only [tower,depth,depths,ih,Nat.max_zero]; omega

theorem tower_subst (n : Nat) (term : Pattern) (capture : Nat → Pattern) :
 (tower n term).subst capture = tower n (term.subst capture) := by
 induction n with
 | zero => simp [tower]
 | succ n ih => simp only [tower,Pattern.subst,substArgs,ih]

theorem additive_bound_sharp (n : Nat) (term : Pattern) :
 depth ((tower n (.var 0)).subst (fun _ => term)) = depth (tower n (.var 0)) + depth term := by
 rw [tower_subst,tower_depth,tower_depth]
 rfl
end Yulang.GeneralPatternAdditiveDepth253
