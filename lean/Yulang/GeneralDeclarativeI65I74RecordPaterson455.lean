import Yulang.GeneralDeclarationPatterns

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordPaterson455

open Roles (Term Subst substArgs argsBound argsOccurrences argsSize sumBelow
  sumBelow_add sumBelow_mono sumBelow_single)
open GeneralDeclarationPatterns (Pattern counted StableSmaller Smaller)

mutual
  theorem subst_term_counts455 (t : Term) (σ : Subst) (n v : Nat) (h : t.bound ≤ n) :
      (t.subst σ).occurrences v =
        sumBelow n (fun w => t.occurrences w * (σ w).occurrences v) := by
    cases t with
    | var w =>
      simp only [Term.bound] at h
      simp only [Term.subst,Term.occurrences]
      rw [sumBelow_single n w _ (by omega)]
    | app k ts =>
      simp only [Term.subst,Term.occurrences]
      exact subst_args_counts455 ts σ n v h
  theorem subst_args_counts455 (ts : List Term) (σ : Subst) (n v : Nat)
      (h : argsBound ts ≤ n) :
      argsOccurrences v (substArgs σ ts) =
        sumBelow n (fun w => argsOccurrences w ts * (σ w).occurrences v) := by
    cases ts with
    | nil =>
      have hz : ∀ n, sumBelow n (fun _ => 0) = 0 := by
        intro n
        induction n <;> simp_all [sumBelow]
      simp [substArgs,argsOccurrences,hz]
    | cons t ts =>
      simp only [argsBound,Nat.max_le] at h
      simp only [substArgs,argsOccurrences,Nat.add_mul]
      rw [sumBelow_add,subst_term_counts455 t σ n v h.1,subst_args_counts455 ts σ n v h.2]
end

theorem substituted_occurrences_preserve_order455 {head child : List Term}
    (counts : ∀ w, argsOccurrences w child ≤ argsOccurrences w head) (σ : Subst) (v : Nat) :
    argsOccurrences v (substArgs σ child) ≤ argsOccurrences v (substArgs σ head) := by
  let n := max (argsBound child) (argsBound head)
  rw [subst_args_counts455 child σ n v (Nat.le_max_left ..),
    subst_args_counts455 head σ n v (Nat.le_max_right ..)]
  exact sumBelow_mono n (fun w => Nat.mul_le_mul_right ((σ w).occurrences v) (counts w))

theorem substituted_size_strict455 {head child : List Term}
    (size : argsSize child < argsSize head)
    (counts : ∀ w, argsOccurrences w child ≤ argsOccurrences w head) (σ : Subst) :
    argsSize (substArgs σ child) < argsSize (substArgs σ head) := by
  let before : Roles.Goal := ⟨0,child⟩
  let decl : Roles.Impl := ⟨0,head,[before],0⟩
  have checked : decl.WellFormed := by
    intro c seen
    have eq : c = before := List.mem_singleton.mp seen
    subst c
    exact ⟨size,counts⟩
  exact Roles.size_decreases checked (c := before) List.mem_cons_self σ

def patternValues455 (cap : Nat → Pattern) : Subst :=
  fun v => (GeneralDeclarationPatterns.normalize (cap v)).encode

/-- Closed record header normalization must independently justify the two
substitution equations; size and variable counts then lift generically. -/
theorem stable_from_counted_substitution455 {head child : List Pattern}
    (headComm : ∀ cap, counted (GeneralDeclarationPatterns.substArgs cap head) =
      substArgs (patternValues455 cap) (counted head))
    (childComm : ∀ cap, counted (GeneralDeclarationPatterns.substArgs cap child) =
      substArgs (patternValues455 cap) (counted child))
    (small : Smaller head child) : StableSmaller head child := by
  intro cap
  unfold Smaller
  rw [headComm cap,childComm cap]
  exact ⟨substituted_size_strict455 small.1 small.2 _,
    fun v => substituted_occurrences_preserve_order455 small.2 _ v⟩

end Yulang.GeneralDeclarativeI65.I72.RecordPaterson455
