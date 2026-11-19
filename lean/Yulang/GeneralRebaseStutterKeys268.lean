import Yulang.GeneralRebaseWeakTerminal268
import Yulang.FiniteWorklist

namespace Yulang.GeneralRebaseStutterKeys268
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseWeakProgress268 (Stutter Lull)
open GeneralRebaseWeakTerminal268 (append)
open FiniteWorklist (Path reachable)

structure Keys (n : Nat) (roles : Roles.RoleDecls) where
 key : State roles → Fin n
 adj : Fin n → List (Fin n)

structure Valid (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (k : Keys n roles) (region : State roles → Prop) : Prop where
 closed : ∀ first last, region first → Stutter registry root owners pool first last → region last
 forward : ∀ first last, region first → Stutter registry root owners pool first last → k.key last ∈ k.adj (k.key first)
 backward : ∀ first next, region first → next ∈ k.adj (k.key first) →
   ∃ after, Stutter registry root owners pool first after ∧ k.key after = next

def visit (k : Keys n roles) (state : State roles) : List (Fin n) :=
 reachable k.adj n (k.key state)

theorem region_after_lull (k : Keys n roles) (valid : Valid registry root owners pool k region)
 (lull : Lull registry root owners pool first last) (start : region first) : region last := by
 induction lull with
 | refl => exact start
 | tail _ moved ih => exact valid.closed _ _ (ih) moved

theorem path_of_lull (k : Keys n roles) (valid : Valid registry root owners pool k region)
 (lull : Lull registry root owners pool first last) (start : region first) : Path k.adj (k.key first) (k.key last) := by
 induction lull with
 | refl => exact .nil _
 | tail past moved ih =>
   exact (ih).append (.cons (valid.forward _ _ (region_after_lull k valid past start) moved) (.nil _))

theorem lift_path {registry : Registry} {root : Occurrence roles} {owners : List Nat} {pool : List Output}
 (k : Keys n roles) (valid : Valid registry root owners pool k region)
 (path : Path k.adj first last) (start : State roles) (same : k.key start = first) (allowed : region start) :
 ∃ finish, Lull registry root owners pool start finish ∧ k.key finish = last := by
 induction path generalizing start with
 | nil _ => exact ⟨start,.refl,same⟩
 | cons edge _ ih =>
   obtain ⟨after,actual,mid⟩ := valid.backward start _ allowed (same.symm ▸ edge)
   obtain ⟨final,tail,ends⟩ := ih after mid (valid.closed _ _ allowed actual)
   exact ⟨final,append (.tail .refl actual) tail,ends⟩

theorem visit_exact (k : Keys n roles) (valid : Valid registry root owners pool k region)
 (start : State roles) (allowed : region start) (target : Fin n) :
 target ∈ visit k start ↔ ∃ final, Lull registry root owners pool start final ∧ k.key final = target := by
 have reachableExact := FiniteWorklist.reachable_exact k.adj n (List.finRange n) (by simp) (by simp) (k.key start) target
 constructor
 · intro listed
   exact lift_path k valid (reachableExact.mp listed) start rfl allowed
 · rintro ⟨final,trace,same⟩
   exact reachableExact.mpr (same ▸ path_of_lull k valid trace allowed)

end Yulang.GeneralRebaseStutterKeys268
