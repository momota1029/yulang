import Yulang.GeneralRebaseInstallGrowth277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseMixedCounts277
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedKernel234 (Step Installable)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable QuietStep reachable_step split administrative_plans)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralRebaseQuietBound277 (Counted quiet_length)
open GeneralRebaseQuietBasis277 (sourceNames centerNames budget)
open GeneralRebaseInstallGrowth277 (reserveBudget centerBudget)
variable {roles : Roles.RoleDecls}

abbrev Actual (r : Registry) (root : Occurrence roles) := Step (registry r) root

inductive Runs (r : Registry) (root : Occurrence roles) : State roles → Nat → Nat → State roles → Prop
  | nil : Runs r root start 0 0 start
  | quiet : Runs r root start n k before → QuietStep r root before after → Runs r root start (n+1) k after
  | installs (e : Effect roles) : Runs r root start n k before → Installable (registry r) before e →
      Actual r root before (install before e) → Runs r root start (n+1) (k+1) (install before e)

theorem classified (formed : Reachable r root start) (trace : Counted (Actual r root) start n after) :
    ∃ k, Runs r root start n k after ∧ after.plans.length = start.plans.length + k ∧ Reachable r root after := by
  induction trace with
  | nil => exact ⟨0,.nil,rfl,formed⟩
  | tail _ action ih =>
    obtain ⟨k,done,counted,ready⟩ := ih
    rcases split ready action with update|⟨effect,enabled,_,rfl⟩
    · have eq : _ := congrArg List.length (administrative_plans update)
      exact ⟨k,.quiet done ⟨action,eq⟩,eq.trans counted,reachable_step ready action⟩
    · refine ⟨k+1,.installs effect done enabled action,?_,reachable_step ready action⟩
      change (_ :: _).length = start.plans.length + (k+1)
      rw [List.length_cons,counted,Nat.add_assoc]

theorem plan_count (walk : Runs r root start n k after) :
    after.plans.length = start.plans.length + k := by
  induction walk with
  | nil => rfl
  | quiet _ update ih => exact update.2.trans ih
  | installs e _ enabled move ih =>
    change (_ :: _).length = start.plans.length + (_+1)
    rw [List.length_cons,ih,Nat.add_assoc]

theorem count_monotone (walk : Runs r root start n k after) : k ≤ n := by
 induction walk with
 | nil => exact Nat.le_refl _
 | quiet _ _ ih => omega
 | installs _ _ _ _ ih => omega

def poly (m c : Nat) : Nat := m + m + m*m + c*c

def sourceCap (r : Registry) (start : State roles) (k : Nat) : Nat :=
  (sourceNames start).length + k * reserveBudget (registry r)

def centerCap (r : Registry) (start : State roles) (k : Nat) : Nat :=
  (centerNames start).length + k * centerBudget (registry r)

def quietCap (r : Registry) (start : State roles) (k : Nat) : Nat :=
  poly (sourceCap r start k) (centerCap r start k)

theorem poly_mono {m M c C : Nat} (source : m ≤ M) (center : c ≤ C) : poly m c ≤ poly M C :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add source source) (Nat.mul_le_mul source source))
    (Nat.mul_le_mul center center)

theorem budget_le (r : Registry) (start s : State roles) (k K : Nat)
    (kLe : k ≤ K) (m : (sourceNames s).length ≤ sourceCap r start k)
    (c : (centerNames s).length ≤ centerCap r start k) : budget s ≤ quietCap r start K := by
  unfold budget quietCap
  exact poly_mono
    (Nat.le_trans m (Nat.add_le_add_left (Nat.mul_le_mul_right _ kLe) _))
    (Nat.le_trans c (Nat.add_le_add_left (Nat.mul_le_mul_right _ kLe) _))

end Yulang.GeneralRebaseMixedCounts277
