import Yulang.GeneralRebaseMixedCounts277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseMixedLength277
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable QuietStep reachable_step same_length_administrative)
open GeneralRebaseQuietBasis277 (sourceNames centerNames source_administrative)
open GeneralRebaseQuietBound277 (Counted quiet_length)
open GeneralRebaseInstallGrowth277 (install_sources install_centers source_le_of_subset)
open GeneralRebaseMixedOwnedTrace277 (adapter_reachable)
open GeneralRebaseMixedCounts277
variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
variable {start finish : State roles}

structure Slice (r : Registry) (root : Occurrence roles) (start : State roles)
    (K n k : Nat) (finish : State roles) : Prop where
  reached : Reachable r root finish
  sources : (sourceNames finish).length ≤ sourceCap r start k
  centers : (centerNames finish).length ≤ centerCap r start k
  suffix : ∃ anchor : State roles, ∃ spent tail : Nat,
    Reachable r root anchor ∧ (sourceNames anchor).length ≤ sourceCap r start k ∧
    (centerNames anchor).length ≤ centerCap r start k ∧
    Counted (QuietStep r root) anchor tail finish ∧ n = spent + tail ∧
    spent ≤ k * (quietCap r start K + 1)

theorem summarize (initial : Reachable r root start)
    (walk : Runs r root start n k finish) {K : Nat} (cap : k ≤ K) :
    Slice r root start K n k finish := by
  induction walk with
  | nil =>
    have source : (sourceNames start).length ≤ sourceCap r start 0 := by simp [sourceCap]
    have center : (centerNames start).length ≤ centerCap r start 0 := by simp [centerCap]
    exact ⟨initial,source,center,⟨start,0,0,initial,source,center,.nil,rfl,by simp⟩⟩
  | @quiet n k before after path quiet ih =>
    have previous := ih cap
    have admin := same_length_administrative previous.reached quiet.1 quiet.2
    have source := Nat.le_trans
      (source_le_of_subset (source_administrative (adapter_reachable previous.reached) admin)) previous.sources
    have center : (centerNames after).length ≤ centerCap r start k := by
      unfold centerNames
      rw [GeneralNominalVersionedMixedAdministrative236.sites admin]
      exact previous.centers
    obtain ⟨anchor,spent,tail,reached,baseSource,baseCenter,trail,decompose,bound⟩ := previous.suffix
    exact ⟨reachable_step previous.reached quiet.1,source,center,
      ⟨anchor,spent,tail+1,reached,baseSource,baseCenter,.tail trail quiet,by omega,bound⟩⟩
  | @installs n k before effect path enabled move ih =>
    have low : k ≤ K := by omega
    have previous := ih low
    have newReach := reachable_step previous.reached move
    have sCount := Nat.le_trans (install_sources effect enabled)
      (Nat.add_le_add_right previous.sources _)
    have cCount := Nat.le_trans (install_centers effect enabled)
      (Nat.add_le_add_right previous.centers _)
    have source : (sourceNames (GeneralNominalVersionedInstall232.install before effect)).length ≤ sourceCap r start (k+1) := by
      simpa only [sourceCap,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using sCount
    have center : (centerNames (GeneralNominalVersionedInstall232.install before effect)).length ≤ centerCap r start (k+1) := by
      simpa only [centerCap,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using cCount
    obtain ⟨anchor,spent,tail,reached,baseSource,baseCenter,trail,decompose,bound⟩ := previous.suffix
    have tailBound := Nat.le_trans (quiet_length reached trail) (budget_le r start anchor k K low baseSource baseCenter)
    have total : n+1 ≤ (k+1) * (quietCap r start K+1) := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    exact ⟨newReach,source,center,⟨_,n+1,0,newReach,source,center,.nil,by simp,total⟩⟩

theorem mixed_length (initial : Reachable r root start) (walk : Runs r root start n k finish) :
    n ≤ k + (k+1) * quietCap r start k := by
  have all := summarize initial walk (Nat.le_refl k)
  obtain ⟨anchor,spent,tail,reached,baseSource,baseCenter,trail,decompose,bound⟩ := all.suffix
  have tailBound := Nat.le_trans (quiet_length reached trail)
    (budget_le r start anchor k k (Nat.le_refl _) baseSource baseCenter)
  rw [Nat.mul_add,Nat.mul_one] at bound
  rw [Nat.add_mul,Nat.one_mul]
  omega

/-- For every actual source trace of length n, its actual number of
installations k is the increase in the plan ledger, and the total length has
a uniform explicit bound in k, the starting name counts and the compiled
registry reservation/requirement sizes. The theorem does not bound k. -/
theorem actual_length (initial : Reachable r root start)
    (walk : Counted (Actual r root) start n finish) :
    ∃ k, finish.plans.length = start.plans.length + k ∧
      n ≤ k + (k+1) * quietCap r start k := by
  obtain ⟨k,counted,names,_⟩ := classified initial walk
  exact ⟨k,names,mixed_length initial counted⟩

end Yulang.GeneralRebaseMixedLength277
