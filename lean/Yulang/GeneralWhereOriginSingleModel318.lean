import Yulang.GeneralWhereOriginSingleCells318
import Yulang.GeneralWhereOriginSingleHead318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 7000000
namespace Yulang.GeneralWhereOriginSingleModel318
open GeneralWhereOriginSingleSource318
open GeneralWhereOriginSingleRead318 (old_reads new_reads)
open GeneralWhereOriginSingleCells318 (loOld loNow hi lower_moves upper_kept)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralWhereVersionCase317 (expr)
open GeneralWhereOriginDelta318 (Cell High)
open GeneralNominalVersionedExpressionFrame236 (variable_value)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCommonBridge (Assignment)
open GeneralFiniteTypedWrites312 (Write applyWrites reflexive)
open GeneralVersionedEndpointBatch315 (outside)
open GeneralVersionedEndpointAddress315 (atCell)
open CommonNominalFullCarrier

abbrev previousLo : Cell oldPlan :=
  ⟨otherChild,0,.lower,.variant 0 (.var 0),expr,List.mem_singleton_self _,rfl,(fun _ eq => by cases eq),rfl⟩
abbrev previousHi : Cell oldPlan :=
  ⟨otherChild,0,.upper,.variant 0 (.var 0),expr,List.mem_singleton_self _,rfl,(fun _ eq => by cases eq),rfl⟩
noncomputable abbrev presentLo : Cell newPlan :=
  ⟨otherChild,0,.lower,.variant 0 (.var 0),expr,List.mem_singleton_self _,rfl,(fun _ eq => by cases eq),rfl⟩
noncomputable abbrev presentHi : Cell newPlan :=
  ⟨otherChild,0,.upper,.variant 0 (.var 0),expr,List.mem_singleton_self _,rfl,(fun _ eq => by cases eq),rfl⟩

theorem old_lo_ne_hi : loOld ≠ hi := by
  intro eq
  have sides := (GeneralVersionedEndpointAddress315.fields
    (p := oldPlan) (q := oldPlan) (e := expr) (f := expr) rfl eq).2.2.1
  cases sides

theorem new_lo_ne_hi : loNow ≠ hi := by
  intro eq
  have sides := (GeneralVersionedEndpointAddress315.fields
    (p := newPlan) (q := oldPlan) (e := expr) (f := expr) rfl eq).2.2.1
  cases sides

theorem older_absent (k : Nat) (tag : High older.context.state k) :
    k ∉ GeneralNominalState.sources older.context.state := by
  rintro hit
  obtain ⟨key,high,eq⟩ := tag
  exact GeneralVersionedHighOrigins315.raw_absent GeneralLiveCompoundInstall316.initial_reachable high
    (eq ▸ hit)

theorem newer_absent (k : Nat) (tag : High newer.context.state k) :
    k ∉ GeneralNominalState.sources newer.context.state := by
  rintro hit
  obtain ⟨key,high,eq⟩ := tag
  exact GeneralVersionedHighOrigins315.raw_absent GeneralLiveCompoundUpperRefresh316.upper_reachable high
    (eq ▸ hit)

noncomputable def previous (m : Assignment) : Assignment :=
  applyWrites [(loOld,variant 0 (m 4).1),(hi,variant 0 (m 2).1)] [] m

noncomputable def patched (m : Assignment) : Assignment :=
  applyWrites [(loNow,variant 0 (m 2).1)] [] m

theorem previous_outside (m : Assignment) (n : Nat) (one : loOld ≠ n) (two : hi ≠ n) :
    m n = previous m n := by
  apply outside
  intro a found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with rfl|rfl
  · exact one
  · exact two

theorem patched_outside (m : Assignment) (n : Nat) (ne : loNow ≠ n) :
    m n = patched m n := by
  apply outside
  intro a found
  cases List.mem_singleton.mp found
  exact ne

theorem old_oldSources (m : Assignment) : Agree (GeneralNominalState.sources older.context.state) m (previous m) := by
  intro n present
  apply previous_outside
  · intro eq
    exact older_absent loOld (previousLo.high rfl) (eq.symm ▸ present)
  · intro eq
    exact older_absent hi (previousHi.high rfl) (eq.symm ▸ present)

theorem old_newSources (m : Assignment) : Agree (GeneralNominalState.sources newer.context.state) m (previous m) := by
  intro n present
  apply previous_outside
  · intro eq
    exact newer_absent loOld (previousLo.high rfl) (eq.symm ▸ present)
  · intro eq
    exact newer_absent hi (previousHi.high rfl) (eq.symm ▸ present)

theorem patch_oldSources (m : Assignment) : Agree (GeneralNominalState.sources older.context.state) m (patched m) := by
  intro n present
  apply patched_outside
  intro eq
  exact older_absent loNow (presentLo.high rfl) (eq.symm ▸ present)

theorem patch_newSources (m : Assignment) : Agree (GeneralNominalState.sources newer.context.state) m (patched m) := by
  intro n present
  apply patched_outside
  intro eq
  exact newer_absent loNow (presentLo.high rfl) (eq.symm ▸ present)

private theorem solves_two (k l : Nat) (ne : k ≠ l) (a b : Ty) (m : Assignment) :
    Equivalent (applyWrites [(k,a),(l,b)] [] m k).1 a ∧
    Equivalent (applyWrites [(k,a),(l,b)] [] m l).1 b := by
  have h : GeneralFiniteTypedWrites312.Coherent [(k,a),(l,b)] := by
    intro x ax y ay equal
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ax ay
    rcases ax with rfl|rfl <;> rcases ay with rfl|rfl
    · exact reflexive _
    · exact False.elim (ne equal)
    · exact False.elim (ne equal.symm)
    · exact reflexive _
  have solved := GeneralFiniteTypedWrites312.solves _ [] m h (fun _ _ impossible => by cases impossible)
  exact ⟨solved _ List.mem_cons_self,solved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

private theorem solves_one (k : Nat) (a : Ty) (m : Assignment) :
    Equivalent (applyWrites [(k,a)] [] m k).1 a := by
  have h : GeneralFiniteTypedWrites312.Coherent [(k,a)] := by
    intro x ax y ay _
    cases List.mem_singleton.mp ax
    cases List.mem_singleton.mp ay
    exact reflexive _
  exact GeneralFiniteTypedWrites312.solves _ [] m h (fun _ _ impossible => by cases impossible)
    _ (List.mem_singleton_self _)

theorem two_writes (m : Assignment) :
    Equivalent (previous m loOld).1 (variant 0 (m 4).1) ∧
    Equivalent (previous m hi).1 (variant 0 (m 2).1) :=
  solves_two loOld hi old_lo_ne_hi _ _ m

theorem new_write (m : Assignment) :
    Equivalent (patched m loNow).1 (variant 0 (m 2).1) :=
  solves_one loNow _ m

end Yulang.GeneralWhereOriginSingleModel318
