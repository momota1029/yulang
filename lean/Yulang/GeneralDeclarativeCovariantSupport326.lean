import Yulang.GeneralDeclarativeCovariantResolve326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCovariantSupport326
open GeneralDeclarativePairDecl326
open GeneralDeclarativeCovariantState326
open GeneralDeclarativeCovariantProbe326 (alias_rank rank no_cycles)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff from_source from_completed pending_only)
open GeneralDeclarativeLowerKnown321 (Alias Ready alias_refl alias_mono knows_row)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeTrace321 (Trace)
open GeneralNominalMaterialization (Mode)

abbrev scalarRow : Equation := ⟨3,.primitive (.scalar .int) []⟩

/-- The ordinary state is unchanged. Only the sole origin for the
generated child's scalar lower observation is moved to a late output. -/
def controlled (done : Nat → Prop) : Supported final done :=
  ⟨fun row origin =>
    (row ∈ sourceRows ∧ row.left ≠ 3 ∧ origin = .source) ∨
    (row = scalarRow ∧ origin = .output 42) ∨
    (row = parentRow ∧ origin = .output 1) ∨ (row = childRow ∧ origin = .output 2),by
      intro row origin given
      rcases given with old|⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩
      · exact old_row old.1
      · exact old_row (by simp [sourceRows])
      · exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
      · exact List.mem_append_right _ List.mem_cons_self⟩

theorem source_outer (done : Nat → Prop) {row : Equation} (recorded : row ∈ sourceRows)
    (outside : row.left ≠ 3) : row ∈ (restriction (controlled done)).equations :=
  from_source _ (.inl ⟨recorded,outside,rfl⟩)

theorem scalar_unavailable (done : Nat → Prop) (notYet : ¬done 42) :
    scalarRow ∉ (restriction (controlled done)).equations := by
  apply pending_only (controlled done)
  intro origin known
  rcases known with old|late|someParent|someChild
  · exact False.elim (old.2.1 rfl)
  · exact ⟨42,late.2,notYet⟩
  · have unequal := congrArg Equation.left someParent.1
    cases unequal
  · have unequal := congrArg Equation.left someChild.1
    cases unequal

theorem child_waits (done : Nat → Prop) (notYet : ¬done 42) : ¬Ready (controlled done) child := by
  intro ready
  obtain ⟨tag,row,stored,alias,shape⟩ := ready leftArg List.mem_cons_self
  have rows : (restriction (controlled done)).equations ⊆ final.equations := by
    intro e present
    obtain ⟨origin,old,_⟩ := (backed_iff (controlled done) e).mp present
    exact (controlled done).ordinary old
  have relaxed := alias_mono (s := restriction (controlled done)) (t := final) rfl rows alias
  have positions := alias_rank relaxed
  have member := rows stored
  simp only [final,middle,appendFacts,sourceRows,List.cons_append,List.nil_append,List.mem_cons,
    List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h <;> cases h
  · exact (show rank 3 ≠ rank 0 by decide +kernel) positions
  · exact (show rank 3 ≠ rank 2 by decide +kernel) positions
  · exact scalar_unavailable done notYet stored
  · exact (show rank 3 ≠ rank 11 by decide +kernel) positions
  · exact (show rank 3 ≠ rank 11 by decide +kernel) positions
  · cases shape
  · cases shape

theorem child_ready_iff (done : Nat → Prop) : Ready (controlled done) child ↔ done 42 := by
  constructor
  · intro enough
    apply Classical.byContradiction
    intro missing
    exact child_waits done missing enough
  · intro now arg there
    cases List.mem_singleton.mp there
    exact ⟨_,knows_row (from_completed (controlled done) (show
      (controlled done).derivesFrom scalarRow (.output 42) from .inr (.inl ⟨rfl,rfl⟩)) now) rfl⟩

theorem lower (done : Nat → Prop) :
    Trace (restriction (controlled done)) .lower 0 normalCode [⟨0,.lower,3⟩,⟨1,.lower,3⟩] :=
  .primitive (args := [3,3]) (alias_refl _) (source_outer done List.mem_cons_self (by decide +kernel))
    (.cons .capture (.cons .capture .nil))

theorem upper (done : Nat → Prop) :
    Trace (restriction (controlled done)) .upper 2 normalCode [⟨0,.upper,4⟩,⟨1,.upper,4⟩] :=
  .primitive (args := [4,4]) (alias_refl _) (source_outer done
    (show (⟨2,hi⟩ : Equation) ∈ sourceRows by simp [sourceRows]) (by decide +kernel)) (.cons .capture (.cons .capture .nil))

end Yulang.GeneralDeclarativeCovariantSupport326
