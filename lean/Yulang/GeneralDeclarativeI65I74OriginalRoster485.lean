import Yulang.GeneralDeclarativeI65I74G04Producer479
import Yulang.GeneralDeclarativeI65SelectedHeadBindings395

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

abbrev declared485 (p : FullProblem) := (authoredRegistry p.old.state.core.current).declarations
abbrev visible485 (p : FullProblem) := visible p.old.state.core p.old.root
abbrev role485 (p : FullProblem) (d : Declaration) : Bool := d.role == p.old.root.demand.role

def rosterCell485 (p : FullProblem) (i : Nat) : Option (Nat × Declaration) := do
  let declaration ← (visible485 p)[i]?
  let authored ← unfilterOrdinal395 (role485 p) (declared485 p) i
  pure (authored,declaration)

def OriginalRosterCell485 (p : FullProblem) (i : Nat) (source : Nat × Declaration) : Prop :=
  (visible485 p)[i]? = some source.2 ∧
  unfilterOrdinal395 (role485 p) (declared485 p) i = some source.1 ∧
  (declared485 p)[source.1]? = some source.2

theorem roster_cell_reads_exactly_its_two_original_slots485
    (p : FullProblem) (i : Nat) (source : Nat × Declaration) :
    rosterCell485 p i = some source ↔ OriginalRosterCell485 p i source := by
  constructor
  · intro ran
    unfold rosterCell485 at ran
    cases found : (visible485 p)[i]? with
    | none => simp [found] at ran
    | some row =>
      cases position : unfilterOrdinal395 (role485 p) (declared485 p) i with
      | none => simp [found,position] at ran
      | some atSource =>
        have eq : (atSource,row) = source := Option.some.inj (by simpa [found,position] using ran)
        clear ran
        cases eq
        obtain ⟨source,readAt,old⟩ := unfilterOrdinal395_exact (role485 p) (declared485 p) i found
        have same := Option.some.inj (readAt.symm.trans position)
        exact ⟨found,position,same ▸ old⟩
  · rintro ⟨visibleAt,sourceAt,_⟩
    rcases source with ⟨ord,row⟩
    simp [rosterCell485,visibleAt,sourceAt]

theorem no_visible_slot_is_lost_in_the_exact_roster485
    (p : FullProblem) (i : Fin (visible485 p).length) :
    ∃ cell, rosterCell485 p i.val = some cell := by
  have visibleAt : (visible485 p)[i.val]? = some (visible485 p)[i] :=
    List.getElem?_eq_getElem i.isLt
  obtain ⟨atSource,readAt,old⟩ := unfilterOrdinal395_exact (role485 p) (declared485 p) i.val visibleAt
  exact ⟨(atSource,_),(roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr ⟨visibleAt,readAt,old⟩⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
