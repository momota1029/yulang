import Yulang.GeneralObservedLadderRefreshProgram301

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderCompilerLaws301
open GeneralObservedLadderJournalCompiler301
open GeneralObservedLadderJournalRows301 (rawRow attached)
open GeneralObservedLadderLedger301 (Phase)
open GeneralObservedLadderRoute301 (site focus)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalRecursiveCandidates (arguments Context)
open GeneralGeneratedDictionaryRun299 (Entry)

theorem probe_unary (c : Context) (bs : List (GeneralNominalInspection.Bounds c.state))
    (e : Entry) (found : probe c bs = some e) :
    e.children = [] ∨ ∃ child, e.children = [child] := by
  unfold probe at found
  dsimp only at found
  split at found
  · split at found
    · split at found
      · cases Option.some.inj found
        exact .inr ⟨_,rfl⟩
      · cases found
    · cases found
  · split at found
    · cases Option.some.inj found
      exact .inl rfl
    · cases found

theorem attached_sound (s : State roles) (i : Nat) (e : Entry) (found : table s i = some e) :
    ∃ row, rawRow s i = some row ∧
      (arguments s.core.erased.current.context row.occurrence).bind (probe s.core.erased.current.context) = some e ∧
      ∀ child ∈ e.children, attached s i child = true := by
  cases live : rawRow s i with
  | none => simp [table,receipt,live] at found
  | some row =>
    cases good : (arguments s.core.erased.current.context row.occurrence).bind
        (probe s.core.erased.current.context) with
    | none => simp [table,receipt,live,good] at found
    | some picked =>
      obtain ⟨bounds,_,probeEq⟩ := Option.bind_eq_some_iff.mp good
      rcases probe_unary s.core.erased.current.context bounds picked probeEq with bare|⟨child,one⟩
      · have eq : picked = e := by simpa [table,receipt,live,good,bare] using found
        subst picked
        exact ⟨row,rfl,good,by intro c hit; rw [bare] at hit; cases hit⟩
      · by_cases stored : attached s i child = true
        · have eq : picked = e := by simpa [table,receipt,live,good,one,stored] using found
          subst picked
          refine ⟨row,rfl,good,?_⟩
          intro c hit
          rw [one] at hit
          cases List.mem_singleton.mp hit
          exact stored
        · simp [table,receipt,live,good,one,stored] at found

theorem supports_actual_edge (p : Phase n k) (i : Nat) (e : Entry)
    (found : table p.state i = some e) (j : Nat) (member : j ∈ e.children) :
    i < k ∧ j = i+1 :=
  (GeneralObservedLadderJournalRows301.attached_exact p i j).mp
    (by obtain ⟨_,_,_,live⟩ := attached_sound p.state i e found; exact live j member)

end Yulang.GeneralObservedLadderCompilerLaws301
