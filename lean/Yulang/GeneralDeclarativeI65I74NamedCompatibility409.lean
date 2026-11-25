import Yulang.GeneralDeclarativeI65I74NamedPriority409

namespace Yulang.GeneralDeclarativeI65.I72.Named409
open GeneralDeclarativeI65 (visible)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarations (Declaration)
open Checker408 (Problem Result)

/-- The literal contents of a successful bare-name report are fixed by
the same visible declaration before selecting a model or producing a tree. -/
theorem bare_name_wire_exact409 (p : Problem) (r : Result) (w : NamedWire)
    (yes : check p r (.bareName w) = true) :
    ∃ (d : Declaration) (scope : visible p.state.core p.root = [d]) (source : VerifiedName p d),
      replayNamedHead p d scope w = some source ∧ r = Check408.nullaryReport d := by
  simp only [check] at yes
  split at yes
  · rename_i d scope
    obtain ⟨found,matchOut⟩ := splitAnd yes
    cases replay : replayNamedHead p d scope w with
    | none => simp [replay] at found
    | some named =>
      obtain ⟨sameTree,sameResult,sameWrites⟩ := Check408.matchesNoWrites_exact408.mp matchOut
      refine ⟨d,scope,named,replay,?_⟩
      cases r
      simp only at sameTree sameResult sameWrites
      subst_vars
      rfl
  · simp at yes

/-- The stronger compatibility property: this positive packet and either
past witness kind cannot both succeed on one Problem. Runtime dispatch
order is not needed to resolve an ambiguity between answers. -/
theorem named_and_prior_witnesses_cannot_both_succeed409 (p : Problem) (r a : Result)
    (w : NamedWire) (old : Checker408.Witness) (yes : check p r (.bareName w) = true) :
    check p a (.previous old) = false := by
  obtain ⟨d,_,packet,_,_⟩ := bare_name_wire_exact409 p r w yes
  cases success : check p a (.previous old) with
  | false => rfl
  | true =>
    have prior : Checker408.check p a old = true := success
    exfalso
    cases old with
    | unsupported => simp [Checker408.check] at prior
    | rawRoot wire =>
      have actual := ((Checker408.raw_closed_cycle_uses_the_same_checker408 p a wire).mp prior).1
      exact packet.rawSafe (GeneralDeclarativeWitnessCycle350.rooted actual)
    | nullary =>
      have branch := Checker408.accepted_implies_branch_engine408 p a .nullary prior
      obtain ⟨_,_,hdr,_⟩ := (Check408.bool_nullary_protocol_exact408 p a).mp branch
      have none := List.isEmpty_iff.mp (splitAnd (splitAnd hdr).1).2
      rw [packet.known.asked] at none
      cases none

theorem checked_results_are_unique409 (p : Problem) (r a : Result) (x y : Witness)
    (first : check p r x = true) (second : check p a y = true) : r = a := by
  cases x with
  | unsupported => simp [check] at first
  | previous old =>
    cases y with
    | unsupported => simp [check] at second
    | previous y => exact Checker408.checked_report_is_unique408 p r a old y first second
    | bareName named =>
      rw [named_and_prior_witnesses_cannot_both_succeed409 p a r named old second] at first
      cases first
  | bareName named =>
    cases y with
    | unsupported => simp [check] at second
    | previous y =>
      rw [named_and_prior_witnesses_cannot_both_succeed409 p r a named y first] at second
      cases second
    | bareName y =>
      obtain ⟨d,firstAt,_,_,firstReport⟩ := bare_name_wire_exact409 p r named first
      obtain ⟨e,secondAt,_,_,secondReport⟩ := bare_name_wire_exact409 p a y second
      have exactDecl := (List.cons.inj (firstAt.symm.trans secondAt)).1
      exact firstReport.trans ((congrArg Check408.nullaryReport exactDecl).trans secondReport.symm)

end Yulang.GeneralDeclarativeI65.I72.Named409
