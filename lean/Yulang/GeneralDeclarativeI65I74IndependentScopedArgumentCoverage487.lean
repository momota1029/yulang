import Yulang.GeneralDeclarativeI65I74IndependentScopedVisitCoverage487
import Yulang.GeneralDeclarativeI65I74CompileScopedRoster487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

theorem generated_ordered_arguments_cover_every_and_only_independent_scoped_original_argument487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {i : Nat} {permit : CandidateVisitKey485 n → Bool} {offset : Nat} {roots : List (Fin n)}
    {keys wires}
    (ran : compileScopedArguments487 p gd pos rel palette i permit offset roots = some (keys,wires))
    (Allowed : CandidateVisitKey485 n → Prop)
    (lawful : ∀ key, permit key = true ↔ Allowed key) (key : CandidateVisitKey485 n) :
    key ∈ keys ↔ ∃ root argument, (root,argument) ∈ roots.zipIdx offset ∧
      ∃ head : OriginalArgumentStart486 p gd pos i argument root,
        IndependentScopedVisit487 rel argument head.site Allowed key := by
  induction roots generalizing offset keys wires with
  | nil =>
    have both : ([],[]) = (keys,wires) := Option.some.inj ran
    have keysEmpty : [] = keys := congrArg Prod.fst both
    rw [← keysEmpty]
    simp
  | cons root tail ih =>
    cases start : readOriginalArgumentStart486 p gd pos i offset root with
    | none => simp [compileScopedArguments487,start] at ran
    | some head =>
      cases front : compileScopedFootprint487 rel palette offset head.site permit with
      | none => simp [compileScopedArguments487,start,front,Option.bind] at ran
      | some pair =>
        obtain ⟨frontKeys,frontWires⟩ := pair
        cases rest : compileScopedArguments487 p gd pos rel palette i permit (offset+1) tail with
        | none => simp [compileScopedArguments487,start,front,rest,Option.bind] at ran
        | some pair =>
          obtain ⟨moreKeys,moreWires⟩ := pair
          have same : (frontKeys ++ moreKeys,frontWires ++ moreWires) = (keys,wires) :=
            Option.some.inj (by simpa [compileScopedArguments487,start,front,rest,Option.bind] using ran)
          have orderedKeys : frontKeys ++ moreKeys = keys := congrArg Prod.fst same
          rw [← orderedKeys]
          rw [List.mem_append,List.zipIdx_cons]
          have localEquiv := successful_scoped_footprint_covers_exactly_independent_prefix_authorized_old_visits487
            front Allowed lawful key
          have moreEquiv := ih rest
          constructor
          · rintro (one | more)
            · exact ⟨root,offset,List.mem_cons_self ..,head,localEquiv.mp one⟩
            · obtain ⟨z,j,found,originalPath,proof⟩ := moreEquiv.mp more
              exact ⟨z,j,List.mem_cons_of_mem _ found,originalPath,proof⟩
          · rintro ⟨z,j,found,originalPath,proof⟩
            rcases List.mem_cons.mp found with top | other
            · cases top
              have known := independently_checked_arg_start_replays_at_exact_original_roster_and_demand_coordinate486
                originalPath
              have equal := Option.some.inj (known.symm.trans start)
              subst originalPath
              exact .inl (localEquiv.mpr proof)
            · exact .inr (moreEquiv.mpr ⟨z,j,other,originalPath,proof⟩)

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
