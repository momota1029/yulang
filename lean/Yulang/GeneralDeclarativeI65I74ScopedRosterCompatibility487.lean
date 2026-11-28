import Yulang.GeneralDeclarativeI65I74CompileScopedRoster487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint GuardedObservationInput read_checkpoint_guards)
open TypedRootSafety482 (requestRootCheck noRootReturnBool)
open GeneralDeclarations (Declaration)

theorem scoped_candidate_preserves_original_ordinal_and_all_packets487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    (complete : CompletePalette486 p.old.state.core pos rel palette)
    (i : Nat) (permit : Nat → CandidateVisitKey485 n → Bool) (roots : List (Fin n))
    (guard : ∀ j ∈ roots, GuardedObservationInput p.old.state.core pos rel j)
    (coherent : ∀ arg root (head : OriginalArgumentStart486 p gd pos i arg root),
      originalTerminalPermissionRespectsPrefixes487 rel palette arg head.site (permit head.ordinal)) :
    compileScopedCandidate487 p gd pos rel palette roots permit i =
      compileOriginalCandidate486 p gd pos rel palette roots permit i := by
  unfold compileScopedCandidate487 compileOriginalCandidate486
  cases h : rosterCell485 p i with
  | none => rfl
  | some item =>
    obtain ⟨ordinal,decl⟩ := item
    change (if decl.head.length = p.old.root.demand.arguments.length &&
        roots.length = p.old.root.demand.arguments.length then _ else _) =
      (if decl.head.length = p.old.root.demand.arguments.length then _ else _)
    by_cases arity : decl.head.length = p.old.root.demand.arguments.length
    · by_cases count : roots.length = p.old.root.demand.arguments.length
      · have eq := scoped_arguments_reproduce_exact_ordered_packet_list487 (gd := gd) complete i (permit ordinal) 0 roots
          guard (fun arg root w => by
            have exactRoster := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr w.cell
            have same : ordinal = w.ordinal := congrArg Prod.fst (Option.some.inj (h.symm.trans exactRoster))
            rw [same]
            exact coherent arg root w)
        simp [arity,count,computeAllActualArgumentFootprints486,eq]
      · simp [arity,count,computeAllActualArgumentFootprints486]
    · simp [arity]

private theorem mapM_agrees_on_each_roster_position487
    {α β : Type} {f g : α → Option β} {xs : List α}
    (same : ∀ x ∈ xs, f x = g x) :
    xs.mapM (m := Option) f = xs.mapM (m := Option) g := by
  induction xs with
  | nil => rfl
  | cons x tail ih =>
    rw [List.mapM_cons,List.mapM_cons,same x (List.mem_cons_self ..)]
    rw [ih (fun v h => same v (List.mem_cons_of_mem _ h))]

theorem scoped_roster_reproduces_the_exact_old_packets_in_original_visible_order487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    (complete : CompletePalette486 p.old.state.core pos rel palette)
    (roots : List (Fin n)) (permit : Nat → CandidateVisitKey485 n → Bool)
    (guard : ∀ j ∈ roots, GuardedObservationInput p.old.state.core pos rel j)
    (coherent : OriginalRosterPermissionIsPrefixCoherent487 p gd pos rel palette permit) :
    compileScopedRoster487 p gd pos rel palette roots permit =
      compileWholeOriginalRoster486 p gd pos rel palette roots permit := by
  unfold compileScopedRoster487 compileWholeOriginalRoster486
  apply mapM_agrees_on_each_roster_position487
  intro i _
  exact scoped_candidate_preserves_original_ordinal_and_all_packets487 complete i permit roots guard (coherent i)

theorem all_checked_request_roots_carry_guards_and_exact_list_length487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {lowers : List Nat} {roots : List (Checkpoint n)}
    (safe : noRootReturnBool s pos rel lowers roots = true) :
    roots.length = lowers.length ∧
    ∀ i ∈ roots.map Checkpoint.which, GuardedObservationInput s pos rel i := by
  induction lowers generalizing roots with
  | nil => cases roots <;> simp_all [noRootReturnBool]
  | cons lower tail ih =>
    cases roots with
    | nil => simp [noRootReturnBool] at safe
    | cons ck after =>
      obtain ⟨head,rest⟩ := Bool.and_eq_true_iff.mp safe
      obtain ⟨len,guard⟩ := ih rest
      refine ⟨by simp [len],?_⟩
      intro i member
      rcases List.mem_cons.mp member with same | later
      · exact same ▸ (read_checkpoint_guards (of_decide_eq_true head)).1
      · exact guard i later

theorem scoped_roster_and_old_guarded_pre_election_have_identical_results487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    (complete : CompletePalette486 p.old.state.core pos rel palette)
    (roots : List (Checkpoint n)) (permit : Nat → CandidateVisitKey485 n → Bool)
    (coherent : OriginalRosterPermissionIsPrefixCoherent487 p gd pos rel palette permit) :
    readScopedPreElection487 p gd pos rel palette roots permit =
      readComputedPreElection486 p gd pos rel palette roots permit := by
  unfold readScopedPreElection487 readComputedPreElection486
  by_cases safe : requestRootCheck p pos rel roots = true
  · have both := all_checked_request_roots_carry_guards_and_exact_list_length487 safe
    rw [ite_eq_left safe,ite_eq_left safe,
      scoped_roster_reproduces_the_exact_old_packets_in_original_visible_order487 complete
        (roots.map Checkpoint.which) permit both.2 coherent]
  · rw [ite_eq_right safe,ite_eq_right safe]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
