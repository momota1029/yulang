import Yulang.GeneralDeclarativeI65I74ReadComputedRosterCompleteness486
import Yulang.GeneralDeclarativeI65I74ReadyAuthorizedRoster486
import Yulang.GeneralDeclarativeI65I74FiniteCandidatePalette486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions graphOf)
open LiteralVisits473 (Checkpoint GuardedObservationInput read_checkpoint_guards)
open TypedRootSafety482 (requestRootCheck noRootReturnBool)
open CommonRoleRegularGraph (successors)
open GeneralDeclarations (Declaration)
open Producer479 (Site)

private theorem a_checked_initial_root_covers_every_old_geometry_successor
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {here next : Fin n} (h : GuardedObservationInput s pos rel here)
    (moves : next ∈ successors (graphOf s pos) here) :
    GuardedObservationInput s pos rel next :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,
    (fun i tail => h.2.2.2.2.1 i (.cons moves tail)),fun i tail => h.2.2.2.2.2 i (.cons moves tail)⟩

theorem a_complete_palette_suffices_on_every_descendant_of_an_exact_checked_root486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {palette : SignedPalette486 n} (complete : CompletePalette486 s pos rel palette)
    (fuel : Nat) (site : Site s pos) (guard : GuardedObservationInput s pos rel site.index) :
    paletteReadyWithinOriginalBudget486 rel palette fuel site = true := by
  induction fuel generalizing site with
  | zero =>
    obtain ⟨bit,read⟩ := complete site.index guard
    simp [paletteReadyWithinOriginalBudget486,read]
  | succ rest ih =>
    obtain ⟨bit,read⟩ := complete site.index guard
    cases bit with
    | true => simp [paletteReadyWithinOriginalBudget486,read]
    | false =>
      simp only [paletteReadyWithinOriginalBudget486,read,List.all_eq_true]
      intro pair member
      obtain ⟨hop⟩ := finite_hops_are_exact_existing_written_visits486.mp member
      exact ih pair.2 (a_checked_initial_root_covers_every_old_geometry_successor guard hop.edge)

private theorem root_checker_supplies_full_guards_for_its_exact_coordinate_list
    {n : Nat} (s : GeneralDeclarativeI65.State) (pos : Positions n) (rel : List (Fin n × Fin n))
    (lower : List Nat) (roots : List (Checkpoint n))
    (safe : noRootReturnBool s pos rel lower roots = true) :
    ∀ i ∈ roots.map Checkpoint.which, GuardedObservationInput s pos rel i := by
  induction lower generalizing roots with
  | nil => cases roots <;> simp_all [noRootReturnBool]
  | cons current more ih =>
    cases roots with
    | nil => simp [noRootReturnBool] at safe
    | cons check rest =>
      obtain ⟨first,after⟩ := Bool.and_eq_true_iff.mp safe
      intro i used
      rcases List.mem_cons.mp used with same|member
      · exact same ▸ (read_checkpoint_guards (of_decide_eq_true first)).1
      · exact ih rest after i member

private theorem every_independent_argument_start_passes_the_geometry_preflight486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    (complete : CompletePalette486 p.old.state.core pos rel palette)
    (i offset : Nat) (roots : List (Fin n))
    (safe : ∀ coord ∈ roots, GuardedObservationInput p.old.state.core pos rel coord)
    (starts : ∀ j coord, roots[j]? = some coord → Nonempty (OriginalArgumentStart486 p gd pos i (offset+j) coord)) :
    allOriginalArgumentPalettesReady486 p gd pos rel palette i offset roots = true := by
  induction roots generalizing offset with
  | nil => rfl
  | cons exact rest ih =>
    obtain ⟨head⟩ := starts 0 exact rfl
    change OriginalArgumentStart486 p gd pos i offset exact at head
    have selected := independently_checked_arg_start_replays_at_exact_original_roster_and_demand_coordinate486 head
    have geometry := a_complete_palette_suffices_on_every_descendant_of_an_exact_checked_root486
      complete (originalNodeBudget486 head.site.pattern) head.site (safe exact (List.mem_cons_self ..))
    have tail := ih (offset+1) (fun atPoint member => safe atPoint (List.mem_cons_of_mem _ member))
      (fun j root witness => by
        have actual := starts (j+1) root witness
        simpa [Nat.add_assoc,Nat.add_comm 1 j] using actual)
    simp only [allOriginalArgumentPalettesReady486,selected,geometry,tail,Bool.and_true]

theorem checked_palette_and_original_candidate_data_reify_pre_election_at_exact_demand_roots486
    {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n))
    (palette : SignedPalette486 n) (complete : CompletePalette486 p.old.state.core pos rel palette)
    (roots : List (Checkpoint n)) (permit : Nat → CandidateVisitKey485 n → Bool)
    (Authorized : Nat → CandidateVisitKey485 n → Prop)
    (permission : ∀ ord key, permit ord key = true → Authorized ord key)
    (rootsChecked : requestRootCheck p pos rel roots = true)
    (count : roots.length = p.old.root.demand.arguments.length)
    (actualArity : ∀ (i : Nat) (d : Declaration), (visible485 p)[i]? = some d →
      d.head.length = p.old.root.demand.arguments.length)
    (starts : ∀ i : Fin (visible485 p).length, ∀ argument root,
      (roots.map Checkpoint.which)[argument]? = some root →
      Nonempty (OriginalArgumentStart486 p gd pos i.val argument root)) :
    ∃ bits : List (Nat × Bool),
      readPaletteCoveredPreElection486 p gd pos rel palette roots permit = some (gate485 bits) := by
  obtain ⟨rows,bits,generated,tape,ran⟩ :=
    independently_scoped_all_canonical_head_coordinates_produce_a_rechecked_whole_tape486
      p gd pos rel palette complete roots permit Authorized permission rootsChecked count actualArity starts
  let lowers : List Nat := p.old.root.demand.arguments.map (fun a => a.lower)
  have checked : noRootReturnBool p.old.state.core pos rel lowers roots = true := rootsChecked
  have safe := root_checker_supplies_full_guards_for_its_exact_coordinate_list p.old.state.core pos rel
    lowers roots checked
  have all : wholeOriginalRosterPaletteReady486 p gd pos rel palette (roots.map Checkpoint.which) = true := by
    unfold wholeOriginalRosterPaletteReady486
    apply List.all_eq_true.mpr
    intro i member
    let idx : Fin (visible485 p).length := ⟨i,List.mem_range.mp member⟩
    apply every_independent_argument_start_passes_the_geometry_preflight486 complete _ _ _ safe
    intro argument root seen
    have start := starts idx argument root seen
    simpa using start
  refine ⟨bits,?_⟩
  change readPaletteCoveredPreElection486 p gd pos rel palette roots permit = some (gate485 bits)
  simp only [readPaletteCoveredPreElection486,rootsChecked,all,Bool.and_true,ite_true,ran]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
