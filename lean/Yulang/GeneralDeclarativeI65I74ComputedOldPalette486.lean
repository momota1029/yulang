import Yulang.GeneralDeclarativeI65I74BoundedCandidateGeometry486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open ObservationAlternatives473 (Positions oldPosition graphOf checkAlternatives readAlternatives)
open QuotientObservation471 (createCone checkCone cone embedded checked_cone_exact created_cone_exact
  constructPartition every_complete_graph_has_a_finite_partition partition_check_exact
  replayCone replay checkOnCycle classOf)
open LiteralVisits473 (GuardedObservationInput Checkpoint readCheck read_checkpoint_guards)

/-- Produce a certificate for an actual old coordinate from existing finite
cone and quotient constructors, then submit it to the unchanged reader.
This does not produce the original position table or source authority. -/
def computeOldObservationCheckpoint486 {n : Nat} (s : GeneralDeclarativeI65.State)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (root : Fin n) : Option (Checkpoint n) :=
  let scope := createCone (graphOf s pos) root
  if check : checkCone (graphOf s pos) root scope = true then
    let closed := (checked_cone_exact.mp check).2.2.1
    let result : Checkpoint n := ⟨root,_,_,scope,constructPartition (cone scope) closed⟩
    (readCheck s pos rel (oldPosition pos root) result).map (fun _ => result)
  else none

theorem computed_old_checkpoint_is_at_its_own_original_coordinate486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {root : Fin n} {ck : Checkpoint n}
    (out : computeOldObservationCheckpoint486 s pos rel root = some ck) :
    ck.which = root ∧ ∃ bit, readCheck s pos rel (oldPosition pos root) ck = some bit := by
  dsimp only [computeOldObservationCheckpoint486] at out
  split at out
  · rename_i good
    let scope := createCone (graphOf s pos) root
    let made : Checkpoint n := ⟨root,_,_,scope,constructPartition (cone scope)
      (checked_cone_exact.mp good).2.2.1⟩
    change (readCheck s pos rel (oldPosition pos root) made).map (fun _ => made) = some ck at out
    cases hit : readCheck s pos rel (oldPosition pos root) made with
    | none => simp [hit] at out
    | some bit =>
      have same : made = ck := by simpa [hit] using out
      subst ck
      exact ⟨rfl,⟨bit,hit⟩⟩
  · cases out

theorem old_input_guards_suffice_for_computing_an_exact_checkpoint486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {root : Fin n}
    (inputs : GuardedObservationInput s pos rel root) :
    ∃ ck, computeOldObservationCheckpoint486 s pos rel root = some ck := by
  obtain ⟨labels,coords,bisim,ends,inside,closed⟩ := inputs
  let g := graphOf s pos
  let scope := createCone g root
  have valid := created_cone_exact closed
  have accepted : checkCone (graphOf s pos) root scope = true := checked_cone_exact.mpr valid
  have proper : ∀ j, cone scope j ≠ .unresolved := valid.2.2.1
  let part := constructPartition (cone scope) proper
  have partition : QuotientObservation471.checkPartition (cone scope) part = true :=
    partition_check_exact.mpr (every_complete_graph_has_a_finite_partition proper)
  have main : (List.finRange _).all (fun j => checkAlternatives s pos rel (embedded scope j)) = true := by
    apply List.all_eq_true.mpr
    intro j _
    apply inside
    change FiniteWorklist.Path (CommonRoleRegularGraph.successors g) root
      (Vector.ofFn (QuotientObservation471.reachableNames g root).get)[j.val]
    simpa using (QuotientObservation471.path_at_cone_point (g := g) (root := root) j)
  have back : rel.all (fun (first,last) =>
      checkAlternatives s pos rel first && checkAlternatives s pos rel last) = true := by
    apply List.all_eq_true.mpr
    rintro ⟨a,d⟩ present
    exact Bool.and_eq_true_iff.mpr (ends a d present)
  have relation : CommonRoleGraphBisimulation.checkBisimulation (graphOf s pos) rel = true :=
    (CommonRoleGraphBisimulation.check_bisimulation_exact ..).mpr bisim
  let ck : Checkpoint n := ⟨root,_,_,scope,part⟩
  have reads : readCheck s pos rel (oldPosition pos root) ck =
      some (checkOnCycle (QuotientObservation471.graphOf part) (classOf part scope.site)) := by
    simp [ck,readCheck,readAlternatives,labels,coords,relation,main,back,replayCone,accepted,replay,partition]
  refine ⟨ck,?_⟩
  unfold computeOldObservationCheckpoint486
  dsimp only
  split
  · change Option.map (fun _ => ck) (readCheck s pos rel (oldPosition pos root) ck) = some ck
    rw [reads]
    rfl
  · rename_i impossible
    exact False.elim (impossible accepted)

def computedOriginalPalette486 {n : Nat} (s : GeneralDeclarativeI65.State) (pos : Positions n)
    (rel : List (Fin n × Fin n)) : SignedPalette486 n :=
  fun i => computeOldObservationCheckpoint486 s pos rel i

theorem computed_old_palette_checks_every_and_only_guarded_original_coordinate486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} (i : Fin n) :
    (∃ b, oldObservedSign486 s pos rel (computedOriginalPalette486 s pos rel) i = some b) ↔
    GuardedObservationInput s pos rel i := by
  constructor
  · rintro ⟨bit,h⟩
    exact (old_palette_sign_is_about_its_own_existing_site486 h).1
  · intro g
    obtain ⟨ck,h⟩ := old_input_guards_suffice_for_computing_an_exact_checkpoint486 g
    obtain ⟨which,bit,read⟩ := computed_old_checkpoint_is_at_its_own_original_coordinate486 h
    exact ⟨bit,by simp [oldObservedSign486,computedOriginalPalette486,h,which,read,Option.bind]⟩

theorem real_existing_graph_finitely_computes_its_verified_optional_palette486
    {n : Nat} (s : GeneralDeclarativeI65.State) (pos : Positions n)
    (rel : List (Fin n × Fin n)) :
    CompletePalette486 s pos rel (computedOriginalPalette486 s pos rel) :=
  fun i => (computed_old_palette_checks_every_and_only_guarded_original_coordinate486 i).mpr

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
