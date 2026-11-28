import Yulang.GeneralDeclarativeI65I74ProducerSpec479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open LiteralVisits473 (Checkpoint readCheck independent_checkpoint_reifies_the_exact_site_and_sign)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open QuotientObservation471 (ReturnsUpToEquality)
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def readCheckpointSequence {n : Nat} (s : GeneralDeclarativeI65.State) (pos : Positions n)
    (rel : List (Fin n × Fin n)) : List (Checkpoint n) → Option (List Bool) :=
  List.mapM (fun check => readCheck s pos rel (oldPosition pos check.which) check)

theorem independent_source_visits_reify_exact_checkpoints479
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel} {first moves indices final bit}
    (visited : Trail s pos rel first moves indices final bit) :
    ∃ checks : List (Checkpoint n),
      checks.map (·.which) = first.index :: indices ∧
      readCheckpointSequence s pos rel checks =
        some (List.replicate indices.length false ++ [bit]) := by
  induction visited with
  | @stop here bit complete meaning =>
    obtain ⟨cp,atHere,valid⟩ := independent_checkpoint_reifies_the_exact_site_and_sign complete bit meaning
    exact ⟨[cp],by simp [atHere],by simp [readCheckpointSequence,atHere,valid,bind,Option.bind]⟩
  | @step here next finish move moves positions bit hop guarded safe nextPath ih =>
    obtain ⟨later,whereFrom,ranLater⟩ := ih
    have sign : false = true ↔ ReturnsUpToEquality (graphOf s pos) here.index := by simp [safe]
    obtain ⟨cp,atHere,ran⟩ := independent_checkpoint_reifies_the_exact_site_and_sign guarded false sign
    refine ⟨cp :: later,by simp [atHere,whereFrom],?_⟩
    simp only [readCheckpointSequence,List.mapM_cons] at ranLater ⊢
    simp [atHere,ran,ranLater,bind,Option.bind,List.replicate_succ]

theorem every_independent_input_has_exact_same_phase_graph_data479
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel}
    (input : TypedInput p gd pos rel) :
    ∃ outer first : Checkpoint n, ∃ rest : List (Checkpoint n),
      outer.which = input.root.index ∧ first.which = input.first.index ∧
      rest.map (·.which) = input.tailPoints ∧
      readCheckpointSequence p.old.state.core pos rel (outer :: first :: rest) =
        some (false :: List.replicate input.tailPoints.length false ++ [input.bit]) := by
  obtain ⟨checks,locations,read⟩ := independent_source_visits_reify_exact_checkpoints479 input.visits
  cases checks with
  | nil => simp at locations
  | cons one after =>
    simp only [List.map_cons,List.cons.injEq] at locations
    have noReturn : false = true ↔ ReturnsUpToEquality (graphOf p.old.state.core pos) input.root.index := by
      simp [input.rootSafe]
    obtain ⟨outer,atRoot,ran⟩ :=
      independent_checkpoint_reifies_the_exact_site_and_sign input.rootGuard false noReturn
    refine ⟨outer,one,after,atRoot,locations.1,locations.2,?_⟩
    have unfoldTop :
        readCheckpointSequence p.old.state.core pos rel (outer :: one :: after) = (do
          let b ← readCheck p.old.state.core pos rel (oldPosition pos outer.which) outer
          let bits ← readCheckpointSequence p.old.state.core pos rel (one :: after)
          pure (b :: bits)) := by
      simp only [readCheckpointSequence,List.mapM_cons]
    rw [unfoldTop]
    simp [atRoot,ran,read,bind,Option.bind]

theorem independent_input_has_one_walk_in_every_original_full_fit479
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} (input : TypedInput p gd pos rel) :
    ∃ rebuilt : Expr, (∀ m : Model, FitsFull p.state m →
      GeneralDeclarativeRepeatedActual323.eqAt m.assignment
        (.variable input.head.orig.capture.lower) rebuilt) ∧
      Walk .actual rebuilt input.head.orig.code input.uses := by
  obtain ⟨term,means,walk⟩ := GeneralDeclarativeInlineTrace331.realize input.typed
  exact ⟨term,fun m fit => means m.assignment fit.1.1.1,walk⟩

end Yulang.GeneralDeclarativeI65.I72.Producer479
