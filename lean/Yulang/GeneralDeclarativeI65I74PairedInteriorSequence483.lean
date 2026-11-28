import Yulang.GeneralDeclarativeI65I74PairedFocusedHop483

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open Producer479 (Site Hop)
open LiteralVisits473 (StepWire)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open GeneralDeclarativeWitnessOrigins350 (Table)
open WrittenPattern460.PhysicalOrigin (atSource literal_occurrence)
open CommonRoleGraphBisimulation (ObservationallyEqual)
open QuotientObservation471 (ReturnsUpToEquality)

theorem paired_exact_pose_selects_the_same_compiled_child
    {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {left right a b : Site s pos} {move : StepWire}
    (shared : left.pattern = right.pattern)
    (one : Hop left a move) (two : Hop right b move) : a.query = b.query := by
  have pat := (paired_exact_pose_selects_the_same_subpattern shared one two).2
  have oneCode := (AuthoredInspectQuery456.compile_query_exact ..).mpr one.typed.exactCompile
  have twoCode := (AuthoredInspectQuery456.compile_query_exact ..).mpr two.typed.exactCompile
  rw [one.written,pat,←two.written] at oneCode
  exact one.query.symm.trans ((Option.some.inj (oneCode.symm.trans twoCode)).trans two.query)

structure InteriorMove (n : Nat) where
  step : StepWire
  author : Fin n
  ambient : Fin n

/-- An independently checked source card is retained for every selected
author-side edge. The old ambient path has a distinct literal read. -/
inductive InteriorSequence {p : FullProblem} {pos : Positions n} (table : Table) :
    Site p.old.state.core pos → Site p.old.state.core pos → ReadCard → List (InteriorMove n) →
    List (Site p.old.state.core pos × Site p.old.state.core pos) → Prop where
  | nil : InteriorSequence table left right card [] []
  | cons (visit : PairedFocusedHop (p := p) table left right move.step card move.author move.ambient) :
      graphOf p.old.state.core pos left.index ≠ .unresolved →
      graphOf p.old.state.core pos right.index ≠ .unresolved →
      InteriorSequence table visit.author.after visit.ambient visit.author.childCard tail rest →
      InteriorSequence table left right card (move :: tail) ((visit.author.after,visit.ambient) :: rest)

structure InteriorSequenceRead {p : FullProblem} {pos : Positions n} (table : Table)
    (left right : Site p.old.state.core pos) (card : ReadCard) (moves : List (InteriorMove n)) where
  path : List (Site p.old.state.core pos × Site p.old.state.core pos)
  actual : InteriorSequence (p := p) table left right card moves path

private def resolvedOrNot {n : Nat} (node : CommonRoleRegularGraph.Node n) :
    Decidable (node ≠ .unresolved) := by
  cases node <;> first | exact isFalse (fun no => no rfl) | exact isTrue (by intro h; cases h)

def readInteriorSequence {p : FullProblem} {pos : Positions n} (table : Table)
    (left right : Site p.old.state.core pos) (card : ReadCard) (moves : List (InteriorMove n)) :
    Option (InteriorSequenceRead (p := p) table left right card moves) :=
  match moves with
  | [] => some ⟨[],.nil⟩
  | move::more =>
    dite (graphOf p.old.state.core pos left.index ≠ .unresolved) (fun l =>
      dite (graphOf p.old.state.core pos right.index ≠ .unresolved) (fun r => do
        let read ← readPairedFocusedHop (p := p) table left right move.step card move.author move.ambient
        let next ← readInteriorSequence table read.author.after read.ambient read.author.childCard more
        some ⟨(read.author.after,read.ambient)::next.path,.cons read l r next.actual⟩)
        (fun _ => none) (h := resolvedOrNot _)) (fun _ => none) (h := resolvedOrNot _)

theorem every_visited_paired_edge_stays_at_the_literal_coordinates_and_authored_pose
    {p : FullProblem} {pos : Positions n} {table : Table}
    {left right : Site p.old.state.core pos} {card : ReadCard} {moves path}
    (chain : InteriorSequence (p := p) table left right card moves path) :
    path.map (fun pair => (pair.1.index,pair.2.index)) = moves.map (fun wire => (wire.author,wire.ambient)) ∧
    ∀ pair ∈ path, pair.1.pattern = pair.2.pattern ∧ pair.1.query = pair.2.query := by
  induction chain with
  | nil => exact ⟨rfl, by simp⟩
  | cons read _ _ _ ih =>
    obtain ⟨i,⟨one⟩,_⟩ := focused_card_hop_is_actual_and_keeps_a_single_checked_occurrence read.author
    obtain ⟨j,⟨two⟩⟩ := Producer479.reified_hop_keeps_the_same_old_place479 read.ambientRead
    constructor
    · simp [i,j,ih.1]
    · intro pair atPath
      rcases List.mem_cons.mp atPath with eq | later
      · subst pair
        exact ⟨(paired_exact_pose_selects_the_same_subpattern read.original one two).2,
          paired_exact_pose_selects_the_same_compiled_child read.original one two⟩
      · exact ih.2 pair later

theorem the_paired_quotient_signs_follow_the_independently_checked_path
    {p : FullProblem} {pos : Positions n} {table : Table}
    {left right : Site p.old.state.core pos} {card : ReadCard} {moves path}
    (ordered : (List.ofFn (oldPosition pos)).Nodup)
    (same : ObservationallyEqual (graphOf p.old.state.core pos) left.index right.index)
    (chain : InteriorSequence (p := p) table left right card moves path) :
    ∀ pair ∈ (left,right)::path,
      ObservationallyEqual (graphOf p.old.state.core pos) pair.1.index pair.2.index ∧
      (ReturnsUpToEquality (graphOf p.old.state.core pos) pair.1.index ↔
        ReturnsUpToEquality (graphOf p.old.state.core pos) pair.2.index) := by
  have data : InteriorCorrespondence483.PairedTrail left right path := by
    induction chain with
    | nil => exact .nil
    | cons read l r _ ih =>
      obtain ⟨_,⟨one⟩,_⟩ :=
        focused_card_hop_is_actual_and_keeps_a_single_checked_occurrence read.author
      obtain ⟨_,⟨two⟩⟩ := Producer479.reified_hop_keeps_the_same_old_place479 read.ambientRead
      exact .cons l r one two rfl (ih (InteriorCorrespondence483.paired_selected_children_have_equal_regular_observations
        ordered l r same one two rfl))
  exact InteriorCorrespondence483.every_paired_actual_position_keeps_its_own_return_status ordered same data

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
