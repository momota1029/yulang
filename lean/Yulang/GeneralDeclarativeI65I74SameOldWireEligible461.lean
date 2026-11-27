import Yulang.GeneralDeclarativeI65I74EarlierHomogeneousScope461
import Yulang.GeneralDeclarativeI65I74ExactRouteFactorization461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open WrittenPattern460
open Checker408 (Problem)
open RetainedFull445 (FullProblem)
open RoutedReadyMixed457 (ReportAtField)
open RoutedNominalMixed456 (actualQueryDecoder)
open RecordTraversal455 (RawSnapshot)
open RecordTraversal455.MixedQA (MixedPath)
open AuthenticatedHop458 (Policy CycleWire)
open InlineStructuralPolicy458 (policy liftCycle)
open RoutedMixed456 (endsAtField)
open RecordK2412 (checkCycleAt412)
open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem exact_raw_cycle_read_keeps_true_stamp_and_original_cycle_wire
    {s : RawSnapshot} {p : Policy} {n q path terminal} {w : CycleWire p}
    (ok : AuthenticatedHop458.readCycle s p n q w = some (path,terminal)) :
    AuthenticatedHop458.readTrail s p n q w.trail = some (path,terminal,true) ∧
      checkCycleAt412 s terminal w.cycle = true := by
  cases raw : AuthenticatedHop458.readTrail s p n q w.trail with
  | none => simp [AuthenticatedHop458.readCycle,raw,Option.bind] at ok
  | some returned =>
    obtain ⟨as,last,stamp⟩ := returned
    cases stamp with
    | false => simp [AuthenticatedHop458.readCycle,raw,Option.bind] at ok
    | true =>
      by_cases found : checkCycleAt412 s last w.cycle = true
      · simp [AuthenticatedHop458.readCycle,raw,found,Option.bind] at ok
        obtain ⟨rfl,rfl⟩ := ok
        exact ⟨rfl,found⟩
      · simp [AuthenticatedHop458.readCycle,raw,found,Option.bind] at ok

theorem coordinate_walk_last_original_cell {keys root t path terminal last}
    (h : CoordinateWalk keys root t path terminal last) :
    lastCoordinate root path = terminal := by
  induction h with
  | stop => rfl
  | down _ _ ih => exact ih

open GeneralDeclarations (Declaration)

private theorem old_pack_success_keeps_actual_header_and_original_path
    {p : Problem} {d : Declaration}
    (h : HomogeneousReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) d)
    (w : HomogeneousClosedEntry459.FieldWire) {a : HomogeneousClosedEntry459.FieldDerivation p}
    (ok : HomogeneousClosedEntry459.packRead p d h w = some a) :
    AuthenticatedHop458.readCycle p.state.core.current.ordinary (policy p.state.core)
      h.arg.lower h.query (liftCycle p.state.core w.cursor) = some (a.path,a.terminal) ∧
    endsAtField a.path a.terminal = true ∧
    exactReport (fromHomogeneous h).anchor a.path a.terminal = a.report := by
  unfold HomogeneousClosedEntry459.packRead at ok
  split at ok
  · rename_i path terminal packet
    split at ok
    · rename_i yes
      obtain rfl := Option.some.inj ok
      exact ⟨packet,yes,rfl⟩
    · cases ok
  · cases ok

theorem installed_field_reader_preserves_actual_header_and_raw_wire
    {p : Problem} {w : HomogeneousClosedEntry459.FieldWire}
    {a : HomogeneousClosedEntry459.FieldDerivation p}
    (ok : HomogeneousClosedEntry459.readField p w = some a) :
    ∃ (d : Declaration)
      (h : HomogeneousReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) d),
      readActualHeader (alreadyHomogeneous p) w.emptyKey = some (fromHomogeneous h) ∧
      AuthenticatedHop458.readCycle p.state.core.current.ordinary (policy p.state.core)
        h.arg.lower h.query (liftCycle p.state.core w.cursor) = some (a.path,a.terminal) ∧
      endsAtField a.path a.terminal = true ∧
      exactReport (fromHomogeneous h).anchor a.path a.terminal = a.report := by
  unfold HomogeneousClosedEntry459.readField at ok
  split at ok
  · rename_i d seen
    cases prior : HomogeneousReadyHeader459.readReadyHeader p (actualQueryDecoder p.state.core) d seen w.emptyKey with
    | none => simp [prior,Option.bind] at ok
    | some author =>
      have check : HomogeneousClosedEntry459.packRead p d author w = some a := by
        simpa [prior,Option.bind] using ok
      have fromSource : readActualHeader (alreadyHomogeneous p) w.emptyKey = some (fromHomogeneous author) := by
        unfold readActualHeader
        split
        · rename_i chosen eq
          have same := List.singleton_inj.mp (eq.symm.trans seen)
          subst chosen
          change (HomogeneousReadyHeader459.readReadyHeader p (actualQueryDecoder p.state.core) d
            seen w.emptyKey).map _ = _
          simp [prior,alreadyHomogeneous]
        · rename_i ruledOut
          exact (ruledOut d seen).elim
      exact ⟨d,author,fromSource,old_pack_success_keeps_actual_header_and_original_path author w check⟩
  · cases ok

theorem any_installed_homogeneous_success_replays_with_the_same_wire_data
    {p : FullProblem} {r : ReportAtField} {w : HomogeneousClosedEntry459.FieldWire}
    (yes : HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 r) (.fieldK2 w) = true) :
    readEligibleField (exactHeaderReader (alreadyHomogeneous p.old)) (fromPriorCertificate p w) = some r := by
  change HomogeneousClosedEntry459.checkField p.old r w = true at yes
  cases decoded : HomogeneousClosedEntry459.readField p.old w with
  | none => simp [HomogeneousClosedEntry459.checkField,decoded] at yes
  | some a =>
    have rEq : a.report = r := by simpa [HomogeneousClosedEntry459.checkField,decoded] using yes
    obtain ⟨d,author,header,raw,field,which⟩ := installed_field_reader_preserves_actual_header_and_raw_wire decoded
    obtain ⟨steps,k2⟩ := exact_raw_cycle_read_keeps_true_stamp_and_original_cycle_wire raw
    have form := existing_homogeneous_header_normal_form_stays_closed_and_authored author
    have source : ActualClosedSyntax p.old.state.core author.emptyKey (normalized (readTerm author.written)) := by
      simpa only [ActualClosedSyntax,normalized_reencodes_exactly,write_read_term] using form
    have empty : queryKeys p.old.state.core author.emptyKey = .emptyRow :=
      query_empty_key_exact.mpr author.actualEmpty
    have start := anchor_compiles_the_normalized_original (fromHomogeneous author).anchor
    obtain ⟨last,result⟩ := old_raw_trail_has_authored_scope_without_extra_path_assumptions
      empty source start (AuthenticatedHop458.read_trail_sound458 steps)
    have written := (authored_trail_normal_form.mp result).2.2
    have ends := coordinate_walk_last_original_cell written
    have walked := (selected_coordinates_iff_independent_walk ends).mpr written
    have align := interleaved_read_factors_through_the_identical_raw_run p.old.state.core.current.ordinary
      (policy p.old.state.core) (fun _ => queryKeys p.old.state.core) author.arg.lower
      (normalized (readTerm author.written)) author.query (liftCycle p.old.state.core w.cursor).trail
    have joint : readJoint p.old.state.core.current.ordinary (policy p.old.state.core)
        (fun _ => queryKeys p.old.state.core) inheritedCompilerPlacement author.arg.lower
        (normalized (readTerm author.written)) author.query
        (addUnitPlacement (liftCycle p.old.state.core w.cursor).trail) =
          some (a.path,a.terminal,last,true) := by
      rw [align,steps]
      change readCoordinates (fun _ => queryKeys p.old.state.core) author.arg.lower
        (normalized (readTerm author.written)) a.path = some last at walked
      simp [walked,Option.bind]
    change (readActualHeader (alreadyHomogeneous p.old) w.emptyKey).bind _ = _
    rw [header]
    change (readAlreadyCompiledField p.old.state.core author.arg.lower
      (normalized (readTerm author.written)) author.query (fromPriorCertificate p w).along).bind _ = _
    change (readJointField _ _ _ _ _ _ _ (fromPriorCertificate p w).along).bind _ = _
    rw [← rEq]
    simp [readJointField,fromPriorCertificate,joint,field,k2,which,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
