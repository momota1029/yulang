import Yulang.GeneralDeclarativeI65I74SameOldWireEligible461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open WrittenPattern460
open Checker408 (Problem)
open RetainedFull445 (FullProblem)
open GeneralDeclarations (Declaration)
open RoutedReadyMixed457 (ReportAtField)
open RoutedNominalMixed456 (actualQueryDecoder)
open RoutedMixed456 (endsAtField)
open InlineStructuralPolicy458 (policy liftCycle)
open RecordK2412 (checkCycleAt412)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- Exposes the existing raw stamp, without synthesizing or upgrading it.
The very same selected grammar walk and raw checks are used. -/
def readSourceAndFieldStamp {p : Problem} (h : ReadyRead p) (w : EligibleWire h) :
    Option (ReportAtField × Bool) := do
  let a ← h.read w.start
  let (path,n,_,used) ← readJoint p.state.core.current.ordinary (policy p.state.core)
      (fun _ => queryKeys p.state.core) inheritedCompilerPlacement a.argument.lower
      (normalized (readTerm a.original)) a.query w.along.visit
  if endsAtField path n && checkCycleAt412 p.state.core.current.ordinary n w.along.cycle
  then return (exactReport a.anchor path n,used)
  else none

theorem forgetting_stamp_is_identical_existing_uniform_receipt {p : Problem}
    (h : ReadyRead p) (w : EligibleWire h) :
    (readSourceAndFieldStamp h w).map Prod.fst = readEligibleField h w := by
  cases header : h.read w.start with
  | none => simp [readSourceAndFieldStamp,readEligibleField,header,Option.bind]
  | some a =>
    cases step : readJoint p.state.core.current.ordinary (policy p.state.core)
        (fun _ => queryKeys p.state.core) inheritedCompilerPlacement a.argument.lower
        (normalized (readTerm a.original)) a.query w.along.visit with
    | none =>
      simp [readSourceAndFieldStamp,readEligibleField,readAlreadyCompiledField,readJointField,
        header,step,Option.bind]
    | some u =>
      obtain ⟨path,n,last,used⟩ := u
      by_cases yes : endsAtField path n = true ∧ checkCycleAt412 p.state.core.current.ordinary n w.along.cycle = true
      · simp [readSourceAndFieldStamp,readEligibleField,readAlreadyCompiledField,readJointField,
          header,step,yes,Option.bind]
      · simp [readSourceAndFieldStamp,readEligibleField,readAlreadyCompiledField,readJointField,
          header,step,yes,Option.bind]

theorem exact_homogeneous_header_read_keeps_supplied_key {p : Problem} {d : Declaration}
    {one : visible p.state.core p.root = [d]} {k : Nat}
    {h : HomogeneousReadyHeader459.AuthoredHeader p (actualQueryDecoder p.state.core) d}
    (ok : HomogeneousReadyHeader459.readReadyHeader p (actualQueryDecoder p.state.core) d one k = some h) :
    h.emptyKey = k := by
  unfold HomogeneousReadyHeader459.readReadyHeader at ok
  dsimp only at ok
  repeat' first | (cases ok <;> rfl) | split at ok

theorem true_reflected_stamp_passes_same_installed_wire {p : FullProblem} {r : ReportAtField}
    {w : EligibleWire (exactHeaderReader (alreadyHomogeneous p.old))}
    (actual : readSourceAndFieldStamp (exactHeaderReader (alreadyHomogeneous p.old)) w = some (r,true)) :
    HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 r)
      (.fieldK2 (toPriorCertificate p w)) = true := by
  unfold readSourceAndFieldStamp at actual
  change ((readActualHeader (alreadyHomogeneous p.old) w.start).bind _) = _ at actual
  unfold readActualHeader at actual
  split at actual
  · rename_i d roster
    change ((HomogeneousReadyHeader459.readReadyHeader p.old (actualQueryDecoder p.old.state.core)
      d roster w.start).map (fun h => fromHomogeneous h)).bind _ = _ at actual
    cases concrete : HomogeneousReadyHeader459.readReadyHeader p.old (actualQueryDecoder p.old.state.core)
        d roster w.start with
    | none => simp [concrete,Option.bind] at actual
    | some h =>
      have sameKey := (exact_homogeneous_header_read_keeps_supplied_key concrete).symm
      cases walked : readJoint p.old.state.core.current.ordinary (policy p.old.state.core)
          (fun _ => queryKeys p.old.state.core) inheritedCompilerPlacement h.arg.lower
          (normalized (readTerm h.written)) h.query w.along.visit with
      | none => simp [concrete,fromHomogeneous,walked,Option.bind] at actual
      | some outcome =>
        rcases outcome with ⟨path,n,last,used⟩
        by_cases closes : endsAtField path n = true ∧ checkCycleAt412 p.old.state.core.current.ordinary n w.along.cycle = true
        · have returned : exactReport (fromHomogeneous h).anchor path n = r ∧ used = true := by
            simpa [concrete,fromHomogeneous,walked,closes,Option.bind] using actual
          obtain ⟨same,trueStamp⟩ := returned
          subst r used
          have field := closes.1
          have cycle := closes.2
          exact actual_structural_true_stamp_replays_same_prior_certificate h w sameKey _ last walked cycle field rfl
        · simp [concrete,fromHomogeneous,walked,closes,Option.bind] at actual
  · simp [Option.bind] at actual

theorem any_prior_success_has_the_original_true_stamp_on_the_same_data
    {p : FullProblem} {r : ReportAtField} {w : HomogeneousClosedEntry459.FieldWire}
    (accepted : HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 r) (.fieldK2 w) = true) :
    readSourceAndFieldStamp (exactHeaderReader (alreadyHomogeneous p.old))
      (fromPriorCertificate p w) = some (r,true) := by
  have chk := any_installed_homogeneous_success_replays_with_the_same_wire_data accepted
  have whole := (forgetting_stamp_is_identical_existing_uniform_receipt _ _).trans chk
  obtain ⟨⟨value,used⟩,pathAndUse,same⟩ := Option.map_eq_some_iff.mp whole
  change value = r at same
  subst value
  change HomogeneousClosedEntry459.checkField p.old r w = true at accepted
  cases resolved : HomogeneousClosedEntry459.readField p.old w with
  | none => simp [HomogeneousClosedEntry459.checkField,resolved] at accepted
  | some exactOld =>
    obtain ⟨decl,src,header,oldCycle,field,origin⟩ :=
      installed_field_reader_preserves_actual_header_and_raw_wire resolved
    have earlier := (exact_raw_cycle_read_keeps_true_stamp_and_original_cycle_wire oldCycle).1
    have unchangedOutput := pathAndUse
    unfold readSourceAndFieldStamp at pathAndUse
    change (readActualHeader (alreadyHomogeneous p.old) w.emptyKey).bind _ = _ at pathAndUse
    rw [header] at pathAndUse
    cases walked : readJoint p.old.state.core.current.ordinary (policy p.old.state.core)
        (fun _ => queryKeys p.old.state.core) inheritedCompilerPlacement src.arg.lower
        (normalized (readTerm src.written)) src.query
        (addUnitPlacement (liftCycle p.old.state.core w.cursor).trail) with
    | none => simp [fromPriorCertificate,fromHomogeneous,walked,Option.bind] at pathAndUse
    | some route =>
      obtain ⟨path,n,last,stamp⟩ := route
      have raw := erasure_keeps_exact_raw_run_and_used_stamp walked
      rw [erase_added_placement_is_same_raw_certificate,earlier] at raw
      have sameStamp : stamp = true := (Prod.mk.inj (Prod.mk.inj (Option.some.inj raw)).2).2.symm
      subst stamp
      by_cases final : endsAtField path n = true ∧
          checkCycleAt412 p.old.state.core.current.ordinary n (liftCycle p.old.state.core w.cursor).cycle = true
      · have stamps : used = true := by
          have eq : exactReport (fromHomogeneous src).anchor path n = r ∧ true = used := by
            simpa [fromPriorCertificate,fromHomogeneous,walked,final,Option.bind] using pathAndUse
          exact eq.2.symm
        simpa [stamps] using unchangedOutput
      · simp [fromPriorCertificate,fromHomogeneous,walked,final,Option.bind] at pathAndUse

/-- Exact Bool agreement at the existing top homogeneous field branch.
All input and witness data are quantified. This is a theorem about the
installed entry, not an installation of a different checker. -/
theorem existing_c459_field_bool_iff_same_data_reflected_original_stamp
    (p : FullProblem) (r : ReportAtField) (w : HomogeneousClosedEntry459.FieldWire) :
    HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 r) (.fieldK2 w) = true ↔
    readSourceAndFieldStamp (exactHeaderReader (alreadyHomogeneous p.old))
      (fromPriorCertificate p w) = some (r,true) := by
  constructor
  · exact any_prior_success_has_the_original_true_stamp_on_the_same_data
  · intro h
    simpa [same_earlier_header_key_and_entire_raw_wire_roundtrip] using
      true_reflected_stamp_passes_same_installed_wire h

theorem existing_c459_same_input_same_certificate_boolean
    (p : FullProblem) (r : ReportAtField) (w : HomogeneousClosedEntry459.FieldWire) :
    HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 r) (.fieldK2 w) =
      decide (readSourceAndFieldStamp (exactHeaderReader (alreadyHomogeneous p.old))
        (fromPriorCertificate p w) = some (r,true)) := by
  have exact := existing_c459_field_bool_iff_same_data_reflected_original_stamp p r w
  by_cases old : HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 r) (.fieldK2 w) = true
  · rw [old,decide_eq_true (exact.mp old)]
  · simp [Bool.eq_false_iff.mpr old,mt exact.mpr old]

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
