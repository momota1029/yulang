import Yulang.GeneralDeclarativeI65I74ExactCanonicalEligible461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open WrittenPattern460
open RecordTraversal455 (RawSnapshot termInspects)
open RecordTraversal455.MixedQA (MixedPath)
open InlineStructuralPolicy458 (policy)
open RetainedFull445 (FullProblem)
open RoutedReadyMixed457 (ReportAtField)
open RoutedNominalMixed456 (actualQueryDecoder)
open RoutedMixed456 (endsAtField)
open RecordK2412 (checkCycleAt412)
open SplitEscape446 (splitCheck446)

def rawPlacement {p : AuthenticatedHop458.Policy} {m : Alignment} :
    JointWire p m → AuthenticatedHop458.Wire p
  | .stop _ => .stop
  | .down _ hop safe rest => .down hop safe (rawPlacement rest)

theorem erasure_keeps_exact_raw_run_and_used_stamp
    {s : RawSnapshot} {p : AuthenticatedHop458.Policy} {keys : Nat → KeyRead}
    {align : Alignment} {root t query path terminal last used} {w : JointWire p align}
    (actual : readJoint s p keys align root t query w = some (path,terminal,last,used)) :
    AuthenticatedHop458.readTrail s p root query (rawPlacement w) = some (path,terminal,used) := by
  induction w generalizing root t query path terminal last used with
  | stop placement =>
    by_cases yes : align.checks root t query placement = true ∧ termInspects query = true
    · simp [readJoint,yes.1,yes.2] at actual
      obtain ⟨rfl,rfl,_,rfl⟩ := actual
      simp [rawPlacement,AuthenticatedHop458.readTrail,yes.2]
    · simp [readJoint,Bool.and_eq_true,yes] at actual
  | down placement hop safe rest ih =>
    by_cases yes : align.checks root t query placement = true ∧ splitCheck446 s root safe = true
    · cases located : AuthenticatedHop458.readStep s p root query hop with
      | none => simp [readJoint,yes.1,yes.2,located,Option.bind] at actual
      | some step =>
        obtain ⟨a,c,n,stamp⟩ := step
        cases written : WrittenPattern460.readStep (keys root) t (writtenAddress a) with
        | none => simp [readJoint,yes.1,yes.2,located,written,Option.bind] at actual
        | some child =>
          cases inner : readJoint s p keys align c child n rest with
          | none => simp [readJoint,yes.1,yes.2,located,written,inner,Option.bind] at actual
          | some out =>
            obtain ⟨tail,lastSite,lastSyntax,other⟩ := out
            simp [readJoint,yes.1,yes.2,located,written,inner,Option.bind] at actual
            obtain ⟨rfl,rfl,_,rfl⟩ := actual
            simp [rawPlacement,AuthenticatedHop458.readTrail,located,yes.2,ih inner,Option.bind]
    · simp [readJoint,Bool.and_eq_true,yes] at actual

def toPriorCertificate (p : FullProblem)
    (w : EligibleWire (exactHeaderReader (alreadyHomogeneous p.old))) :
    HomogeneousClosedEntry459.FieldWire :=
  ⟨w.start,InlineStructuralPolicy458.eraseCycle p.old.state.core
    ⟨rawPlacement w.along.visit,w.along.cycle⟩⟩

/-- Uses exactly the old header key and old raw tickets. Does not assume
old acceptance or copy the wanted report into the certificate. -/
theorem actual_structural_true_stamp_replays_same_prior_certificate {p : FullProblem} {d}
    (h : HomogeneousReadyHeader459.AuthoredHeader p.old (actualQueryDecoder p.old.state.core) d)
    (w : EligibleWire (exactHeaderReader (alreadyHomogeneous p.old)))
    (key : w.start = h.emptyKey) (r : ReportAtField) (last : Term)
    (traversed : readJoint p.old.state.core.current.ordinary (policy p.old.state.core)
      (fun _ => queryKeys p.old.state.core) inheritedCompilerPlacement h.arg.lower
      (normalized (readTerm h.written)) h.query w.along.visit = some (r.path,r.terminal,last,true))
    (k2 : checkCycleAt412 p.old.state.core.current.ordinary r.terminal w.along.cycle = true)
    (field : endsAtField r.path r.terminal = true)
    (original : exactReport (fromHomogeneous h).anchor r.path r.terminal = r) :
    HomogeneousClosedEntry459.check_full_homogeneous459 p (.fieldK2 r)
      (.fieldK2 (toPriorCertificate p w)) = true := by
  have raw := erasure_keeps_exact_raw_run_and_used_stamp traversed
  have cursor : AuthenticatedHop458.readCycle p.old.state.core.current.ordinary (policy p.old.state.core)
      h.arg.lower h.query ⟨rawPlacement w.along.visit,w.along.cycle⟩ = some (r.path,r.terminal) := by
    simp [AuthenticatedHop458.readCycle,raw,k2,Option.bind]
  change HomogeneousClosedEntry459.checkField p.old r (toPriorCertificate p w) = true
  unfold HomogeneousClosedEntry459.checkField HomogeneousClosedEntry459.readField
  split
  · rename_i seen eq
    have same := List.singleton_inj.mp (eq.symm.trans h.only)
    subst seen
    have hdr := HomogeneousReadyHeader459.actual_original_homogeneous_header_replays459 h
    simp only [toPriorCertificate,key,hdr,Bind.bind,Option.bind,HomogeneousClosedEntry459.packRead]
    split
    · rename_i path terminal result
      rw [InlineStructuralPolicy458.lift_erase_cycle458,cursor] at result
      obtain ⟨samePath,sameTerminal⟩ := Prod.mk.inj (Option.some.inj result)
      subst path terminal
      simpa [field,HomogeneousClosedEntry459.FieldDerivation.report,exactReport,
        fromHomogeneous,EligibleStart.anchor] using original
    · rename_i missing
      rw [InlineStructuralPolicy458.lift_erase_cycle458,cursor] at missing
      cases missing
  · rename_i notVisible
    exact (notVisible _ h.only).elim

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
