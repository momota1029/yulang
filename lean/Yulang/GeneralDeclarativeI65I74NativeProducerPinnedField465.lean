import Yulang.GeneralDeclarativeI65I74NativeProducerPinnedTicket465
import Yulang.GeneralDeclarativeI65I74NativeProducerMergedReceipt465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465.PinnedTicket
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open PreparedDeclarations463
open PhysicalVisit463
open PhysicalVisit463.IssuedProjection464 (logicalBeforeHop)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessNativeOrder362 (node)
open GeneralDeclarativeWitnessNativeInstall360 (interpreted)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)

structure PinnedHeadField (p : Problem) where
  visit : HeadFieldWire p
  phase : PhaseAtHop

/-- Replay the exact existing head-field witness, and compare its literal
native origin ordinal against the existing exact full-address release.
The origin list need not be slot-unique. This is not a new resolver. -/
def readPinnedHeadField {p : Problem} {phase : CheckedPhase p.state.core}
    (table : CheckedTable p.state.core.current) (w : PinnedHeadField p) : Option HeadFieldReceipt := do
  if (visible p.state.core p.root).length ≠ 1 then none else
    let report ← readHeadField (p := p) table w.visit
    let arg ← p.root.demand.arguments[report.authored.headArgument]?
    if checkPinnedPhaseAt phase w.phase.write arg.lower report.path
        (pinnedOrdinals w.visit.spine.visit) w.phase.hop w.phase.sourceOrdinal then
      some report
    else none

def AgreesWithPinnedPhase {p : Problem} (phase : CheckedPhase p.state.core)
    (w : PinnedHeadField p) (r : HeadFieldReceipt) : Prop :=
  (visible p.state.core p.root).length = 1 ∧
    ∃ c, p.root.demand.arguments[r.authored.headArgument]? = some c ∧
      ExactSelectedPhase phase w.phase.write c.lower r.path
        (pinnedOrdinals w.visit.spine.visit) w.phase.hop w.phase.sourceOrdinal

theorem same_existing_report_checked_at_exact_ordinal
    {p : Problem} (phase : CheckedPhase p.state.core)
    (table : CheckedTable p.state.core.current) (w : PinnedHeadField p) (r : HeadFieldReceipt) :
    readPinnedHeadField (phase := phase) table w = some r ↔
      readHeadField (p := p) table w.visit = some r ∧ AgreesWithPinnedPhase phase w r := by
  unfold AgreesWithPinnedPhase
  by_cases one : (visible p.state.core p.root).length = 1
  · cases ro : readHeadField (p := p) table w.visit with
    | none => simp [readPinnedHeadField,one,ro,Option.bind]
    | some rep =>
      cases hh : p.root.demand.arguments[rep.authored.headArgument]? with
      | none =>
        constructor
        · simp [readPinnedHeadField,one,ro,hh,Option.bind]
        · rintro ⟨eq,_,c,contr,_⟩
          have same := Option.some.inj eq
          subst r
          rw [hh] at contr
          cases contr
      | some c =>
        by_cases checked : checkPinnedPhaseAt phase w.phase.write c.lower rep.path
            (pinnedOrdinals w.visit.spine.visit) w.phase.hop w.phase.sourceOrdinal = true
        · constructor
          · intro ok
            have eq : rep = r := by simpa [readPinnedHeadField,one,ro,hh,checked,Option.bind] using ok
            subst r
            exact ⟨rfl,one,c,hh,(pinned_phase_check_is_exact ..).mp checked⟩
          · rintro ⟨eq,_,_,_,_⟩
            have same := Option.some.inj eq
            subst r
            simp [readPinnedHeadField,one,ro,hh,checked,Option.bind]
        · constructor
          · simp [readPinnedHeadField,one,ro,hh,checked,Option.bind]
          · rintro ⟨eq,_,other,q,valid⟩
            have same := Option.some.inj eq
            subst r
            have eq := Option.some.inj (hh.symm.trans q)
            subst other
            exact False.elim (checked ((pinned_phase_check_is_exact ..).mpr valid))
  · simp [readPinnedHeadField,one]

theorem pinned_report_keeps_the_issued_origin_and_cycle_in_every_fit
    {input : Input} {phase : CheckedPhase input.problem.old.state.core}
    {w : PinnedHeadField input.problem.old} {r : HeadFieldReceipt}
    (read : readPinnedHeadField (phase := phase) input.checked w = some r)
    (m : I72.Model) (fit : FitsFull input.problem.state m) :
    r.literal ≠ [] ∧
      AliasCycle input.problem.old.state.core.current.ordinary
        (observed input.problem.old.state.core.current.ordinary) r.terminal ∧
      ∃ raw logical row,
        (pinnedOrdinals w.visit.spine.visit)[w.phase.hop]? = some (raw,w.phase.sourceOrdinal) ∧
        input.problem.old.state.core.current.ordinary.equations[raw]? = some row ∧
        row.left = w.phase.write.address.target ∧
        OriginRoute input.problem.old.state.core (originalOfWrite w.phase.write) logical ∧
        m.nativeSyntax row.left = some (node w.phase.write.code) ∧
        interpreted phase.world.board m.assignment row.left = some (w.phase.write.code.eval m.assignment) := by
  obtain ⟨older,_,c,actual,atPhase⟩ := (same_existing_report_checked_at_exact_ordinal ..).mp read
  obtain ⟨a,location,trail⟩ :=
    field_reader_pins_shared_literal_ticket_ordinals input.checked w.visit r older
  have argument := a.orig.actualArgument
  rw [location] at argument
  have eq : c = a.orig.capture := Option.some.inj (actual.symm.trans argument)
  subst c
  have pinned := (pinned_phase_check_is_exact ..).mpr atPhase
  obtain ⟨raw,logical,row,idx,_,rowAt,target,released⟩ :=
    phase_at_the_literal_pinned_wire_cannot_substitute_a_same_slot_origin trail phase
      w.phase.write w.phase.hop w.phase.sourceOrdinal pinned
  have field := (prechecked_head_field_iff_finite_exact_wire ..).mpr ⟨w.visit,older⟩
  obtain ⟨_,_,_,nonempty,_,cycle⟩ :=
    exact_prechecked_head_field_keeps_original_and_evidence_in_each_fit input field m fit
  have native := actual_phase_origin_ordinal_and_native_view_hold_in_every_same_fit
    ((finite_phase_origin_check_iff_literal_placed_active_row ..).mpr released) m fit.1
  exact ⟨nonempty,cycle,raw,logical,row,idx,rowAt,target,released.2.1,
    target.symm ▸ native.1,target.symm ▸ native.2⟩

end Yulang.GeneralDeclarativeI65.I72.NativeProducer465.PinnedTicket
