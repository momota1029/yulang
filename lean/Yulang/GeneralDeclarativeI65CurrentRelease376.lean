import Yulang.GeneralDeclarativeI65RetainedEvent372
import Yulang.GeneralDeclarativeWitnessNativeRelease360

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessNativePreparation360 (Prepared)
open GeneralDeclarativeWitnessNativeValue360 (Address Write Compiled)
open GeneralDeclarativeWitnessNativeInstall360
  (Board World NativeViews Committed atTarget check check_exact add install
   authored_target_appears other_target_unchanged)
open GeneralDeclarativeWitnessNativeRelease360
  (ReleaseAuthority ExactRelease openWrite checkExactRelease checked_exact_written_value)
open GeneralDeclarativeWitnessTypedRelease354 (position)
open GeneralDeclarativeWitnessCompiler350 (Finished execute)
open GeneralDeclarativeWitnessDeclaredState357 (context)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeHead320 (Equation)

/-- An actual compiler install, not value equality, fixes this full
address, its active version, and the exact code at the target. -/
theorem installed_literal_address {env frame d layout table wire version}
    {p : Prepared env frame d layout} (emission : Compiled p table wire version)
    {base : Board} {out : World} (installed : install p emission base = some out) :
    atTarget out.board emission.write.address.target = some emission.write ∧
      emission.write.address.owner ∈ out.board.active ∧
      (out.board.active.map position).Nodup := by
  unfold install at installed
  split at installed
  · rename_i positive
    have fact := check_exact.mp positive
    have exact := Option.some.inj installed
    cases exact
    exact ⟨authored_target_appears fact,fact.active,fact.unique⟩
  · cases installed

/-- This is the actual executable exact-release check, not a new
definition of acceptable inputs. It cannot supply its own grant. -/
theorem exact_open_iff_independent_grant {board : Board} {gate : ReleaseAuthority}
    {written : Write} (stored : atTarget board written.address.target = some written)
    (active : written.address.owner ∈ board.active) (unique : (board.active.map position).Nodup) :
    (checkExactRelease board gate written).isSome = true ↔ written.address ∈ gate.grants := by
  by_cases allowed : written.address ∈ gate.grants
  · have ran : ∃ released, openWrite board gate written.address = some released ∧
        released.stored = written := by
      unfold openWrite
      split
      · rename_i absent
        rw [stored] at absent
        cases absent
      · rename_i row located
        have same := Option.some.inj (located.symm.trans stored)
        subst row
        simp [active,unique,allowed]
    obtain ⟨opened,ran,same⟩ := ran
    simp [checkExactRelease,ran,same,allowed]
  · have absent := GeneralDeclarativeWitnessNativeRelease360.not_granted_not_released
        (board := board) allowed
    simp [checkExactRelease,absent,allowed]

theorem checked_install_opens_iff_granted {env frame d layout table wire version}
    {p : Prepared env frame d layout} (emission : Compiled p table wire version)
    {base : Board} {out : World} (ran : install p emission base = some out) (gate : ReleaseAuthority) :
    (checkExactRelease out.board gate emission.write).isSome = true ↔
      emission.write.address ∈ gate.grants := by
  obtain ⟨stored,active,unique⟩ := installed_literal_address emission ran
  exact exact_open_iff_independent_grant stored active unique

theorem same_target_different_source_address_not_open {board : Board} {gate : ReleaseAuthority}
    {written : Write} {asked : Address}
    (stored : atTarget board written.address.target = some written)
    (same : asked.target = written.address.target) (wrong : written.address ≠ asked) :
    openWrite board gate asked = none := by
  have forward : atTarget board asked.target = some written := same ▸ stored
  unfold openWrite
  split
  · rfl
  · rename_i row located
    have one := Option.some.inj (located.symm.trans forward)
    subst row
    simp [wrong]

def appendOtherWrites (board : Board) (rows : List Write) : Board :=
  rows.foldl add board

theorem appends_away_preserve_literal_read {board : Board} {rows : List Write} {n : Nat}
    (away : ∀ row ∈ rows,n ≠ row.address.target) :
    atTarget (appendOtherWrites board rows) n = atTarget board n := by
  induction rows generalizing board with
  | nil => rfl
  | cons row rest ih =>
    change atTarget (appendOtherWrites (add board row) rest) n = atTarget board n
    rw [ih (fun other seen => away other (List.mem_cons_of_mem _ seen))]
    exact other_target_unchanged board row n (away row List.mem_cons_self)

theorem appends_keep_active_versions (board : Board) (rows : List Write) :
    (appendOtherWrites board rows).active = board.active := by
  induction rows generalizing board with
  | nil => rfl
  | cons row rest ih =>
    change (appendOtherWrites (add board row) rest).active = board.active
    exact ih (add board row)

/-- The fitted model is for the same current ordinary table and
current native board. No new values or renamed targets are chosen. -/
theorem current_ordinary_and_native_receipts {s : State} {q : Request}
    {row : GeneralDeclarations.Declaration} {named spans keep fallback targets}
    {f : Finished}
    (ordinaryRan : execute (context s.current q.demand row named spans keep fallback targets) = some f)
    (atoms : f.state.normal.ordinary ⊆ s.current.ordinary.normal.ordinary)
    (intervals : f.state.normal.intervals ⊆ s.current.ordinary.normal.intervals)
    (later : List Equation)
    (prior : s.current.ordinary.equations = f.state.equations ++ later)
    (m : Model) (fit : Fits s m)
    {board : Board} {gate : ReleaseAuthority} {written : Write} (views : NativeViews)
    (observes : GeneralDeclarativeWitnessNativeInstall360.Fits
      (⟨s.current.ordinary,board⟩ : World) m.assignment views)
    (released : ExactRelease board gate written) :
    (∀ eq ∈ f.fixed,Holds m.assignment eq) ∧
      views written.address.target = some (written.code.eval m.assignment) :=
  ⟨(body_facts_sound (retained_body_facts_at_same_current ordinaryRan atoms intervals later prior) m fit).2,
   checked_exact_written_value (w := ⟨s.current.ordinary,board⟩) released m.assignment views observes⟩

theorem emitted_row_remains_exactly_openable {env frame d layout table wire version}
    {p : Prepared env frame d layout} (emission : Compiled p table wire version)
    {base : Board} {out : World} (ran : install p emission base = some out)
    {more : List Write}
    (disjoint : ∀ row ∈ more,emission.write.address.target ≠ row.address.target)
    (gate : ReleaseAuthority) :
    (checkExactRelease (appendOtherWrites out.board more) gate emission.write).isSome = true ↔
      emission.write.address ∈ gate.grants := by
  obtain ⟨stored,active,unique⟩ := installed_literal_address emission ran
  apply exact_open_iff_independent_grant
  · rw [appends_away_preserve_literal_read disjoint]
    exact stored
  · rw [appends_keep_active_versions]
    exact active
  · rw [appends_keep_active_versions]
    exact unique

end Yulang.GeneralDeclarativeI65
