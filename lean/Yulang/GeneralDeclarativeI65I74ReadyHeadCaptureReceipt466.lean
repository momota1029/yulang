import Yulang.GeneralDeclarativeI65I74ReadOldCaptureReceipt466
import Yulang.GeneralDeclarativeI65I74PreparedHeadStart463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466WrittenBinderCoordinates
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeI65 (visible)
open GeneralDeclarativeI65.I72.PreparedDeclarations463
open GeneralDeclarativeI65.I72.Checker408 (Problem)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (atSource)

abbrev ordinary (p : Problem) : State := p.state.core.current.ordinary
def actualConstructors (p : Problem) := (authoredRegistry p.state.core.current).constructors
def actualInterpretation (p : Problem) := interpretation p.state.core.current.environment.source.snapshot

structure CheckedCaptureHead (p : Problem) (tab : CheckedTable p.state.core.current) where
  original : PrecheckedHead (p := p) tab
  allocated : OldCaptureReceipt

/-- Same input as the existing prechecked head. The supplied source view is
independently authorized in the theorem below, not inferred from success.
No native origin, new graph step, or selected-rule verdict is produced. -/
def readCaptureFromReadyHead (p : Problem) (tab : CheckedTable p.state.core.current)
    {legacySource : State} (idx : Sources legacySource) (addr : HeadAddress)
    (keep : List Nat) (job : Nat) : Option (CheckedCaptureHead p tab) :=
  if (visible p.state.core p.root).length = 1 then do
    let head ← readPrecheckedHead (p := p) tab addr
    let receipt ← readOldCaptureReceipt (ordinary p) idx (actualConstructors p)
      (actualInterpretation p) head.orig.capture keep head.orig.original job
    pure ⟨head,receipt⟩
  else none

theorem previous_compiler_receipt_requires_the_actual_request_and_prechecked_head
    (p : Problem) (tab : CheckedTable p.state.core.current)
    {done : Nat → Prop} {pinned : Supported (ordinary p) done}
    (idx : Sources (restriction pinned)) (addr : HeadAddress) (keep : List Nat)
    (job : Nat) (r : CheckedCaptureHead p tab) :
    readCaptureFromReadyHead p tab idx addr keep job = some r ↔
      (visible p.state.core p.root).length = 1 ∧
      readPrecheckedHead (p := p) tab addr = some r.original ∧
      ExactOldCaptureExecution idx (actualConstructors p) (actualInterpretation p)
        r.original.orig.capture keep r.original.orig.original job r.allocated := by
  constructor
  · intro accepted
    by_cases one : (visible p.state.core p.root).length = 1
    · cases anchor : readPrecheckedHead (p := p) tab addr with
      | none => simp [readCaptureFromReadyHead,one,anchor,Option.bind] at accepted
      | some h =>
        cases allocation : readOldCaptureReceipt (ordinary p) idx (actualConstructors p)
            (actualInterpretation p) h.orig.capture keep h.orig.original job with
        | none => simp [readCaptureFromReadyHead,one,anchor,allocation,Option.bind] at accepted
        | some read =>
          have eq : (⟨h,read⟩ : CheckedCaptureHead p tab) = r := by
            simpa [readCaptureFromReadyHead,one,anchor,allocation,Option.bind] using accepted
          subst r
          exact ⟨one,rfl,(exact_old_capture_execution_has_data_only_receipt ..).mp allocation⟩
    · simp [readCaptureFromReadyHead,one] at accepted
  · rintro ⟨one,head,receipt⟩
    have success := (exact_old_capture_execution_has_data_only_receipt ..).mpr receipt
    cases r
    simp_all [readCaptureFromReadyHead,Option.bind]

theorem ready_head_receipt_preserves_actual_source_identity_and_physical_coordinate
    (p : Problem) (tab : CheckedTable p.state.core.current)
    {done : Nat → Prop} {available : Supported (ordinary p) done}
    (idx : Sources (restriction available)) (addr : HeadAddress) (keep : List Nat)
    (job : Nat) (r : CheckedCaptureHead p tab)
    (accepted : readCaptureFromReadyHead p tab idx addr keep job = some r) :
    r.original.orig.location = addr ∧
    DeclarationReady (authoredRegistry p.state.core.current) r.original.orig.declaration ∧
    r.allocated.after.equations[r.allocated.rawOrdinal]? = some ⟨r.allocated.target,r.allocated.captured.term⟩ ∧
    atSource (normalize r.original.orig.original) r.allocated.written =
      some (.var r.allocated.captured.binder) := by
  obtain ⟨_,anchor,actual⟩ :=
    (previous_compiler_receipt_requires_the_actual_request_and_prechecked_head ..).mp accepted
  exact ⟨prechecked_reader_never_renumbers_the_visible_roster anchor,
    prechecked_head_is_genuinely_ready r.original,
    a_receipt_really_names_the_original_capture_and_the_appended_ordinary_row
      ((exact_old_capture_execution_has_data_only_receipt ..).mpr actual)⟩

end Yulang.C466WrittenBinderCoordinates
