import Yulang.GeneralDeclarativeI65I74CompiledCaptureCoordinate466
import Yulang.GeneralDeclarativeNestedDecode332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466WrittenBinderCoordinates
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeNestedDecode332 (normalized normalized_sound)
open GeneralDeclarativeNestedMaterial332 (assemble)
open GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin (Pose atSource)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeInlineTrace331 (Read)
open OrdinaryOccurrenceStamp466

structure OldCaptureReceipt where
  after : State
  captures : List (Nat × Capture)
  rawOrdinal : Nat
  target : Nat
  captureOrdinal : Nat
  written : List Pose
  captured : Occurrence

/-- This invokes the existing source reader and the actual old assembler.
Output names/ordinals and written paths are obtained from that very run.
The returned snapshot is never installed in an I65 state. -/
def readOldCaptureReceipt (s : State) {legacySource : State}
    (auth : Sources legacySource) (c : Constructors) (i : Interpretation)
    (arg : Capture) (kept : List Nat) (p : Pattern) (job : Nat) : Option OldCaptureReceipt := do
  let code ← translate c i (normalize p)
  let uses ← normalized auth c i .actual (.variable arg.center) p
  let (after,captures) ← assemble s arg kept code uses
  let (target,site,term) ← existingCaptureJob s arg kept uses job
  let (written,_) ← (bindersAt (normalize p))[site]?
  pure ⟨after,captures,s.equations.length + job,target,site,written,term⟩

def ExactOldCaptureExecution {s : State} {done : Nat → Prop} {old : Supported s done}
    (auth : Sources (restriction old)) (c : Constructors) (i : Interpretation)
    (arg : Capture) (kept : List Nat) (p : Pattern) (job : Nat)
    (r : OldCaptureReceipt) : Prop :=
  ∃ code uses,
    translate c i (normalize p) = some code ∧
    normalized auth c i .actual (.variable arg.center) p = some uses ∧
    assemble s arg kept code uses = some (r.after,r.captures) ∧
    existingCaptureJob s arg kept uses job = some (r.target,r.captureOrdinal,r.captured) ∧
    (bindersAt (normalize p))[r.captureOrdinal]? = some (r.written,r.captured.binder) ∧
    r.rawOrdinal = s.equations.length + job

theorem exact_old_capture_execution_has_data_only_receipt
    {s : State} {done : Nat → Prop} {old : Supported s done}
    (auth : Sources (restriction old)) (c : Constructors) (i : Interpretation)
    (arg : Capture) (kept : List Nat) (p : Pattern) (job : Nat) (r : OldCaptureReceipt) :
    readOldCaptureReceipt s auth c i arg kept p job = some r ↔
      ExactOldCaptureExecution auth c i arg kept p job r := by
  constructor
  · intro ok
    cases rendered : translate c i (normalize p) with
    | none => simp [readOldCaptureReceipt,rendered,Option.bind] at ok
    | some code =>
      cases saw : normalized auth c i .actual (.variable arg.center) p with
      | none => simp [readOldCaptureReceipt,rendered,saw,Option.bind] at ok
      | some uses =>
        cases ran : assemble s arg kept code uses with
        | none => simp [readOldCaptureReceipt,rendered,saw,ran,Option.bind] at ok
        | some result =>
          obtain ⟨state,caps⟩ := result
          cases chosen : existingCaptureJob s arg kept uses job with
          | none => simp [readOldCaptureReceipt,rendered,saw,ran,chosen,Option.bind] at ok
          | some build =>
            obtain ⟨target,site,term⟩ := build
            obtain ⟨rebuilt,printed,source⟩ := normalized_sound saw
            have sameCode := Option.some.inj (printed.symm.trans rendered)
            subst rebuilt
            obtain ⟨_,path,exactAt,_⟩ :=
              original_normalized_capture_path_and_raw_allocated_row_share_one_old_compiler_read
                rendered source ran chosen
            have eq : ⟨state,caps,s.equations.length+job,target,site,path,term⟩ = r := by
              simpa [readOldCaptureReceipt,rendered,saw,ran,chosen,exactAt,Option.bind] using ok
            subst r
            exact ⟨code,uses,rendered,saw,ran,chosen,exactAt,rfl⟩
  · rintro ⟨code,uses,printed,saw,ran,chosen,site,exact⟩
    cases r
    simp_all [readOldCaptureReceipt,Option.bind]

theorem a_receipt_really_names_the_original_capture_and_the_appended_ordinary_row
    {s : State} {done : Nat → Prop} {old : Supported s done}
    {auth : Sources (restriction old)} {c i arg kept p job r}
    (proof : readOldCaptureReceipt s auth c i arg kept p job = some r) :
    r.after.equations[r.rawOrdinal]? = some ⟨r.target,r.captured.term⟩ ∧
      atSource (normalize p) r.written = some (.var r.captured.binder) := by
  obtain ⟨code,used,printed,saw,ran,chosen,actual,rawOrdinal⟩ :=
    (exact_old_capture_execution_has_data_only_receipt ..).mp proof
  obtain ⟨another,compiled,source⟩ := normalized_sound saw
  have useSame := Option.some.inj (compiled.symm.trans printed)
  subst another
  obtain ⟨raw,site,resolved,sourceAt⟩ :=
    original_normalized_capture_path_and_raw_allocated_row_share_one_old_compiler_read
      printed source ran chosen
  have siteSame := congrArg Prod.fst (Option.some.inj (actual.symm.trans resolved))
  refine ⟨rawOrdinal.symm ▸ raw,?_⟩
  change r.written = site at siteSame
  rw [siteSame]
  exact sourceAt

end Yulang.C466WrittenBinderCoordinates
