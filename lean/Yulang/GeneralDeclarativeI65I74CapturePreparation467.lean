import Yulang.GeneralDeclarativeI65I74ActualHeadFrame467
import Yulang.GeneralDeclarativeI65I74PreparedExecution467

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CapturePreparation467
open Yulang.C466WrittenBinderCoordinates
open GeneralDeclarativeI65 (visible)
open GeneralDeclarativeI65.I72.Checker408 (Problem)
open GeneralDeclarativeI65.I72.PreparedDeclarations463
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWitnessNativePreparation360 (Layout Prepared prepare)
open GeneralDeclarativeI65.I72.ActualHeadFrame467
open GeneralDeclarativeI65.I72.PreparedExecution467 (native_preparation_replays_exact_independent_record)
open GeneralDeclarations (Clause)

/-- The actual old allocator determines just the named snapshot and the
literal source key. Port requests/targets are already owned inputs of the
existing native preparation phase; this API does not invent them. -/
structure PortInput where
  spans : List (Nat × Capture)
  keep : List Nat
  fallback : Nat → Capture
  targets : Clause → Nat → Nat

def PortInput.useExactOldAfter (i : PortInput) (r : OldCaptureReceipt) : Layout :=
  ⟨r.after,i.spans,i.keep,i.fallback,i.targets⟩

structure PreparedFromActualCapture {p : Problem} {tab : CheckedTable p.state.core.current}
    (i : PortInput) where
  captured : CheckedCaptureHead p tab
  frame : FrameKey
  authored : actualCompilerFrameKey captured.original.orig = some frame
  prepared : Prepared p.state.core.current.environment frame p.root.demand
    (i.useExactOldAfter captured.allocated)

private def finishPreparation {p : Problem} {tab : CheckedTable p.state.core.current}
    (r : CheckedCaptureHead p tab) (i : PortInput) :
    Option (PreparedFromActualCapture (p := p) (tab := tab) i) :=
  match named : actualCompilerFrameKey r.original.orig with
  | none => none
  | some frame =>
    (prepare p.state.core.current.environment frame p.root.demand (i.useExactOldAfter r.allocated)).map
      (fun ready => ⟨r,frame,named,ready⟩)

def readCompilerPreparation {p : Problem} {tab : CheckedTable p.state.core.current}
    {old : GeneralDeclarativeHead320.State}
    (idx : Sources old) (address : HeadAddress) (protect : List Nat) (job : Nat)
    (i : PortInput) : Option (PreparedFromActualCapture (p := p) (tab := tab) i) :=
  (readCaptureFromReadyHead p tab idx address protect job).bind (fun r => finishPreparation r i)

/-- This is independent evidence for an actual old capture and permitted
native preparation. It is not a head-output issuer or a selected rule. -/
def ExactActualPreparation {p : Problem} {tab : CheckedTable p.state.core.current} {done : Nat → Prop}
    {old : Supported (ordinary p) done} (idx : Sources (restriction old)) (address : HeadAddress)
    (protect : List Nat) (job : Nat) {i : PortInput} (answer : PreparedFromActualCapture (p := p) (tab := tab) i) : Prop :=
  (visible p.state.core p.root).length = 1 ∧
  readPrecheckedHead (p := p) tab address = some answer.captured.original ∧
  ExactOldCaptureExecution idx (actualConstructors p) (actualInterpretation p)
    answer.captured.original.orig.capture protect answer.captured.original.orig.original job answer.captured.allocated

theorem actual_preparation_wire_iff_old_source_and_native_compiler_record
    {p : Problem} {tab : CheckedTable p.state.core.current} {done : Nat → Prop}
    {old : Supported (ordinary p) done} (idx : Sources (restriction old)) (address : HeadAddress)
    (protect : List Nat) (job : Nat) (i : PortInput)
    (answer : PreparedFromActualCapture (p := p) (tab := tab) i) :
    readCompilerPreparation idx address protect job i = some answer ↔
      ExactActualPreparation idx address protect job answer := by
  have same : (readCaptureFromReadyHead p tab idx address protect job =
      some answer.captured) ↔ ExactActualPreparation idx address protect job answer :=
    previous_compiler_receipt_requires_the_actual_request_and_prechecked_head _ _ _ _ _ _ _
  constructor
  · intro hit
    cases found : readCaptureFromReadyHead p tab idx address protect job with
    | none => simp [readCompilerPreparation,found,Option.bind] at hit
    | some r =>
      simp only [readCompilerPreparation,found,Option.bind,finishPreparation] at hit
      split at hit
      · cases hit
      · rename_i frame key
        cases made : prepare p.state.core.current.environment frame p.root.demand
            (i.useExactOldAfter r.allocated) with
        | none => simp [made] at hit
        | some value =>
          have arrived : (⟨r,frame,key,value⟩ : PreparedFromActualCapture i) = answer := by
            simpa [made] using hit
          cases arrived
          exact same.mp found
  · intro exactInput
    have runs := same.mpr exactInput
    have compiled := native_preparation_replays_exact_independent_record answer.prepared
    rcases answer with ⟨r,frame,key,prepared⟩
    unfold readCompilerPreparation
    rw [runs]
    simp only [Option.bind,finishPreparation]
    split
    · rename_i missing
      rw [key] at missing
      cases missing
    · rename_i returned here
      have eq := Option.some.inj (key.symm.trans here)
      subst returned
      change prepare p.state.core.current.environment frame p.root.demand
        (i.useExactOldAfter r.allocated) = some prepared at compiled
      simp [compiled]

theorem actual_prepared_source_preserves_separate_old_raw_coordinate
    {p : Problem} {tab : CheckedTable p.state.core.current} {done : Nat → Prop}
    {old : Supported (ordinary p) done} (idx : Sources (restriction old)) (address : HeadAddress)
    (protect : List Nat) (job : Nat) (i : PortInput)
    (answer : PreparedFromActualCapture (p := p) (tab := tab) i)
    (hit : readCompilerPreparation idx address protect job i = some answer) :
    answer.frame.occurrence = p.root.occurrence ∧
    answer.prepared.impl = answer.captured.original.orig.declaration ∧
    answer.captured.allocated.after.equations[answer.captured.allocated.rawOrdinal]? =
      some ⟨answer.captured.allocated.target,answer.captured.allocated.captured.term⟩ := by
  have works := (actual_preparation_wire_iff_old_source_and_native_compiler_record ..).mp hit
  obtain ⟨frame,actual,occurrence,_id,_decl,agrees⟩ :=
    a_real_single_head_fixes_an_existing_prepared_frame_without_generating_authority
      answer.captured.original.orig works.1
  have sameFrame := Option.some.inj (actual.symm.trans answer.authored)
  subst frame
  have selected := (previous_compiler_receipt_requires_the_actual_request_and_prechecked_head ..).mpr works
  exact ⟨occurrence,agrees _ answer.prepared,
    (ready_head_receipt_preserves_actual_source_identity_and_physical_coordinate _ _ _ _ _ _ _ selected).2.2.1⟩


/-- Only the existing port policy inputs remain supplied. The native
span table is now computed from this exact ordinary compiler execution. -/
structure PortPolicy where
  keep : List Nat
  fallback : Nat → Capture
  targets : Clause → Nat → Nat

def oldProducedPortInput (policy : PortPolicy) (r : OldCaptureReceipt) : PortInput :=
  ⟨r.captures,policy.keep,policy.fallback,policy.targets⟩

def readUsingOldCaptureTable {p : Problem} {tab : CheckedTable p.state.core.current}
    {old : GeneralDeclarativeHead320.State}
    (idx : Sources old) (address : HeadAddress) (protect : List Nat) (job : Nat)
    (policy : PortPolicy) :
    Option (Σ i, PreparedFromActualCapture (p := p) (tab := tab) i) := do
  let receipt ← readCaptureFromReadyHead p tab idx address protect job
  let i := oldProducedPortInput policy receipt.allocated
  let got ← readCompilerPreparation (tab := tab) idx address protect job i
  pure ⟨i,got⟩

theorem using_old_capture_table_has_only_the_exact_bound_layout
    {p : Problem} {tab : CheckedTable p.state.core.current} {done : Nat → Prop}
    {old : Supported (ordinary p) done} (idx : Sources (restriction old)) (address : HeadAddress)
    (protect : List Nat) (job : Nat) (policy : PortPolicy)
    (i : PortInput) (answer : PreparedFromActualCapture (p := p) (tab := tab) i)
    (ran : readUsingOldCaptureTable idx address protect job policy = some ⟨i,answer⟩) :
    i = oldProducedPortInput policy answer.captured.allocated ∧
      ExactActualPreparation idx address protect job answer := by
  cases fromOld : readCaptureFromReadyHead p tab idx address protect job with
  | none => simp [readUsingOldCaptureTable,fromOld,Option.bind] at ran
  | some first =>
    let cfg := oldProducedPortInput policy first.allocated
    cases done : readCompilerPreparation (tab := tab) idx address protect job cfg with
    | none => simp [readUsingOldCaptureTable,fromOld,Option.bind,cfg,done] at ran
    | some got =>
      have same : (⟨cfg,got⟩ : Σ i, PreparedFromActualCapture (p := p) (tab := tab) i) =
          ⟨i,answer⟩ := by
        simpa [readUsingOldCaptureTable,fromOld,Option.bind,cfg,done] using ran
      have iSame : cfg = i := congrArg Sigma.fst same
      have rSame : got.captured = answer.captured :=
        congrArg (fun z : Σ i, PreparedFromActualCapture (p := p) (tab := tab) i => z.snd.captured) same
      have actual := (actual_preparation_wire_iff_old_source_and_native_compiler_record ..).mp done
      have oldAgain := (previous_compiler_receipt_requires_the_actual_request_and_prechecked_head ..).mpr actual
      have unique := Option.some.inj (oldAgain.symm.trans fromOld)
      refine ⟨?_,?_⟩
      · exact iSame.symm.trans (congrArg (fun r : CheckedCaptureHead p tab => oldProducedPortInput policy r.allocated) (unique.symm.trans rSame))
      · apply (previous_compiler_receipt_requires_the_actual_request_and_prechecked_head ..).mp
        exact oldAgain.trans (congrArg some rSame)

theorem using_old_capture_table_replays_any_exact_independent_output
    {p : Problem} {tab : CheckedTable p.state.core.current} {done : Nat → Prop}
    {old : Supported (ordinary p) done} (idx : Sources (restriction old)) (address : HeadAddress)
    (protect : List Nat) (job : Nat) (policy : PortPolicy) (chosen : CheckedCaptureHead p tab)
    (answer : PreparedFromActualCapture (p := p) (tab := tab) (oldProducedPortInput policy chosen.allocated))
    (same : answer.captured = chosen)
    (exact : ExactActualPreparation idx address protect job answer) :
    readUsingOldCaptureTable idx address protect job policy = some ⟨_,answer⟩ := by
  have fromOld := (previous_compiler_receipt_requires_the_actual_request_and_prechecked_head ..).mpr exact
  rw [same] at fromOld
  have compiled := (actual_preparation_wire_iff_old_source_and_native_compiler_record ..).mpr exact
  simp [readUsingOldCaptureTable,fromOld,Option.bind,compiled]

end Yulang.GeneralDeclarativeI65.I72.CapturePreparation467
