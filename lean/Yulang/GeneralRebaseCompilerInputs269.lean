import Yulang.GeneralRebaseRawActualProbe269
import Yulang.GeneralRebaseMergeJournal269
import Yulang.GeneralRebaseDiagnosticCompiler268
import Yulang.GeneralRebaseOriginEdgeScan269

namespace Yulang.GeneralRebaseCompilerInputs269
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedCycles232 (Cyclic)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalRecursiveCandidates (Metadata)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseDiagnosticCompiler268 (Replies Certified compile)
open GeneralRebaseRawActualProbe269 (orProbe orProbe_sound)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralRebaseJournalInequalities269 (Between)
open GeneralRebaseSlotInequalities269 (Bound)
open GeneralRebaseOriginCycles268 (Window Sound Closure NonemptyCycle)
open GeneralNominalVersionedCycles232 (Equal)

structure Inputs (state : State roles) where
 rawBounds : Fin state.core.erased.current.context.state.base.slots →
    Fin state.core.erased.current.context.state.base.slots → Answer
 journalBounds : Nat → Nat → Answer
 origin : Origin → Answer

structure Checked (state : State roles) (inputs : Inputs state) : Prop where
 raw : ∀ a b, Reflect (Bound state.core.erased.current.context.state a b) (inputs.rawBounds a b)
 journal : ∀ a b, Reflect (Between state a b) (inputs.journalBounds a b)
 origin : ∀ o, Reflect (Cyclic state o) (inputs.origin o)

def enhance (state : State roles) (inputs : Inputs state) (fallback : Replies state) : Replies state :=
 { fallback with
   rawCycle := GeneralRebaseRawActualProbe269.enhance _ fallback.rawCycle inputs.rawBounds
   cyclic := fun o => orProbe (inputs.origin o) (fallback.cyclic o)
   compare := fun a b => orProbe (GeneralRebaseSameInputs269.probe state inputs.journalBounds a b) (fallback.compare a b) }

theorem certify (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (inputs : Inputs state) (valid : Checked state inputs) (fallback : Replies state)
 (cert : Certified registry state root focus checked fallback) :
 Certified registry state root focus checked (enhance state inputs fallback) :=
 ⟨cert.metadata,GeneralRebaseRawActualProbe269.enhance_sound _ _ cert.rawCycle _ valid.raw,
  fun o => orProbe_sound (valid.origin o) (cert.cyclic o),cert.head,cert.planHead,
  fun a one b two => orProbe_sound (GeneralRebaseSameInputs269.probe_sound state _ valid.journal a b) (cert.compare a one b two),
  cert.chosenHead,cert.chosenEffects,cert.share,cert.inhabited,cert.slice,cert.extendedSlice⟩

/-- Upgrade finite comparisons and edge witnesses without replacing the
actual V8 precedence, installation conditions or any independent model tests. -/
theorem run_sound (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (generated : Generated state.core.erased.current root focus)
 (metadata : Metadata (Encoded registry) state.core.erased.current.context)
 (inputs : Inputs state) (valid : Checked state inputs) (fallback : Replies state)
 (cert : Certified registry state root focus checked fallback)
 (result : GeneralRebaseConsensusDiagnostic268.run (compile registry state root focus checked (enhance state inputs fallback)) = some verdict) :
 B4TargetV8.Local (Boundary roles) registry state focus verdict :=
 GeneralRebaseDiagnosticCompiler268.sound registry state root focus checked reachable generated metadata _
   (certify registry state root focus checked inputs valid fallback cert) result

def forWindow (state : State roles)
 (raw : Fin state.core.erased.current.context.state.base.slots →
    Fin state.core.erased.current.context.state.base.slots → Answer)
 (journal : Nat → Nat → Answer) (window : Window n)
 (matchOrigin : Origin → Fin n → Answer) (forwardCover : Fin n → Bool) (queryCover : Origin → Bool) : Inputs state :=
 ⟨raw,journal,GeneralRebaseOriginExecutable269.cyclic window matchOrigin forwardCover queryCover⟩

theorem window_certifies (state : State roles)
 (raw : Fin state.core.erased.current.context.state.base.slots →
    Fin state.core.erased.current.context.state.base.slots → Answer)
 (journal : Nat → Nat → Answer) (window : Window n)
 (matchOrigin : Origin → Fin n → Answer) (forwardCover : Fin n → Bool) (queryCover : Origin → Bool)
 (rawSound : ∀ a b, Reflect (Bound state.core.erased.current.context.state a b) (raw a b))
 (journalSound : ∀ a b, Reflect (Between state a b) (journal a b))
 (sound : Sound state window) (eq : ∀ o i, Reflect (Equal state o (window.point i)) (matchOrigin o i))
 (forward : ∀ j, forwardCover j = true → Closure state window j)
 (query : ∀ o, queryCover o = true → NonemptyCycle state o → ∃ i, Equal state o (window.point i)) :
 Checked state (forWindow state raw journal window matchOrigin forwardCover queryCover) :=
 ⟨rawSound,journalSound,fun o => GeneralRebaseOriginExecutable269.cyclic_sound window sound matchOrigin
   forwardCover queryCover (eq o) forward (query o)⟩

end Yulang.GeneralRebaseCompilerInputs269
