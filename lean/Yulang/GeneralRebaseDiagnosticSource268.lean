import Yulang.GeneralRebaseDiagnosticV8268
import Yulang.GeneralRebaseCompleteHeadProbe267

namespace Yulang.GeneralRebaseDiagnosticSource268
open GeneralDeclarations (Registry)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)
open CommonRoleOutermostResolver (Frontier)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (Honest atFocus)
open GeneralRebaseCandidateChecks267 (allKnown allKnown_exact)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralRebaseDiagnosticData268 (Inputs Valid)
open GeneralRebaseDiagnosticV8268 (Complete)
open GeneralRebaseCompleteHeadProbe267 (Covered unresolved_empty)

structure Probes where
 rootK2 : Answer
 candidateK2 : Answer
 inspection : Answer
 outputConflict : Nat → Answer
 mergedConflict : Answer
 sharingConflict : Answer

structure Sound (registry : Registry) (state : State roles) (focus : Occurrence roles) (p : Probes) : Prop where
 rootK2 : Reflect ((Boundary roles).RootK2 registry state focus) p.rootK2
 candidateK2 : Reflect ((Boundary roles).CandidateK2 registry state focus) p.candidateK2
 inspection : Reflect ((Boundary roles).InspectionPending registry state focus) p.inspection
 outputConflict : ∀ key, Reflect ((Boundary roles).OutputConflict registry state focus key) (p.outputConflict key)
 mergedConflict : Reflect ((Boundary roles).MergedOutputConflict registry state focus) p.mergedConflict
 sharingConflict : Reflect ((Boundary roles).SharingConflict registry state focus) p.sharingConflict

def prepare (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (head : Plan roles → Option Bool) (p : Probes) : Inputs (Occurrence roles) :=
 ⟨some (!(allKnown state.core.erased.current.context.state (GeneralNominalVersionedCandidates231.inputs focus).demand)),
  p.rootK2,p.candidateK2,p.inspection,
  GeneralRebaseSourceClassification267.verdict head (atFocus (Encoded registry) state root focus (declChecked checked)),
  p.outputConflict,p.mergedConflict,p.sharingConflict⟩

theorem pending_exact (registry : Registry) (state : State roles) (focus : Occurrence roles) :
 Reflect ((Boundary roles).RootPending registry state focus)
  (some (!(allKnown state.core.erased.current.context.state (GeneralNominalVersionedCandidates231.inputs focus).demand))) := by
 let demand := (GeneralNominalVersionedCandidates231.inputs focus).demand
 have exactness := allKnown_exact state.core.erased.current.context.state demand
 cases h : allKnown state.core.erased.current.context.state demand with
 | false =>
   change GeneralNominalState.RootPending state.core.erased.current.context.state demand
   simpa [h] using exactness
 | true =>
   change Reflect (GeneralNominalState.RootPending state.core.erased.current.context.state demand) (some (!true))
   exact exactness.mp h

theorem survivor_bridge (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (v : GeneralRebasePartialClassification267.Verdict (GeneralRebaseHeadProbe267.Match roles)) :
 GeneralRebaseSourceClassification267.Justified (Encoded registry) state focus v →
 GeneralRebaseDiagnosticData268.SurvivorSound (Boundary roles) registry state focus v := by
 cases v with
 | none | deferred => exact id
 | unique item => cases item; exact id
 | ambiguous a b => cases a; cases b; exact id

theorem valid (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus)
 (metadata : GeneralNominalRecursiveCandidates.Metadata (Encoded registry) state.core.erased.current.context)
 (head : Plan roles → Option Bool)
 (honest : Honest head (atFocus (Encoded registry) state root focus (declChecked checked)))
 (p : Probes) (sound : Sound registry state focus p) :
 Valid (Boundary roles) registry state focus (prepare registry state root focus checked head p) :=
 ⟨pending_exact registry state focus,sound.rootK2,sound.candidateK2,sound.inspection,
  survivor_bridge registry state focus _
   (GeneralRebaseSourceClassification267.source_valid registry state root focus checked reachable generated metadata head honest),
  sound.outputConflict,sound.mergedConflict,sound.sharingConflict⟩

theorem survivor_total (head : Plan roles → Option Bool) (entries : List (Plan roles))
 (covered : Covered head entries) : GeneralRebaseSourceClassification267.verdict head entries ≠ .deferred := by
 unfold GeneralRebaseSourceClassification267.verdict
 rw [unresolved_empty head entries covered]
 simp only [List.map_nil]
 cases h : GeneralRebaseHeadProbe267.positive head entries with
 | nil => simp [GeneralRebasePartialClassification267.classify]
 | cons first tail =>
   simp only [GeneralRebasePartialClassification267.classify]
   split <;> simp

theorem total (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (head : Plan roles → Option Bool)
 (headTotal : Covered head (atFocus (Encoded registry) state root focus (declChecked checked)))
 (p : Probes) (rootKnown : p.rootK2 ≠ none) (candidateKnown : p.candidateK2 ≠ none)
 (inspectKnown : p.inspection ≠ none) (outputKnown : ∀ key, p.outputConflict key ≠ none)
 (mergeKnown : p.mergedConflict ≠ none) (shareKnown : p.sharingConflict ≠ none) :
 Complete (prepare registry state root focus checked head p) :=
 ⟨by simp [prepare],rootKnown,candidateKnown,inspectKnown,survivor_total head _ headTotal,
   fun key _ _ => outputKnown key,mergeKnown,shareKnown⟩

end Yulang.GeneralRebaseDiagnosticSource268
