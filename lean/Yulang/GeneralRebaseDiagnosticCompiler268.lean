import Yulang.GeneralRebaseConflictModel268
import Yulang.GeneralRebaseMergedSlices268
import Yulang.GeneralRebaseConsensusDiagnostic268

namespace Yulang.GeneralRebaseDiagnosticCompiler268
open GeneralDeclarations (Registry Declaration)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCenters (Plan Site SameInputs)
open GeneralNominalRecursiveCandidates (arguments Metadata)
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalVersionedCycles232 (Cyclic)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseCandidatePrepared267 (headCondition)
open GeneralRebaseInspectionChecks268 (Head BoundList)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralRebaseDiagnosticSource268 (Probes prepare)
open GeneralRebaseDiagnosticData268 (Inputs Valid)
open GeneralRebaseCandidateK2Source268 (focusPlans preparedBit preparedBit_sound)
open GeneralRebaseConflictModel268 (HeadFit EffectsFit SharedFit output sharing output_sound sharing_sound)
open GeneralRebaseMergedSlices268 (Atom atoms classes)
open GeneralRebaseFiniteSlices268 (slices)
open GeneralNominalVersionedMergedConflict232 (ContextModels ClassEquations)

structure Replies (state : State roles) where
 metadata : Answer
 rawCycle : GeneralRebaseRawK2Probe268.Probes state.core.erased.current.context.state
 cyclic : Origin → Answer
 head : Declaration → BoundList state.core.erased.current.context → Answer
 planHead : Plan roles → Answer
 compare : Site roles → Site roles → Answer
 chosenHead : Plan roles → Answer
 chosenEffects : Plan roles → Answer
 share : Plan roles → Answer
 inhabited : Answer
 slice : List Atom → List (Occurrence roles) → Answer
 extendedSlice : List Atom → List (Occurrence roles) → Answer

structure Certified (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (p : Replies state) : Prop where
 metadata : Reflect (Metadata (Encoded registry) state.core.erased.current.context) p.metadata
 rawCycle : GeneralRebaseRawK2Probe268.Sound _ p.rawCycle
 cyclic : ∀ o, Reflect (Cyclic state o) (p.cyclic o)
 head : ∀ d ∈ (Encoded registry).declarations, ∀ bounds,
   arguments state.core.erased.current.context (inputs focus) = some bounds →
   Reflect (Head (Encoded registry) state.core.erased.current.context focus d bounds) (p.head d bounds)
 planHead : ∀ plan ∈ focusPlans registry state root focus checked, Reflect (headCondition plan) (p.planHead plan)
 compare : ∀ first ∈ state.core.sites, ∀ last ∈ state.core.sites,
   Reflect (SameInputs (Models state) first last) (p.compare first last)
 chosenHead : ∀ plan ∈ focusPlans registry state root focus checked, Reflect (HeadFit state focus plan) (p.chosenHead plan)
 chosenEffects : ∀ plan ∈ focusPlans registry state root focus checked, Reflect (EffectsFit state focus plan) (p.chosenEffects plan)
 share : ∀ plan ∈ focusPlans registry state root focus checked, Reflect (SharedFit state plan) (p.share plan)
 inhabited : Reflect (∃ model, Models state model) p.inhabited
 slice : ∀ used ∈ slices (atoms state), ∀ linked ∈ slices (classes state),
   Reflect (∃ model, ContextModels state used linked model) (p.slice used linked)
 extendedSlice : ∀ used ∈ slices (atoms state), ∀ linked ∈ slices (classes state),
   Reflect (∃ model, ContextModels state used linked model ∧ ClassEquations state focus model) (p.extendedSlice used linked)

def firstPass (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (p : Replies state) : Probes :=
 ⟨GeneralRebaseVersionedK2Probe268.root registry state focus p.rawCycle p.cyclic,
  GeneralRebaseCandidateK2Source268.probe registry state root focus checked p.metadata p.head p.planHead p.cyclic p.rawCycle,
  GeneralRebaseInspectionProbe268.probe registry state focus p.metadata p.head p.compare,
  fun _ => none,GeneralRebaseMergedSlices268.probe state focus p.slice p.extendedSlice,none⟩

theorem firstPass_sound (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (generated : Generated state.core.erased.current root focus)
 (p : Replies state) (cert : Certified registry state root focus checked p) :
 GeneralRebaseDiagnosticSource268.Sound registry state focus (firstPass registry state root focus checked p) :=
 ⟨GeneralRebaseVersionedK2Probe268.root_sound registry state focus p.rawCycle cert.rawCycle p.cyclic cert.cyclic,
  GeneralRebaseCandidateK2Source268.probe_sound registry state root focus checked generated p.metadata p.head
    p.planHead p.cyclic p.rawCycle cert.rawCycle cert.metadata cert.head cert.planHead cert.cyclic,
  GeneralRebaseInspectionProbe268.probe_sound registry state focus p.metadata p.head p.compare cert.metadata cert.head cert.compare,
  fun _ => True.intro,GeneralRebaseMergedSlices268.probe_sound state focus p.slice p.extendedSlice cert.slice cert.extendedSlice,
  True.intro⟩

theorem honest (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (p : Replies state)
 (cert : Certified registry state root focus checked p) :
 GeneralRebaseHeadProbe267.Honest p.planHead (GeneralRebaseHeadProbe267.atFocus (Encoded registry) state root focus (declChecked checked)) := by
 have allCertified : ∀ plan ∈ GeneralRebaseHeadProbe267.atFocus (Encoded registry) state root focus (declChecked checked),
    Reflect (headCondition plan) (p.planHead plan) := by
   intro plan onList
   obtain ⟨ready,same⟩ := (GeneralRebaseHeadProbe267.atFocus_exact ..).mp onList
   have shell := ((GeneralRebaseCandidatePrepared267.ready_exact ..).mp ready).1
   exact cert.planHead plan ((GeneralRebaseCandidateK2Source268.focusPlans_exact ..).mpr
     ⟨(GeneralRebaseEnumeratePlans267.plans_exact ..).mpr shell,same⟩)
 constructor <;> intro plan listed reply
 · simpa only [reply,Reflect] using allCertified plan listed
 · simpa only [reply,Reflect] using allCertified plan listed

def compile (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (p : Replies state) : Inputs (Occurrence roles) :=
 let base := prepare registry state root focus checked p.planHead (firstPass registry state root focus checked p)
 let candidates := focusPlans registry state root focus checked
 let frame := preparedBit p.metadata p.planHead
 { base with
   outputConflict := output base candidates frame p.chosenHead p.chosenEffects
   sharingConflict := sharing base candidates frame p.share p.inhabited }

theorem valid (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (generated : Generated state.core.erased.current root focus)
 (metadata : Metadata (Encoded registry) state.core.erased.current.context)
 (p : Replies state) (cert : Certified registry state root focus checked p) :
 Valid (Boundary roles) registry state focus (compile registry state root focus checked p) := by
 let base := prepare registry state root focus checked p.planHead (firstPass registry state root focus checked p)
 have before : Valid (Boundary roles) registry state focus base :=
   GeneralRebaseDiagnosticSource268.valid registry state root focus checked reachable generated metadata p.planHead
     (honest registry state root focus checked p cert) _
     (firstPass_sound registry state root focus checked generated p cert)
 have frame : ∀ plan ∈ focusPlans registry state root focus checked,
   Reflect (GeneralRebaseVersionedK2Probe268.framed registry state focus plan)
      (preparedBit p.metadata p.planHead plan) := by
   intro plan listed
   exact preparedBit_sound registry state root focus checked p.metadata p.planHead cert.metadata
     plan listed (cert.planHead plan listed)
 refine ⟨before.rootPending,before.rootK2,before.candidateK2,before.inspection,before.survivors,?_,
    before.mergedConflict,?_⟩
 · exact output_sound registry state root focus checked generated base before.survivors _ _ _
     frame cert.chosenHead cert.chosenEffects
 · exact sharing_sound registry state root focus checked generated base before _ _ _
     frame cert.share cert.inhabited

theorem sound (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (generated : Generated state.core.erased.current root focus)
 (metadata : Metadata (Encoded registry) state.core.erased.current.context)
 (p : Replies state) (cert : Certified registry state root focus checked p)
 (found : GeneralRebaseConsensusDiagnostic268.run (compile registry state root focus checked p) = some result) :
 B4TargetV8.Local (Boundary roles) registry state focus result :=
 GeneralRebaseConsensusDiagnostic268.sound _ _ _ _ _
   (valid registry state root focus checked reachable generated metadata p cert) found

theorem exact_of_complete (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (generated : Generated state.core.erased.current root focus)
 (metadata : Metadata (Encoded registry) state.core.erased.current.context)
 (p : Replies state) (cert : Certified registry state root focus checked p)
 (complete : GeneralRebaseDiagnosticV8268.Complete (compile registry state root focus checked p))
 (result : CommonRoleOutermostResolver.Frontier (Occurrence roles)) :
 GeneralRebaseConsensusDiagnostic268.run (compile registry state root focus checked p) = some result ↔
 B4TargetV8.Local (Boundary roles) registry state focus result :=
 GeneralRebaseConsensusDiagnostic268.exact_of_complete _ _ _ _ _
   (valid registry state root focus checked reachable generated metadata p cert) complete result

end Yulang.GeneralRebaseDiagnosticCompiler268
