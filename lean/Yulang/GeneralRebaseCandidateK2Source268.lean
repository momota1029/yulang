import Yulang.GeneralRebaseRawCandidate268
import Yulang.GeneralRebaseEnumeratePlans267

namespace Yulang.GeneralRebaseCandidateK2Source268
open GeneralDeclarations (Registry Declaration)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedCycles232 (Cyclic)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalRecursiveCandidates (Metadata arguments)
open GeneralNominalVersionedCandidates231 (inputs Prepared)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebasePartialBool268 (Answer Reflect both either)
open GeneralRebasePartialFinite268 (transfer)
open GeneralRebaseOccurrenceEq267 (same same_exact)
open GeneralRebaseRawK2Probe268 (bool_reflect)
open GeneralRebaseInspectionChecks268 (Head BoundList)
open GeneralRebaseEnumeratePlans267 (plans plans_exact frame_of_member includes_frame)
open GeneralRebaseCandidatePrepared267 (preflight prepared_iff headCondition)
open GeneralRebaseVersionedK2Probe268 (framed candidateOrigin candidateOrigin_sound)

def focusPlans (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) : List (Plan roles) :=
 (plans (Encoded registry) state root (declChecked checked)).filter
  fun plan => same plan.packet.site.occurrence focus

theorem focusPlans_exact (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (plan : Plan roles) :
 plan ∈ focusPlans registry state root focus checked ↔
 plan ∈ plans (Encoded registry) state root (declChecked checked) ∧ plan.packet.site.occurrence = focus := by
 simp [focusPlans,same_exact]

theorem includes (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (generated : Generated state.core.erased.current root focus)
 (plan : Plan roles) (frame : framed registry state focus plan) :
 plan ∈ focusPlans registry state root focus checked := by
 have equality := frame.occurrence_eq
 apply (focusPlans_exact ..).mpr
 refine ⟨includes_frame _ _ _ (declChecked checked) plan (equality.symm ▸ generated) ?_,equality⟩
 rw [equality]
 exact frame

def preparedBit (metadata : Answer) (head : Plan roles → Answer) (plan : Plan roles) : Answer :=
 both metadata (both (some (preflight plan)) (head plan))

theorem preparedBit_sound (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (metadata : Answer) (head : Plan roles → Answer)
 (knownMeta : Reflect (Metadata (Encoded registry) state.core.erased.current.context) metadata)
 (plan : Plan roles) (listed : plan ∈ focusPlans registry state root focus checked)
 (knownHead : Reflect (headCondition plan) (head plan)) :
 Reflect (framed registry state focus plan) (preparedBit metadata head plan) := by
 obtain ⟨allPlans,atFocus⟩ := (focusPlans_exact ..).mp listed
 have shell := (plans_exact ..).mp allPlans
 apply transfer (p := Metadata (Encoded registry) state.core.erased.current.context ∧
   preflight plan = true ∧ headCondition plan)
 · have prep := prepared_iff (Encoded registry) state root plan shell
   constructor
   · intro given
     have actual := frame_of_member _ _ _ (declChecked checked) plan allPlans (prep.mpr given)
     rwa [atFocus] at actual
   · intro onFrame
     exact prep.mp (atFocus.symm ▸ onFrame.prepared)
 · exact GeneralRebasePartialBool268.both_sound knownMeta
     (GeneralRebasePartialBool268.both_sound (bool_reflect _ _ Iff.rfl) knownHead)

def probe (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (metadata : Answer)
 (head : Declaration → BoundList state.core.erased.current.context → Answer)
 (planHead : Plan roles → Answer) (cyclic : Origin → Answer)
 (rawK2 : GeneralRebaseRawK2Probe268.Probes state.core.erased.current.context.state) : Answer :=
 either (GeneralRebaseRawCandidate268.check (Encoded registry) state.core.erased.current.context focus metadata
    head (GeneralRebaseRawK2Probe268.recurs _ rawK2))
  (candidateOrigin (focusPlans registry state root focus checked) (preparedBit metadata planHead) cyclic)

theorem probe_sound (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry) (generated : Generated state.core.erased.current root focus)
 (metadata : Answer) (head : Declaration → BoundList state.core.erased.current.context → Answer)
 (planHead : Plan roles → Answer) (cyclic : Origin → Answer)
 (rawK2 : GeneralRebaseRawK2Probe268.Probes state.core.erased.current.context.state)
 (knownRaw : GeneralRebaseRawK2Probe268.Sound _ rawK2)
 (knownMeta : Reflect (Metadata (Encoded registry) state.core.erased.current.context) metadata)
 (knownHead : ∀ d ∈ (Encoded registry).declarations, ∀ bounds,
   arguments state.core.erased.current.context (inputs focus) = some bounds →
   Reflect (Head (Encoded registry) state.core.erased.current.context focus d bounds) (head d bounds))
 (knownPlan : ∀ plan ∈ focusPlans registry state root focus checked, Reflect (headCondition plan) (planHead plan))
 (knownCycles : ∀ o, Reflect (Cyclic state o) (cyclic o)) :
 Reflect ((Boundary roles).CandidateK2 registry state focus)
   (probe registry state root focus checked metadata head planHead cyclic rawK2) := by
 apply GeneralRebasePartialBool268.either_sound
 · exact GeneralRebaseRawCandidate268.check_sound _ _ _ _ _ _ knownMeta knownHead
     (GeneralRebaseRawK2Probe268.recurs_sound _ rawK2 knownRaw) (declChecked checked)
 · exact candidateOrigin_sound registry state focus _ _ cyclic
     (fun p listed => preparedBit_sound registry state root focus checked metadata planHead knownMeta p listed
       (knownPlan p listed)) (includes registry state root focus checked generated) knownCycles

end Yulang.GeneralRebaseCandidateK2Source268
