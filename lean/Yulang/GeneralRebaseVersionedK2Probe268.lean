import Yulang.GeneralRebaseOriginCycles268
import Yulang.GeneralRebaseInspectionProbe268

namespace Yulang.GeneralRebaseVersionedK2Probe268
open GeneralDeclarations (Registry Declaration DeclarationChecked)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedCycles232 (Cyclic RootCycle CandidateCycle RawCandidateK2)
open GeneralNominalCenters (Plan)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalCandidates (Context Metadata)
open GeneralNominalRecursiveCandidates (arguments report)
open GeneralNominalVersionedCandidates231 (inputs Prepared)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebasePartialBool268 (Answer Reflect either both neg)
open GeneralRebasePartialFinite268 (any any_sound transfer)
open GeneralRebaseOccurrenceEq267 (same same_exact)
open GeneralRebaseRawK2Probe268 (bool_reflect)
open GeneralRebaseInspectionChecks268 (Head BoundList check check_sound)

def indexed (f : Fin n → Answer) : Answer := any f (List.finRange n)

theorem indexed_sound (P : Fin n → Prop) (f : Fin n → Answer) (now : ∀ i, Reflect (P i) (f i)) :
 Reflect (∃ i, P i) (indexed f) :=
 transfer (by simp : (∃ i ∈ List.finRange n, P i) ↔ ∃ i, P i)
   (any_sound P f _ (fun i _ => now i))

def rootOrigin (state : State roles) (focus : Occurrence roles) (cyclic : Origin → Answer) : Answer :=
 either (indexed (fun i => cyclic (.source (focus.demand.arguments i).1)))
   (any (fun site => both (some (same site.occurrence focus))
     (indexed (fun i => cyclic (.source (site.center i))))) state.core.sites)

theorem rootOrigin_sound (state : State roles) (focus : Occurrence roles) (cyclic : Origin → Answer)
 (cert : ∀ o, Reflect (Cyclic state o) (cyclic o)) :
 Reflect (RootCycle state focus) (rootOrigin state focus cyclic) :=
 GeneralRebasePartialBool268.either_sound (indexed_sound _ _ (fun _ => cert _))
   (any_sound _ _ _ (fun _ _ => GeneralRebasePartialBool268.both_sound (bool_reflect _ _ (same_exact ..))
     (indexed_sound _ _ (fun _ => cert _))))

def root (_registry : Registry) (state : State roles) (focus : Occurrence roles)
 (p : GeneralRebaseRawK2Probe268.Probes state.core.erased.current.context.state)
 (cyclic : Origin → Answer) : Answer :=
 either (GeneralRebaseRawK2Probe268.root _ p (inputs focus).demand) (rootOrigin state focus cyclic)

theorem root_sound (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (p : GeneralRebaseRawK2Probe268.Probes state.core.erased.current.context.state)
 (known : GeneralRebaseRawK2Probe268.Sound _ p) (cyclic : Origin → Answer)
 (cert : ∀ o, Reflect (Cyclic state o) (cyclic o)) :
 Reflect ((Boundary roles).RootK2 registry state focus) (root registry state focus p cyclic) :=
 GeneralRebasePartialBool268.either_sound (GeneralRebaseRawK2Probe268.root_sound _ p known _)
   (rootOrigin_sound state focus cyclic cert)

def framed (registry : Registry) (state : State roles) (focus : Occurrence roles) (plan : Plan roles) : Prop :=
 GeneralNominalVersionedEvidence231.Frame (Encoded registry) state.core focus plan.packet.declaration.id plan

def candidateOrigin (plans : List (Plan roles)) (frame : Plan roles → Answer) (cyclic : Origin → Answer) : Answer :=
 any (fun plan => both (frame plan)
   (any (fun entry => cyclic entry.1) (GeneralNominalCenteredSteps.inspection plan).tests)) plans

theorem candidateOrigin_sound (registry : Registry) (state : State roles) (focus : Occurrence roles)
 (plans : List (Plan roles)) (frame : Plan roles → Answer) (cyclic : Origin → Answer)
 (frames : ∀ plan ∈ plans, Reflect (framed registry state focus plan) (frame plan))
 (support : ∀ plan, framed registry state focus plan → plan ∈ plans)
 (cert : ∀ o, Reflect (Cyclic state o) (cyclic o)) :
 Reflect (CandidateCycle (Encoded registry) state focus) (candidateOrigin plans frame cyclic) := by
 apply transfer (p := ∃ plan ∈ plans, framed registry state focus plan ∧
   ∃ entry ∈ (GeneralNominalCenteredSteps.inspection plan).tests, Cyclic state entry.1)
 · constructor
   · rintro ⟨plan,_,formation,hits⟩
     exact ⟨plan,formation,hits⟩
   · rintro ⟨plan,formation,hits⟩
     exact ⟨plan,support plan formation,formation,hits⟩
 · exact any_sound _ _ _ (fun plan listed => GeneralRebasePartialBool268.both_sound (frames plan listed)
     (any_sound _ _ _ (fun entry _ => cert entry.1)))

end Yulang.GeneralRebaseVersionedK2Probe268
