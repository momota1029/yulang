import Yulang.GeneralRebaseCandidateK2Source268
import Yulang.GeneralRebaseDiagnosticSource268

namespace Yulang.GeneralRebaseConflictRouting268
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebasePartialBool268 (Reflect Answer both neg either)
open GeneralRebasePartialFinite268 (transfer any any_sound)
open GeneralRebaseDiagnosticData268 (Inputs Valid SurvivorSound k2_sound)
open GeneralRebaseCandidateK2Source268 (focusPlans includes)
open GeneralRebaseVersionedK2Probe268 (framed)
open GeneralNominalVersionedDiagnostic232 (ChosenHead ChosenEffects HeadEquations Feasible AtKey)
open GeneralNominalCenters (Plan)
open GeneralRebaseRawK2Probe268 (bool_reflect)

def uniqueKey (x : Inputs Demand) (key : Nat) : Answer :=
 match x.survivors with
 | .unique w => some (w.1 == key)
 | .none | .ambiguous .. => some false
 | .deferred => none

theorem uniqueKey_sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (w : SurvivorSound b r s d x.survivors) (key : Nat) :
 Reflect (∃ children, B4TargetV8.Unique b r s d key children) (uniqueKey x key) := by
 unfold uniqueKey
 cases view : x.survivors with
 | deferred => trivial
 | none =>
   rw [view] at w
   rintro ⟨children,chosen⟩
   exact w key children chosen.1
 | ambiguous first last =>
   rcases first with ⟨a,one⟩
   rcases last with ⟨z,two⟩
   rw [view] at w
   rintro ⟨_,chosen⟩
   exact w.1 ((chosen.2 a one w.2.1).1.trans (chosen.2 z two w.2.2).1.symm)
 | unique wKey =>
   rcases wKey with ⟨k,kids⟩
   rw [view] at w
   apply bool_reflect
   rw [beq_iff_eq]
   constructor
   · rintro rfl
     exact ⟨kids,w⟩
   · rintro ⟨_,chosen⟩
     exact (chosen.2 k kids w.1).1

def safe (x : Inputs Demand) : Answer :=
 both (neg x.rootPending) (both (neg (GeneralRebaseDiagnosticData268.k2 x)) (neg x.inspection))

theorem safe_sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : Valid b r s d x) : Reflect (B4TargetV8.SafeKnown b r s d) (safe x) := by
 apply transfer (p := ¬ b.RootPending r s d ∧ ¬ (b.RootK2 r s d ∨ b.CandidateK2 r s d) ∧ ¬ b.InspectionPending r s d)
 · constructor
   · rintro ⟨root,block,inspection⟩
     exact ⟨root,(fun h => block (Or.inl h)),(fun h => block (Or.inr h)),inspection⟩
   · rintro ⟨root,raw,candidate,inspection⟩
     exact ⟨root,fun h => h.elim raw candidate,inspection⟩
 · exact GeneralRebasePartialBool268.both_sound (GeneralRebasePartialBool268.neg_sound valid.rootPending)
     (GeneralRebasePartialBool268.both_sound (GeneralRebasePartialBool268.neg_sound (k2_sound b r s d x valid))
       (GeneralRebasePartialBool268.neg_sound valid.inspection))

def atKey (plans : List (Plan roles)) (frame accept : Plan roles → Answer) (key : Nat) : Answer :=
 any (fun plan => both (some (plan.packet.declaration.id == key)) (both (frame plan) (accept plan))) plans

theorem atKey_sound (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus)
 (frame accept : Plan roles → Answer) (P : Plan roles → Prop)
 (frameSound : ∀ p ∈ focusPlans registry state root focus checked,
   Reflect (framed registry state focus p) (frame p))
 (acceptSound : ∀ p ∈ focusPlans registry state root focus checked, Reflect (P p) (accept p))
 (key : Nat) :
 Reflect (∃ p, GeneralNominalVersionedEvidence231.Frame (Encoded registry) state.core focus key p ∧ P p)
   (atKey (focusPlans registry state root focus checked) frame accept key) := by
 apply transfer (p := ∃ p ∈ focusPlans registry state root focus checked,
    p.packet.declaration.id = key ∧ framed registry state focus p ∧ P p)
 · constructor
   · rintro ⟨p,_,exactKey,onFrame,h⟩
     exact ⟨p,exactKey ▸ onFrame,h⟩
   · rintro ⟨p,onFrame,h⟩
     have exactKey := onFrame.key_eq
     have relative : framed registry state focus p := by
       unfold framed
       rwa [exactKey]
     exact ⟨p,includes registry state root focus checked generated p relative,exactKey,relative,h⟩
 · exact any_sound _ _ _ (fun p listed =>
     GeneralRebasePartialBool268.both_sound (bool_reflect _ _ (beq_iff_eq ..))
      (GeneralRebasePartialBool268.both_sound (frameSound p listed) (acceptSound p listed)))

end Yulang.GeneralRebaseConflictRouting268
