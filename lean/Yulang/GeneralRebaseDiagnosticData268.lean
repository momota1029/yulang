import Yulang.GeneralRebasePartialBool268
import Yulang.GeneralRebaseSourceClassification267
import Yulang.B4TargetV8

namespace Yulang.GeneralRebaseDiagnosticData268
open B4Target (Vocabulary)
open CommonRoleOutermostResolver (Frontier)
open GeneralRebasePartialBool268 (Answer Reflect neg either both)
open GeneralRebasePartialClassification267 (Verdict)

structure Inputs (Demand : Type) where
 rootPending : Answer
 rootK2 : Answer
 candidateK2 : Answer
 inspection : Answer
 survivors : Verdict (Nat × List Demand)
 outputConflict : Nat → Answer
 mergedConflict : Answer
 sharingConflict : Answer

def SurvivorSound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand) :
 Verdict (Nat × List v.Demand) → Prop
 | .none => ∀ key kids, ¬ b.Survivor r s d key kids
 | .unique (key,kids) => B4TargetV8.Unique b r s d key kids
 | .ambiguous (a,one) (z,two) => a ≠ z ∧ b.Survivor r s d a one ∧ b.Survivor r s d z two
 | .deferred => True

structure Valid (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) : Prop where
 rootPending : Reflect (b.RootPending r s d) x.rootPending
 rootK2 : Reflect (b.RootK2 r s d) x.rootK2
 candidateK2 : Reflect (b.CandidateK2 r s d) x.candidateK2
 inspection : Reflect (b.InspectionPending r s d) x.inspection
 survivors : SurvivorSound b r s d x.survivors
 outputConflict : ∀ key, Reflect (b.OutputConflict r s d key) (x.outputConflict key)
 mergedConflict : Reflect (b.MergedOutputConflict r s d) x.mergedConflict
 sharingConflict : Reflect (b.SharingConflict r s d) x.sharingConflict

def Ambiguity (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand) : Prop :=
 ∃ a one z two, b.Survivor r s d a one ∧ b.Survivor r s d z two ∧ a ≠ z

def multiple : Verdict (Nat × List Demand) → Answer
 | .ambiguous .. => some true
 | .deferred => none
 | _ => some false

theorem multiple_sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (view : Verdict (Nat × List v.Demand)) (valid : SurvivorSound b r s d view) :
 Reflect (Ambiguity b r s d) (multiple view) := by
 cases view with
 | none =>
   intro ambiguity
   obtain ⟨a,one,_,_,first,_,_⟩ := ambiguity
   exact valid a one first
 | unique item =>
   rcases item with ⟨key,kids⟩
   intro ambiguity
   obtain ⟨a,one,z,two,first,last,different⟩ := ambiguity
   exact different ((valid.2 a one first).1.trans (valid.2 z two last).1.symm)
 | ambiguous first last =>
   rcases first with ⟨a,one⟩
   rcases last with ⟨z,two⟩
   exact ⟨a,one,z,two,valid.2.1,valid.2.2,valid.1⟩
 | deferred => trivial

def k2 (x : Inputs Demand) : Answer := either x.rootK2 x.candidateK2

def priority (x : Inputs Demand) : Answer :=
 both (neg (both (neg x.rootPending) (k2 x))) (multiple x.survivors)

theorem k2_sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : Valid b r s d x) :
 Reflect (b.RootK2 r s d ∨ b.CandidateK2 r s d) (k2 x) :=
 GeneralRebasePartialBool268.either_sound valid.rootK2 valid.candidateK2

theorem priority_sound (b : B4TargetV8.SourceBoundary v) (r : v.Registry) (s : v.State) (d : v.Demand)
 (x : Inputs v.Demand) (valid : Valid b r s d x) :
 Reflect (B4TargetV8.PriorityAmbiguity b r s d) (priority x) :=
 GeneralRebasePartialBool268.both_sound (GeneralRebasePartialBool268.neg_sound
   (GeneralRebasePartialBool268.both_sound (GeneralRebasePartialBool268.neg_sound valid.rootPending)
     (k2_sound b r s d x valid))) (multiple_sound b r s d x.survivors valid.survivors)

end Yulang.GeneralRebaseDiagnosticData268
