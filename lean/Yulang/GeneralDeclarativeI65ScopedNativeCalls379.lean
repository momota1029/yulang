import Yulang.GeneralDeclarativeI65ActualCandidateOrder379

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence)
open GeneralDeclarativeWitnessNativePortTransport361 (Port)
open GeneralDeclarativeWitnessNativeAmbiguity361 (inspect Candidate)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)

/-- Call readback of the exact two-candidate C361 Option continuation.
The last candidate has an actual call only with a positive receipt
from the first; a none is not assigned a language verdict. -/
inductive ScopedNativeCalls {negative : Bool} (r : Run negative)
    (d : Demand) (first last : Declaration) : Type where
  | firstOnly : inspect r d first = none → ScopedNativeCalls r d first last
  | both (receipt : Candidate r d first) :
    inspect r d first = some receipt →
    (final : Option (Candidate r d last)) →
    inspect r d last = final →
    ScopedNativeCalls r d first last

def scopedNativeCalls {negative : Bool} (r : Run negative)
    (d : Demand) (first last : Declaration) : ScopedNativeCalls r d first last :=
  match returned : inspect r d first with
  | none => .firstOnly returned
  | some result => .both result returned (inspect r d last) rfl

def ScopedNativeCalls.positions {negative : Bool} {r : Run negative}
    {d : Demand} {first last : Declaration} :
    ScopedNativeCalls r d first last → List Nat
  | .firstOnly _ => [0]
  | .both .. => [0,1]

def ScopedNativeCalls.finished {negative : Bool} {r : Run negative}
    {d : Demand} {first last : Declaration} :
    ScopedNativeCalls r d first last → Bool
  | .firstOnly _ => false
  | .both _ _ second _ => second.isSome

theorem only_first_position_on_missing_result {negative : Bool} {r : Run negative}
    {d : Demand} {a b : Declaration} (miss : inspect r d a = none) :
    (scopedNativeCalls r d a b).positions = [0] := by
  unfold scopedNativeCalls
  split
  · rfl
  · rename_i result checked
    rw [miss] at checked
    cases checked

theorem second_position_requires_positive_first {negative : Bool} {r : Run negative}
    {d : Demand} {a b : Declaration}
    (trace : ScopedNativeCalls r d a b) (visited : 1 ∈ trace.positions) :
    ∃ checked : Candidate r d a, inspect r d a = some checked := by
  cases trace with
  | firstOnly miss =>
    simp [ScopedNativeCalls.positions] at visited
  | both checked returned last actual =>
    exact ⟨checked,returned⟩

theorem scoped_calls_return_same_scanner_result
    {negative : Bool} {r : Run negative} {s : Sequence r} {gate : ReleaseAuthority}
    {w : GeneralDeclarativeWitnessNativeDirectSource361.Wire}
    (port : Port s gate w) {a b : Declaration}
    (listed : GeneralDeclarativeWitnessNativeLeafClassify361.visible s = [a,b])
    (distinct : a.id ≠ b.id)
    (allowed : GeneralDeclarativeWitnessMixedDependency361.exactGraph s = true) :
    (GeneralDeclarativeWitnessNativeAmbiguity361.compare port).isSome =
      (scopedNativeCalls r s.receiver a b).finished := by
  rw [actual_c361_scans_the_second_only_after_first port listed distinct allowed]
  unfold scopedNativeCalls
  split
  · rename_i first
    simp [first,ScopedNativeCalls.finished]
  · rename_i receipt first
    simp [first,ScopedNativeCalls.finished]

def callsAfterActualGate
    {negative : Bool} {r : Run negative} {s : Sequence r} {gate : ReleaseAuthority}
    {w : GeneralDeclarativeWitnessNativeDirectSource361.Wire}
    (port : Port s gate w) {a b : Declaration}
    (listed : GeneralDeclarativeWitnessNativeLeafClassify361.visible s = [a,b])
    (distinct : a.id ≠ b.id)
    (allowed : GeneralDeclarativeWitnessMixedDependency361.exactGraph s = true) :
    {trace : ScopedNativeCalls r s.receiver a b //
      (GeneralDeclarativeWitnessNativeAmbiguity361.compare port).isSome = trace.finished} :=
  ⟨scopedNativeCalls r s.receiver a b,
    scoped_calls_return_same_scanner_result port listed distinct allowed⟩

end Yulang.GeneralDeclarativeI65
