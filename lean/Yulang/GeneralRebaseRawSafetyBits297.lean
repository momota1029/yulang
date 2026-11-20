import Yulang.GeneralRebaseRawObserver297
import Yulang.GeneralRebaseDiagnosticData268

namespace Yulang.GeneralRebaseRawSafetyBits297
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseSourceSurvivor267 (Encoded)
open GeneralRebaseRawInstallScan297 (Known)
open GeneralRebaseRawObserver297 (ExactSafety)
open GeneralRebasePartialBool268 (Answer Reflect both neg)

structure Bits where
  pending : Answer
  rootK2 : Answer
  candidateK2 : Answer
  inspection : Answer
 deriving DecidableEq, Repr

def fromDiagnostic (x : GeneralRebaseDiagnosticData268.Inputs Demand) : Bits :=
  ⟨x.rootPending,x.rootK2,x.candidateK2,x.inspection⟩

def run (b : Bits) : Answer :=
  both (neg b.pending) (both (neg b.rootK2) (both (neg b.candidateK2) (neg b.inspection)))

structure Certified (r : Registry) (s : State roles) (f : Occurrence roles) (b : Bits) : Prop where
 pending : Reflect ((GeneralNominalVersionedDiagnostic232.boundary roles).RootPending (Encoded r) s f) b.pending
 rootK2 : Reflect ((GeneralNominalVersionedDiagnostic232.boundary roles).RootK2 (Encoded r) s f) b.rootK2
 candidateK2 : Reflect ((GeneralNominalVersionedDiagnostic232.boundary roles).CandidateK2 (Encoded r) s f) b.candidateK2
 inspection : Reflect ((GeneralNominalVersionedDiagnostic232.boundary roles).InspectionPending (Encoded r) s f) b.inspection

theorem reflect {r : Registry} {s : State roles} {f : Occurrence roles} {b : Bits}
    (cert : Certified r s f b) : Reflect (Known r s f) (run b) := by
  exact GeneralRebasePartialBool268.both_sound (GeneralRebasePartialBool268.neg_sound cert.pending)
    (GeneralRebasePartialBool268.both_sound (GeneralRebasePartialBool268.neg_sound cert.rootK2)
      (GeneralRebasePartialBool268.both_sound (GeneralRebasePartialBool268.neg_sound cert.candidateK2)
        (GeneralRebasePartialBool268.neg_sound cert.inspection)))

theorem all_false : run ⟨some false,some false,some false,some false⟩ = some true := rfl
theorem unknown_not_negative : run ⟨some false,some false,none,some false⟩ = none := rfl
theorem known_violation : run ⟨some false,some true,none,none⟩ = some false := rfl

def allow (bits : Occurrence roles → Bits) (focus : Occurrence roles) : Bool :=
  run (bits focus) == some true

theorem allow_exact (r : Registry) (s : State roles) (root : Occurrence roles)
    (bits : Occurrence roles → Bits)
    (cert : ∀ f, GeneralNominalSaturationState.Generated s.core.erased.current root f → Certified r s f (bits f))
    (resolved : ∀ f, GeneralNominalSaturationState.Generated s.core.erased.current root f → run (bits f) ≠ none) :
    ExactSafety r s root (allow bits) := by
  intro f generated
  unfold allow
  rw [beq_iff_eq]
  exact GeneralRebasePartialBool268.true_iff (reflect (cert f generated)) (resolved f generated)

theorem allow_positive (r : Registry) (s : State roles) (f : Occurrence roles)
    (bits : Occurrence roles → Bits) (cert : Certified r s f (bits f)) :
    allow bits f = true → Known r s f := by
  intro succeeds
  have recorded : run (bits f) = some true := beq_iff_eq.mp succeeds
  have good := reflect cert
  rwa [recorded] at good

end Yulang.GeneralRebaseRawSafetyBits297
