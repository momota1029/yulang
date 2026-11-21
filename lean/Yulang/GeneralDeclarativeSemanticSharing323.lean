import Yulang.GeneralDeclarativeRigidOccurrences323
import Yulang.GeneralDeclarativeTermCapture322
import Yulang.GeneralDeclarativeMerge320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSemanticSharing323
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeRepeatedActual323 (eqAt BindsAt OccursAt)
open GeneralDeclarativeRigidOccurrences323 (exact_occurrences)
open GeneralDeclarativeRigidSource323 (Ordered compiled_results)
open GeneralDeclarativeTermCapture322 (first occurs_if repr_found)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMaterialization (Mode)

def SameBinder (s : State) (seen : List Occurrence) : Prop :=
  ∀ one ∈ seen, ∀ two ∈ seen, one.binder = two.binder →
    ∀ m, Models s m → eqAt m one.term two.term

def SharedAt (s : State) (seen : List Occurrence) (capture : Nat → Capture) : Prop :=
  ∀ m, Models s m → BindsAt m capture seen

/-- A center chosen for each binder at its first actual occurrence.
The map is given by source names, not allowed to vary by assignment. -/
def FirstNames (s : State) (seen : List Occurrence) (before : Nat → Capture) : Prop :=
  ∀ binder o, first seen binder = some o →
    Entails s ⟨(before binder).center,o.term⟩

theorem necessary {s : State} {seen : List Occurrence}
    (mode : ∀ o ∈ seen, o.mode = .actual) (selected : SharedAt s seen capture) :
    SameBinder s seen := by
  intro one ha two hb id m valid
  have a := selected m valid one ha
  have b := selected m valid two hb
  simp only [OccursAt, mode one ha,mode two hb,GeneralDeclarativeHead320.byMode,id] at a b
  exact eqv_trans a (eqv_symm b)

theorem sufficient {s : State} {seen : List Occurrence}
    (mode : ∀ o ∈ seen, o.mode = .actual) (same : SameBinder s seen)
    (anchored : FirstNames s seen capture) :
    SharedAt s seen capture := by
  intro m valid o there
  obtain ⟨chosen,found⟩ := occurs_if there (mode o there)
  have rep := repr_found found
  have link := same o there chosen rep.1 rep.2.1.symm m valid
  have anchor := anchored o.binder chosen found m valid
  rw [OccursAt,mode o there,GeneralDeclarativeHead320.byMode]
  exact
    eqv_trans link (eqv_symm anchor)

theorem exact_shared {s : State} (view : Ordered s c interp args pats seen)
    (anchored : FirstNames s seen capture) :
    SharedAt s seen capture ↔ SameBinder s seen :=
  ⟨necessary (exact_occurrences view).2,fun shares => sufficient (exact_occurrences view).2 shares anchored⟩

/-- Mutual ordinary bounds are one independent producer of the actual
name equalities. Interval overlap is not used as a substitute. -/
theorem by_bounds {s : State} {seen : List Occurrence}
    (names : ∀ o ∈ seen, ∃ n, o.term = .variable n ∧
      GeneralDeclarativeBounds319.Bound s.normal n (capture o.binder).center ∧
      GeneralDeclarativeBounds319.Bound s.normal (capture o.binder).center n)
    (mode : ∀ o ∈ seen, o.mode = .actual) :
    SharedAt s seen capture := by
  intro m valid o seen
  obtain ⟨n,identified,both⟩ := names o seen
  simp only [OccursAt,mode o seen,identified,GeneralDeclarativeHead320.byMode]
  exact ⟨GeneralDeclarativeBounds319.bound_sound m valid.1 both.1,
    GeneralDeclarativeBounds319.bound_sound m valid.1 both.2⟩

end Yulang.GeneralDeclarativeSemanticSharing323
