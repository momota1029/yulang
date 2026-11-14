import Yulang.GeneralNominalCenteredTerminalForkSource
import Yulang.GeneralDictionaryCenteredCandidate176

/-! The terminal observation fork is not a counterexample to EvidenceNode:
its only generated demand has no selected declaration. The differing observer
is outside the generated scope, even for the original ground boundary G. -/
namespace Yulang.GeneralDictionaryCenteredTerminalScope177
open GeneralNominalCenteredTerminalForkSource
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDeclarationExamples (roles display)

 theorem root_not_selected (side : Bool) (key : Nat) (children : List (Occurrence roles)) :
    ¬ GeneralNominalCenteredBoundary.Local registry (finish side) root (.selected key children) := by
  intro selected
  cases selected with
  | selected safe unique =>
    obtain ⟨_,declaration,visible,checked,identity,role,rest⟩ := unique.1
    have same : declaration = display := List.mem_singleton.mp visible
    rw [same] at role
    contradiction

 theorem reached_not_selected (side : Bool) (focus : Occurrence roles)
    (reached : focus = root ∨ GeneralNominalSaturationState.Generated
      (finish side).erased.current root focus)
    (key : Nat) (children : List (Occurrence roles)) :
    ¬ GeneralNominalCenteredBoundary.Local registry (finish side) focus (.selected key children) := by
  have same : focus = root := reached.elim id (generated_only_root side focus)
  subst focus
  exact root_not_selected side key children

 theorem observer_not_generated (side : Bool) :
    ¬ GeneralNominalSaturationState.Generated (finish side).erased.current root observer := by
  intro generated
  have same := generated_only_root side observer generated
  have identities := congrArg Occurrence.identity same
  change 100 = 700 at identities
  contradiction

/-- The fork preserves commitment predicates, but that does not assert that
any proposed observer packet is committed. Every non-leaf packet fails its
edge commitment here because both terminal journals have no edges. -/
theorem nonleaf_not_committed (side : Bool)
    (packet : GeneralNominalSaturationState.Packet roles)
    (child : Occurrence roles) (member : child ∈ packet.children) :
    ¬ GeneralNominalFeedbackSteps.Committed (finish side).erased.current packet := by
  intro committed
  have edge := committed.2 child member
  change (packet.site.occurrence,child) ∈ ([] : List (Occurrence roles × Occurrence roles)) at edge
  cases edge

end Yulang.GeneralDictionaryCenteredTerminalScope177
