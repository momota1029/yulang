import Yulang.GeneralDictionaryDefaultEvidence204
import Yulang.GeneralDictionaryMatGuardWitness199

/-! A retained limitation, not a refutation of the selected-stable node theorem.
The source fixture has a nonstable parent and an unsolved child. -/
namespace Yulang.GeneralDictionaryDefaultPartialBoundary204
open GeneralNominalCenteredHeadWFJoinSource hiding start reachable inhabited initial_source
open GeneralDictionaryMatGuardObstruction199 (start)
open GeneralDictionaryDefaultEvidence204
open GeneralNominalCommonBridge (Assignment)

theorem no_instance (assignment : Assignment) (key : Nat) (children) :
    ¬ Instance registry start.core assignment root key children := by
  rintro ⟨candidate,source⟩
  have explicit : GeneralNominalMaterialization.RootDefined candidate.packet.declaration root := by
    intro output member
    cases member
  exact GeneralDictionaryMatGuardObstruction199.no_instance assignment key children
    (certificate_legacy source explicit)

/-- Keeping the old generated-request guard means a total packet alone still
cannot supply arbitrary source evidence. Defaults do not repair emitted joins. -/
theorem no_total_instance_conversion : ¬ (∀ assignment : Assignment,
    GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment →
      Instance registry start.core assignment root 37 children) := by
  intro convert
  obtain ⟨assignment,holds⟩ := GeneralDictionaryMatGuardWitness199.packet_inhabited
  exact no_instance assignment 37 children (convert assignment holds)

end Yulang.GeneralDictionaryDefaultPartialBoundary204
