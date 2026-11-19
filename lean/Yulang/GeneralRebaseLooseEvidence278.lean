import Yulang.GeneralRebaseTerminalEvidence278
import Yulang.GeneralRebaseLoosePrivate278

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseLooseEvidence278
open GeneralDictionaryLooseLoopSource240 (roles registry root sourceRegistry declaration snapshot model)
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralDictionaryLooseIterationBook240 (plan packet)
open GeneralDictionaryLooseIterationInstall240 (chosen installable frame_plan classes)
open GeneralDictionaryLooseIterationFrame240 (children_empty requests_empty)
open GeneralRebaseLooseMicro278 (installed)
open GeneralRebaseLoosePrivate278 (installed_exact)
open GeneralRebaseTerminalEvidence278 (effect_leaf leaf_shape)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload payload_iff_erased)
open GeneralDictionaryInitialFill258 (complete)

theorem enter_leaf (n : Nat) (m : Assignment) (valid : Holds (plan n) m) :
    Evidence registry (state n).core m root (.node 0 []) :=
  effect_leaf (chosen (stages n).shape) m valid (requests_empty (stages n).shape) (children_empty n)

theorem evidence_holds (n : Nat) (m : Assignment) (data : Payload)
    (given : Evidence registry (state n).core m root data) : Holds (plan n) m := by
  have shown := (payload_iff_erased _ _ _).mpr given
  cases shown with
  | node rule _ =>
    obtain ⟨p,cert⟩ := rule
    have same := frame_plan (stages n).shape cert.frame
    subst p
    exact cert.packet

theorem enter_exact (n : Nat) (m : Assignment) (data : Payload) :
    Evidence registry (state n).core m root data ↔
      data = .node 0 [] ∧ Holds (plan n) m := by
  constructor
  · intro existed
    exact ⟨leaf_shape (d := declaration) rfl rfl existed,evidence_holds n m data existed⟩
  · rintro ⟨rfl,held⟩
    exact enter_leaf n m held

theorem installed_leaf (n : Nat) (m : Assignment) (valid : Models (installed n) m) :
    Evidence registry (installed n).core m root (.node 0 []) :=
  GeneralNominalVersionedInstalledEvidence233.evidence
    (effect := chosen (stages n).shape) rfl (children_empty n) valid

theorem installed_shape (n : Nat) (m : Assignment) (valid : Models (installed n) m) (data : Payload) :
    Evidence registry (installed n).core m root data ↔ data = .node 0 [] := by
  constructor
  · exact leaf_shape (d := declaration) rfl rfl
  · rintro rfl
    exact installed_leaf n m valid

theorem actual_adapter_leaf (n : Nat) (m : Assignment) (valid : Models (installed n) m) :
    (GeneralNominalPointSourceBoundary240.boundary roles).Evidence sourceRegistry
      (installed n) m root (.node 0 []) := installed_leaf n m valid

theorem bad_before_no_payload (n : Nat) (data : Payload) :
    ¬ Evidence registry (state n).core (GeneralDictionaryLooseFamilyNovel240.bad n) root data :=
  fun given => GeneralRebaseLoosePrivate278.bad_not_packet n (evidence_holds n _ data given)

theorem same_witness_leaves (boundaryData : Assignment) (source : GeneralNominalState.Models snapshot boundaryData)
    (n : Nat) :
    Evidence registry (state n).core (complete boundaryData) root (.node 0 []) ∧
    Evidence registry (installed n).core (complete boundaryData) root (.node 0 []) ∧
    Evidence registry (state (n+1)).core (complete boundaryData) root (.node 0 []) := by
  have first := (GeneralDictionaryRebaseCertificate259.certificate n boundaryData source).packet
  have next := (GeneralDictionaryRebaseCertificate259.certificate (n+1) boundaryData source).packet
  exact ⟨enter_leaf n _ first,installed_leaf n _ (GeneralRebaseLooseMicro278.complete_all ⟨n,.installed⟩ _ source),
    enter_leaf (n+1) _ next⟩

end Yulang.GeneralRebaseLooseEvidence278
