import Yulang.GeneralRebaseDepthGroundModels285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralRebaseDepthPayload285
open GeneralDictionaryOutputDepth252 (plan declaration root registry initial children_empty)
open GeneralDictionaryOutputDepthInstall252 (installed effect)
open GeneralNominalVersionedEvidence231 (Evidence Certificate)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload payload_iff_erased)
open GeneralRebaseDepthGroundModels285 (InitialTypeCheck FinalTypeCheck final_check canonical_check)
open GeneralRebaseDepthPublic285 (inflate project row_preservation)

theorem payload_shape (a : Assignment) (p : Payload)
    (ev : Evidence registry installed.core a root p) : p = .node 0 [] := by
  have rendered := (payload_iff_erased _ _ _).mpr ev
  cases rendered with
  | node rule children =>
    obtain ⟨c,cert⟩ := rule
    have decl : c.packet.declaration = declaration := List.mem_singleton.mp cert.frame.visible
    have key := cert.frame.key_eq
    rw [decl] at key
    have empty : GeneralNominalVersionedFrame231.children c.packet = [] := by
      unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
      simp only [GeneralCanonicalChildOrder.canonicalEmit,decl,
        show GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration by decide +kernel]
      rfl
    rw [cert.children_eq,empty] at children
    cases children
    exact congrArg (fun k => CommonRoleOutermostResolver.Dictionary.node k []) key.symm

theorem evidence_exact (a : Assignment) (held : Models installed a) (p : Payload) :
    Evidence registry installed.core a root p ↔ p = .node 0 [] := by
  constructor
  · exact payload_shape a p
  · rintro rfl
    exact GeneralNominalVersionedInstalledEvidence233.evidence (effect := effect) rfl children_empty held

theorem same_assignment_exact (a : Assignment) (p : Payload) :
    Models installed a ∧ Evidence registry installed.core a root p ↔
      FinalTypeCheck a ∧ p = .node 0 [] := by
  constructor
  · rintro ⟨held,ev⟩
    exact ⟨(final_check a).mp held,payload_shape a p ev⟩
  · rintro ⟨check,equal⟩
    have held := (final_check a).mpr check
    exact ⟨held,(evidence_exact a held p).mpr equal⟩

theorem canonical_exact (a : Assignment) (p : Payload) :
    (let b := inflate (project a) (fun n => (a n).2)
     Models installed b ∧ Evidence registry installed.core b root p) ↔
    InitialTypeCheck a ∧ p = .node 0 [] := by
  let b := inflate (project a) (fun n => (a n).2)
  change Models installed b ∧ Evidence registry installed.core b root p ↔ _
  constructor
  · rintro ⟨held,ev⟩
    exact ⟨(canonical_check a).mp held,payload_shape b p ev⟩
  · rintro ⟨check,equal⟩
    have held : Models installed b := (canonical_check a).mpr check
    exact ⟨held,(evidence_exact b held p).mpr equal⟩

end Yulang.GeneralRebaseDepthPayload285
