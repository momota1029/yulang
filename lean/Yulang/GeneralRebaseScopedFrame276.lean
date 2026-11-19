import Yulang.GeneralRebaseDisplaySafety276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 8400000
namespace Yulang.GeneralRebaseScopedFrame276
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedEvidence231 (Frame)

theorem frame_input_occurrence {p : Plan roles} (given : Frame registry state root key p) :
 p.input.occurrence = root := by
 exact p.input_exact.trans given.occurrence_eq

theorem same_frame {p q : Plan roles}
 (one : Frame registry state root key p) (two : Frame registry state root other q)
 (decl : p.packet.declaration = q.packet.declaration)
 (raw : p.packet.site = q.packet.site) (center : p.input = q.input) : p = q := by
 rcases p with ⟨⟨reg₁,c₁,s₁,d₁,check₁,b₁⟩,i₁,center₁⟩
 rcases q with ⟨⟨reg₂,c₂,s₂,d₂,check₂,b₂⟩,i₂,center₂⟩
 have regEq : reg₂ = reg₁ := two.registry_eq.trans one.registry_eq.symm
 have ctxEq : c₂ = c₁ := two.context_eq.trans one.context_eq.symm
 change d₁ = d₂ at decl
 change s₁ = s₂ at raw
 change i₁ = i₂ at center
 subst reg₂; subst c₂; subst d₂; subst s₂; subst i₂
 have bound : b₂ = b₁ := Option.some.inj (two.located.symm.trans one.located)
 subst b₂
 rfl

theorem declaration_for_focus {p : Plan GeneralDeclarationExamples.roles}
 (given : Frame GeneralNominalExamples.registry state GeneralNominalExamples.displayRoot key p)
 (wrong : ¬ GeneralNominalVersionedCandidates231.Prepared GeneralNominalExamples.registry
   state.erased.current.context GeneralNominalExamples.displayRoot GeneralNominalExamples.intDisplay) :
 p.packet.declaration = GeneralDeclarationExamples.display := by
 have seen := given.visible
 simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
 rcases seen with int|right|wrap
 · exact False.elim (wrong (int ▸ given.prepared))
 · exact right
 · have bad := given.role_eq
   rw [wrap] at bad
   cases bad

end Yulang.GeneralRebaseScopedFrame276
