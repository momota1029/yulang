import Yulang.GeneralDictionaryMixedGround218Leaf235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218Fresh235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryMixedGround218Leaf235
open GeneralDictionaryGroundCopy218Stability (Owned owned_not_child)

theorem declaration_invocation {declaration : GeneralDeclarations.Declaration}
    (member : key ∈ GeneralNominalVersionedAllocation231.declarationKeys invocation declaration bindings) :
    key.1 = invocation := by
  simp only [GeneralNominalVersionedAllocation231.declarationKeys,List.mem_append,List.mem_flatMap,List.mem_map,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (⟨name,_,rfl | rfl⟩ | ⟨name,_,rfl⟩) |
    ⟨clause,_,(rfl | ⟨index,_,rfl | rfl⟩) | ⟨equation,_,rfl⟩⟩
  all_goals rfl

theorem key_invocation (member : key ∈ GeneralNominalVersionedAllocation231.keys value invocation bindings) : key.1 = invocation := by
  obtain ⟨declaration,_,member⟩ := List.mem_flatMap.mp member
  exact declaration_invocation member

theorem ordinary_exact : ctx.state.ordinary =
    [.tyLe (.var 2) (.var 3),.tyLe (.var 2) (.var 3),
     .tyLe (.var 6) (.var 6),.tyLe (.var 6) (.var 6),
     .tyLe (.var 2) (.var 3),.tyLe (.var 2) (.var 3)] := by
  change GeneralNominalVersionedInstallation231.atoms parentPacket = _
  unfold GeneralNominalVersionedInstallation231.atoms
  rw [GeneralDictionaryGroundCopy218Install.bindings_exact]
  change (GeneralNominalAllocation.cross [(0,2,3),(1,2,3)] ++
    GeneralNominalVersionedAllocation231.merges snapshot registry 0
      GeneralDictionaryGroundCopy218Install.declaration [(0,2,3),(1,2,3)]) ++ _ = _
  unfold GeneralNominalPacketSupport.report
  rw [GeneralDictionaryGroundCopy218Install.report_exact]
  rfl

theorem source_owned (member : identity ∈ GeneralNominalState.sources ctx.state) : Owned identity := by
  simp only [GeneralNominalState.sources,List.mem_append] at member
  rcases member with ((type | row) | reserved) | ordinary
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp type
    change Fin 8 at slot
    change slot.val = identity at equal
    exact Or.inl (by have bound := slot.isLt; omega)
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp row
    change Fin 8 at slot
    change slot.val = identity at equal
    exact Or.inl (by have bound := slot.isLt; omega)
  · rcases reserved with empty | reserved
    · cases empty
    · obtain ⟨key,member,equal⟩ := List.mem_map.mp reserved
      exact Or.inr ⟨key,key_invocation member,equal⟩
  · change identity ∈ ctx.state.ordinary.flatMap GeneralNominalState.atomSources at ordinary
    rw [ordinary_exact] at ordinary
    change identity ∈ [2,3,2,3,6,6,6,6,2,3,2,3] at ordinary
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ordinary
    exact Or.inl (by omega)

theorem missing : ∀ identity ∈ GeneralNominalState.sources ctx.state, identity ≠ lo ∧ identity ≠ hi := by
  intro identity member
  exact ⟨owned_not_child (source_owned member) _ rfl,owned_not_child (source_owned member) _ rfl⟩

theorem fresh (bindings) : GeneralNominalVersionedAllocation231.Fresh ctx.state registry childId bindings := by
  intro key member collision
  exact False.elim (owned_not_child (source_owned collision) key (key_invocation member) rfl)

theorem context_eq : GeneralDictionaryMixedGround218Install234.installed.core.erased.current.context = ctx := rfl

theorem current_model : GeneralNominalState.Models ctx.state GeneralDictionaryGroundCopy218Install.model :=
  GeneralDictionaryMixedGround218Install234.installed_model.1.1

theorem prepared : GeneralNominalVersionedCandidates231.Prepared registry ctx oldChild leafDecl :=
  GeneralDictionaryMixedGround218Leaf235.prepared _ current_model GeneralDictionaryGroundCopy218Install.low_high missing (fresh _)

theorem unique : GeneralNominalVersionedCandidates231.Unique registry ctx oldChild 1 [] :=
  GeneralDictionaryMixedGround218Leaf235.unique _ current_model GeneralDictionaryGroundCopy218Install.low_high missing (fresh _)
end Yulang.GeneralDictionaryMixedGround218Fresh235
