import Yulang.GeneralDictionaryMixedGround218FinalState235
import Yulang.GeneralDictionaryMixedGround218PointLeaf235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218FinalFresh235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Stability (Owned owned_not_child)
open GeneralDictionaryMixedGround218FinalState235
open GeneralDictionaryMixedGround218PointPacket235 (packet)
open GeneralDictionaryMixedGround218PointInstall235 (installed)

theorem new_atoms : GeneralNominalVersionedInstallation231.atoms packet =
    [.tyLe (.var 4) (.var 4),.tyLe (.var 5) (.var 5),
     .tyLe (.var 6) (.var 6),.tyLe (.var 6) (.var 6),
     .tyLe (.var 4) (.var 4),.tyLe (.var 5) (.var 5)] := by
  unfold GeneralNominalVersionedInstallation231.atoms
  rw [GeneralDictionaryMixedGround218PointPacket235.bindings_exact]
  unfold GeneralNominalPacketSupport.report
  rw [GeneralDictionaryGroundCopy218SaturatedParent.report_exact]
  rfl

theorem installed_owned (member : identity ∈ GeneralNominalState.sources installed.core.erased.current.context.state) : Owned identity := by
  change identity ∈ GeneralNominalState.sources
    (GeneralDictionaryOrdinaryTransport.extendState packet.context.state
      (GeneralNominalVersionedInstallation231.reserved packet)
      (GeneralNominalVersionedInstallation231.atoms packet)
      (GeneralNominalVersionedInstallation231.allocated packet)) at member
  have split : identity ∈ GeneralNominalState.sources packet.context.state ∨
      identity ∈ GeneralNominalVersionedInstallation231.reserved packet ∨
      identity ∈ (GeneralNominalVersionedInstallation231.atoms packet).flatMap GeneralNominalState.atomSources := by
    simp only [GeneralNominalState.sources,GeneralDictionaryOrdinaryTransport.extendState,
      List.flatMap_append,List.mem_append,or_assoc] at member ⊢
    rcases member with a | b | c | d | e | f
    · exact Or.inl a
    · exact Or.inr (Or.inl b)
    · exact Or.inr (Or.inr (Or.inl c))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl d))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr f))))

  rcases split with old | reserved | atoms
  · exact GeneralDictionaryMixedGround218Fresh235.source_owned old
  · obtain ⟨key,member,equal⟩ := List.mem_map.mp reserved
    exact Or.inr ⟨key,GeneralDictionaryMixedGround218Fresh235.key_invocation member,equal⟩
  · rw [new_atoms] at atoms
    change identity ∈ [4,4,5,5,6,6,6,6,4,4,5,5] at atoms
    simp only [List.mem_cons,List.not_mem_nil,or_false] at atoms
    exact Or.inl (by omega)

theorem source_owned (member : identity ∈ GeneralNominalState.sources finalState.core.erased.current.context.state) : Owned identity :=
  installed_owned ((GeneralNominalVersionedMixedEqualityClosure235.trace_sources equality_path).mp member)

theorem missing : ∀ identity ∈ GeneralNominalState.sources finalState.core.erased.current.context.state,
    identity ≠ GeneralDictionaryMixedGround218PointLeaf235.lo ∧ identity ≠ GeneralDictionaryMixedGround218PointLeaf235.hi := by
  intro identity member
  exact ⟨owned_not_child (source_owned member) _ rfl,owned_not_child (source_owned member) _ rfl⟩

theorem fresh (bindings) : GeneralNominalVersionedAllocation231.Fresh finalState.core.erased.current.context.state
    registry GeneralDictionaryMixedGround218PointLeaf235.childId bindings := by
  intro key member collision
  have seed : finalState.core.erased.current.context.state.seed = 7 := by rw [final_context]
  rw [seed] at collision
  exact False.elim (owned_not_child (source_owned collision) key
    (GeneralDictionaryMixedGround218Fresh235.key_invocation member) rfl)

theorem prepared : GeneralNominalVersionedCandidates231.Prepared registry finalState.core.erased.current.context
    GeneralDictionaryMixedGround218PointLeaf235.oldChild GeneralDictionaryMixedGround218PointLeaf235.leafDecl := by
  have raw := final_model.1.1
  have absent := missing
  have owned := fresh [(0,2,3),(0,2,3)]
  rw [final_context] at raw absent owned ⊢
  exact GeneralDictionaryMixedGround218PointLeaf235.prepared allocated reserved ordinary _ raw
    GeneralDictionaryGroundCopy218Install.low_high absent owned

theorem unique : GeneralNominalVersionedCandidates231.Unique registry finalState.core.erased.current.context
    GeneralDictionaryMixedGround218PointLeaf235.oldChild 1 [] := by
  have raw := final_model.1.1
  have absent := missing
  have owned := fresh [(0,2,3),(0,2,3)]
  rw [final_context] at raw absent owned ⊢
  exact GeneralDictionaryMixedGround218PointLeaf235.unique allocated reserved ordinary _ raw
    GeneralDictionaryGroundCopy218Install.low_high absent owned
end Yulang.GeneralDictionaryMixedGround218FinalFresh235
