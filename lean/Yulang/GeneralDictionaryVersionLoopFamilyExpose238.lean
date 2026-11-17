import Yulang.GeneralDictionaryVersionLoopFamilyInstallation238
import Yulang.GeneralDictionaryVersionLoopFamilyFresh238
set_option backward.isDefEq.respectTransparency false
/-! Uniform support and strict Known-growth guards for exposing the next
lower after the actual private installation. Trusted observation soundness
is not supplied, so no complete mixed Refresh or infinite path is claimed. -/
namespace Yulang.GeneralDictionaryVersionLoopFamilyExpose238
open GeneralDictionaryVersionLoopFamilyBase238 GeneralDictionaryVersionLoopFamilyPacket238
open GeneralDictionaryVersionLoopFamilyFresh238 (next_lower_not_base)
open GeneralDictionaryVersionLoopNames238 (lower)
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))
abbrev replay := GeneralNominalVersionedInstallation231.replayPlan (plan n allocated reserved ordinary)
abbrev exposed : GeneralNominalCandidates.Context :=
 ⟨GeneralDictionaryVersionLoopFamilyRefines238.state n
   (replay n allocated reserved ordinary).packet.context.state.allocated
   (replay n allocated reserved ordinary).packet.context.state.reserved
   (replay n allocated reserved ordinary).packet.context.state.ordinary,
 GeneralDictionaryVersionLoopSource237.interpretation⟩

noncomputable def refines : GeneralNominalRefinements.Refines
 (replay n allocated reserved ordinary).packet.context.state
 (exposed n allocated reserved ordinary).state :=
 GeneralDictionaryVersionLoopFamilyRefines238.refines n _ _ _

theorem lower_supported : lower (n+1) ∈ GeneralNominalState.sources (replay n allocated reserved ordinary).packet.context.state := by
 apply List.mem_append_left
 apply List.mem_append_right
 apply List.mem_append_right
 change lower (n+1) ∈ GeneralNominalVersionedAllocation231.reserved
   (GeneralDictionaryVersionLoopFamilySnapshot238.snapshot n allocated reserved ordinary)
   GeneralDictionaryVersionLoopSource237.registry 0 (packet n allocated reserved ordinary).bindings
 have member := (GeneralNominalVersionedAllocation231.aggregate_reserved
   (registry := GeneralDictionaryVersionLoopSource237.registry)
   (state := GeneralDictionaryVersionLoopFamilySnapshot238.snapshot n allocated reserved ordinary)
   (root := 0) (bindings := (packet n allocated reserved ordinary).bindings)
   (by exact List.mem_singleton_self GeneralDictionaryVersionLoopSource237.declaration)
   (by decide +kernel : 0 ∈ GeneralDictionaryVersionLoopSource237.declaration.inputNames)).1
 rw [bindings_exact] at member
 rw [bindings_exact]
 exact member

theorem lower_unknown : ¬ GeneralNominalState.Known (replay n allocated reserved ordinary).packet.context.state (lower (n+1)) := by
 rintro ⟨slot,same,_⟩
 exact next_lower_not_base n slot same.symm

def last : Fin ((n+1)+4) := ⟨n+4,by omega⟩
theorem last_source : source (n+1) (last n) = lower (n+1) := by
 rw [source_large _ (by change 4 ≤ n+4; omega)]
 change lower ((n+4)-3) = lower (n+1)
 congr 1

theorem lower_known : GeneralNominalState.Known (exposed n allocated reserved ordinary).state (lower (n+1)) := by
 refine ⟨last n,last_source n,Or.inr ⟨GeneralDictionaryVersionLoopFamilyRefines238.looseDescriptor n,?_⟩⟩
 simp only [exposed,GeneralDictionaryVersionLoopFamilyRefines238.state,last,ite_true]

theorem support : ∀ identity ∈ GeneralNominalState.sources (exposed n allocated reserved ordinary).state,
 identity ∈ GeneralNominalState.sources (replay n allocated reserved ordinary).packet.context.state := by
 intro identity member
 simp only [GeneralNominalState.sources,List.mem_append] at member ⊢
 rcases member with ((type | row) | reserved) | ordinary
 · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp type
   by_cases old : slot.val < n+4
   · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨⟨slot.val,old⟩,rfl⟩)))
   · have same : slot = last n := by apply Fin.ext; change slot.val = n+4; have := slot.isLt; omega
     rw [same]
     rw [last_source]
     have found := lower_supported n allocated reserved ordinary
     simpa only [GeneralNominalState.sources,List.mem_append,last_source] using found
 · obtain ⟨slot,rfl⟩ := List.mem_ofFn.mp row
   by_cases old : slot.val < n+4
   · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨⟨slot.val,old⟩,rfl⟩)))
   · have same : slot = last n := by apply Fin.ext; change slot.val = n+4; have := slot.isLt; omega
     rw [same]
     rw [last_source]
     have found := lower_supported n allocated reserved ordinary
     simpa only [GeneralNominalState.sources,List.mem_append,last_source] using found
 · exact Or.inl (Or.inr reserved)
 · exact Or.inr ordinary
end Yulang.GeneralDictionaryVersionLoopFamilyExpose238
