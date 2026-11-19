import Yulang.GeneralRebaseCompiledChild277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralRebaseCompiledChildFresh277
open GeneralNominalExamples (registry state displayRoot displayChild)
open GeneralNominalVersionedAllocation231 (Fresh keys reserved declarationKeys)
open GeneralNominalIdentities (Origin source source_identity source_above_seed source_above_invocation)
open GeneralRebaseCompiledChild277 (context packet bindings_empty)
open GeneralRebaseCompiledDisplay277 (compiled parent)
open GeneralRebaseDisplayChildFresh276 (keys_root invocation_distinct)
open GeneralNominalState (sources)

noncomputable abbrev parentReserved := GeneralNominalVersionedInstallation231.reserved parent.packet

theorem old_support : ∀ id ∈ sources context.state, id ≤ 1 ∨ id ∈ parentReserved := by
 intro id member
 change id ∈ List.ofFn (state true).base.source ++ List.ofFn (state true).base.rowSource ++
   ([] ++ parentReserved) ++ ([] ++ GeneralNominalVersionedInstallation231.atoms parent.packet).flatMap
   GeneralNominalState.atomSources at member
 simp only [List.nil_append,List.mem_append] at member
 rcases member with ((types|rows)|reserved)|atoms
 · obtain ⟨i,same⟩ := List.mem_ofFn.mp types
   change i.val = id at same
   have bound := i.isLt
   exact Or.inl (by omega)
 · obtain ⟨i,same⟩ := List.mem_ofFn.mp rows
   change i.val = id at same
   have bound := i.isLt
   exact Or.inl (by omega)
 · exact Or.inr reserved
 · left
   change id ∈ (GeneralNominalVersionedInstallation231.atoms GeneralNominalNonleafPlan193.packet).flatMap GeneralNominalState.atomSources at atoms
   unfold GeneralNominalVersionedInstallation231.atoms at atoms
   rw [GeneralNominalNonleafPlan193.bindings,GeneralNominalNonleafPlan193.raw_report] at atoms
   have small : ∀ id ∈ ((GeneralNominalAllocation.cross [(0,(1,1))] ++
     GeneralNominalVersionedAllocation231.merges parent.packet.context.state registry displayRoot.identity
       GeneralNominalNonleafPlan193.declaration [(0,(1,1))]) ++
       GeneralNominalRecursiveInspection.selfChecks (state true)
         (GeneralNominalUnaryCaptureFacts.captured (state true) 0 0 0 (1,1))).flatMap GeneralNominalState.atomSources, id ≤ 1 :=
      by decide +kernel
   exact small _ atoms

theorem child_fresh : Fresh context.state compiled displayChild.identity packet.bindings := by
 intro key tracked collision
 have root := keys_root tracked
 have support := old_support _ collision
 rcases support with small | reserved
 · have huge : 1 < source context.state.seed key := source_above_seed _ _
   omega
 · obtain ⟨prior,member,same⟩ := List.mem_map.mp reserved
   have rootPrior : prior.1 = displayRoot.identity := keys_root member
   have equal : prior = key := (source_identity context.state.seed _ _).mp same
   exact False.elim (invocation_distinct (rootPrior.symm.trans ((congrArg Prod.fst equal).trans root)))

end Yulang.GeneralRebaseCompiledChildFresh277
