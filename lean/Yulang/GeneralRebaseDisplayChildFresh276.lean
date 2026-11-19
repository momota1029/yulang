import Yulang.GeneralRebaseDisplayChild276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralRebaseDisplayChildFresh276
open GeneralNominalExamples (registry state displayRoot displayChild)
open GeneralNominalVersionedAllocation231 (Fresh keys reserved declarationKeys)
open GeneralNominalIdentities (Origin source source_identity source_above_seed source_above_invocation)
open GeneralRebaseDisplayChild276 (context packet bindings_empty)
open GeneralNominalState (sources)

theorem keys_root {key : Origin} (member : key ∈ keys reg root bindings) : key.1 = root := by
 obtain ⟨decl,_,present⟩ := List.mem_flatMap.mp member
 unfold declarationKeys at present
 simp only [List.mem_append] at present
 rcases present with (input|output)|clause
 · obtain ⟨name,_,m⟩ := List.mem_flatMap.mp input
   rcases List.mem_cons.mp m with rfl|m
   · rfl
   · cases List.mem_singleton.mp m
     rfl
 · obtain ⟨name,_,rfl⟩ := List.mem_map.mp output
   rfl
 · obtain ⟨c,_,atClause⟩ := List.mem_flatMap.mp clause
   simp only [List.mem_append,List.mem_cons] at atClause
   rcases atClause with (rfl|arguments)|outputs
   · rfl
   · obtain ⟨index,_,present⟩ := List.mem_flatMap.mp arguments
     rcases List.mem_cons.mp present with rfl|h
     · rfl
     · cases List.mem_singleton.mp h
       rfl
   · obtain ⟨e,_,rfl⟩ := List.mem_map.mp outputs
     rfl

noncomputable abbrev parentReserved := GeneralNominalVersionedInstallation231.reserved GeneralNominalNonleafPlan193.packet

theorem old_support : ∀ id ∈ sources context.state, id ≤ 1 ∨ id ∈ parentReserved := by
 intro id member
 change id ∈ List.ofFn (state true).base.source ++ List.ofFn (state true).base.rowSource ++
   ([] ++ parentReserved) ++ ([] ++ GeneralNominalVersionedInstallation231.atoms GeneralNominalNonleafPlan193.packet).flatMap
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
   unfold GeneralNominalVersionedInstallation231.atoms at atoms
   rw [GeneralNominalNonleafPlan193.bindings,GeneralNominalNonleafPlan193.raw_report] at atoms
   have small : ∀ id ∈ ((GeneralNominalAllocation.cross [(0,(1,1))] ++
     GeneralNominalVersionedAllocation231.merges GeneralNominalNonleafPlan193.packet.context.state registry displayRoot.identity
       GeneralNominalNonleafPlan193.declaration [(0,(1,1))]) ++
       GeneralNominalRecursiveInspection.selfChecks (state true)
         (GeneralNominalUnaryCaptureFacts.captured (state true) 0 0 0 (1,1))).flatMap GeneralNominalState.atomSources, id ≤ 1 :=
      by decide +kernel
   exact small _ atoms

theorem invocation_distinct : displayRoot.identity ≠ displayChild.identity := by
 have large : displayRoot.identity < displayChild.identity :=
   source_above_invocation _ (GeneralNominalAllocation.origin 100 1 6 10 0)
 omega

theorem child_fresh : Fresh context.state registry displayChild.identity packet.bindings := by
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

end Yulang.GeneralRebaseDisplayChildFresh276
