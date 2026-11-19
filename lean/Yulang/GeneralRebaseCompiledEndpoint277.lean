import Yulang.GeneralRebaseCompiledEvidence277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9300000
namespace Yulang.GeneralRebaseCompiledEndpoint277
open GeneralNominalExamples (registry state model displayRoot displayChild intDisplay listDescriptor)
open GeneralDeclarationExamples (roles display wrap)
open GeneralNominalNonleafPlan193 (centerSite)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledDisplay277 (compiled after)
open GeneralRebaseCompiledInstall277 (edges_eq)
open GeneralRebaseCompiledChild277 (context)
open GeneralRebaseCompiledEvidence277 (center_sites raw_sites)
open GeneralRebaseDisplaySafety276 (after_model raw_acyclic semantic)
open GeneralNominalVersionedCandidates231 (Prepared Failed)
open GeneralNominalVersionedJournal232
open GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalState (Known)

theorem known_zero : Known context.state 0 := ⟨(0 : Fin 2),rfl,Or.inr ⟨listDescriptor,rfl⟩⟩
theorem known_one : Known context.state 1 := ⟨(1 : Fin 2),rfl,Or.inl (by intro never; cases never)⟩

theorem any_parent_fresh (bindings : GeneralNominalAllocation.Bindings) :
 GeneralNominalVersionedAllocation231.Fresh context.state compiled displayRoot.identity bindings := by
 intro key present collision
 rcases GeneralRebaseCompiledChildFresh277.old_support _ collision with small|reserved
 · have high : 1 < GeneralNominalIdentities.source context.state.seed key :=
   GeneralNominalIdentities.source_above_seed _ _
   omega
 · obtain ⟨old,member,equal⟩ := List.mem_map.mp reserved
   have eq := (GeneralNominalIdentities.source_identity context.state.seed old key).mp equal
   subst old
   exact List.mem_append_right _ member

theorem bad_parent_report :
 GeneralNominalRecursiveCandidates.report context intDisplay [((0 : Fin 2),(0 : Fin 2))] =
 { inspected := [((0 : Fin 2),(0 : Fin 2))],
   checked := [((0 : Fin 2),(0 : Fin 2)),((0 : Fin 2),(0 : Fin 2))],
   conflicts := [((0 : Fin 2),(0 : Fin 2))] } := by
 unfold GeneralNominalRecursiveCandidates.report
 rw [GeneralRebaseCompiledChild277.query]
 have nominal : context.state.nominals (0 : Fin 2) = some listDescriptor := rfl
 simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
   GeneralNominalRecursiveInspection.Report.visit,GeneralNominalRecursiveInspection.Report.append,nominal]

theorem bad_child_report :
 GeneralNominalRecursiveCandidates.report context display [((1 : Fin 2),(1 : Fin 2))] =
 { inspected := [((1 : Fin 2),(1 : Fin 2))],
   checked := [((1 : Fin 2),(1 : Fin 2)),((1 : Fin 2),(1 : Fin 2))],
   conflicts := [((1 : Fin 2),(1 : Fin 2))] } := by
 unfold GeneralNominalRecursiveCandidates.report
 have q : GeneralNominalInspection.queries context.state context.interpretation display =
   [.nominal 0 [.variables [0]]] := GeneralNominalNonleafPlan193.query
 rw [q]
 have no : context.state.nominals (1 : Fin 2) = none := rfl
 have scalar : context.state.view.heads (1 : Fin 2) = .scalar .int := rfl
 simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
   GeneralNominalRecursiveInspection.Report.visit,GeneralNominalRecursiveInspection.Report.append,no,scalar]

theorem bad_parent : Failed compiled context displayRoot intDisplay := by
 refine ⟨GeneralNominalNonleafLocal193.prepared.1,[((0 : Fin 2),(0 : Fin 2))],rfl,any_parent_fresh _,?_,?_,Or.inl ?_⟩
 all_goals rw [bad_parent_report]
 all_goals decide +kernel

theorem bad_child : Failed compiled context displayChild display := by
 refine ⟨GeneralNominalNonleafLocal193.prepared.1,[((1 : Fin 2),(1 : Fin 2))],rfl,?_,?_,?_,Or.inl ?_⟩
 · rw [bad_child_report]
   change GeneralNominalVersionedAllocation231.Fresh context.state compiled displayChild.identity []
   have found : GeneralRebaseCompiledChild277.packet.bindings = [] :=
     GeneralRebaseCompiledChild277.bindings_empty
   rw [← found]
   exact GeneralRebaseCompiledChildFresh277.child_fresh
 all_goals rw [bad_child_report]
 all_goals decide +kernel

theorem wrong_parent_prepared : ¬ Prepared compiled context displayRoot intDisplay := by
 rintro ⟨_,_,bounds,loc,_,done,_⟩
 have eq : bounds = [((0 : Fin 2),(0 : Fin 2))] := Option.some.inj loc.symm
 subst bounds
 rw [bad_parent_report] at done
 cases done.2.1

theorem wrong_child_prepared : ¬ Prepared compiled context displayChild display := by
 rintro ⟨_,_,bounds,loc,_,done,_⟩
 have eq : bounds = [((1 : Fin 2),(1 : Fin 2))] := Option.some.inj loc.symm
 subst bounds
 rw [bad_child_report] at done
 cases done.2.1

theorem root_distinct : displayRoot ≠ displayChild :=
 fun equal => GeneralRebaseDisplayChildFresh276.invocation_distinct (congrArg Occurrence.identity equal)

theorem centers_for {focus : Occurrence roles} {one two : Site roles}
 (a : one ∈ after.core.sites) (atA : one.occurrence = focus)
 (b : two ∈ after.core.sites) (atB : two.occurrence = focus) : one = two :=
 GeneralRebaseDisplayEndpoint276.centers_for
   (GeneralRebaseCompiledInstall277.center_sites_eq ▸ a) atA
   (GeneralRebaseCompiledInstall277.center_sites_eq ▸ b) atB

theorem raw_for {focus : Occurrence roles} {one two : GeneralNominalDemandMerging.Site roles}
 (a : one ∈ after.core.erased.current.sites) (atA : one.occurrence = focus)
 (b : two ∈ after.core.erased.current.sites) (atB : two.occurrence = focus) : one = two :=
 GeneralRebaseDisplayEndpoint276.raw_for
   (GeneralRebaseCompiledInstall277.raw_sites_eq ▸ a) atA
   (GeneralRebaseCompiledInstall277.raw_sites_eq ▸ b) atB

theorem generates_only {focus : Occurrence roles}
 (given : GeneralNominalSaturationState.Generated after.core.erased.current displayRoot focus) :
 focus = displayRoot ∨ focus = displayChild := by
 induction given with
 | root => exact Or.inl rfl
 | child _ member _ =>
   rw [edges_eq,GeneralRebaseDisplayFrame276.actual_edges] at member
   exact Or.inr (congrArg Prod.snd (List.mem_singleton.mp member))
 | alias _ _ there _ _ =>
   rw [raw_sites] at there
   simp only [List.mem_cons,List.not_mem_nil,or_false] at there
   rcases there with rfl|rfl
   · exact Or.inl rfl
   · exact Or.inr rfl

end Yulang.GeneralRebaseCompiledEndpoint277
