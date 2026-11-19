import Yulang.GeneralRebaseClosedEdgeObstruction279
import Yulang.GeneralDictionaryCompoundStep238

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseClosedEdgeCompound279
open GeneralDictionaryJournalRefinement228Source (roles root context)
open GeneralDictionaryCompoundSource238 (sourceRegistry registry declaration child start checked)
open GeneralDictionaryCompoundFrame238 (before effect installed)
open GeneralDictionaryCompoundPacket238 (plan)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseClosedChildShape279 (ClosedArguments argList)
open GeneralRebaseFullEdgeBasis279 (OnTrace finite_full_edges)
open GeneralRebaseInstallNovelty279 (Edge LostModel FreshChild)
open GeneralDeclarationPatterns (normalize)

theorem initial : (boundary roles).Initial sourceRegistry root before :=
  ⟨start,GeneralDictionaryCompoundSource238.initial,rfl⟩

theorem closed : ClosedArguments registry := by
  intro d visible c mentioned p used name
  cases List.mem_singleton.mp visible
  cases List.mem_singleton.mp mentioned
  cases List.mem_singleton.mp used
  change normalize (.variant 0 (.var 0)) ≠ .var name
  simp only [normalize]
  intro clash
  cases clash

noncomputable def emittedChild : GeneralSourceDictionaries.Occurrence roles :=
  GeneralNominalVersionedFrame231.clauseChild plan.packet child
    (GeneralDictionaryCompoundSource238.declaration_checked.signature.2.2.2 _ (by decide +kernel))

theorem singleton : GeneralNominalVersionedFrame231.children plan.packet = [emittedChild] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  rfl

theorem canonical_ports : List.ofFn emittedChild.demand.arguments =
    argList roles context.state.seed root.identity declaration.id child :=
  GeneralRebaseClosedChildShape279.clause_arguments (p := plan) closed
    (List.mem_singleton_self _) child (List.mem_singleton_self _) _

theorem new_child : FreshChild before plan := by
  have member : emittedChild ∈ GeneralNominalVersionedFrame231.children plan.packet := singleton ▸ List.mem_singleton_self _
  exact ⟨emittedChild,member,fun absent => nomatch absent⟩

theorem full_model_cut : LostModel before effect := by
  refine ⟨GeneralDictionaryOptionalInstall229.model,GeneralDictionaryCompoundStep238.old_model_initial,?_⟩
  intro after
  apply GeneralDictionaryCompoundStep238.no_packet
  exact after.2.1 plan (List.mem_cons_self ..)

theorem nonempty_full_cover : ∃ pool : List (Edge roles), pool ≠ [] ∧
    ∀ edge, edge ∈ pool ↔ OnTrace sourceRegistry root before edge := by
  obtain ⟨pool,covers⟩ := finite_full_edges initial ⟨rfl,checked⟩ closed
  refine ⟨pool,?_,covers⟩
  intro empty
  have edge := (GeneralRebaseInstallNovelty279.fresh_iff_edge before effect).mp new_child
  obtain ⟨w,after,_⟩ := edge
  have seen := (covers w).mpr ⟨installed,.tail .refl GeneralDictionaryCompoundStep238.step,after⟩
  rw [empty] at seen
  cases seen

end Yulang.GeneralRebaseClosedEdgeCompound279
