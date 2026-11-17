import Yulang.GeneralDictionaryMixedGround218Fresh235
import Yulang.GeneralDictionaryMixedGround218Obstruction234
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218LeafFrame235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (childSite)
open GeneralDictionaryMixedGround218Leaf235
open GeneralDictionaryMixedGround218Install234 (installed)
open GeneralNominalCenters

theorem child_eq : childSite.occurrence = oldChild := by
  have arguments := funext GeneralDictionaryGroundCopy218Install.child_arguments
  change (⟨childId,⟨1,childSite.occurrence.demand.arguments,[],_⟩⟩ : GeneralSourceDictionaries.Occurrence roles) = _
  rw [arguments]
  rfl

theorem emitted_eq : GeneralNominalVersionedChildren232.emitted GeneralDictionaryGroundCopy218Install.plan = [childSite] := by
  have occurrences := GeneralNominalVersionedChildren232.emitted_occurrences GeneralDictionaryGroundCopy218Install.plan
  rw [GeneralDictionaryMixedGround218Frame234.children_eq,GeneralDictionaryGroundCopy218Install.children_exact] at occurrences
  obtain ⟨site,listEq,occEq⟩ := List.map_eq_singleton_iff.mp occurrences
  have member : site ∈ GeneralNominalVersionedChildren232.emitted GeneralDictionaryGroundCopy218Install.plan := by
    rw [listEq]; exact List.mem_singleton_self _
  obtain ⟨clause,_,siteEq⟩ := List.mem_map.mp member
  have clauseMem := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  have clauseEq : clause.val = GeneralDictionaryGroundCopy218Install.clause := List.mem_singleton.mp clauseMem
  subst site
  rcases clause with ⟨clause,present⟩
  change clause = GeneralDictionaryGroundCopy218Install.clause at clauseEq
  subst clause
  have centerEq := GeneralNominalVersionedFrame231.childSite_center_eq
    GeneralDictionaryGroundCopy218Install.plan GeneralDictionaryGroundCopy218Install.clause
    (GeneralDictionaryGroundCopy218Install.declaration_checked.signature.2.2.2 _ clauseMem)
  rw [listEq]
  apply congrArg List.singleton
  change (⟨_,_⟩ : Site roles) = ⟨_,_⟩
  congr 1
  exact funext centerEq

theorem sites_exact : installed.core.sites = [GeneralDictionaryGroundCopy218Install.plan.input,childSite] := by
  change [_] ++ GeneralNominalVersionedChildren232.emitted GeneralDictionaryGroundCopy218Install.plan = _
  rw [emitted_eq]; rfl

theorem raw_sites_exact : installed.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,childSite.observed] := by
  change [_] ++ (GeneralNominalVersionedChildren232.emitted GeneralDictionaryGroundCopy218Install.plan).map Site.observed = _
  rw [emitted_eq]; rfl

noncomputable abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,ctx,childSite.observed,leafDecl,leafCheck,[(2,3),(2,3)]⟩
noncomputable abbrev plan : Plan roles := ⟨packet,childSite,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry installed.core oldChild 1 plan := by
  refine ⟨rfl,rfl,child_eq,rfl,?_,?_,List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl,located,GeneralDictionaryMixedGround218Fresh235.prepared⟩
  · rw [raw_sites_exact]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · rw [sites_exact]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem candidate_input {candidate : Plan roles} {key}
    (framed : GeneralNominalVersionedEvidence231.Frame registry installed.core oldChild key candidate) :
    candidate.input = childSite := by
  have member := framed.center_recorded
  rw [sites_exact] at member
  rcases List.mem_cons.mp member with same | last
  · have eq := candidate.input_exact.trans framed.occurrence_eq
    rw [same] at eq
    have role := congrArg (fun o => o.demand.role) eq
    cases role
  · exact List.mem_singleton.mp last

theorem candidate_queries {candidate : Plan roles}
    (framed : GeneralNominalVersionedEvidence231.Frame registry installed.core oldChild 1 candidate) :
    GeneralNominalInspection.queries candidate.packet.context.state candidate.packet.context.interpretation
      candidate.packet.declaration = [.variables [0],.variables [0]] := by
  have decl := leaf_only framed.visible framed.role_eq
  rw [decl,framed.context_eq,GeneralDictionaryMixedGround218Fresh235.context_eq]
  exact query

theorem infeasible : ¬ GeneralNominalVersionedDiagnostic232.Feasible registry installed oldChild 1 := by
  rintro ⟨given,held,candidate,framed,shared⟩
  exact GeneralDictionaryMixedGround218Obstruction234.child_input_infeasible candidate
    (candidate_input framed) (candidate_queries framed) given held shared

theorem at_key : GeneralNominalVersionedDiagnostic232.AtKey registry installed oldChild 1 :=
  ⟨⟨_,GeneralDictionaryMixedGround218Install234.installed_model⟩,⟨plan,frame⟩,infeasible⟩
end Yulang.GeneralDictionaryMixedGround218LeafFrame235
