import Yulang.GeneralNominalInspectionMatching

/-! Actual prepared packets construct head matching. The ground-root
accessibility theorem has no remaining producer or budget hypothesis. -/
namespace Yulang.GeneralNominalGroundHeadMatching
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSharedCaptures GeneralNominalSupport
open GeneralNominalActualInspectionSteps GeneralNominalMatchedAssembly
open GeneralNominalGroundAccessibility GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalRecursiveInspection
open GeneralNominalInspectionAlignment GeneralNominalInspectionPositions GeneralNominalInspectionMatching

set_option backward.isDefEq.respectTransparency false

theorem aligned_of_positions (first : List α) (last : List β) (length : first.length = last.length)
    (known : ∀ index : Fin first.length, relation first[index] (last[index.val]'(by rw [← length]; exact index.isLt))) :
    Aligned relation first last := by
  induction first generalizing last with
  | nil => have empty : last = [] := List.eq_nil_of_length_eq_zero length.symm; subst last; exact .nil
  | cons head tail ih =>
    cases last with
    | nil => cases length
    | cons next rest =>
      refine .cons (by simpa using known ⟨0,by simp⟩) ?_
      apply ih rest (Nat.add_right_cancel length)
      intro index
      simpa using known ⟨index.val+1,Nat.succ_lt_succ index.isLt⟩

theorem prepared_finished (packet : Packet roles)
    (prepared : GeneralNominalRecursiveCandidates.Prepared packet.registry packet.context packet.site.occurrence packet.declaration packet.checked)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds) :
    Finished (inheritedReport packet) := by
  obtain ⟨_,_,_,bounds,found,finished,_,_⟩ := prepared
  have same := Option.some.inj (found.symm.trans located)
  subst bounds
  exact finished_origins packet.context.state _ packet.bounds (fun _ => none) _ 0 0 finished

theorem packet_matching (state : State roles) (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state packet)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation)
    (nonempty : packet.declaration.requirements ≠ [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) (branch : packet.Holds model)
    (generation : GenerationGuard tracked packet) (known : Inputs context model packet.site labels) :
    HeadMatches context packet model labels := by
  classical
  obtain ⟨_,sameContext,_,_,_,located,prepared,_,_,_,_,_⟩ := enabled.1
  have current : GeneralNominalState.Models packet.context.state model := by rw [sameContext]; exact valid.1
  have finished := prepared_finished packet prepared located
  obtain ⟨clause,present⟩ := List.exists_mem_of_ne_nil _ nonempty
  have covered := (packet.checked.countsCovered clause present).1
  let queries := GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration
  have single : ∀ query ∈ queries, Single query := by
    intro query member
    obtain ⟨pattern,present,rfl⟩ := List.mem_map.mp member
    exact translated_single pattern (GeneralNominalChildAssembly.covered_member _ covered pattern present)
  obtain ⟨labelLength,meanings⟩ := known
  let trees : Fin (roles packet.site.occurrence.demand.role).arity → Expr Nat := fun index => Classical.choose (meanings index)
  have treeFacts (index : Fin (roles packet.site.occurrence.demand.role).arity) := Classical.choose_spec (meanings index)
  have boundsLength : packet.bounds.length = (roles packet.site.occurrence.demand.role).arity := by
    simpa only [List.length_ofFn] using GeneralNominalPacketCodes.locate_length packet.context.state.base
      (List.ofFn packet.site.occurrence.demand.arguments) packet.bounds located
  have inputTrees : InputsAt context model packet.context.state
      (fun index => (packet.site.inputs[index]?).join) 0 packet.bounds (List.ofFn trees) := by
    apply inputs_at _ _ (by rw [List.length_ofFn,boundsLength])
    intro index
    let position : Fin (roles packet.site.occurrence.demand.role).arity := ⟨index.val,by rw [← boundsLength]; exact index.isLt⟩
    have facts := treeFacts position
    have inside : index.val < (roles packet.site.occurrence.demand.role).arity := position.isLt
    have sources := congrArg (fun inputs => inputs[index.val]?)
      (GeneralNominalPacketCaptureReadback.locate_sources packet.context.state.base
        (List.ofFn packet.site.occurrence.demand.arguments) packet.bounds located)
    have same : (packet.context.state.base.source packet.bounds[index.val].1,packet.context.state.base.source packet.bounds[index.val].2) =
        packet.site.occurrence.demand.arguments position := by
      simpa only [List.getElem?_map,List.getElem?_eq_getElem index.isLt,Option.map_some,List.getElem?_ofFn,
        inside,dite_eq_left,Option.some.injEq] using sources
    simp only [Fin.getElem_fin,List.getElem_ofFn,Nat.zero_add]
    refine ⟨⟨_,facts.1⟩,?_,?_⟩
    · change GeneralNominalCaptureMerges.Fits model _ _
      rw [same]
      exact facts.2.1
    · intro origin retained
      exact facts.2.2 origin (Option.join_eq_some_iff.mp retained)
  have matched := many_matched packet model current branch generation queries packet.bounds _ 0 (List.ofFn trees)
    single finished inputTrees (fun _ h => h)
  have queryLength : queries.length = packet.bounds.length := finished_length packet.context.state queries packet.bounds _ 0 finished
  have headLength : (normalizeArgs packet.declaration.head).length = labels.length := by
    have heads : queries.length = (normalizeArgs packet.declaration.head).length := List.length_map ..
    omega
  apply aligned_of_positions _ _ headLength
  intro index
  let position : Fin (roles packet.site.occurrence.demand.role).arity := ⟨index.val,by rw [← labelLength,← headLength]; exact index.isLt⟩
  refine ⟨trees position,(treeFacts position).1,?_⟩
  have headQueries : queries.length = (normalizeArgs packet.declaration.head).length := List.length_map ..
  have atIndex := aligned_position matched (by rw [List.length_ofFn,queryLength,boundsLength])
    ⟨index.val,by rw [headQueries]; exact index.isLt⟩
  simpa only [queries,GeneralNominalInspection.queries,Declaration.normalHead,Fin.getElem_fin,
    List.getElem_map,List.getElem_ofFn,constructors,interpretation] using atIndex

theorem reachable_head_matching : ReachableHeadMatching roles registry context root := by
  intro state packet support trace constructors interpretation enabled guard nonempty model valid branch labels known
  exact packet_matching state.current packet enabled (by rw [enabled.1.2.1]; exact constructors)
    (by rw [enabled.1.2.1]; exact interpretation) nonempty model valid branch guard.1.2.2.1 known

theorem ground_class_p_accessible (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : GeneralNominalActualBudget.PointSource context root)
    (ground : GroundRoots context root rootLabels) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  ground_accessible_of_matching checked source point ground reachable_head_matching


theorem normalized_capture_assembly : GeneralNominalCaptureAssembly.NormalizedCaptureAssembly roles registry context root :=
  assembly_of_matching reachable_head_matching

theorem installed_depth_bound
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GroundRoots context root rootLabels) :
    GeneralNominalInvocationAncestry.InstalledDepthBound registry context root
      (GeneralNominalPatersonLineage.mass rootLabels) :=
  GeneralNominalNormalizedGround.installed_depth_bound
    (GeneralNominalNormalizedGround.packet_production
      (GeneralNominalCaptureAssembly.factorization_of_assembly normalized_capture_assembly)) source point ground

theorem ground_point_root_accessible (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GroundRoots context root rootLabels) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  GeneralNominalActualBudget.accessible_of_installed_depth_bound checked source (installed_depth_bound source point ground)

end Yulang.GeneralNominalGroundHeadMatching
