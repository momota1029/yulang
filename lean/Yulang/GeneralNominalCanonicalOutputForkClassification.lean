import Yulang.GeneralNominalCanonicalOutputFork

/-! Observation completion exposes a real associated-output installation.
The source permits both int and str at its named output. Full stability after
the precise view must enforce int and therefore cannot preserve both models. -/
namespace Yulang.GeneralNominalCanonicalOutputForkClassification

open GeneralNominalCanonicalOutputFork GeneralDeclarations GeneralDeclarationPatterns
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralSourceDictionaries GeneralNominalSaturationState CommonNominalFullCarrier
open GeneralDeclarationExamples (roles)

abbrev calculated : Report (state (some false)) where
  inspected := [(0,0),(2,2),(3,3)]
  checked := [(0,0),(0,0),(2,2),(3,3)]
  anchors := [(GeneralNominalRefreshForkClassification.outer,(2,2)),
    (GeneralNominalRefreshForkClassification.inner,(3,3))]
  tests := [(GeneralNominalRefreshForkClassification.outer,.nominal 0 1),
    (GeneralNominalRefreshForkClassification.inner,.scalar .int)]

theorem point_report : report (context (some false)) declaration [(0,0)] = calculated := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,inspectMany,inspect,
    typeArguments,Report.visit,Report.append,calculated,state,GeneralNominalRefreshFork.state,
    GeneralNominalRefreshFork.view]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_5]
  simp [typeArguments,Report.visit,Report.append]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_3]
  simp [Report.visit,Report.append]

theorem wide_blocked : (report (context (some true)) declaration [(0,0)]).blocked = [(2,4)] := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,inspectMany,inspect,
    typeArguments,Report.visit,Report.append,state,GeneralNominalRefreshFork.state,GeneralNominalRefreshFork.view]
  rw [inspectMany.eq_2,inspectMany.eq_1,inspect.eq_5]
  simp [typeArguments,Report.visit,Report.append,block]

theorem located (choice : Option Bool) : arguments (context choice) root = some [(0,0)] := by
  change arguments (context none) root = some [(0,0)]
  decide +kernel

theorem children_empty (choice : Option Bool) (checked : DeclarationChecked registry.constructors roles declaration)
    (bindings : GeneralNominalAllocation.Bindings) :
    GeneralNominalAllocation.children (state choice) registry root declaration checked bindings = [] := by
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem schema_calculated (choice : Option Bool) (checked : DeclarationChecked registry.constructors roles declaration) :
    generated registry (context choice) root declaration checked [(0,0)] =
      { tests := [(.source 5,.scalar .int)] } := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,normalize,normalizeArgs,GeneralNominalInspection.translate,
    GeneralNominalExamples.interpretation]

theorem point_projections (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state (some false)) m) :
    ProjectionModels (state (some false)) calculated m := by
  simpa [ProjectionModels,calculated,GeneralNominalRefreshForkClassification.calculated,Fits]
    using GeneralNominalRefreshForkClassification.point_projections m valid

theorem point_branch (checked : DeclarationChecked registry.constructors roles declaration)
    (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state (some false)) m)
    (output : Equivalent (m 5).1 (.base .int)) :
    BranchModels registry (context (some false)) root declaration checked [(0,0)] m := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [point_report]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨valid,?_,?_⟩
      · intro first member; cases member
      · exact PresenceNormalForm.all_nil _ _
    · intro atom member
      simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact subtype_refl _
  · rw [point_report]; exact point_projections m valid
  · rw [schema_calculated]
    refine ⟨?_,?_,?_,?_⟩
    · intro test member
      have same := List.mem_singleton.mp member
      subst test
      refine ⟨⟨_,.source 5⟩,?_⟩
      intro actual seen
      cases seen
      exact output
    · intro entry member; cases member
    · intro entry member; cases member
    · intro entry member; cases member

theorem branch_output (checked : DeclarationChecked registry.constructors roles declaration)
    (m : GeneralNominalCommonBridge.Assignment)
    (branch : BranchModels registry (context (some false)) root declaration checked [(0,0)] m) :
    Equivalent (m 5).1 (.base .int) := by
  have materialized := branch.2.2
  rw [schema_calculated] at materialized
  exact (materialized.1 (.source 5,.scalar .int) (by simp)).2 _ (.source 5)

theorem fresh (choice : Option Bool) : GeneralNominalAllocation.Fresh (state choice) registry root.identity := by
  intro key member
  simp [GeneralNominalAllocation.keys,GeneralNominalAllocation.declarationKeys,
    declaration,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
    variablesArgs,Pattern.variables] at member

theorem point_prepared : Prepared registry (context (some false)) root declaration declaration_checked := by
  refine ⟨metadata _,linked _,fresh _,[(0,0)],located _,?_,?_,model .int,?_⟩
  · rw [point_report]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      have same := List.mem_singleton.mp member
      subst output
      exact ⟨equation,by simp,rfl⟩
    · rw [schema_calculated]
  · exact point_branch declaration_checked (model .int) (after_models false .int).1
      ⟨subtype_refl _,subtype_refl _⟩

theorem point_survivor : Survivor registry (context (some false)) root 90 [] := by
  refine ⟨?_,declaration,by simp,declaration_checked,rfl,rfl,[(0,0)],located _,point_prepared,?_⟩
  · rintro ⟨index,unknown⟩; exact unknown (zero_known false)
  · exact (children_empty ..).symm

theorem wide_not_prepared (checked : DeclarationChecked registry.constructors roles declaration) :
    ¬ Prepared registry (context (some true)) root declaration checked := by
  rintro ⟨_,_,_,bounds,found,finished,_⟩
  have same := Option.some.inj ((located _).symm.trans found)
  subst bounds
  have impossible := finished.1
  rw [wide_blocked] at impossible
  cases impossible

theorem generated_only_root (wide : Bool) (focus : Occurrence roles)
    (generated : Generated (after wide) root focus) : focus = root := by
  induction generated with
  | root => rfl
  | child _ member _ => cases member
  | alias _ _ member _ _ =>
    exact congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp member)

theorem wide_stable : GeneralNominalFeedbackSteps.Stable registry (after true) root := by
  intro focus generated next action
  have same := generated_only_root true focus generated
  cases action with
  | enqueue focus _ absent => exact absent _ (List.mem_singleton_self _) same.symm
  | install packet enabled novel =>
    rcases packet with ⟨reg,ctx,site,d,checked,bounds⟩
    have regEq := enabled.1.1
    have ctxEq := enabled.1.2.1
    have visible := enabled.1.2.2.2.1
    have prepared := enabled.1.2.2.2.2.2.2.1
    dsimp only at regEq ctxEq visible prepared same
    subst reg
    change ctx = context (some true) at ctxEq
    subst ctx
    have declEq := List.mem_singleton.mp visible
    subst d
    rw [same] at prepared
    exact wide_not_prepared checked prepared
  | merge first last one two _ novel =>
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)
  | refresh _ next certificate source member unknown known =>
    exact no_refresh true next certificate source member unknown known
  | equate _ first last _ _ equal novel =>
    exact novel (GeneralDictionaryReachableEvidenceInitial.initial_equal_is_raw (context (some true)) root first last equal)

private theorem old_model (wide : Bool) : Models (after wide) GeneralNominalRefreshFork.model :=
  (GeneralNominalSaturationState.initial_models ..).mpr (GeneralNominalRefreshFork.after_models wide).1

private theorem feedback_edge_forward (wide : Bool) (first last : Nat)
    (edge : GeneralNominalFeedbackK2.Edge (after wide) first last) : first < last := by
  have firstBound := source_bound (some wide) first edge.1
  have lastBound := source_bound (some wide) last edge.2.1
  have argument : GeneralNominalFeedbackK2.Argument (after wide) first last := by
    rcases edge.2.2 with ⟨parent,child,⟨kind,_,_,_⟩,_,_⟩ | argument
    · exact Fin.elim0 kind
    · exact argument
  have firstSmall : first < 5 := by
    by_cases five : first = 5
    · subst first
      obtain ⟨name,index,observed⟩ := argument
      obtain ⟨actual,seen,_⟩ := observed GeneralNominalRefreshFork.model (old_model wide)
      cases seen with
      | argument sourceSeen compared found =>
        cases sourceSeen
        exact False.elim (GeneralNominalTopObservation.top_not_nominal _ _ compared.1)
    · omega
  by_cases five : last = 5
  · omega
  have lastSmall : last < 5 := by omega
  apply GeneralNominalRefreshForkCycles.feedback_edge_forward wide first last
  refine ⟨?_,?_,Or.inr ?_⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨⟨first,firstSmall⟩,rfl⟩)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨⟨last,lastSmall⟩,rfl⟩)))
  · obtain ⟨name,index,observed⟩ := argument
    exact ⟨name,index,fun m valid => observed m
      ((GeneralNominalSaturationState.initial_models ..).mpr valid.1)⟩

theorem feedback_acyclic (wide : Bool) (source : Nat) :
    ¬ GeneralNominalFeedbackK2.Cycle (after wide) source := by
  rintro ⟨next,edge,path⟩
  have forward := feedback_edge_forward wide source next edge
  have backward : next ≤ source := GeneralNominalFeedbackK2.Path.rec
    (motive := fun first last _ => first ≤ last) (fun _ => Nat.le_refl _)
    (fun edge _ ih => Nat.le_trans (Nat.le_of_lt (feedback_edge_forward wide _ _ edge)) ih) path
  omega

private theorem raw_edge_feedback (wide : Bool) (first last : Fin 5)
    (edge : GeneralNominalMixedRecurrence.Edge (state (some wide)) first last) :
    GeneralNominalFeedbackK2.Edge (after wide) first.val last.val := by
  refine ⟨?_,?_,?_⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨first,rfl⟩)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨last,rfl⟩)))
  · rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · exact Or.inr (GeneralNominalFeedbackK2.actual_argument (after wide) first last argument)

theorem raw_acyclic (wide : Bool) (slot : Fin 5) :
    ¬ GeneralNominalCycleK2.RecursAt (state (some wide)) slot := by
  intro recurs
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ recurs
  have transported : GeneralNominalFeedbackK2.Path (after wide) next.val slot.val :=
    GeneralNominalMixedRecurrence.Path.rec
      (motive := fun first last _ => GeneralNominalFeedbackK2.Path (after wide) first.val last.val)
      (fun _ => .nil _) (fun edge _ ih => .cons (raw_edge_feedback wide _ _ edge) ih) path
  exact feedback_acyclic wide slot.val ⟨next.val,raw_edge_feedback wide _ _ edge,transported⟩

theorem not_rootK2 (wide : Bool) (demand : Occurrence roles) :
    ¬ GeneralNominalFeedbackK2.RootK2 (after wide) demand := by
  rintro (⟨_,_,_,slot,_,recurs⟩ | ⟨_,_,_,cycle,_⟩)
  · exact raw_acyclic wide slot recurs
  · exact feedback_acyclic wide _ cycle

theorem not_candidateK2 (wide : Bool) (r : Registry) (demand : Occurrence roles) :
    ¬ GeneralNominalFeedbackK2.CandidateK2 r (after wide) demand := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,recurs⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact raw_acyclic wide visited.1 recurs
  · exact feedback_acyclic wide _ cycle

theorem point_selected : GeneralNominalFeedbackK2.Local registry (after false) root (.selected 90 []) := by
  refine .selected ⟨point_survivor.1,not_rootK2 false root,not_candidateK2 false registry root,?_⟩
    ⟨point_survivor,?_⟩
  · rintro (⟨_,d,visible,checked,_,_,unprepared⟩ | ⟨_,legacy⟩)
    · have same := List.mem_singleton.mp visible
      subst d
      exact unprepared point_prepared
    · rcases legacy with ⟨rootK2,_⟩ | ⟨candidateK2,_⟩
      · obtain ⟨_,_,_,slot,_,⟨⟨kind,_,_⟩,_⟩⟩ := rootK2
        exact Fin.elim0 kind
      · obtain ⟨_,_,_,_,_,_,_,_,visited,_,⟨⟨kind,_,_⟩,_⟩⟩ := candidateK2
        exact Fin.elim0 kind
  · intro key children given
    have original := given
    obtain ⟨_,d,visible,_,identity,_⟩ := given
    have same := List.mem_singleton.mp visible
    subst d
    have same : key = 90 := identity.symm
    subst key
    exact ⟨rfl,survivor_children_functional registry registry_checked _ root 90 children [] original point_survivor⟩

abbrev packet : Packet roles :=
  ⟨registry,context (some false),GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(0,0)]⟩

theorem packet_children : packet.children = [] := children_empty ..

theorem good_packet : packet.Holds (model .int) :=
  point_branch declaration_checked (model .int) (after_models false .int).1 ⟨subtype_refl _,subtype_refl _⟩

theorem bad_packet : ¬ packet.Holds (model .str) := by
  intro holds
  exact GeneralDictionaryRecursiveObstruction.bad_output_equation (branch_output declaration_checked (model .str) holds)

theorem point_installable : GeneralNominalFeedbackSteps.Installable registry (after false) packet := by
  refine ⟨?_,?_,?_⟩
  · refine ⟨rfl,rfl,by simp [after,initial],by simp,rfl,located _,point_prepared,?_,?_,?_,?_,?_⟩
    · rw [packet_children]
      exact GeneralNominalFeedbackK2.selected_legacy point_selected
    · intro prior member; cases member
    · intro other member _
      have same := List.mem_singleton.mp member
      subst other
      exact .refl _
    · exact ⟨_,after_models false .int,good_packet⟩
    · exact GeneralNominalJointCandidates.initial_joint registry (context (some false)) root declaration
        (by simp) declaration_checked rfl [(0,0)] (located _) point_prepared _ good_packet
  · rw [packet_children]; exact point_selected
  · intro other member _
    have same := List.mem_singleton.mp member
    subst other
    exact .refl _

theorem point_not_committed : ¬ GeneralNominalFeedbackSteps.Committed (after false) packet :=
  fun committed => bad_packet (committed.1 _ (after_models false .str))

noncomputable abbrev installed := GeneralNominalFeedbackSites.install (after false) packet (GeneralNominalFeedbackSites.emitted packet)

theorem actual_install : GeneralNominalReobservationSteps.Step registry root (after false) installed :=
  GeneralNominalReobservationSteps.old_step ⟨root,.root,.install packet point_installable point_not_committed⟩

theorem installed_excludes_bad : ¬ Models installed (model .str) := by
  intro valid
  exact bad_packet ((GeneralNominalFeedbackSites.install_models _ packet _ rfl _).mp valid).2

theorem installed_good : Models installed (model .int) :=
  (GeneralNominalFeedbackSites.install_models _ packet _ rfl _).mpr ⟨after_models false .int,good_packet⟩

theorem point_not_stable : ¬ GeneralNominalReobservationSteps.Stable registry (after false) root := by
  intro stable
  exact GeneralNominalReobservationSteps.stable_halted stable _ actual_install

theorem no_stable_same_models_with_installable (final : State roles)
    (stable : GeneralNominalReobservationSteps.Stable registry final root)
    (same : ∀ m, Models (after true) m ↔ Models final m)
    (enabled : GeneralNominalFeedbackSteps.Installable registry final packet) : False := by
  have forced := GeneralNominalReobservationSteps.same_models_stable_requires_constraints
    stable same packet GeneralNominalSaturationState.Generated.root enabled
  exact bad_packet (forced _ (after_models true .str))

theorem installed_trace_loses_bad (final : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) installed final) :
    ¬ Models final (model .str) :=
  fun valid => installed_excludes_bad (GeneralNominalReobservationSteps.steps_models path _ valid)

theorem concrete_completion_requires_output :
    Checked registry ∧
    B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles) registry root (after true) ∧
    GeneralNominalFeedbackSteps.Stable registry (after true) root ∧
    GeneralNominalReobservationSteps.Step registry root (after true) (after false) ∧
    (∀ m, Models (after true) m ↔ Models (after false) m) ∧
    Models (after true) (model .int) ∧ Models (after true) (model .str) ∧
    GeneralNominalFeedbackSteps.Installable registry (after false) packet ∧
    ¬ GeneralNominalReobservationSteps.Stable registry (after false) root ∧
    GeneralNominalReobservationSteps.Step registry root (after false) installed ∧
    Models installed (model .int) ∧ ¬ Models installed (model .str) :=
  ⟨registry_checked,after_reachable true,wide_stable,repair_step,
    fun m => (same_models true m).trans (same_models false m).symm,
    after_models true .int,after_models true .str,point_installable,point_not_stable,actual_install,
    installed_good,installed_excludes_bad⟩

end Yulang.GeneralNominalCanonicalOutputForkClassification
