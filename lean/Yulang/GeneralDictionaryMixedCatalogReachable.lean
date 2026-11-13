import Yulang.GeneralDictionaryMixedCatalogInhabited

/-! The mixed-packet catalog separation is realized by an actual initial-source
Value installation. It is not a terminal-state or general coverage claim. -/
namespace Yulang.GeneralDictionaryMixedCatalogReachable
open GeneralDictionaryMixedCatalogExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalSupportSteps
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalExamples (context state model state_models listDescriptor displayRoot interpretation)
open GeneralDictionaryMixedCatalogInhabited (query)

theorem registry_checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro d member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact checked
  · exact terminal_checked

abbrev start (root : Occurrence roles) : Tracked roles := GeneralNominalSupport.initial (context true) root
private theorem all_heads (slot : Fin (state true).base.slots) :
    ∃ test observation, Head (state true) ((state true).base.source slot) test observation := by
  have bounded := slot.isLt
  change slot.val < 2 at bounded
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero
    subst slot
    exact ⟨_,_,.nominal 0 listDescriptor rfl⟩
  · have same : slot = (1 : Fin 2) := by
      apply Fin.ext
      change slot.val = 1
      omega
    subst slot
    exact ⟨_,_,.scalar 1 .int rfl⟩

private theorem roots (root : Occurrence roles) (arguments : ∀ index, root.demand.arguments index = (0,0)) :
    Roots (start root) [] root := by
  intro index
  rw [show (root.demand.arguments index).1 = 0 by rw [arguments index]]
  exact source_ready (start root) 0 (.nominal 0 1) _ _
    (Head.nominal (snapshot := state true) 0 listDescriptor rfl) (Head.nominal (snapshot := state true) 0 listDescriptor rfl) []

theorem all_source_decisions (root : Occurrence roles) (arguments : ∀ index, root.demand.arguments index = (0,0)) :
    DecisionGuard (start root) registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),roots root arguments,?_⟩
  intro declaration visible role bounds located slot member
  obtain ⟨test,observation,head⟩ := all_heads slot
  exact source_ready (start root) _ test observation observation head head []

private def height (source : Nat) : Nat := if source = 0 then 1 else 0

private theorem model_height (source : Nat) : (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

private theorem raw_acyclic (slot : Fin (state true).base.slots) : ¬ GeneralNominalCycleK2.Cycle (state true) slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge (state true) first last →
      height last.val < height first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model (state_models true)
      exact GeneralNominalOutputGrowthModels.observation_decreases model height model_height _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path (state true) first last → height last.val ≤ height first.val := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

private theorem no_raw_recurs (slot : Fin (state true).base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt (state true) slot := by
  rintro (⟨child,edge,path⟩ | ⟨cycle,_⟩)
  · exact raw_acyclic slot ⟨child,GeneralNominalCycleK2.direct_edge_sound edge,GeneralNominalCycleK2.direct_path_sound path⟩
  · exact raw_acyclic slot cycle

private theorem no_feedback_cycle (root : Occurrence roles) (identity : Nat) :
    ¬ GeneralNominalFeedbackK2.Cycle (start root).current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model ((initial_models ..).mpr (state_models true))
    height model_height (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

private theorem no_root (root : Occurrence roles) : ¬ GeneralNominalFeedbackK2.RootK2 (start root).current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,index,cycle,_⟩)
  · exact no_raw_recurs slot cycle
  · exact no_feedback_cycle root _ cycle

private theorem no_candidate (root : Occurrence roles) :
    ¬ GeneralNominalFeedbackK2.CandidateK2 registry (start root).current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw_recurs visited.1 cycle
  · exact no_feedback_cycle root _ cycle


theorem prepared : Prepared registry (context true) displayRoot declaration checked := by
  refine ⟨GeneralDictionarySupportRecursiveExample.initial_source.metadata,
    GeneralDictionarySupportRecursiveExample.initial_source.linked,
    initial_fresh _ _ _ (by decide +kernel),[(0,0)],rfl,?_,?_,model,GeneralDictionaryMixedCatalogInhabited.branch⟩
  · rw [report_exact (context true) declaration 0 listDescriptor rfl 0 (1,1) rfl query]
    exact ⟨rfl,rfl,rfl⟩
  · refine ⟨(by intro _ h; cases h),?_⟩; change (GeneralNominalPacketSupport.namedSchema packet).unknown = false; rw [generated_exact]

noncomputable abbrev children := GeneralNominalAllocation.children (state true) registry displayRoot declaration checked
    (bindings (state true) (report (context true) declaration [(0,0)]))

theorem survivor : Survivor registry (context true) displayRoot 1 children :=
  ⟨GeneralNominalRecursiveExamples.display_survivor.1,declaration,by simp,checked,rfl,rfl,[(0,0)],rfl,prepared,rfl⟩

theorem selected : GeneralNominalSupportBoundary.Local registry (start displayRoot) displayRoot (.selected 1 children) := by
  apply GeneralNominalSupportBoundary.selected_supported (support := []) _ (all_source_decisions displayRoot (fun _ => rfl))
  refine .selected ⟨survivor.1,no_root _,no_candidate _,?_⟩ ⟨survivor,?_⟩
  · rintro (⟨_,d,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl
      · exact notPrepared prepared
      · contradiction
    · rcases legacy with ⟨⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ |
        ⟨⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩,_⟩ <;> exact Fin.elim0 kind
  · intro key cs found
    have original := found
    obtain ⟨_,d,visible,check,identity,role,_⟩ := found
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl
    · have equal : key = 1 := identity.symm; subst key
      exact ⟨rfl,survivor_children_functional registry registry_checked (context true) displayRoot 1 cs children original survivor⟩
    · contradiction

theorem enabled : GeneralNominalFeedbackSteps.Installable registry (start displayRoot).current packet := by
  have localRule := GeneralNominalSupportBoundary.selected_old selected
  refine ⟨⟨rfl,rfl,by simp [start,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial],by simp,rfl,rfl,prepared,
    GeneralNominalFeedbackK2.selected_legacy localRule,?_,?_,?_,?_⟩,localRule,?_⟩
  · intro prior member; cases member
  · intro other member _; have eq := List.mem_singleton.mp member; subst other; exact .refl _
  · exact ⟨model,(initial_models ..).mpr (state_models true),GeneralDictionaryMixedCatalogInhabited.branch⟩
  · exact GeneralNominalJointCandidates.initial_joint registry (context true) displayRoot declaration
      (by simp) checked rfl [(0,0)] rfl prepared model (GeneralDictionaryMixedCatalogInhabited.branch)
  · intro other member _; have eq := List.mem_singleton.mp member; subst other; exact .refl _

theorem packet_guard : PacketGuard (start displayRoot) packet [] := by
  have decisions := all_source_decisions displayRoot (fun _ => rfl)
  exact ⟨⟨decisions.1,decisions.2.1,decisions.2.2 declaration (by simp) rfl _ rfl⟩,decisions⟩

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed (start displayRoot).current packet := by
  intro committed
  have empty : packet.children = [] := List.eq_nil_iff_forall_not_mem.mpr (by
    intro child member
    have absent := committed.2 child member
    cases absent)
  have size := congrArg List.length empty
  change children.length = 0 at size
  have count : children.length = 2 := by
    simp [children,GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,
      GeneralCanonicalChildOrder.canonicalEmit,GeneralDeclarationDemands.emitAll,
      GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
      declaration,List.mergeSort_pair]
  omega

theorem source : GeneralNominalSourceFormation.InitialSource registry (context true) displayRoot where
  roles_agree := rfl
  metadata := prepared.1
  linked := prepared.2.1
  intervals := GeneralDictionarySupportRecursiveExample.initial_source.intervals
  below_seed := GeneralDictionarySupportRecursiveExample.initial_source.below_seed
  unallocated := rfl

noncomputable abbrev installed := GeneralNominalValueSteps.install (start displayRoot) packet []

theorem value_step : GeneralNominalValueSteps.Step registry displayRoot (start displayRoot) installed :=
  GeneralNominalValueSteps.source_install (start displayRoot) packet .root enabled novel packet_guard

theorem reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles)
    registry displayRoot installed :=
  ⟨start displayRoot,⟨context true,source,rfl⟩,.tail .refl value_step⟩

theorem installed_model : Models installed.current model :=
  (GeneralNominalFeedbackSites.install_models (start displayRoot).current packet
    (GeneralNominalFeedbackSites.emitted packet) rfl model).mpr
    ⟨(initial_models ..).mpr (state_models true),GeneralDictionaryMixedCatalogInhabited.branch⟩

theorem recorded : packet ∈ installed.current.packets := by exact List.mem_cons_self

theorem old_catalog_empty : GeneralDictionaryReachableRequestHistory.safeCatalog installed = [] := by
  change ([packet] : List (Packet roles)).reverse.flatMap GeneralDictionaryReachableRequestHistory.eligible = []
  simp [GeneralDictionaryReachableRequestHistory.eligible,mixed]

theorem new_catalog_contains : closedRequest ∈ GeneralDictionaryRequestCatalog.catalog installed := by
  apply (GeneralDictionaryRequestCatalog.member_iff installed closedRequest).mpr
  exact ⟨packet,recorded,by rw [emissions]; exact List.mem_cons_self,closed⟩

/-- Strictly finer filtering on an actual reachable, satisfiable post-install
state. No Stable assumption, synthetic journal, or assumed path is used. -/
theorem reachable_strict_coverage :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry displayRoot installed ∧
    Models installed.current model ∧
    closedRequest ∈ GeneralDictionaryRequestCatalog.catalog installed ∧
    closedRequest ∉ GeneralDictionaryReachableRequestHistory.safeCatalog installed := by
  refine ⟨reachable,installed_model,new_catalog_contains,?_⟩
  rw [old_catalog_empty]; simp
end Yulang.GeneralDictionaryMixedCatalogReachable
