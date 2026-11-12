import Yulang.GeneralDictionaryDiagnosticAccessibility
import Yulang.GeneralDictionarySupportRecursiveClosure

/-! Verified stability of the concrete early-merge fixture. A stable failed-child
diagnostic is not a successful dictionary and is not claimed as a V5 contradiction. -/
namespace Yulang.GeneralDictionaryEarlyMergeClosure
open GeneralDictionaryEarlyMergeExample GeneralDictionaryEarlyMergeDiagnostics
open GeneralNominalExamples (context state model state_models listDescriptor displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState CommonNominalFullCarrier

theorem models_of_source (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state true) m) : Models finish.current m := by
  apply (merge_models before.current (site 10) (site 11) m).mpr
  refine ⟨?_,by intro atom member; cases member⟩
  apply (GeneralNominalFeedbackSites.install_models (start displayRoot).current packet
    (GeneralNominalFeedbackSites.emitted packet) rfl m).mpr
  exact ⟨(initial_models ..).mpr valid,branch m valid⟩

abbrev varying := GeneralDictionaryTerminalRefresh.varying

theorem varying_model (name : Nat) (large : 2 ≤ name) : Models finish.current (varying name) :=
  models_of_source _ (GeneralDictionarySupportRecursiveClosure.varying_source name large)
/-- Every certified refresh must keep all reserved origins unknown. -/
theorem refresh_large_unknown (next : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalCycleSteps.Refresh finish.current next) (source : Nat) (large : 2 ≤ source) :
    ¬ GeneralNominalState.Known next.state source :=
  GeneralDictionaryTerminalRefresh.no_known_distinct next.state model (varying source) source
    (by change (if source = 0 then nominal 0 [.inl (.base .int)] else .base .int) = .base .int; exact ite_eq_right (by omega))
    (by simp only [varying,GeneralDictionaryTerminalRefresh.varying,ite_true]; rfl)
    (certificate.exact _ finish_model) (certificate.exact _ (varying_model source large))

theorem context_complete : ContextComplete finish.current := by
  intro m valid
  obtain ⟨reserved,atoms,allocated,growth⟩ := GeneralDictionaryOrdinaryTrace.extension_trans
    (GeneralDictionaryOrdinaryTrace.packet_extension packet)
    (GeneralDictionaryOrdinaryTrace.merge_extension before.current (site 10) (site 11))
  change current = GeneralDictionaryOrdinaryTrace.extendContext (context true) reserved atoms allocated at growth
  change GeneralNominalState.Models current.state m at valid
  rw [growth] at valid
  have old := (GeneralDictionaryOrdinaryTransport.models_extended allocated reserved atoms (context true).state m).mp valid |>.1
  exact models_of_source m old
theorem point_closed : GeneralNominalReobservationSteps.PointClosed current.state := by
  intro slot descriptor recorded
  change Fin 2 at slot
  change (if slot = (0 : Fin 2) then some listDescriptor else none) = some descriptor at recorded
  by_cases zero : slot = (0 : Fin 2)
  · subst slot
    have same := Option.some.inj recorded
    subst descriptor
    intro parameter member
    have same := List.mem_singleton.mp member
    subst parameter
    exact rfl
  · simp [zero] at recorded


noncomputable abbrev rootSite := GeneralNominalDemandMerging.pointSite displayRoot

theorem sites_exact : finish.current.sites = [rootSite,site 10,site 11] := by
  change [rootSite] ++ packet.children.map (GeneralNominalFeedbackSites.childSite packet) = _
  change [rootSite] ++ children.map (GeneralNominalFeedbackSites.childSite packet) = _
  rw [children_exact]; rfl

theorem edges_exact : finish.current.edges = [(displayRoot,child 10),(displayRoot,child 11)] := by
  change [] ++ packet.children.map (fun child => (displayRoot,child)) = _
  change [] ++ children.map (fun child => (displayRoot,child)) = _
  rw [children_exact]; rfl

theorem generated_cases (focus : GeneralSourceDictionaries.Occurrence roles)
    (generated : Generated finish.current displayRoot focus) :
    focus = displayRoot ∨ focus = child 10 ∨ focus = child 11 := by
  induction generated with
  | root => exact Or.inl rfl
  | child _ member _ =>
    rw [edges_exact] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h
    · exact Or.inr (Or.inl (congrArg Prod.snd h))
    · exact Or.inr (Or.inr (congrArg Prod.snd h))
  | alias _ _ member _ _ =>
    rw [sites_exact] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem sameInputs_no_cross (n : Nat) : ¬ GeneralNominalFeedbackSites.SameInputs finish.current rootSite (site n) := by
  intro same
  have left := GeneralNominalFeedbackSites.recover_sound finish.current rootSite model finish_model (point_holds displayRoot model)
  have right := GeneralNominalFeedbackSites.recover_sound finish.current (site n) model finish_model
    (GeneralNominalFeedbackSites.child_sound packet (child n) model (finish_model.2.1 packet (by exact List.mem_singleton_self _)))
  have relation := same.2
  change GeneralNominalDemandMerging.All₂ _
    [GeneralNominalFeedbackSites.recoverOrigin finish.current rootSite ⟨0,by change 0 < 1; decide +kernel⟩]
    [GeneralNominalFeedbackSites.recoverOrigin finish.current (site n) ⟨0,by change 0 < 1; decide +kernel⟩] at relation
  cases relation with
  | cons related _ =>
    obtain ⟨a,b,one,two,equal⟩ := related
    have firstFits := left ⟨0,by change 0 < 1; decide +kernel⟩ a (by
      change some (GeneralNominalFeedbackSites.recoverOrigin finish.current rootSite _) = some (some a)
      exact congrArg some one)
    have lastFits := right ⟨0,by change 0 < 1; decide +kernel⟩ b (by
      change some (GeneralNominalFeedbackSites.recoverOrigin finish.current (site n) _) = some (some b)
      exact congrArg some two)
    obtain ⟨x,hx⟩ := firstFits.1
    obtain ⟨y,hy⟩ := lastFits.1
    have xfit := firstFits.2 x hx
    have yfit := lastFits.2 y hy
    have sameValue := (equal model finish_model).2.2 x y hx hy
    have impossible : Equivalent (GeneralNominalOutputGrowth.tower 1) (GeneralNominalOutputGrowth.tower 0) :=
      ⟨subtype_trans xfit.1 (subtype_trans sameValue.1 yfit.2),
        subtype_trans yfit.1 (subtype_trans sameValue.2 xfit.2)⟩
    have contradiction := (GeneralNominalOutputGrowth.tower_equivalent 1 0).mp impossible
    cases contradiction

private theorem sameInputs_symm {first last : GeneralNominalDemandMerging.Site roles}
    (same : GeneralNominalFeedbackSites.SameInputs finish.current first last) :
    GeneralNominalFeedbackSites.SameInputs finish.current last first := by
  refine ⟨same.1.symm,?_⟩
  have relation := same.2
  generalize (GeneralNominalFeedbackSites.recover finish.current first).inputs = xs at relation ⊢
  generalize (GeneralNominalFeedbackSites.recover finish.current last).inputs = ys at relation ⊢
  induction relation with
  | nil => exact .nil
  | cons head tail ih =>
    refine .cons ?_ ih
    obtain ⟨a,b,one,two,equal⟩ := head
    refine ⟨b,a,two,one,?_⟩
    intro m valid
    have original := equal m valid
    exact ⟨original.2.1,original.1,fun x y hx hy => ⟨(original.2.2 y x hy hx).2,(original.2.2 y x hy hx).1⟩⟩



theorem merges_closed (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ finish.current.sites) (two : last ∈ finish.current.sites)
    (same : GeneralNominalFeedbackSites.SameInputs finish.current first last) :
    Alias finish.current first.occurrence.identity last.occurrence.identity := by
  have paired : Alias finish.current (site 10).occurrence.identity (site 11).occurrence.identity :=
    .edge (List.mem_singleton_self _)
  rw [sites_exact] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
  · exact .refl _
  · exact False.elim (sameInputs_no_cross 10 same)
  · exact False.elim (sameInputs_no_cross 11 same)
  · exact False.elim (sameInputs_no_cross 10 (sameInputs_symm same))
  · exact .refl _
  · exact paired
  · exact False.elim (sameInputs_no_cross 11 (sameInputs_symm same))
  · exact paired.symm
  · exact .refl _

open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

private theorem parent_branch (m : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current m) :
    BranchModels registry current displayRoot declaration checked [((0 : Fin 2),(0 : Fin 2))] m := by
  have source := ((merge_models before.current (site 10) (site 11) m).mp valid).1
  have old := ((GeneralNominalFeedbackSites.install_models (start displayRoot).current packet
    (GeneralNominalFeedbackSites.emitted packet) rfl m).mp source).1.1
  have original := GeneralDictionaryRecursiveEvidence.survivor_instance_of_branch registry registry_checked (context true)
    m displayRoot 1 children survivor declaration (by simp) checked rfl [(0,0)] rfl (branch m old)
  have rule := GeneralDictionaryOrdinaryTrace.instance_extension registry (context true) current
    (GeneralDictionaryOrdinaryTrace.extension_trans (GeneralDictionaryOrdinaryTrace.packet_extension packet)
      (GeneralDictionaryOrdinaryTrace.merge_extension before.current (site 10) (site 11)))
    m valid.1 displayRoot 1 children original
  obtain ⟨decl,visible,check,key,role,bounds,located,_,_,_,_,branch⟩ := rule
  have eq := List.mem_singleton.mp visible; subst decl
  have found : arguments current displayRoot = some [((0 : Fin 2),(0 : Fin 2))] := rfl
  have eq := Option.some.inj (located.symm.trans found)
  subst bounds
  exact branch

theorem installs_committed (p : Packet roles)
    (reached : Generated finish.current displayRoot p.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry finish.current p) :
    GeneralNominalFeedbackSteps.Committed finish.current p := by
  rcases generated_cases _ reached with same | same | same
  · have selected := enabled.2.1
    rw [same] at selected
    have agreement := GeneralNominalFeedbackK2.local_functional selected parent_selected
    have childrenEq := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).2
    constructor
    · intro m valid
      rcases p with ⟨preg,pctx,psite,pdecl,pchecked,pbounds⟩
      have reg := enabled.1.1
      have ctx := enabled.1.2.1
      dsimp only at reg ctx
      subst preg; subst pctx
      have visible := enabled.1.2.2.2.1
      have decl := List.mem_singleton.mp visible; change pdecl = declaration at decl; subst pdecl
      have found := enabled.1.2.2.2.2.2.1
      change arguments current psite.occurrence = some pbounds at found
      change psite.occurrence = displayRoot at same
      rw [same] at found
      have located : arguments current displayRoot = some [((0 : Fin 2),(0 : Fin 2))] := rfl
      have equal := Option.some.inj (found.symm.trans located)
      subst pbounds
      change BranchModels registry current psite.occurrence declaration pchecked [((0 : Fin 2),(0 : Fin 2))] m
      rw [same]
      exact parent_branch m valid
    · intro c member
      rw [childrenEq,children_exact] at member
      rw [same,edges_exact]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      rcases member with rfl | rfl <;> simp
  · have selected := enabled.2.1
    rw [same] at selected
    have impossible := GeneralNominalFeedbackK2.local_functional selected (child_rejected 10)
    cases impossible
  · have selected := enabled.2.1
    rw [same] at selected
    have impossible := GeneralNominalFeedbackK2.local_functional selected (child_rejected 11)
    cases impossible

theorem feedback_stable : GeneralNominalFeedbackSteps.Stable registry finish.current displayRoot := by
  intro focus generated next update
  cases update with
  | enqueue focus _ absent =>
    rcases generated_cases focus generated with same | same | same
    · exact absent rootSite (by rw [sites_exact]; simp) same.symm
    · exact absent (site 10) (by rw [sites_exact]; simp) same.symm
    · exact absent (site 11) (by rw [sites_exact]; simp) same.symm
  | install p enabled novel => exact novel (installs_committed p generated enabled)
  | merge first last one two same novel => exact novel (merges_closed first last one two same)
  | refresh _ next certificate source _ unknown known =>
    by_cases zero : source = 0
    · subst source
      exact unknown ⟨(0 : Fin 2),rfl,Or.inr ⟨listDescriptor,rfl⟩⟩
    · by_cases one : source = 1
      · subst source
        exact unknown ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩
      · exact refresh_large_unknown next certificate source (by omega) known
  | equate _ first last _ _ equal novel =>
    exact novel (fun m valid => equal m (context_complete m valid))

theorem stable : GeneralNominalSupportSteps.Stable registry finish displayRoot := by
  intro focus generated next update
  have old := GeneralNominalSupportSteps.at_old update
  exact (GeneralNominalReobservationSteps.stable_of_pointClosed feedback_stable point_closed) focus generated _ old




/-- Actual reachable, inhabited, stable early merge with finite where diagnostics
and no four-way Classify result at the selected parent. The failed children are
retained in the diagnostic tree; this is not a general V5 impossibility theorem. -/
theorem stable_diagnostic_without_classify :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧
    GeneralNominalSupportSteps.Stable registry finish displayRoot ∧
    Acc (CommonRoleOutermostResolver.Child
      (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish)) displayRoot ∧
    ∀ outcome, ¬ B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot outcome :=
  ⟨reachable,finish_model,stable,
    GeneralDictionaryDiagnosticAccessibility.resolved_accessible
      (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish displayRoot _ diagnostic,
    root_no_classify⟩

end Yulang.GeneralDictionaryEarlyMergeClosure
