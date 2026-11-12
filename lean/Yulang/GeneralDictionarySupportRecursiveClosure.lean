import Yulang.GeneralDictionarySupportRecursiveClassification
import Yulang.GeneralDictionaryTerminalRefresh

/-! Administrative closure facts for the concrete recursive support installation.
Reserved identities are excluded by separating models, not by PointClosed. -/
namespace Yulang.GeneralDictionarySupportRecursiveClosure
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralNominalExamples
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalSaturationState CommonNominalFullCarrier

abbrev varying := GeneralDictionaryTerminalRefresh.varying

theorem varying_source (name : Nat) (large : 2 ≤ name) : GeneralNominalState.Models (state true) (varying name) := by
  have low : ∀ slot : Fin 2, varying name slot.val = model slot.val := by
    intro slot
    simp [varying,GeneralDictionaryTerminalRefresh.varying,show slot.val ≠ name by omega]
  have assigned : GeneralNominalCommonBridge.assignment (base true) (varying name) =
      GeneralNominalCommonBridge.assignment (base true) model := by
    funext slot; exact low slot
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · change PresenceNormalForm.All CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment (base true) (varying name)) _
    rw [assigned]
    exact (state_models true).1.1
  · intro slot term recorded
    have original := (state_models true).1.2.1 slot term recorded
    change Equivalent (varying name slot.val).1 (term.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment (base true) (varying name)))
    rw [low slot,assigned]
    exact original
  · intro pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact subtype_refl _
  · intro slot descriptor recorded
    obtain ⟨values,fits,equal⟩ := (state_models true).2.1 slot descriptor recorded
    refine ⟨values,?_,?_⟩
    · have transform : ∀ parameters values, GeneralNominalState.FitsAll (state true).base model parameters values → GeneralNominalState.FitsAll (state true).base (varying name) parameters values := by
        intro parameters values fits
        induction fits with
        | nil => exact .nil
        | @cons parameter value parameters values head tail ih =>
          refine .cons ?_ ih
          cases parameter <;> cases value <;> first | exact head | simpa [GeneralNominalState.Fits,low] using head
      exact transform _ _ fits
    · simpa [low] using equal

theorem varying_model (name : Nat) (large : 2 ≤ name) : Models finish.current (varying name) :=
  models_of_source _ (varying_source name large)

/-- Every certified refresh must keep all reserved origins unknown. -/
theorem refresh_large_unknown (next : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalCycleSteps.Refresh finish.current next) (source : Nat) (large : 2 ≤ source) :
    ¬ GeneralNominalState.Known next.state source :=
  GeneralDictionaryTerminalRefresh.no_known_distinct next.state model (varying source) source
    (by change (if source = 0 then nominal 0 [.inl (.base .int)] else .base .int) = .base .int; exact ite_eq_right (by omega))
    (by simp only [varying,GeneralDictionaryTerminalRefresh.varying,ite_true]; rfl)
    (certificate.exact _ current_model) (certificate.exact _ (varying_model source large))

theorem context_complete : ContextComplete finish.current := by
  intro m valid
  obtain ⟨reserved,atoms,allocated,growth⟩ := GeneralDictionaryOrdinaryTrace.packet_extension packet
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
noncomputable abbrev leafSite := GeneralNominalFeedbackSites.childSite packet displayChild

theorem sites_exact : finish.current.sites = [rootSite,leafSite] := by
  change [rootSite] ++ packet.children.map (GeneralNominalFeedbackSites.childSite packet) = _
  rw [children_exact]; rfl

theorem edges_exact : finish.current.edges = [(displayRoot,displayChild)] := by
  change [] ++ packet.children.map (fun child => (displayRoot,child)) = _
  rw [children_exact]; rfl

theorem generated_cases (focus : GeneralSourceDictionaries.Occurrence roles)
    (generated : Generated finish.current displayRoot focus) : focus = displayRoot ∨ focus = displayChild := by
  induction generated with
  | root => exact Or.inl rfl
  | child _ member _ =>
    rw [edges_exact] at member
    have same := congrArg Prod.snd (List.mem_singleton.mp member)
    exact Or.inr same
  | alias _ _ member _ _ =>
    rw [sites_exact] at member
    rcases List.mem_cons.mp member with rfl | rest
    · exact Or.inl rfl
    · have same := List.mem_singleton.mp rest
      subst_vars
      exact Or.inr rfl

theorem sameInputs_no_cross : ¬ GeneralNominalFeedbackSites.SameInputs finish.current rootSite leafSite := by
  intro same
  have left := GeneralNominalFeedbackSites.recover_sound finish.current rootSite model current_model (point_holds displayRoot model)
  have right := GeneralNominalFeedbackSites.recover_sound finish.current leafSite model current_model
    (GeneralNominalFeedbackSites.child_sound packet displayChild model (current_model.2.1 packet (by exact List.mem_singleton_self _)))
  have relation := same.2
  change GeneralNominalDemandMerging.All₂ _
    [GeneralNominalFeedbackSites.recoverOrigin finish.current rootSite ⟨0,by decide +kernel⟩]
    [GeneralNominalFeedbackSites.recoverOrigin finish.current leafSite ⟨0,by decide +kernel⟩] at relation
  cases relation with
  | cons related _ =>
    obtain ⟨a,b,one,two,equal⟩ := related
    have firstFits := left ⟨0,by decide +kernel⟩ a (by
      change some (GeneralNominalFeedbackSites.recoverOrigin finish.current rootSite _) = some (some a)
      exact congrArg some one)
    have lastFits := right ⟨0,by decide +kernel⟩ b (by
      change some (GeneralNominalFeedbackSites.recoverOrigin finish.current leafSite _) = some (some b)
      exact congrArg some two)
    obtain ⟨x,hx⟩ := firstFits.1
    obtain ⟨y,hy⟩ := lastFits.1
    have xfit := firstFits.2 x hx
    have yfit := lastFits.2 y hy
    have sameValue := (equal model current_model).2.2 x y hx hy
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
  rw [sites_exact] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl <;> rcases two with rfl | rfl
  · exact .refl _
  · exact False.elim (sameInputs_no_cross same)
  · exact False.elim (sameInputs_no_cross (sameInputs_symm same))
  · exact .refl _


open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

private theorem parent_branch (m : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current m) :
    BranchModels registry current displayRoot display display_checked [((0 : Fin 2),(0 : Fin 2))] m := by
  obtain ⟨decl,visible,checked,key,role,bounds,located,_,_,_,_,branch⟩ := parent_instance m valid
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · contradiction
  · have found : arguments current displayRoot = some [((0 : Fin 2),(0 : Fin 2))] := by rfl
    have equal := Option.some.inj (located.symm.trans found)
    subst bounds
    exact branch
  · contradiction

private theorem leaf_branch (m : GeneralNominalCommonBridge.Assignment) (valid : Models finish.current m) :
    BranchModels registry current displayChild intDisplay int_display_checked [((1 : Fin 2),(1 : Fin 2))] m := by
  have old := ((GeneralNominalFeedbackSites.install_models start.current packet
    (GeneralNominalFeedbackSites.emitted packet) rfl m).mp valid).1.1
  have rule := GeneralDictionaryOrdinaryTrace.instance_extension registry (context true)
    current (GeneralDictionaryOrdinaryTrace.packet_extension packet) m valid.1
    displayChild 3 [] (leaf_instance m old)
  obtain ⟨decl,visible,checked,key,role,bounds,located,_,_,_,_,branch⟩ := rule
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · have found : arguments current displayChild = some [((1 : Fin 2),(1 : Fin 2))] := by rfl
    have equal := Option.some.inj (located.symm.trans found)
    subst bounds
    exact branch
  · contradiction
  · contradiction

theorem installs_committed (p : Packet roles)
    (reached : Generated finish.current displayRoot p.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry finish.current p) :
    GeneralNominalFeedbackSteps.Committed finish.current p := by
  rcases generated_cases _ reached with same | same
  · have selected := enabled.2.1
    rw [same] at selected
    have agreement := GeneralNominalFeedbackK2.local_functional selected parent_selected
    have key := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).1
    have children := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).2
    constructor
    · intro m valid
      rcases p with ⟨preg,pctx,psite,pdecl,pchecked,pbounds⟩
      have reg := enabled.1.1
      have ctx := enabled.1.2.1
      dsimp only at reg ctx
      subst preg; subst pctx
      have visible := enabled.1.2.2.2.1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with decl | decl | decl
      · subst pdecl; cases key
      · subst pdecl
        have found := enabled.1.2.2.2.2.2.1
        change arguments current psite.occurrence = some pbounds at found
        change psite.occurrence = displayRoot at same
        rw [same] at found
        have located : arguments current displayRoot = some [((0 : Fin 2),(0 : Fin 2))] := by rfl
        have equal := Option.some.inj (found.symm.trans located)
        subst pbounds
        change BranchModels registry current psite.occurrence display pchecked [((0 : Fin 2),(0 : Fin 2))] m
        rw [same]
        exact parent_branch m valid
      · subst pdecl; cases key
    · intro child member
      rw [children] at member
      have childSame := List.mem_singleton.mp member
      subst child
      rw [same,edges_exact]
      exact List.mem_singleton_self _
  · have selected := enabled.2.1
    rw [same] at selected
    have agreement := GeneralNominalFeedbackK2.local_functional selected leaf_selected
    have key := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).1
    have children := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).2
    constructor
    · intro m valid
      rcases p with ⟨preg,pctx,psite,pdecl,pchecked,pbounds⟩
      have reg := enabled.1.1
      have ctx := enabled.1.2.1
      dsimp only at reg ctx
      subst preg; subst pctx
      have visible := enabled.1.2.2.2.1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with decl | decl | decl
      · subst pdecl
        have found := enabled.1.2.2.2.2.2.1
        change arguments current psite.occurrence = some pbounds at found
        change psite.occurrence = displayChild at same
        rw [same] at found
        have located : arguments current displayChild = some [((1 : Fin 2),(1 : Fin 2))] := by rfl
        have equal := Option.some.inj (found.symm.trans located)
        subst pbounds
        change BranchModels registry current psite.occurrence intDisplay pchecked [((1 : Fin 2),(1 : Fin 2))] m
        rw [same]
        exact leaf_branch m valid
      · subst pdecl; cases key
      · subst pdecl; cases key
    · intro child member
      rw [children] at member
      cases member

theorem feedback_stable : GeneralNominalFeedbackSteps.Stable registry finish.current displayRoot := by
  intro focus generated next update
  cases update with
  | enqueue focus _ absent =>
    rcases generated_cases focus generated with same | same
    · exact absent rootSite (by rw [sites_exact]; simp) same.symm
    · exact absent leafSite (by rw [sites_exact]; simp) same.symm
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


/-- Actual source-supported recursive resolution, on the unchanged V5 Local
judgment, after one real installation. No fabricated leaf installation occurs. -/
theorem resolves : CommonRoleOutermostResolver.Resolves
    (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish)
    displayRoot (.selected 1 [.selected 3 []]) :=
  .selected ((GeneralNominalSupportBoundary.local_correspondence registry finish displayRoot _).mpr supported_parent_selected)
    (.cons (.selected ((GeneralNominalSupportBoundary.local_correspondence registry finish displayChild _).mpr supported_leaf_selected) .nil) .nil)

/-- A concrete, nonempty, genuinely recursive stable completion. This combines
actual reachability and classification with a concrete model and source Evidence
for the same payload in EVERY final model. It is not a uniform V5 executor. -/
theorem completed :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    GeneralNominalSupportSteps.Stable registry finish displayRoot ∧
    finish.current.packets ≠ [] ∧ Models finish.current model ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot (.selected (.node 1 [.node 3 []])) ∧
    ∀ m, Models finish.current m → GeneralDictionaryRecursiveEvidence.Evidence registry current m displayRoot (.node 1 [.node 3 []]) :=
  ⟨actual_reachable,stable,nonempty_journal,current_model,classified,final_recursive_evidence⟩

end Yulang.GeneralDictionarySupportRecursiveClosure
