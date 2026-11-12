import Yulang.GeneralDictionaryJournalTreeFormation
/-! Exact source-preserving scalar refresh after the genuine terminal output
installation, with actual feedback stability and current-context source evidence.
Reserved identities remain unknown because they retain different scalar models;
no artificial observation or fixed-view transport theorem is used. -/
namespace Yulang.GeneralDictionaryTerminalRefresh
open GeneralDictionaryRecursiveObstruction
open GeneralDictionaryCommittedEvidenceExamples (packet)
open GeneralDictionaryJournalTreeExamples
open GeneralNominalSaturationState CommonNominalFullCarrier

noncomputable abbrev nextState : GeneralNominalState.State :=
  { GeneralNominalExamples.state true with
    reserved := after.context.state.reserved
    ordinary := after.context.state.ordinary
    allocated := after.context.state.allocated }
noncomputable abbrev nextContext : GeneralNominalCandidates.Context := ⟨nextState,context.interpretation⟩
noncomputable abbrev refreshed := regenerate after nextContext

noncomputable def refines : GeneralNominalRefinements.Refines after.context.state nextState := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · refine ⟨id,(by intro _; rfl),(by intro _; rfl),?_,?_,?_⟩
    · intro atom member; cases member
    · intro slot known; exact False.elim (known (by change (GeneralNominalExamples.heads false slot).node = _; simp only [GeneralNominalExamples.heads,Bool.false_eq_true,and_false,ite_false,GeneralSourceState.Head.node]; rfl))
    · intro pair member; exact member
  · intro slot term recorded
    change (GeneralNominalExamples.heads false slot).equation = some term at recorded
    simp [GeneralNominalExamples.heads,GeneralSourceState.Head.equation] at recorded
  · intro slot descriptor recorded
    change Fin 2 at slot
    change (if slot = (0 : Fin 2) then some GeneralNominalExamples.listDescriptor else none) = some descriptor at recorded
    by_cases zero : slot = (0 : Fin 2)
    · subst slot
      have same := Option.some.inj recorded
      subst descriptor
      rfl
    · simp [zero] at recorded
  · intro atom member; exact member
  · intro source known
    obtain ⟨slot,same,head | nominal⟩ := known
    · exact False.elim (head (by change ((GeneralNominalExamples.view false).heads slot).node = _; simp only [Bool.false_eq_true,and_false,ite_false,GeneralNormalizedObservation.Head.node]; rfl))
    · exact ⟨slot,same,Or.inr nominal⟩
  · intro source member; exact member
  · intro key member; exact member

theorem output_int (m : GeneralNominalCommonBridge.Assignment) (valid : Models after m) :
    Equivalent (m 1).1 (.base .int) :=
  (branch_iff_output m).mp ((GeneralNominalFeedbackSites.install_models _ packet _ rfl m).mp valid).2 |>.2

noncomputable def certificate : GeneralNominalCycleSteps.Refresh after nextContext where
  refines := refines
  interpretation := rfl
  exact := by
    intro m valid
    have equal := output_int m valid
    refine ⟨⟨?_,?_,valid.1.1.2.2⟩,?_,valid.1.2.2⟩
    · intro atom member
      change atom ∈ GeneralSourceState.equationAtoms (1 : Fin 2) (.base .int) at member
      simp only [GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact equal.1
      · exact equal.2
    · intro slot term recorded
      by_cases one : slot = (1 : Fin 2)
      · subst slot
        have same : term = .base .int := Option.some.inj recorded.symm
        subst term
        exact equal
      · simp [nextState,GeneralNominalExamples.heads,one,GeneralSourceState.Head.equation] at recorded
    · intro slot descriptor recorded
      change (if slot = (0 : Fin 2) then some GeneralNominalExamples.listDescriptor else none) = some descriptor at recorded
      by_cases zero : slot = (0 : Fin 2)
      · subst slot
        have same := Option.some.inj recorded
        subst descriptor
        obtain ⟨values,fits,equal⟩ := valid.1.2.1 (0 : Fin 2) GeneralNominalExamples.listDescriptor rfl
        have transform : ∀ parameters values,
            GeneralNominalState.FitsAll after.context.state.base m parameters values →
            GeneralNominalState.FitsAll nextState.base m parameters values := by
          intro parameters values given
          induction given with
          | nil => exact .nil
          | @cons parameter value parameters values head tail ih =>
            refine .cons ?_ ih
            cases parameter <;> cases value <;> exact head
        exact ⟨values,transform _ _ fits,equal⟩
      · simp [zero] at recorded
  support := by intro source member; exact member

theorem source_known : GeneralNominalState.Known nextState 1 :=
  ⟨1,rfl,Or.inl (by decide +kernel)⟩

theorem source_unknown : ¬ GeneralNominalState.Known after.context.state 1 := by
  rintro ⟨slot,same,head | ⟨descriptor,recorded⟩⟩
  · exact head (by change ((GeneralNominalExamples.view false).heads slot).node = _; simp only [Bool.false_eq_true,and_false,ite_false,GeneralNormalizedObservation.Head.node]; rfl)
  · have one : slot = (1 : Fin 2) := Fin.ext same
    subst slot
    cases recorded

theorem actual_refresh : GeneralNominalFeedbackSteps.Step registry root after refreshed := by
  refine ⟨root,.root,.refresh root nextContext certificate 1 ?_ source_unknown source_known⟩
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(1 : Fin 2),rfl⟩)))

theorem exact_models (m : GeneralNominalCommonBridge.Assignment) : Models refreshed m ↔ Models after m :=
  GeneralNominalCycleSteps.refresh_models certificate m

theorem formed : GeneralNominalFeedbackSteps.SourceFormed registry root refreshed :=
  .update GeneralDictionaryJournalTreeFormation.formed_after actual_refresh

theorem inhabited : Models refreshed GeneralNominalExamples.model := (exact_models _).mpr good_after

theorem context_complete : ContextComplete refreshed := by
  intro m valid
  have original : GeneralNominalState.Models context.state m :=
    (GeneralNominalRefinements.models refines m valid).1 |> fun base => ⟨base,(GeneralNominalRefinements.models refines m valid).2.1,PresenceNormalForm.all_nil _ _⟩
  have int : Equivalent (m 1).1 (.base .int) := by
    exact valid.1.2.1 (1 : Fin 2) (.base .int) rfl
  have branch := (branch_iff_output m).mpr ⟨original,int⟩
  refine ⟨valid,?_,?_⟩
  · intro p member
    have same : p = packet := List.mem_singleton.mp member
    subst p
    exact branch
  · intro site member
    have same : site = GeneralNominalDemandMerging.pointSite root := by
      simpa [refreshed,regenerate,after,GeneralNominalFeedbackSites.install,
        GeneralNominalFeedbackSites.emitted,GeneralDictionaryCommittedEvidenceExamples.before,initial,GeneralDictionaryCommittedEvidenceExamples.packet_children] using member
    subst site
    exact point_holds root m
private theorem int_not_nominal (name : Nat) (arguments : List Argument) : ¬ Subtype (.base .int) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

private theorem int_not_shape (shape : GeneralNormalizedObservation.Shape)
    (children : Fin shape.arity → Fin slots)
    (assignment : Fin slots → Core.PresenceGeneration.Comp CommonNominalFullCarrier.model) :
    ¬ Subtype (.base .int) ((shape.term children).eval CommonNominalFullCarrier.model assignment) := by
  intro below
  let role : CommonNominalFullDemand.Head := match shape with
    | .pair => .pair | .variant tag => .variant tag | _ => .records
  have probe := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => [role]⟩ (.role 0)
  cases shape with
  | pair | variant | exactEmpty =>
    simp [role, GeneralNormalizedObservation.Shape.term,Core.PresenceGeneration.TyTerm.eval,
      CommonNominalFullCarrier.model,CommonNominalFullCarrier.pair,CommonNominalFullCarrier.variant,observeTy,CommonNominalSyntax.Layer.evalAt,
      CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep] at probe
  | record labels =>
    cases labels <;>
      simp [role, GeneralNormalizedObservation.Shape.term,GeneralNormalizedObservation.recordTerm,List.ofFn_succ,
        Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model,CommonNominalFullCarrier.record,
        observeTy,CommonNominalSyntax.Layer.evalAt,CommonNominalFullDemand.ProbeAt,
        CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep] at probe

/-- Two distinct scalar models prevent any certified known normalized head. -/
theorem no_known_distinct (state : GeneralNominalState.State)
    (first second : GeneralNominalCommonBridge.Assignment) (sourceName : Nat)
    (firstAt : (first sourceName).1 = .base .int) (secondAt : (second sourceName).1 = .base .str)
    (one : GeneralNominalState.Models state first)
    (two : GeneralNominalState.Models state second) :
    ¬ GeneralNominalState.Known state sourceName := by
  rintro ⟨slot,source,head | ⟨descriptor,recorded⟩⟩
  · have seen1 := GeneralNominalState.normalized_models state _ one
    have seen2 := GeneralNominalState.normalized_models state _ two
    cases equation : state.view.heads slot with
    | deferred reason => exact head (by simp [GeneralNormalizedObservation.Snapshot.graph,equation,GeneralNormalizedObservation.Head.node])
    | scalar base =>
      have a := seen1 slot (.base base) (by simp [equation,GeneralNormalizedObservation.Head.term])
      have b := seen2 slot (.base base) (by simp [equation,GeneralNormalizedObservation.Head.term])
      have x : Equivalent (.base .int) (.base base) := by simpa [source,firstAt,secondAt,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model] using a
      have y : Equivalent (.base .str) (.base base) := by simpa [source,firstAt,secondAt,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model] using b
      exact bad_output_equation ⟨subtype_trans y.1 x.2,subtype_trans x.1 y.2⟩
    | structural kind children =>
      have a := seen1 slot ((state.view.shapes kind).term children) (by simp [equation,GeneralNormalizedObservation.Head.term])
      exact int_not_shape _ children _ (by simpa [source,firstAt,secondAt,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model] using a.1)
  · obtain ⟨values,_,equal⟩ := one.2.1 slot descriptor recorded
    exact int_not_nominal _ _ (by simpa [GeneralNominalState.Denotes,source,firstAt] using equal.1)




abbrev varying (name : Nat) : GeneralNominalCommonBridge.Assignment :=
  fun source => if source = name then (.base .str,Common.rowEmpty) else GeneralNominalExamples.model source

theorem varying_original (name : Nat) (large : 2 ≤ name) : GeneralNominalState.Models context.state (varying name) := by
  have low : ∀ slot : Fin 2, varying name slot.val = GeneralNominalExamples.model slot.val := by
    intro slot
    simp [varying,show slot.val ≠ name by omega]
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro slot term recorded
    simp [GeneralNominalExamples.heads,GeneralSourceState.Head.equation] at recorded
  · intro pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact subtype_refl _
  · intro slot descriptor recorded
    have original := (GeneralNominalExamples.state_models false).2.1 slot descriptor recorded
    obtain ⟨values,fits,equal⟩ := original
    refine ⟨values,?_,?_⟩
    · have transform : ∀ parameters values, GeneralNominalState.FitsAll context.state.base GeneralNominalExamples.model parameters values → GeneralNominalState.FitsAll context.state.base (varying name) parameters values := by
        intro parameters values fits
        induction fits with
        | nil => exact .nil
        | @cons parameter value parameters values head tail ih =>
          refine .cons ?_ ih
          cases parameter <;> cases value <;> first | exact head | simpa [GeneralNominalState.Fits,low] using head
      exact transform _ _ fits
    · simpa [low] using equal

theorem varying_model (name : Nat) (large : 2 ≤ name) : Models refreshed (varying name) := by
  apply (exact_models _).mpr
  apply (GeneralNominalFeedbackSites.install_models _ packet _ rfl _).mpr
  refine ⟨(initial_models _ _ _).mpr (varying_original name large),?_⟩
  apply (branch_iff_output _).mpr
  exact ⟨varying_original name large,by simpa [varying,show 1 ≠ name by omega] using
    (show Equivalent (.base .int) (.base .int) from ⟨subtype_refl _,subtype_refl _⟩)⟩

theorem refresh_large_unknown (next : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalCycleSteps.Refresh refreshed next) (source : Nat) (large : 2 ≤ source) :
    ¬ GeneralNominalState.Known next.state source :=
  no_known_distinct next.state GeneralNominalExamples.model (varying source) source
    (by change (if source = 0 then nominal 0 [.inl (.base .int)] else .base .int) = .base .int; exact ite_eq_right (by omega)) (by simp only [varying,ite_true]; rfl)
    (certificate.exact _ inhabited) (certificate.exact _ (varying_model source large))

theorem current_query : GeneralNominalInspection.queries nextState context.interpretation declaration = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem current_schema : GeneralNominalRecursiveCandidates.generated registry nextContext root declaration declaration_checked [(0,0)] =
    { tests := [(.source 1,.scalar .int)] } := by
  unfold GeneralNominalRecursiveCandidates.generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem every_current_branch (m : GeneralNominalCommonBridge.Assignment) (valid : Models refreshed m) :
    GeneralNominalRecursiveCandidates.BranchModels registry nextContext root declaration declaration_checked [(0,0)] m := by
  have privateModel := GeneralNominalUnaryCaptureFacts.private_models nextContext registry root declaration 0
    GeneralNominalExamples.listDescriptor rfl 0 rfl (1,1) rfl current_query m valid.1
  refine ⟨privateModel.1,privateModel.2,?_⟩
  rw [current_schema]
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    have same := List.mem_singleton.mp member
    subst test
    refine ⟨⟨_,.source 1⟩,?_⟩
    intro actual observed
    cases observed
    exact output_int m ((exact_models m).mp valid)
  · intro entry member; cases member
  · intro entry member; cases member
  · intro entry member; cases member

theorem installs_committed (p : Packet GeneralDeclarationExamples.roles)
    (same : p.site.occurrence = root) (enabled : GeneralNominalFeedbackSteps.Installable registry refreshed p) :
    GeneralNominalFeedbackSteps.Committed refreshed p := by
  rcases p with ⟨preg,pcontext,psite,pdecl,pchecked,pbounds⟩
  have ctx := enabled.1.2.1
  have reg := enabled.1.1
  have decl : pdecl = declaration := List.mem_singleton.mp enabled.1.2.2.2.1
  dsimp only at ctx reg
  subst preg; subst pcontext; subst pdecl
  have found := enabled.1.2.2.2.2.2.1
  change GeneralNominalRecursiveCandidates.arguments refreshed.context psite.occurrence = some pbounds at found
  change psite.occurrence = root at same
  rw [same] at found
  have located : GeneralNominalRecursiveCandidates.arguments refreshed.context root = some [((0 : Fin 2),(0 : Fin 2))] := by rfl
  have bounds := (Option.some.inj (found.symm.trans located))
  subst pbounds
  constructor
  · intro m valid
    change GeneralNominalRecursiveCandidates.BranchModels registry refreshed.context psite.occurrence declaration pchecked [((0 : Fin 2),(0 : Fin 2))] m
    rw [same]
    exact every_current_branch m valid
  · intro child member
    change child ∈ GeneralNominalAllocation.children refreshed.context.state registry psite.occurrence declaration pchecked
      (GeneralNominalRecursiveInspection.bindings refreshed.context.state
        (GeneralNominalRecursiveCandidates.report refreshed.context declaration [((0 : Fin 2),(0 : Fin 2))])) at member
    unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit at member
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil] at member
    change child ∈ [] at member
    cases member

theorem generated_only_root (child : GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles)
    (generated : Generated refreshed root child) : child = root := by
  induction generated with
  | root => rfl
  | child _ member _ =>
    have empty : refreshed.edges = [] := by
      simp [refreshed,regenerate,after,GeneralNominalFeedbackSites.install,GeneralDictionaryCommittedEvidenceExamples.before,initial,
        GeneralDictionaryCommittedEvidenceExamples.packet_children]
    rw [empty] at member
    cases member
  | alias _ _ member _ _ =>
    have single : refreshed.sites = [GeneralNominalDemandMerging.pointSite root] := by
      simp [refreshed,regenerate,after,GeneralNominalFeedbackSites.install,GeneralDictionaryCommittedEvidenceExamples.before,initial,
        GeneralNominalFeedbackSites.emitted,GeneralDictionaryCommittedEvidenceExamples.packet_children]
    rw [single] at member
    exact congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp member)

theorem stable : GeneralNominalFeedbackSteps.Stable registry refreshed root := by
  intro focus generated next update
  have same := generated_only_root focus generated
  have single : refreshed.sites = [GeneralNominalDemandMerging.pointSite root] := by
    simp [refreshed,regenerate,after,GeneralNominalFeedbackSites.install,GeneralDictionaryCommittedEvidenceExamples.before,initial,
      GeneralNominalFeedbackSites.emitted,GeneralDictionaryCommittedEvidenceExamples.packet_children]
  cases update with
  | enqueue focus _ absent => exact absent (GeneralNominalDemandMerging.pointSite root) (by rw [single]; exact List.mem_singleton_self _) same.symm
  | install p enabled novel => exact novel (installs_committed p same enabled)
  | merge first last one two _ novel =>
    rw [single] at one two
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)
  | refresh _ next certificate source member unknown known =>
    by_cases zero : source = 0
    · subst source
      exact unknown ⟨(0 : Fin 2),rfl,Or.inr ⟨GeneralNominalExamples.listDescriptor,rfl⟩⟩
    · by_cases one : source = 1
      · subst source
        exact unknown source_known
      · exact refresh_large_unknown next certificate source (by omega) known
  | equate _ first last _ _ equal novel =>
    exact novel (fun m valid => equal m (context_complete m valid))

theorem current_instance (m : GeneralNominalCommonBridge.Assignment) (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Instance registry nextContext m root 40 [] := by
  refine ⟨declaration,by simp,declaration_checked,rfl,rfl,[(0,0)],rfl,?_,?_,?_,?_,every_current_branch m valid⟩
  · have report := GeneralNominalUnaryCaptureFacts.report_exact nextContext declaration 0
      GeneralNominalExamples.listDescriptor rfl 0 (1,1) rfl current_query
    rw [report]
    exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      have same := List.mem_singleton.mp member
      subst output
      exact ⟨equation,by simp,rfl⟩
    · rw [current_schema]
  · unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
    rfl
  · exact metadata

/-- Same terminal payload, independently rechecked at the refreshed context. -/
theorem current_evidence (m : GeneralNominalCommonBridge.Assignment) (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Evidence registry refreshed.context m root (.node 40 []) :=
  (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry nextContext m root 40).mpr (current_instance m valid)

/-- An actual source-formed, stable and inhabited positive completion. -/
theorem completed : GeneralNominalFeedbackSteps.SourceFormed registry root refreshed ∧
    GeneralNominalFeedbackSteps.Stable registry refreshed root ∧ Models refreshed GeneralNominalExamples.model ∧
    (∀ m, Models refreshed m → GeneralDictionaryRecursiveEvidence.Evidence registry refreshed.context m root (.node 40 [])) :=
  ⟨formed,stable,inhabited,current_evidence⟩
end Yulang.GeneralDictionaryTerminalRefresh
