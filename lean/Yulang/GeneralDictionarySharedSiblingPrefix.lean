import Yulang.GeneralDictionarySharedTerminalInstallation

/-! The sibling fixture's inherited capture is unique. For this packet only,
certified origin forwarding agrees with the legacy emitter. This is proved
from its capture report, not assumed for SharedSteps in general. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDictionarySharedSiblingPrefix
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSiblings
open GeneralNominalSharedCaptures GeneralNominalRecursiveInspection
open GeneralDeclarationExamples (roles)
local instance : NeZero src.base.slots := ⟨by change 1+2 ≠ 0; omega⟩
abbrev origin : Origin := .nominal (.source 0) 0 0

theorem inherited : (inheritedReport pk).captures = [⟨0,(1,1),some origin⟩] := by
  unfold inheritedReport
  rw [p_query]
  rw [inspectMany.eq_def]
  simp only [bs,List.zip_cons_cons,List.zip_nil_right,List.map_cons,List.map_nil]
  rw [inspect.eq_def]
  change (Report.append
    (Report.visit (0,0) (some (.source 0)) (.nominal 0 1)
      (inspectMany src [.variables [0]] [(1,1)]
        (fun index => some (.nominal (.source 0) 0 index)) 0))
    (inspectMany src [] [] _ 1)).captures = _
  simp only [inspectMany.eq_def,inspect.eq_def]
  rfl

theorem usable : Usable pk 0 origin :=
  GeneralNominalSharedPositive.single_capture_usable pk 0 (1,1) origin
    (by change (GeneralNominalRecursiveCandidates.report ctx p bs).captures = _; rw [p_report]; rfl)
    inherited
    (by change (origin,(1,1)) ∈ (GeneralNominalRecursiveCandidates.report ctx p bs).anchors
        rw [p_report]; simp [GeneralNominalUnaryCaptureFacts.captured,origin]; rfl)

theorem generation : GenerationGuard start pk := by
  rintro name ⟨clause,member,used⟩
  simp only [pk,p,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    have zero : name = 0 := by
      simpa [cp,wp,pp,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables] using used
    subst name
    exact ⟨origin,usable⟩

theorem input_empty : GeneralNominalPacketSupport.inputSchema pk = {} := by
  have canon : GeneralCanonicalChildOrder.canonicalDeclaration p = p := by
    change {p with requirements := GeneralCanonicalChildOrder.canonicalRequirements p.requirements} = p
    rw [sorted]
  unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canon]
  simp [root,p,cp,wp,pp,GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,GeneralDeclarationPatterns.normalize,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate]


theorem guard : GeneralNominalSharedSteps.PacketGuard start pk [] := by
  refine ⟨GeneralNominalValueSupport.source_packet start pk p_guard,
    GeneralNominalSharedPositive.initial_decision ctx root root reg [] decisions,
    generation,GeneralNominalSharedCaptures.empty_input_coherent ?_⟩
  rw [input_empty]

theorem origin_iff (child : Occurrence roles) (position : Nat) (observed : Origin) :
    GeneralNominalSharedEmission.OriginAt pk child position observed ↔
      GeneralNominalFeedbackSites.OriginAt pk child position observed := by
  constructor
  · rintro ⟨clause,member,signature,index,equal,same,name,known,pattern⟩
    obtain ⟨captured,present,named,recorded⟩ := known.1.1
    rw [inherited] at present
    cases List.mem_singleton.mp present
    have nameZero : name = 0 := named.symm
    subst name
    have originSame : observed = origin := (Option.some.inj recorded).symm
    subst observed
    refine ⟨clause,member,signature,index,equal,same,⟨0,(1,1),some origin⟩,?_,by decide +kernel,rfl,pattern⟩
    change _ ∈ (GeneralNominalRecursiveCandidates.report ctx p bs).captures
    rw [p_report]; simp [GeneralNominalUnaryCaptureFacts.captured]; rfl
  · rintro ⟨clause,member,signature,index,equal,same,captured,present,declared,recorded,pattern⟩
    change captured ∈ (GeneralNominalRecursiveCandidates.report ctx p bs).captures at present
    rw [p_report] at present
    have captureSame : captured = ⟨0,(1,1),some origin⟩ := List.mem_singleton.mp present
    subst captured
    have originSame : observed = origin := (Option.some.inj recorded).symm
    subst observed
    exact ⟨clause,member,signature,index,equal,same,0,usable,pattern⟩

theorem origin_unique (child : Occurrence roles) (position : Nat) (observed : Origin)
    (recorded : GeneralNominalFeedbackSites.OriginAt pk child position observed) : observed = origin := by
  obtain ⟨_,_,_,_,_,_,capture,member,_,found,_⟩ := recorded
  change capture ∈ (GeneralNominalRecursiveCandidates.report ctx p bs).captures at member
  rw [p_report] at member
  cases List.mem_singleton.mp member
  exact (Option.some.inj found).symm

theorem child_origin (child : Occurrence roles) (index : Fin (roles child.demand.role).arity) :
    GeneralNominalSharedEmission.childOrigin pk child index =
      GeneralNominalFeedbackSites.childOrigin pk child index := by
  classical
  unfold GeneralNominalSharedEmission.childOrigin
  split
  · rename_i available
    have oldAvailable : ∃ observed, GeneralNominalFeedbackSites.OriginAt pk child index.val observed :=
      ⟨_,(origin_iff _ _ _).mp (Classical.choose_spec available)⟩
    have newSame := origin_unique _ _ _ ((origin_iff _ _ _).mp (Classical.choose_spec available))
    simp only [GeneralNominalFeedbackSites.childOrigin,dite_eq_left oldAvailable]
    exact congrArg some (newSame.trans (origin_unique _ _ _ (Classical.choose_spec oldAvailable)).symm)
  · rfl

theorem child_site (child : Occurrence roles) :
    GeneralNominalSharedEmission.childSite pk child = GeneralNominalFeedbackSites.childSite pk child := by
  unfold GeneralNominalSharedEmission.childSite GeneralNominalFeedbackSites.childSite
  have same : GeneralNominalSharedEmission.childOrigin pk child =
      GeneralNominalFeedbackSites.childOrigin pk child := funext (child_origin child)
  simp only [same]

theorem parent_install_eq :
    GeneralNominalSharedSteps.install start pk [] = afterP := by
  unfold GeneralNominalSharedSteps.install afterP GeneralNominalSupportSteps.install
    GeneralNominalFeedbackSites.install GeneralNominalSharedEmission.emitted GeneralNominalFeedbackSites.emitted
  have sites : GeneralNominalSharedEmission.childSite pk = GeneralNominalFeedbackSites.childSite pk := funext child_site
  dsimp only
  rw [sites]

theorem parent_step : GeneralNominalSharedSteps.Step reg root start afterP := by
  rw [← parent_install_eq]
  refine ⟨root,.root,.install pk [] enabled ?_ guard⟩
  intro committed
  have absent := committed.2 kidC (by rw [p_children]; simp)
  cases absent

theorem shared_prefix :
    B4Target.Steps (GeneralNominalSharedSteps.Step reg root) start
      GeneralDictionarySharedTerminalInstallation.after :=
  .tail (.tail .refl parent_step) GeneralDictionarySharedTerminalInstallation.step

theorem shared_formed :
    GeneralNominalSharedSteps.SourceFormed reg root GeneralDictionarySharedTerminalInstallation.after :=
  .update (.update (.initial ctx initial_source) parent_step)
    GeneralDictionarySharedTerminalInstallation.step

/-- The terminal dictionary is now attached to a wholly Shared-generated prefix. -/
theorem reached_terminal_dictionary :
    B4Target.Steps (GeneralNominalSharedSteps.Step reg root) start
      GeneralDictionarySharedTerminalInstallation.after ∧
    (∃ model, Models GeneralDictionarySharedTerminalInstallation.after.current model) ∧
    ∀ model, Models GeneralDictionarySharedTerminalInstallation.after.current model →
      GeneralDictionaryRecursiveEvidence.Evidence reg
        GeneralDictionarySharedTerminalInstallation.after.current.context model kidC (.node c.id []) :=
  ⟨shared_prefix,GeneralDictionarySharedTerminalInstallation.inhabited,
    GeneralDictionarySharedTerminalInstallation.current_dictionary⟩

end Yulang.GeneralDictionarySharedSiblingPrefix
