import Yulang.GeneralNominalCenteredTerminalObservations
import Yulang.GeneralDictionaryEarlyMergeClosure
import Yulang.GeneralNominalGroundExamples
import Yulang.GeneralNominalPeelingExamples
import Yulang.GeneralNominalCenteredModelExtension
import Yulang.GeneralNominalCenteredRegisteredLocal
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! A registered Display root retains the two certified descriptor choices.
All branch and center equations in this fixture are source consequences. -/
namespace Yulang.GeneralNominalCenteredRegisteredFork
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenteredSteps GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates CommonNominalFullCarrier
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalCenteredTerminalForkSource (base view snapshot context registry descriptor bounds observer metadata
  registry_checked scalar models_forward models_iff point_closed)
open GeneralNominalCenteredTerminalObservations (target child model source_model query report_exact children_exact survivor)

abbrev start := initial (context none) observer
abbrev revised (side : Bool) := refresh start (context (some side))
abbrev packet (side : Bool) : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context (some side),GeneralNominalDemandMerging.pointSite observer,display,display_checked,[(0,0)]⟩
abbrev plan (side : Bool) : Plan roles :=
  ⟨packet side,rootSite (snapshot none).seed observer,rfl⟩
noncomputable abbrev finish (side : Bool) := install (revised side) (plan side) []

private theorem root_linked (choice) : GeneralNominalState.Linked (snapshot choice) observer.demand := by
  constructor
  · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
  · intro output member; cases member

theorem source : GeneralNominalSourceFormation.InitialSource registry (context none) observer :=
  { GeneralNominalCenteredTerminalForkSource.source none with
    linked := root_linked none
    intervals := fun _ _ _ => subtype_refl _ }

def revision (side : Bool) : GeneralNominalReobservationSteps.Revision start.erased.current :=
  { GeneralNominalCenteredTerminalForkSource.revision side with }

theorem revision_certified (side : Bool) : GeneralNominalReobservationSteps.Certified (revision side) where
  raw := models_forward (some side) none
  exact := by
    intro m
    change GeneralNominalSaturationState.Models (GeneralNominalSaturationState.initial (context (some side)) observer) m ↔
      GeneralNominalSaturationState.Models (GeneralNominalSaturationState.initial (context none) observer) m
    rw [GeneralNominalSaturationState.initial_models,GeneralNominalSaturationState.initial_models]
    exact models_iff (some side) none m

theorem revise_step (side : Bool) : Step registry observer start (revised side) :=
  ⟨observer,.root,.administrative observer _ (.reobserve observer (revision side)
    (revision_certified side) (GeneralNominalCenteredTerminalForkSource.revision_improves side))⟩

theorem branch (side : Bool) (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (snapshot (some side)) m) : (packet side).Holds m := by
  change BranchModels registry (context (some side)) observer display display_checked [(0,0)] m
  have privateModels := GeneralNominalUnaryCaptureFacts.private_models (context (some side)) registry observer
    display 0 (descriptor (some side)) rfl 0 rfl (bounds (some side)) rfl (query side) m valid
  refine ⟨privateModels.1,privateModels.2,?_⟩
  rw [GeneralNominalRecursiveExamples.display_schema registry (context (some side)) observer rfl display_checked [(0,0)]]
  exact GeneralNominalMaterialization.empty_models ..

theorem bindings (side : Bool) : (packet side).bindings = [(0,(target side,target side))] := by
  change GeneralNominalRecursiveInspection.bindings _ (report (context (some side)) display [(0,0)]) = _
  rw [report_exact]; cases side <;> rfl

theorem packet_children (side : Bool) : (packet side).children = [child side] := by
  unfold GeneralNominalSaturationState.Packet.children
  rw [bindings]
  exact children_exact side

theorem binder (side : Bool) : (plan side).binder 0 = target side := by
  unfold Plan.binder GeneralNominalPacketSupport.capture
  change (if 0 ∈ display.outputNames then _ else _) = _
  simp only [show ¬ 0 ∈ display.outputNames from by decide +kernel,ite_false]
  rw [bindings]
  simp [GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences]

theorem head_schema (side : Bool) : (plan side).headSchema =
    ⟨[⟨0,.nominal (.source 0) 0 0,.actual⟩],[(.source 0,.nominal 0 1)],false⟩ := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,plan,rootSite,observer,GeneralNominalExamples.displayRoot,
    GeneralNominalExamples.displayDemand,roles,GeneralDeclarationExamples.bareRole,List.ofFn_succ]

theorem input_empty (side : Bool) : GeneralNominalPacketSupport.inputSchema (packet side) = {} := by
  have sorted : GeneralCanonicalChildOrder.canonicalDeclaration display = display := by
    simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
      display,List.mergeSort_singleton]
  unfold GeneralNominalPacketSupport.inputSchema GeneralNominalPacketSupport.inputRequests
  change GeneralNominalMaterialization.generated _ _
    ((GeneralCanonicalChildOrder.canonicalEmit observer.identity display display_checked _ _).flatMap _) = _
  simp only [GeneralCanonicalChildOrder.canonicalEmit,sorted]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,normalize,
    GeneralNominalMaterialization.generated,display,GeneralDeclarationExamples.displayChild]

theorem named_empty (side : Bool) : GeneralNominalPacketSupport.namedSchema (packet side) = {} := by
  change generated registry (context (some side)) observer display display_checked [(0,0)] = {}
  exact GeneralNominalRecursiveExamples.display_schema registry (context (some side)) observer rfl display_checked [(0,0)]

abbrev centerChild (side : Bool) : Site roles := ⟨child side,fun _ => target side⟩

theorem child_site (side : Bool) : (plan side).childSite GeneralDeclarationExamples.displayChild
    (display_checked.signature.2.2.2 _ (List.mem_singleton_self _)) = centerChild side := by
  unfold Plan.childSite centerChild
  congr 1
  · have member := GeneralNominalCenteredTrace.clauseChild_mem (packet side) GeneralDeclarationExamples.displayChild
      (List.mem_singleton_self _) (display_checked.signature.2.2.2 _ (List.mem_singleton_self _))
    rw [packet_children] at member
    exact List.mem_singleton.mp member
  · funext index
    have zero : index.val = 0 := by have bounded := index.isLt; change index.val < 1 at bounded; omega
    simpa only [zero,GeneralDeclarationExamples.displayChild,List.getElem_cons_zero,
      Plan.emittedCenter,normalize] using binder side

theorem emitted (side : Bool) : (plan side).emitted = [centerChild side] := by
  change [(plan side).childSite GeneralDeclarationExamples.displayChild _] = _
  rw [child_site]

private theorem fit_length {base : GeneralSourceState.State} {m : GeneralNominalCommonBridge.Assignment}
    {parameters : List (GeneralNominalState.Parameter base.slots)} {values : List CommonNominalFullCarrier.Argument}
    (fit : GeneralNominalState.FitsAll base m parameters values) : parameters.length = values.length := by
  induction fit with
  | nil => rfl
  | cons head rest ih => exact congrArg Nat.succ ih

theorem equations (side : Bool) (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (snapshot (some side)) m) : (plan side).Equations m := by
  have seen := nominal_argument_bounds (snapshot (some side)) m valid 0 (descriptor (some side)) rfl 0
    (bounds (some side)) rfl
  have actual : GeneralNominalOriginTerms.Same m (.nominal (.source 0) 0 0) (.source (target side)) := by
    refine ⟨seen.1,⟨_,.source _⟩,?_⟩
    intro a b ha hb
    cases hb
    have fit := seen.2 a ha
    cases side <;> exact ⟨fit.2,fit.1⟩
  refine ⟨point_root_holds _ observer (fun _ => rfl) m,?_,?_,?_,?_,?_⟩
  · intro name used
    have zero : name = 0 := by
      rcases used with used | ⟨clause,member,used⟩
      · simpa [packet,display,Declaration.inputNames,variablesArgs,Pattern.variables,normalizeArgs,normalize] using used
      · cases List.mem_singleton.mp member
        simpa [GeneralDeclarationExamples.displayChild,variablesArgs,Pattern.variables,normalizeArgs,normalize] using used
    subst name
    rw [binder]
    change GeneralNominalCaptureMerges.Fits m ((GeneralNominalPacketSupport.capture (packet side)).inputs 0) _
    unfold GeneralNominalPacketSupport.capture
    rw [bindings]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    constructor
    · intro entry member
      cases List.mem_singleton.mp member
      obtain ⟨arguments,fit,equal⟩ := valid.2.1 0 (descriptor (some side)) rfl
      have length : arguments.length = 1 := (fit_length fit).symm
      exact ⟨⟨_,.source 0⟩,by intro value observed; cases observed; exact ⟨arguments,length,equal⟩⟩
    · intro entry member
      cases List.mem_singleton.mp member
      simp only [ite_true]
      rw [binder]
      exact actual
  · rw [input_empty]
    exact ⟨(by intro _ member; cases member),(by intro _ member; cases member)⟩
  · rw [named_empty]
    exact ⟨(by intro _ member; cases member),(by intro _ member; cases member)⟩
  · intro clause member signature
    cases List.mem_singleton.mp member
    constructor
    · rw [child_site]
      intro index; exact ⟨subtype_refl _,subtype_refl _⟩
    · change (plan side).SchemaHolds (GeneralNominalMaterialization.generated _ _
        [⟨.var 0,(plan side).binder 0,.actual⟩]) m
      simp only [GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
        GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,
        normalize,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,List.append_nil,Plan.SchemaHolds]
      refine ⟨(by intro _ member; cases member),?_⟩
      intro entry member
      cases List.mem_singleton.mp member
      exact GeneralNominalOriginTerms.source_self m _


theorem models_of_source (side : Bool) (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (snapshot (some side)) m) : Models (finish side) m :=
  (install_models (plan := plan side) (state := revised side) (support := []) rfl m).mpr
    ⟨(point_initial_models (context (some side)) observer (fun _ => rfl) m).mpr valid,
      branch side m valid,equations side m valid⟩

private def height (name : Nat) : Nat := if name = 0 then 1 else 0
private theorem model_height (name : Nat) : (model name).1 = GeneralNominalOutputGrowth.tower (height name) := by
  by_cases zero : name = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

private theorem no_raw_cycle (state : GeneralNominalSaturationState.State roles)
    (valid : GeneralNominalSaturationState.Models state model)
    (noStructural : ∀ first last, ¬ GeneralNominalFeedbackK2.Structural state first last)
    (slot : Fin state.context.state.base.slots) : ¬ GeneralNominalCycleK2.RecursAt state.context.state slot := by
  have acyclic := GeneralNominalOutputGrowthModels.feedback_acyclic state model valid height model_height noStructural
  have edge {first last} (given : GeneralNominalMixedRecurrence.Edge state.context.state first last) :
      GeneralNominalFeedbackK2.Edge state (state.context.state.base.source first) (state.context.state.base.source last) := by
    refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨first,rfl⟩))),
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨last,rfl⟩))),?_⟩
    rcases given with structural | argument
    · exact Or.inl ⟨first,last,structural,GeneralNominalFeedbackK2.equal_refl _ _,GeneralNominalFeedbackK2.equal_refl _ _⟩
    · exact Or.inr (GeneralNominalFeedbackK2.actual_argument state first last argument)
  have path {first last} (given : GeneralNominalMixedRecurrence.Path state.context.state first last) :
      GeneralNominalFeedbackK2.Path state (state.context.state.base.source first) (state.context.state.base.source last) := by
    induction given with
    | nil => exact .nil _
    | cons head tail ih => exact .cons (edge head) ih
  intro recurrent
  obtain ⟨next,first,rest⟩ := GeneralNominalCycleK2.recurs_cycle _ _ recurrent
  exact acyclic _ ⟨_,edge first,path rest⟩

private theorem no_root (state : GeneralNominalSaturationState.State roles)
    (valid : GeneralNominalSaturationState.Models state model)
    (noStructural : ∀ first last, ¬ GeneralNominalFeedbackK2.Structural state first last)
    (demand) : ¬ GeneralNominalFeedbackK2.RootK2 state demand := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · exact no_raw_cycle state valid noStructural slot cycle
  · exact GeneralNominalOutputGrowthModels.feedback_acyclic state model valid height model_height noStructural _ cycle

private theorem no_candidate (state : GeneralNominalSaturationState.State roles)
    (valid : GeneralNominalSaturationState.Models state model)
    (noStructural : ∀ first last, ¬ GeneralNominalFeedbackK2.Structural state first last)
    (demand) : ¬ GeneralNominalFeedbackK2.CandidateK2 registry state demand := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw_cycle state valid noStructural visited.1 cycle
  · exact GeneralNominalOutputGrowthModels.feedback_acyclic state model valid height model_height noStructural _ cycle

private theorem revised_no_structural (side : Bool) (first last) :
    ¬ GeneralNominalFeedbackK2.Structural (revised side).erased.current first last := by
  rintro ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind

private theorem final_no_structural (side : Bool) (first last) :
    ¬ GeneralNominalFeedbackK2.Structural (finish side).erased.current first last := by
  rintro ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind

private theorem revised_model (side : Bool) : Models (revised side) model :=
  (point_initial_models (context (some side)) observer (fun _ => rfl) model).mpr (source_model _)

private theorem no_legacy (state : GeneralNominalState.State) (kinds : state.view.kinds = 0)
    (interpretation : GeneralNominalInspection.Interpretation) (demand : Occurrence roles) :
    ¬ (GeneralNominalLocalBoundary.recursiveFields roles).RootK2 registry ⟨state,interpretation⟩ demand ∧
    ¬ (GeneralNominalLocalBoundary.recursiveFields roles).CandidateK2 registry ⟨state,interpretation⟩ demand := by
  constructor
  · rintro ⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩; exact Fin.elim0 (kinds ▸ kind)
  · rintro ⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩; exact Fin.elim0 (kinds ▸ kind)

private theorem revised_selected (side : Bool) :
    GeneralNominalFeedbackK2.Local registry (revised side).erased.current observer (.selected 1 [child side]) := by
  obtain ⟨ready,decl,visible,checked,key,role,intervals,located,prepared,kids⟩ := survivor side
  have declaration : decl = display := List.mem_singleton.mp visible
  subst decl
  refine .selected ⟨ready,no_root _ (revised_model side).1 (revised_no_structural side) _,
    no_candidate _ (revised_model side).1 (revised_no_structural side) _,?_⟩ ⟨survivor side,?_⟩
  · rintro (⟨_,decl,visible,checked,_,_,unprepared⟩ | ⟨_,legacy⟩)
    · cases List.mem_singleton.mp visible; exact unprepared prepared
    · exact legacy.elim (fun h => (no_legacy _ rfl _ _).1 h.1) (fun h => (no_legacy _ rfl _ _).2 h.1)
  · intro other children found
    have copy := found
    obtain ⟨_,decl,visible,check,identity,_⟩ := found
    cases List.mem_singleton.mp visible
    have same : other = 1 := identity.symm
    subst other
    exact ⟨rfl,survivor_children_functional registry registry_checked _ _ _ _ _
      copy (survivor side)⟩


private theorem all_heads (side : Bool) (slot : Fin 3) :
    ∃ test old current, GeneralNominalSupport.Head (snapshot none) slot.val test old ∧
      GeneralNominalSupport.Head (snapshot (some side)) slot.val test current := by
  by_cases zero : slot = 0
  · subst slot
    exact ⟨_,_,_,GeneralNominalSupport.Head.nominal (snapshot := snapshot none) 0 (descriptor none) rfl,
      GeneralNominalSupport.Head.nominal (snapshot := snapshot (some side)) 0 (descriptor (some side)) rfl⟩
  · exact ⟨_,_,_,GeneralNominalSupport.Head.scalar (snapshot := snapshot none) slot .int (by simp [view,zero]),
      GeneralNominalSupport.Head.scalar (snapshot := snapshot (some side)) slot .int (by simp [view,zero])⟩

private theorem raw_decision (side : Bool) :
    GeneralNominalSupport.DecisionGuard (revised side).erased registry observer [] := by
  refine ⟨(by intro _ member; cases member),?_,?_⟩
  · intro index
    obtain ⟨test,old,current,one,two⟩ := all_heads side 0
    exact GeneralNominalSupport.source_ready _ _ _ _ _ one two []
  · intro decl member role intervals located slot visited
    obtain ⟨test,old,current,one,two⟩ := all_heads side slot
    exact GeneralNominalSupport.source_ready _ _ _ _ _ one two []

private theorem decision (side : Bool) : DecisionGuard registry (revised side) observer := by
  apply GeneralNominalCenteredSupport.legacy_decision
  have ready (slot : Fin 3) : GeneralNominalSharedSupport.ReadyAt (revised side).erased slot.val := by
    obtain ⟨test,old,current,one,two⟩ := all_heads side slot
    exact ⟨test,current,two,GeneralNominalSharedSupport.source_head _ one⟩
  exact ⟨fun _ => ready 0,fun _ _ _ _ _ slot _ => ready slot⟩

private theorem revised_acyclic (side : Bool) (origin) : ¬ Cyclic (revised side) origin := by
  apply GeneralNominalCenteredSteps.initial_acyclic (context (some side)) observer
  exact GeneralNominalOutputGrowthModels.feedback_acyclic _ model (revised_model side).1 height model_height (revised_no_structural side)

theorem revised_local (side : Bool) : GeneralNominalCenteredAdministrativeLocal.Local registry
    (revised side) observer (.selected 1 [child side]) := by
  apply (GeneralNominalCenteredAdministrativeLocal.selected_iff).mpr
  exact ⟨GeneralNominalCenteredBoundary.selected_of_old (revised_selected side) (revised_acyclic side) (decision side),
    GeneralNominalCenteredAdministrativeLocal.initial_ready (context (some side)) observer⟩

private theorem enabled (side : Bool) :
    GeneralNominalFeedbackSteps.Installable registry (revised side).erased.current (packet side) := by
  obtain ⟨_,decl,visible,checked,key,role,intervals,located,prepared,kids⟩ := survivor side
  cases List.mem_singleton.mp visible
  have locatedRoot : arguments (context (some side)) observer = some [(0,0)] := by
    change arguments (context none) observer = some [(0,0)]
    decide +kernel
  have same : intervals = [(0,0)] := Option.some.inj (located.symm.trans locatedRoot)
  subst intervals
  have selected : GeneralNominalFeedbackK2.Local registry (revised side).erased.current observer
      (.selected 1 (packet side).children) := by rw [packet_children]; exact revised_selected side
  refine ⟨⟨rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,rfl,locatedRoot,prepared,
    GeneralNominalFeedbackK2.selected_legacy selected,?_,?_,
    ⟨model,(revised_model side).1,branch side model (source_model _)⟩,?_⟩,selected,?_⟩
  · intro other member; cases member
  · intro other member same; cases List.mem_singleton.mp member; exact .refl _
  · exact GeneralNominalJointCandidates.initial_joint registry (context (some side)) observer display
      (List.mem_singleton_self _) display_checked rfl [(0,0)] locatedRoot prepared model (branch side model (source_model _))
  · intro other member same; cases List.mem_singleton.mp member; exact .refl _

private theorem guard (side : Bool) : PacketGuard (revised side) (plan side) [] := by
  apply (GeneralNominalCenteredInspection.selected_guard_reduction (plan side)
    (GeneralNominalCenteredAdministrativeLocal.selected_old (revised_local side)) (enabled side)
    (List.mem_singleton_self _) []).mpr
  refine ⟨GeneralNominalValueSupport.source_packet _ _ ⟨?_,raw_decision side⟩,
    model,revised_model side,branch side model (source_model _),equations side model (source_model _)⟩
  exact ⟨(raw_decision side).1,(raw_decision side).2.1,
    (raw_decision side).2.2 display (List.mem_singleton_self _) rfl [((0 : Fin 3),(0 : Fin 3))] (by
      change arguments (context none) observer = some [(0,0)]
      decide +kernel)⟩

theorem install_step (side : Bool) : Step registry observer (revised side) (finish side) := by
  refine ⟨observer,.root,.install (plan side) [] (enabled side) ?_ (guard side)⟩
  intro committed
  have impossible := committed.2 (child side) (by rw [packet_children]; simp)
  cases impossible

theorem ground : GeneralNominalGroundAccessibility.GroundRoots (context none) observer [.app 0 [.app 2 []]] := by
  refine ⟨rfl,?_⟩
  intro index
  have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
  simp only [zero]
  refine ⟨GeneralNominalGroundExamples.listTerm,⟨?_,rfl,⟨trivial,fun _ => ⟨trivial,fun i => Fin.elim0 i⟩⟩⟩,?_⟩
  · simp [normalize,normalizeArgs,GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
      GeneralNominalCompoundReadback.quote,GeneralNominalGroundExamples.listTerm,
      GeneralNominalGroundExamples.intTerm,List.ofFn_succ,GeneralNominalOriginTerms.arity]
  · intro m valid
    have precise := models_forward none (some false) m valid
    have parent := (GeneralNominalState.denotes_singleton_exact base m (0 : Fin 3) (1 : Fin 3)
      (descriptor (some false)) rfl).mp (precise.2.1 0 _ rfl)
    have lifted := GeneralNominalPeelingExamples.nominal_congr (scalar m valid 1 (by decide +kernel)) 0
    exact ⟨subtype_trans parent.1 lifted.1,subtype_trans lifted.2 parent.2⟩

theorem path (side : Bool) : B4Target.Steps (Step registry observer) start (finish side) :=
  .tail (.tail .refl (revise_step side)) (install_step side)

theorem reachable (side : Bool) : B4TargetV5.Reachable
    (GeneralNominalCenteredAdministrativeLocal.boundary roles) registry observer (finish side) :=
  ⟨start,⟨context none,[.app 0 [.app 2 []]],source,(fun _ => rfl),ground,rfl⟩,path side⟩


noncomputable abbrev current (side : Bool) := (finish side).erased.current.context

private theorem source_of_current (side : Bool) (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (current side).state m) :
    GeneralNominalState.Models (snapshot (some side)) m :=
  GeneralNominalRefinements.models
    (GeneralNominalRefinements.installed registry (context (some side)) observer display [((0 : Fin 3),(0 : Fin 3))]) m valid

theorem context_complete (side : Bool) : GeneralNominalSaturationState.ContextComplete (finish side).erased.current :=
  fun m valid => (models_of_source side m (source_of_current side m valid)).1

private theorem branch_final (side : Bool) (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (current side).state m) :
    BranchModels registry (current side) observer display display_checked [((0 : Fin 3),(0 : Fin 3))] m := by
  have privateModels := GeneralNominalUnaryCaptureFacts.private_models (current side) registry observer
    display (0 : Fin 3) (descriptor (some side)) rfl 0 rfl (bounds (some side)) rfl (query side) m valid
  refine ⟨privateModels.1,privateModels.2,?_⟩
  rw [GeneralNominalRecursiveExamples.display_schema registry (current side) observer rfl display_checked [((0 : Fin 3),(0 : Fin 3))]]
  exact GeneralNominalMaterialization.empty_models ..

private theorem sources_shape (side : Bool) (name : Nat)
    (member : name ∈ GeneralNominalState.sources (current side).state) :
    name ≤ 2 ∨ name ∈ GeneralNominalAllocation.reserved (snapshot (some side)) registry observer.identity := by
  simp only [GeneralNominalState.sources] at member
  change name ∈ (([0,1,2] ++ [0,1,2]) ++ GeneralNominalAllocation.reserved (snapshot (some side)) registry observer.identity ++ []) ++ _ at member
  rcases List.mem_append.mp member with prior | ordinary
  · simp only [List.append_nil] at prior
    rcases List.mem_append.mp prior with base | reserved
    · simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at base
      omega
    · exact Or.inr reserved
  · have shape : (current side).state.ordinary.flatMap GeneralNominalState.atomSources =
        [target side,target side,0,0,0,0,target side,target side] := by cases side <;> decide +kernel
    rw [shape] at ordinary
    have bound : target side ≤ 2 := by cases side <;> decide +kernel
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ordinary
    omega

private theorem fresh (side : Bool) (invocation : Nat) :
    GeneralNominalAllocation.Fresh (current side).state registry invocation := by
  intro key member collision
  rcases sources_shape side _ collision with small | reserved
  · have above := GeneralNominalIdentities.source_above_seed (snapshot (some side)).seed key
    change GeneralNominalIdentities.source 2 key ≤ 2 at small
    change 2 < GeneralNominalIdentities.source 2 key at above
    omega
  · obtain ⟨other,owned,equal⟩ := List.mem_map.mp reserved
    have same := (GeneralNominalIdentities.source_identity (snapshot (some side)).seed other key).mp equal
    subst other
    exact List.mem_append_right _ owned

private theorem prepared_final (side : Bool) : Prepared registry (current side) observer display display_checked := by
  have located : arguments (current side) observer = some [((0 : Fin 3),(0 : Fin 3))] := by
    change arguments (context none) observer = some [((0 : Fin 3),(0 : Fin 3))]; decide +kernel
  refine ⟨metadata (some side),?_,fresh side _,[((0 : Fin 3),(0 : Fin 3))],located,?_,⟨(by intro output member; cases member),?_⟩,
    model,branch_final side model (models_of_source side model (source_model _)).1.1⟩
  · exact GeneralNominalRefinements.linked
      (GeneralNominalRefinements.installed registry (context (some side)) observer display [((0 : Fin 3),(0 : Fin 3))])
      observer.demand (root_linked _)
  · rw [GeneralNominalUnaryCaptureFacts.report_exact (current side) display (0 : Fin 3) (descriptor (some side)) rfl
      0 (bounds (some side)) rfl (query side)]
    exact ⟨rfl,rfl,rfl⟩
  · rw [GeneralNominalRecursiveExamples.display_schema registry (current side) observer rfl display_checked [((0 : Fin 3),(0 : Fin 3))]]

private theorem final_survivor (side : Bool) : Survivor registry (current side) observer 1 [child side] := by
  refine ⟨?_,display,List.mem_singleton_self _,display_checked,rfl,rfl,[((0 : Fin 3),(0 : Fin 3))],?_,prepared_final side,?_⟩
  · rintro ⟨index,unknown⟩
    exact unknown ⟨(0 : Fin 3),rfl,Or.inr ⟨descriptor (some side),rfl⟩⟩
  · change arguments (context none) observer = some [((0 : Fin 3),(0 : Fin 3))]; decide +kernel
  · rw [GeneralNominalUnaryCaptureFacts.report_exact (current side) display (0 : Fin 3) (descriptor (some side)) rfl
      0 (bounds (some side)) rfl (query side)]
    have same : GeneralNominalRecursiveInspection.bindings (current side).state
        (GeneralNominalUnaryCaptureFacts.captured (current side).state (0 : Fin 3) 0 0 (bounds (some side))) =
        [(0,(target side,target side))] := by cases side <;> rfl
    rw [same]
    exact (children_exact side).symm

private theorem final_selected (side : Bool) : GeneralNominalFeedbackK2.Local registry
    (finish side).erased.current observer (.selected 1 [child side]) := by
  refine .selected ⟨(final_survivor side).1,no_root _ (models_of_source side model (source_model _)).1
    (final_no_structural side) _,no_candidate _ (models_of_source side model (source_model _)).1
    (final_no_structural side) _,?_⟩ ⟨final_survivor side,?_⟩
  · rintro (⟨_,decl,visible,checked,_,_,unprepared⟩ | ⟨_,legacy⟩)
    · cases List.mem_singleton.mp visible; exact unprepared (prepared_final side)
    · exact legacy.elim (fun h => (no_legacy _ rfl _ _).1 h.1) (fun h => (no_legacy _ rfl _ _).2 h.1)
  · intro other children found
    have copy := found
    obtain ⟨_,decl,visible,check,identity,_⟩ := found
    cases List.mem_singleton.mp visible
    have same : other = 1 := identity.symm
    subst other
    exact ⟨rfl,survivor_children_functional registry registry_checked _ _ _ _ _ copy (final_survivor side)⟩

abbrev targetSlot (side : Bool) : Fin 3 := if side then 2 else 1

private theorem child_located (side : Bool) : arguments (current side) (child side) =
    some [(targetSlot side,targetSlot side)] := by cases side <;> decide +kernel

private theorem child_conflicts (side : Bool) : (report (current side) display
    [(targetSlot side,targetSlot side)]).conflicts ≠ [] := by cases side <;> decide +kernel

private theorem child_unprepared (side : Bool) (checked : DeclarationChecked registry.constructors roles display) :
    ¬ Prepared registry (current side) (child side) display checked := by
  rintro ⟨_,_,_,intervals,located,finished,_⟩
  have same := Option.some.inj (located.symm.trans (child_located side))
  rw [same] at finished
  exact child_conflicts side finished.2.1

private theorem raw_sites (side : Bool) : (finish side).erased.current.sites =
    [GeneralNominalDemandMerging.pointSite observer,GeneralNominalSharedEmission.childSite (packet side) (child side)] := by
  change [GeneralNominalDemandMerging.pointSite observer] ++ (packet side).children.map _ = _
  rw [packet_children]; rfl

private theorem center_sites (side : Bool) : (finish side).sites = [(plan side).input,centerChild side] := by
  change [(plan side).input] ++ (plan side).emitted = _
  rw [emitted]; rfl

private theorem edges (side : Bool) : (finish side).erased.current.edges = [(observer,child side)] := by
  change [] ++ (packet side).children.map _ = _
  rw [packet_children]; rfl

private theorem generated_cases (side : Bool) (focus)
    (generated : GeneralNominalSaturationState.Generated (finish side).erased.current observer focus) :
    focus = observer ∨ focus = child side := by
  induction generated with
  | root => exact Or.inl rfl
  | child _ member _ => rw [edges] at member; exact Or.inr (congrArg Prod.snd (List.mem_singleton.mp member))
  | alias _ _ member _ _ =>
    rw [raw_sites] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl rfl
    · cases List.mem_singleton.mp member; exact Or.inr rfl

private theorem installs_committed (side : Bool) (p : GeneralNominalSaturationState.Packet roles)
    (generated : GeneralNominalSaturationState.Generated (finish side).erased.current observer p.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry (finish side).erased.current p) :
    GeneralNominalFeedbackSteps.Committed (finish side).erased.current p := by
  rcases generated_cases side _ generated with same | same
  · have localRule := enabled.2.1
    rw [same] at localRule
    have children := (CommonRoleOutermostResolver.Frontier.selected.inj
      (GeneralNominalFeedbackK2.local_functional localRule (final_selected side))).2
    constructor
    · intro m valid
      rcases p with ⟨preg,pctx,site,decl,check,intervals⟩
      have reg : preg = registry := enabled.1.1
      have ctx : pctx = current side := enabled.1.2.1
      subst preg; subst pctx
      have declaration : decl = display := List.mem_singleton.mp enabled.1.2.2.2.1
      subst decl
      have located : arguments (current side) observer = some intervals := by
        have occurrence : site.occurrence = observer := same
        exact occurrence ▸ enabled.1.2.2.2.2.2.1
      have found : arguments (current side) observer = some [((0 : Fin 3),(0 : Fin 3))] := by
        change arguments (context none) observer = some [((0 : Fin 3),(0 : Fin 3))]; decide +kernel
      have equal := Option.some.inj (located.symm.trans found)
      subst intervals
      change BranchModels registry (current side) site.occurrence display check [((0 : Fin 3),(0 : Fin 3))] m
      rw [same]
      exact branch_final side m valid.1
    · intro c member
      rw [children] at member
      cases List.mem_singleton.mp member
      rw [same,edges]; exact List.mem_singleton_self _
  · have prepared := enabled.1.2.2.2.2.2.2.1
    have declaration : p.declaration = display := List.mem_singleton.mp enabled.1.2.2.2.1
    have ctx := enabled.1.2.1
    have reg := enabled.1.1
    have impossible : Prepared registry (current side) (child side) display (reg ▸ declaration ▸ p.checked) := by
      simpa only [reg,ctx,same,declaration] using prepared
    exact False.elim (child_unprepared side _ impossible)


private theorem same_inputs_symm {models : GeneralNominalCommonBridge.Assignment → Prop}
    {first last : GeneralNominalDemandMerging.Site roles}
    (same : GeneralNominalDemandMerging.SameInputs models first last) :
    GeneralNominalDemandMerging.SameInputs models last first := by
  refine ⟨same.1.symm,?_⟩
  have relation := same.2
  generalize first.inputs = xs at relation ⊢
  generalize last.inputs = ys at relation ⊢
  induction relation with
  | nil => exact .nil
  | cons head tail ih =>
    obtain ⟨a,b,one,two,equal⟩ := head
    exact .cons ⟨b,a,two,one,fun m valid =>
      ⟨(equal m valid).2.1,(equal m valid).1,fun x y hx hy =>
        ⟨((equal m valid).2.2 y x hy hx).2,((equal m valid).2.2 y x hy hx).1⟩⟩⟩ ih

private theorem point_same_values {models : GeneralNominalCommonBridge.Assignment → Prop}
    (valid : models m) (first last : GeneralNominalDemandMerging.Site roles)
    (one : first.occurrence.demand.role = 0) (two : last.occurrence.demand.role = 0)
    (firstFits : GeneralNominalSaturationState.SiteHolds first m)
    (lastFits : GeneralNominalSaturationState.SiteHolds last m)
    (a b : Nat) (firstArg : ∀ index, first.occurrence.demand.arguments index = (a,a))
    (lastArg : ∀ index, last.occurrence.demand.arguments index = (b,b))
    (same : GeneralNominalDemandMerging.SameInputs models first last) : Equivalent (m a).1 (m b).1 := by
  have firstArity : first.inputs.length = 1 := by rw [first.arity,one]; rfl
  have lastArity : last.inputs.length = 1 := by rw [last.arity,two]; rfl
  have relation := same.2
  cases firstInputs : first.inputs with
  | nil => simp [firstInputs] at firstArity
  | cons x xs =>
    cases lastInputs : last.inputs with
    | nil => simp [lastInputs] at lastArity
    | cons y ys =>
      rw [firstInputs,lastInputs] at relation
      cases relation with
      | cons related rest =>
        obtain ⟨origin,target,original,other,equal⟩ := related
        have firstIndex : 0 < (roles first.occurrence.demand.role).arity := by rw [one]; decide +kernel
        have lastIndex : 0 < (roles last.occurrence.demand.role).arity := by rw [two]; decide +kernel
        have left := firstFits ⟨0,firstIndex⟩ origin (by rw [firstInputs]; exact congrArg some original)
        have right := lastFits ⟨0,lastIndex⟩ target (by rw [lastInputs]; exact congrArg some other)
        obtain ⟨x,hx⟩ := left.1
        obtain ⟨y,hy⟩ := right.1
        have xf := left.2 x hx
        have yf := right.2 y hy
        rw [firstArg] at xf
        rw [lastArg] at yf
        have related := (equal m valid).2.2 x y hx hy
        exact ⟨subtype_trans xf.1 (subtype_trans related.1 yf.2),
          subtype_trans yf.1 (subtype_trans related.2 xf.2)⟩

private theorem distinct_values (side : Bool) : ¬ Equivalent (model 0).1 (model (target side)).1 := by
  have target : (model (target side)).1 = GeneralNominalOutputGrowth.tower 0 := by cases side <;> rfl
  rw [target]
  intro equal
  have impossible : 1 = 0 := (GeneralNominalOutputGrowth.tower_equivalent 1 0).mp equal
  cases impossible

private theorem raw_no_cross (side : Bool) : ¬ GeneralNominalFeedbackSites.SameInputs (finish side).erased.current
    (GeneralNominalDemandMerging.pointSite observer) (GeneralNominalSharedEmission.childSite (packet side) (child side)) := by
  intro same
  have valid := (models_of_source side model (source_model _)).1
  have one : GeneralNominalDemandMerging.pointSite observer ∈ (finish side).erased.current.sites := by rw [raw_sites]; simp
  have two : GeneralNominalSharedEmission.childSite (packet side) (child side) ∈ (finish side).erased.current.sites := by rw [raw_sites]; simp
  exact distinct_values side (point_same_values valid _ _ rfl rfl
    (GeneralNominalFeedbackSites.recover_sound _ _ model valid (valid.2.2 _ one))
    (GeneralNominalFeedbackSites.recover_sound _ _ model valid (valid.2.2 _ two))
    0 (target side) (fun _ => rfl) (fun _ => rfl) same)

private theorem raw_closed (side : Bool) (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ (finish side).erased.current.sites) (two : last ∈ (finish side).erased.current.sites)
    (same : GeneralNominalFeedbackSites.SameInputs (finish side).erased.current first last) :
    GeneralNominalSaturationState.Alias (finish side).erased.current first.occurrence.identity last.occurrence.identity := by
  rw [raw_sites] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl <;> rcases two with rfl | rfl
  · exact .refl _
  · exact False.elim (raw_no_cross side same)
  · exact False.elim (raw_no_cross side (same_inputs_symm same))
  · exact .refl _

private theorem center_no_cross (side : Bool) : ¬ SameInputs (Models (finish side)) (plan side).input (centerChild side) := by
  intro same
  have valid := models_of_source side model (source_model _)
  exact distinct_values side (point_same_values valid _ _ rfl rfl
    (observed_holds _ _ (valid.2.1 _ (by rw [center_sites]; simp)))
    (observed_holds _ _ (valid.2.1 _ (by rw [center_sites]; simp)))
    0 (target side) (fun _ => rfl) (fun _ => rfl) same)

private theorem center_closed (side : Bool) (first last : Site roles)
    (one : first ∈ (finish side).sites) (two : last ∈ (finish side).sites)
    (same : SameInputs (Models (finish side)) first last) :
    GeneralNominalSaturationState.Alias (finish side).erased.current first.occurrence.identity last.occurrence.identity := by
  rw [center_sites] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl <;> rcases two with rfl | rfl
  · exact .refl _
  · exact False.elim (center_no_cross side same)
  · exact False.elim (center_no_cross side (same_inputs_symm same))
  · exact .refl _

private theorem varying_source (side : Bool) (name : Nat) (large : 3 ≤ name) :
    GeneralNominalState.Models (snapshot (some side)) (GeneralDictionaryTerminalRefresh.varying name) := by
  apply GeneralNominalCenteredModelExtension.source_models_same _ (first := model) _ (source_model _)
  intro source member
  have small : source ≤ 2 := (GeneralNominalCenteredTerminalForkSource.source (some side)).below_seed source member
  simp only [GeneralDictionaryTerminalRefresh.varying,show source ≠ name by omega,ite_false]

private theorem final_known (side : Bool) (name : Nat) (small : name ≤ 2) :
    GeneralNominalState.Known (current side).state name := by
  have casesName : name = 0 ∨ name = 1 ∨ name = 2 := by omega
  rcases casesName with rfl | rfl | rfl
  · exact ⟨(0 : Fin 3),rfl,Or.inr ⟨descriptor (some side),rfl⟩⟩
  · exact ⟨(1 : Fin 3),rfl,Or.inl (by intro bad; cases bad)⟩
  · exact ⟨(2 : Fin 3),rfl,Or.inl (by intro bad; cases bad)⟩

private theorem no_new_known (side : Bool) (after : GeneralNominalState.State)
    (exact : ∀ m, Models (finish side) m → GeneralNominalState.Models after m)
    (name : Nat) (large : 3 ≤ name) : ¬ GeneralNominalState.Known after name :=
  GeneralDictionaryTerminalRefresh.no_known_distinct after model (GeneralDictionaryTerminalRefresh.varying name) name
    (by change (if name = 0 then _ else _) = _; rw [ite_eq_right (by omega)])
    (by simp only [GeneralDictionaryTerminalRefresh.varying,ite_true])
    (exact model (models_of_source side model (source_model _)))
    (exact _ (models_of_source side _ (varying_source side name large)))

theorem stable (side : Bool) : Stable registry (finish side) observer := by
  intro focus generated after action
  cases action with
  | install plan support enabled novel guard => exact novel (installs_committed side plan.packet generated enabled)
  | merge first last support one two same novel guard => exact novel (center_closed side first last one two same)
  | refresh focus context certificate name member unknown known =>
    by_cases small : name ≤ 2
    · exact unknown (final_known side name small)
    · exact no_new_known side context.state certificate.exact name (by omega) known
  | administrative focus after action =>
    cases action with
    | enqueue linked absent =>
      rcases generated_cases side focus generated with same | same
      · exact absent (GeneralNominalDemandMerging.pointSite observer) (by rw [raw_sites]; simp) same.symm
      · exact absent (GeneralNominalSharedEmission.childSite (packet side) (child side)) (by rw [raw_sites]; simp) same.symm
    | refresh context certificate name member unknown known =>
      by_cases small : name ≤ 2
      · exact unknown (final_known side name small)
      · exact no_new_known side context.state (fun m valid => certificate.exact m valid.1) name (by omega) known
    | equate first last one two equal novel => exact novel (fun m valid => equal m (context_complete side m valid))
    | reobserve revision certificate improved =>
      have closed : GeneralNominalReobservationSteps.PointClosed (current side).state := point_closed side
      exact GeneralNominalReobservationSteps.pointClosed_no_revision closed revision improved

theorem halted (side : Bool) : ∀ after, ¬ Step registry observer (finish side) after := by
  rintro after ⟨focus,generated,action⟩
  exact stable side focus generated after action


private theorem graph_tests (side : Bool) : (graph (finish side)).tests = [(.source 0,.nominal 0 1)] := by
  change GeneralNominalCenteredSteps.Plan.tests (plan side) ++ [] = _
  rw [List.append_nil]
  unfold GeneralNominalCenteredSteps.Plan.tests
  rw [head_schema,named_empty]
  simp [Plan.schema,Plan.childRequests,List.ofFn_succ,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,
    GeneralNominalInspection.translate,normalize]

private theorem graph_acyclic (side : Bool) (origin : Origin) :
    ¬ GeneralNominalCenteredGraph.Cyclic (graph (finish side)) origin := by
  have valid := models_of_source side model (source_model _)
  have different : ¬ GeneralNominalOriginTerms.Same model (.source 0) (.source (target side)) :=
    fun same => distinct_values side (same.2.2 _ _ (.source _) (.source _))
  have recorded {first last} (edge : GeneralNominalCenteredGraph.Recorded (graph (finish side)) first last) :
      GeneralNominalOriginTerms.Same model first (.source 0) ∧
      GeneralNominalOriginTerms.Same model last (.source (target side)) := by
    cases edge with
    | structural shape index member => rw [graph_tests] at member; cases List.mem_singleton.mp member
    | nominal name arity index member =>
      rw [graph_tests] at member
      cases List.mem_singleton.mp member
      have zero : index.val = 0 := by omega
      rw [zero]
      refine ⟨GeneralNominalOriginTerms.source_self model 0,?_⟩
      have schema := (equations side model (source_model _)).2.2.1
      rw [head_schema] at schema
      have sharing := schema.2 ⟨0,.nominal (.source 0) 0 0,.actual⟩ (by simp)
      simpa only [ite_true,binder] using sharing
  have endpoints {first last} (edge : GeneralNominalCenteredGraph.Edge (graph (finish side)) first last) :
      GeneralNominalOriginTerms.Same model first (.source 0) ∧
      GeneralNominalOriginTerms.Same model last (.source (target side)) := by
    obtain ⟨parent,child,present,one,two⟩ := edge
    have exact := recorded present
    exact ⟨GeneralNominalOriginTerms.same_trans (one model valid) exact.1,
      GeneralNominalOriginTerms.same_trans (GeneralNominalOriginTerms.same_symm (two model valid)) exact.2⟩
  rintro ⟨⟨next,edge,path⟩,_⟩
  have one := endpoints edge
  cases path with
  | nil => exact different (GeneralNominalOriginTerms.same_trans (GeneralNominalOriginTerms.same_symm one.1) one.2)
  | cons edge rest =>
    have two := endpoints edge
    exact different (GeneralNominalOriginTerms.same_trans (GeneralNominalOriginTerms.same_symm two.1) one.2)

private theorem final_acyclic (side : Bool) (origin : Origin) : ¬ Cyclic (finish side) origin := by
  rintro (⟨name,_,cycle,_⟩ | cycle)
  · exact GeneralNominalOutputGrowthModels.feedback_acyclic _ model (models_of_source side model (source_model _)).1
      height model_height (final_no_structural side) name cycle
  · exact graph_acyclic side origin cycle

private theorem final_decision (side : Bool) : DecisionGuard registry (finish side) observer := by
  apply GeneralNominalCenteredSupport.legacy_decision
  have ready (slot : Fin 3) : GeneralNominalSharedSupport.ReadyAt (finish side).erased slot.val := by
    by_cases zero : slot = 0
    · subst slot
      exact ⟨_,_,GeneralNominalSupport.Head.nominal (snapshot := (current side).state) (0 : Fin 3) (descriptor (some side)) rfl,
        GeneralNominalSharedSupport.source_head _
          (GeneralNominalSupport.Head.nominal (snapshot := snapshot none) 0 (descriptor none) rfl)⟩
    · exact ⟨_,_,GeneralNominalSupport.Head.scalar (snapshot := (current side).state) slot .int (by
        change (if slot = 0 then _ else _) = _
        simp only [zero,ite_false]),
        GeneralNominalSharedSupport.source_head _
          (GeneralNominalSupport.Head.scalar (snapshot := snapshot none) slot .int (by simp [view,zero]))⟩
  exact ⟨fun _ => ready 0,fun _ _ _ _ _ slot _ => ready slot⟩

theorem final_local (side : Bool) : GeneralNominalCenteredAdministrativeLocal.Local registry
    (finish side) observer (.selected 1 [child side]) := by
  apply GeneralNominalCenteredAdministrativeLocal.selected_iff.mpr
  refine ⟨GeneralNominalCenteredBoundary.selected_of_old (final_selected side) (final_acyclic side) (final_decision side),
    ⟨(plan side).input,by rw [center_sites]; simp,rfl⟩,?_,?_⟩
  · intro first one same last two inputs
    exact raw_closed side first last one two inputs
  · intro first one same last two inputs
    exact center_closed side first last one two inputs

theorem local_different : ¬ (∀ frontier,
    GeneralNominalCenteredAdministrativeLocal.Local registry (finish false) observer frontier ↔
      GeneralNominalCenteredAdministrativeLocal.Local registry (finish true) observer frontier) := by
  intro agreement
  have carried := (agreement _).mp (final_local false)
  have equal := GeneralNominalCenteredAdministrativeLocal.local_functional carried (final_local true)
  exact GeneralNominalCenteredTerminalObservations.children_different
    (CommonRoleOutermostResolver.Frontier.selected.inj equal).2

theorem terminal_local_confluence_false :
    ¬ GeneralNominalCenteredTerminalAgreement.TerminalLocalConfluence roles := by
  intro confluence
  exact local_different (fun frontier => confluence registry registry ⟨rfl,registry_checked⟩ ⟨rfl,registry_checked⟩
    (GeneralRegistryReordering.reorders_refl registry) (context none) observer [.app 0 [.app 2 []]]
    source (fun _ => rfl) ground (finish false) (finish true) (path false) (path true) (halted false) (halted true) observer frontier)

theorem registered_terminal_fork :
    (∀ side, B4TargetV5.Reachable (GeneralNominalCenteredAdministrativeLocal.boundary roles) registry observer (finish side)) ∧
    (∀ side next, ¬ Step registry observer (finish side) next) ∧
    (∀ side, Models (finish side) model) ∧
    (∀ side, GeneralNominalSaturationState.Generated (finish side).erased.current observer observer) ∧
    (∀ side, GeneralNominalCenteredAdministrativeLocal.Local registry (finish side) observer (.selected 1 [child side])) ∧
    [child false] ≠ [child true] :=
  ⟨reachable,halted,fun side => models_of_source side model (source_model _),fun _ => .root,
    final_local,GeneralNominalCenteredTerminalObservations.children_different⟩


theorem final_models_iff (side : Bool) (m : GeneralNominalCommonBridge.Assignment) :
    Models (finish side) m ↔ GeneralNominalState.Models (snapshot (some side)) m :=
  ⟨fun valid => source_of_current side m valid.1.1,models_of_source side m⟩

theorem final_models_agree (m : GeneralNominalCommonBridge.Assignment) :
    Models (finish false) m ↔ Models (finish true) m :=
  (final_models_iff false m).trans ((models_iff (some false) (some true) m).trans (final_models_iff true m).symm)

theorem child_semantics_agree (m : GeneralNominalCommonBridge.Assignment) (valid : Models (finish false) m) :
    (child false).identity = (child true).identity ∧
    (child false).demand.role = (child true).demand.role ∧
    Equivalent (m 1).1 (m 2).1 := by
  have source := (final_models_iff false m).mp valid
  have first := scalar m source 1 (by decide +kernel)
  have last := scalar m source 2 (by decide +kernel)
  exact ⟨rfl,rfl,subtype_trans first.1 last.2,subtype_trans last.1 first.2⟩

theorem terminal_generated_local_confluence_false :
    ¬ GeneralNominalCenteredRegisteredLocal.TerminalGeneratedLocalConfluence roles := by
  intro confluence
  exact local_different (fun frontier => confluence registry registry ⟨rfl,registry_checked⟩ ⟨rfl,registry_checked⟩
    (GeneralRegistryReordering.reorders_refl registry) (context none) observer [.app 0 [.app 2 []]]
    source (fun _ => rfl) ground (finish false) (finish true) (path false) (path true)
    (halted false) (halted true) observer (Or.inl .root) frontier)

end Yulang.GeneralNominalCenteredRegisteredFork
