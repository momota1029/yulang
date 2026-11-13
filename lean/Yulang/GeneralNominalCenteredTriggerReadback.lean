import Yulang.GeneralNominalCenteredAllocation
import Yulang.GeneralNominalCenteredExamples

/-! Readback of the two W packets emitted by P. Both associated requests
use the same target. The cycle is derived from stored schemas and shared
centers; constructing the execution that records these packets is separate. -/
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalCenteredTriggerReadback
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSteps GeneralNominalRecursiveInspection
open GeneralNominalOriginTerms GeneralNominalMaterialization
open GeneralNominalSettledIntervalDeclarations
open CommonNominalFullCarrier

abbrev V (value : Ty) := variant 0 value
abbrev tail (origin : Origin) : Origin := .structural origin (.variant 0) 0

theorem tick_value {model : GeneralNominalCommonBridge.Assignment}
    (head : Head model (.source source) (.structural (.variant 0)))
    (payload : Same model (tail (.source source)) (.source child)) :
    Equivalent (model source).1 (V (model child).1) := by
  obtain ⟨values,length,equal⟩ := head.2 _ (.source source)
  cases values with
  | nil => cases length
  | cons first rest =>
    have empty : rest = [] := by
      have size : rest.length = 0 := by
        simp only [List.length_cons,GeneralNormalizedObservation.Shape.arity] at length
        omega
      exact List.eq_nil_of_length_eq_zero size
    subst rest
    have observed : Observes model (tail (.source source)) first :=
      .structural (.source source) rfl equal rfl
    have same := payload.2.2 _ _ observed (.source child)
    exact ⟨subtype_trans equal.1 ((common_variant_iff 0 _ _).mpr same.1),
      subtype_trans ((common_variant_iff 0 _ _).mpr same.2) equal.2⟩

theorem w_named_schema (plan : Plan roles)
    (declaration : plan.packet.declaration = w)
    (outputs : plan.packet.site.occurrence.demand.outputs = [⟨0,target⟩,⟨1,target⟩,⟨2,extra⟩]) :
    GeneralNominalPacketSupport.namedSchema plan.packet =
      ⟨[⟨0,.source target,.actual⟩,⟨1,tail (.source target),.actual⟩,
        ⟨1,.source extra,.actual⟩],[(.source target,.structural (.variant 0))],false⟩ := by
  unfold GeneralNominalPacketSupport.namedSchema GeneralNominalRecursiveCandidates.generated
    GeneralNominalMaterialization.requests
  have sorted : GeneralCanonicalChildOrder.canonicalDeclaration w = w := by
    simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,w]
  simp only [GeneralCanonicalChildOrder.canonicalEmit,declaration,sorted]
  simp only [GeneralDeclarationDemands.emitAll,w,List.map_nil,List.flatMap_nil,List.append_nil]
  unfold GeneralNominalMaterialization.rootRequests
  simp [declaration,outputs,w,tick,GeneralDeclarationPatterns.normalize,
    GeneralNominalMaterialization.generated,GeneralNominalInspection.translate,
    schema,schemas,Schema.append,tail,GeneralCandidateInspection.plainNames]

theorem w_output_equation {model : GeneralNominalCommonBridge.Assignment} (plan : Plan roles)
    (declaration : plan.packet.declaration = w)
    (outputs : plan.packet.site.occurrence.demand.outputs = [⟨0,target⟩,⟨1,target⟩,⟨2,extra⟩])
    (equations : plan.Equations model) :
    Equivalent (model (plan.binder 0)).1 (V (model (plan.binder 1)).1) ∧
      Same model (tail (.source target)) (.source (plan.binder 1)) := by
  have named := equations.2.2.2.2.1
  rw [w_named_schema plan declaration outputs] at named
  have anchor := named.2 ⟨0,.source target,.actual⟩ (by simp)
  have payload := named.2 ⟨1,tail (.source target),.actual⟩ (by simp)
  simp only [ite_true] at anchor payload
  have whole := tick_value (named.1 (.source target,.structural (.variant 0)) (by simp)) payload
  have same := anchor.2.2 _ _ (.source target) (.source (plan.binder 0))
  exact ⟨⟨subtype_trans same.2 whole.1,subtype_trans whole.2 same.1⟩,payload⟩

theorem w_recorded (plan : Plan roles)
    (declaration : plan.packet.declaration = w)
    (outputs : plan.packet.site.occurrence.demand.outputs = [⟨0,target⟩,⟨1,target⟩,⟨2,extra⟩])
    (member : plan ∈ state.plans) :
    GeneralNominalCenteredGraph.Recorded (graph state) (.source target) (tail (.source target)) := by
  apply GeneralNominalCenteredGraph.Recorded.structural _ _ ⟨0,by decide +kernel⟩
  apply List.mem_flatMap.mpr
  refine ⟨plan,member,List.mem_append_left _ (List.mem_append_right _ ?_)⟩
  rw [w_named_schema plan declaration outputs]
  simp

def center (plan : Plan roles) (position : Nat) : Nat :=
  ((List.ofFn plan.input.center)[position]?).getD 0

theorem p_head_schema (plan : Plan roles) (declaration : plan.packet.declaration = p) :
    plan.headSchema =
      ⟨[⟨0,tail (tail (.source (center plan 0))),.actual⟩,
        ⟨1,.source (center plan 1),.actual⟩],
       [(.source (center plan 0),.structural (.variant 0)),
        (tail (.source (center plan 0)),.structural (.variant 0))],false⟩ := by
  simp [Plan.headSchema,GeneralNominalInspection.queries,declaration,
    Declaration.normalHead,p,tick,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
    GeneralCandidateInspection.plainNames,schemas,schema,Schema.append,center,tail]

theorem w_head_schema (plan : Plan roles) (declaration : plan.packet.declaration = w) :
    plan.headSchema =
      ⟨[⟨0,tail (.source (center plan 0)),.actual⟩,
        ⟨1,.source (center plan 1),.actual⟩],
       [(.source (center plan 0),.structural (.variant 0))],false⟩ := by
  simp [Plan.headSchema,GeneralNominalInspection.queries,declaration,
    Declaration.normalHead,w,tick,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
    GeneralCandidateInspection.plainNames,schemas,schema,Schema.append,center,tail]

theorem tick_at {model : GeneralNominalCommonBridge.Assignment}
    (unique : GeneralNominalReadbackFunctionality.Unique model origin)
    (head : Head model origin (.structural (.variant 0)))
    (payload : GeneralNominalFiniteMeaning.At model .actual (tail origin) value) :
    GeneralNominalFiniteMeaning.At model .actual origin (V value) := by
  have result := GeneralNominalFiniteMeaning.assemble (.structural (.variant 0)) .actual
    (fun _ => value) unique head (by
      intro index
      have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
      simpa only [GeneralNominalOriginTerms.project,zero,GeneralNominalFiniteMeaning.childMode] using payload)
  simpa [GeneralNominalFiniteMeaning.build,List.ofFn_succ,shapeValue,
    GeneralNormalizedObservation.Shape.term,CommonNominalFullCarrier.model,
    Core.PresenceGeneration.TyTerm.eval,arity,GeneralNormalizedObservation.Shape.arity] using result

theorem same_at_source {model : GeneralNominalCommonBridge.Assignment}
    (same : Same model origin (.source identity)) :
    GeneralNominalFiniteMeaning.At model .actual origin (model identity).1 :=
  ⟨same.1,fun _ seen => same.2.2 _ _ seen (.source identity)⟩

theorem p_head_value {model : GeneralNominalCommonBridge.Assignment} (plan : Plan roles)
    (declaration : plan.packet.declaration = p) (equations : plan.Equations model) :
    Equivalent (model (center plan 0)).1 (V (V (model (plan.binder 0)).1)) ∧
      Same model (.source (center plan 1)) (.source (plan.binder 1)) := by
  have head := equations.2.2.1
  rw [p_head_schema plan declaration] at head
  have payload := head.2 ⟨0,tail (tail (.source (center plan 0))),.actual⟩ (by simp)
  have second := head.2 ⟨1,.source (center plan 1),.actual⟩ (by simp)
  simp only [ite_true] at payload second
  have inner := tick_at
    (GeneralNominalReadbackFunctionality.projection_unique
      (GeneralNominalReadbackFunctionality.source_unique model (center plan 0))
      (.structural (.variant 0)) trivial ⟨0,by decide +kernel⟩)
    (head.1 (tail (.source (center plan 0)),.structural (.variant 0)) (by simp)) (same_at_source payload)
  have outer := tick_at (GeneralNominalReadbackFunctionality.source_unique model (center plan 0))
    (head.1 (.source (center plan 0),.structural (.variant 0)) (by simp)) inner
  exact ⟨outer.2 _ (.source _),second⟩

theorem w_head_value {model : GeneralNominalCommonBridge.Assignment} (plan : Plan roles)
    (declaration : plan.packet.declaration = w) (equations : plan.Equations model) :
    Equivalent (model (center plan 0)).1 (V (model (plan.binder 0)).1) ∧
      Same model (.source (center plan 1)) (.source (plan.binder 1)) := by
  have head := equations.2.2.1
  rw [w_head_schema plan declaration] at head
  have payload := head.2 ⟨0,tail (.source (center plan 0)),.actual⟩ (by simp)
  have second := head.2 ⟨1,.source (center plan 1),.actual⟩ (by simp)
  simp only [ite_true] at payload second
  exact ⟨tick_value (head.1 (.source (center plan 0),.structural (.variant 0)) (by simp)) payload,second⟩

abbrev wrapSignature : wrapChild.Signature roles :=
  p_checked.signature.2.2.2 wrapChild (by simp [p])
abbrev recurSignature : recurChild.Signature roles :=
  p_checked.signature.2.2.2 recurChild (by simp [p])
def compound (plan : Plan roles) (clause : Nat) : Nat :=
  fresh plan.packet.context.state.seed plan.packet.site.occurrence.identity plan.packet.declaration.id 9 clause 0

theorem child_centers (plan : Plan roles) (clause : Clause) (present : clause ∈ p.requirements)
    (signature : clause.Signature roles) :
    List.ofFn (plan.childSite clause signature).center = [compound plan clause.id,plan.binder 1] := by
  simp only [p,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl
  all_goals
    change List.ofFn (fun index : Fin 2 => plan.emittedCenter _ index.val _) = _
    simp [Plan.childSite,Plan.emittedCenter,GeneralDeclarationPatterns.normalize,
    wrapChild,recurChild,tick,roles,bareRole,GeneralNominalProvenanceDeclarations.bareRole,List.ofFn_succ,compound]

theorem child_value {model : GeneralNominalCommonBridge.Assignment} (plan : Plan roles)
    (declaration : plan.packet.declaration = p) (clause : Clause) (present : clause ∈ p.requirements)
    (signature : clause.Signature roles) (equations : plan.Equations model) :
    Equivalent (model (compound plan clause.id)).1 (V (model (plan.binder 0)).1) := by
  have schema := (equations.2.2.2.2.2 clause (declaration ▸ present) signature).2
  have shape : plan.schema (plan.childRequests clause signature) =
      ⟨[⟨0,tail (.source (compound plan clause.id)),.actual⟩,
        ⟨1,.source (plan.binder 1),.actual⟩],[(.source (compound plan clause.id),.structural (.variant 0))],false⟩ := by
    simp only [p,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl
    all_goals simp [Plan.schema,Plan.childRequests,Plan.childSite,Plan.emittedCenter,
      GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,GeneralNominalMaterialization.schemas,
      GeneralNominalMaterialization.Schema.append,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate,GeneralCandidateInspection.plainNames,
      wrapChild,recurChild,tick,roles,bareRole,GeneralNominalProvenanceDeclarations.bareRole,List.ofFn_succ,compound,tail]
  rw [shape] at schema
  have actual := schema.2 ⟨0,tail (.source (compound plan clause.id)),.actual⟩ (by simp)
  simp only [ite_true] at actual
  exact tick_value (schema.1 (.source (compound plan clause.id),.structural (.variant 0)) (by simp)) actual

theorem wrap_outputs (plan : Plan roles) (declaration : plan.packet.declaration = p) :
    (plan.childSite wrapChild wrapSignature).occurrence.demand.outputs =
      [⟨0,(GeneralNominalPacketSupport.capture plan.packet).outputs 2⟩,
       ⟨1,(GeneralNominalPacketSupport.capture plan.packet).outputs 2⟩,
       ⟨2,(GeneralNominalPacketSupport.capture plan.packet).outputs 3⟩] := by
  unfold Plan.childSite GeneralNominalFeedbackSites.clauseChild GeneralNominalFeedbackSites.frame
    GeneralNominalAllocation.frame GeneralDictionaryEmissionPlans.occurrence
  simp [GeneralDeclarationDemands.emit,GeneralDeclarationDemands.childDemand,
    GeneralDeclarationDemands.outputTarget,declaration,p,wrapChild,
    GeneralDeclarationPatterns.normalize,Declaration.outputNames,GeneralNominalPacketSupport.capture]

theorem two_w_cycle (first last : Plan roles)
    (firstMember : first ∈ state.plans) (lastMember : last ∈ state.plans)
    (firstDeclaration : first.packet.declaration = w) (lastDeclaration : last.packet.declaration = w)
    (firstOutputs : first.packet.site.occurrence.demand.outputs = [⟨0,firstTarget⟩,⟨1,firstTarget⟩,⟨2,firstExtra⟩])
    (lastOutputs : last.packet.site.occurrence.demand.outputs = [⟨0,lastTarget⟩,⟨1,lastTarget⟩,⟨2,lastExtra⟩])
    (shared : ∀ model, Models state model → Same model (.source (first.binder 1)) (.source (last.binder 1)))
    (descent : ∀ model, Models state model →
      Equivalent (model (first.binder 0)).1 (V (model (last.binder 0)).1))
    (inhabited : ∃ model, Models state model) :
    GeneralNominalCenteredGraph.Cyclic (graph state) (.source (first.binder 1)) := by
  apply GeneralNominalCenteredGraph.self_cycle (graph state)
    (w_recorded first firstDeclaration firstOutputs firstMember) ?_ ?_ inhabited
  · apply GeneralNominalCenteredGraph.source_equal
    intro model valid
    have firstEquations := valid.2.2 first firstMember
    have lastEquations := valid.2.2 last lastMember
    have one := (w_output_equation first firstDeclaration firstOutputs firstEquations).1
    have two := (w_output_equation last lastDeclaration lastOutputs lastEquations).1
    have b := (shared model valid).2.2 _ _ (.source _) (.source _)
    have lastTick : Equivalent (model (last.binder 0)).1 (V (model (first.binder 1)).1) :=
      ⟨subtype_trans two.1 ((common_variant_iff 0 _ _).mpr b.2),
        subtype_trans ((common_variant_iff 0 _ _).mpr b.1) two.2⟩
    have cycle := GeneralNominalSharedPump.shared_round_cycle one (descent model valid) lastTick
    have named := firstEquations.2.2.2.2.1
    rw [w_named_schema first firstDeclaration firstOutputs] at named
    have anchor := named.2 ⟨0,.source firstTarget,.actual⟩ (by simp)
    simp only [ite_true] at anchor
    have target := anchor.2.2 _ _ (.source firstTarget) (.source (first.binder 0))
    exact ⟨subtype_trans cycle.1 (subtype_trans one.2 target.2),
      subtype_trans target.1 (subtype_trans one.1 cycle.2)⟩
  · intro model valid
    exact (w_output_equation first firstDeclaration firstOutputs (valid.2.2 first firstMember)).2


private theorem equivalent_trans (one : Equivalent a b) (two : Equivalent b c) : Equivalent a c :=
  ⟨subtype_trans one.1 two.1,subtype_trans two.2 one.2⟩
private theorem equivalent_symm (same : Equivalent a b) : Equivalent b a := ⟨same.2,same.1⟩
private theorem tick_congr (same : Equivalent a b) : Equivalent (V a) (V b) :=
  ⟨(common_variant_iff 0 _ _).mpr same.1,(common_variant_iff 0 _ _).mpr same.2⟩

theorem emitted_input_values {model : GeneralNominalCommonBridge.Assignment}
    (parent child : Plan roles) (declaration : parent.packet.declaration = p)
    (clause : Clause) (present : clause ∈ p.requirements) (signature : clause.Signature roles)
    (input : child.input = parent.childSite clause signature) (equations : parent.Equations model) :
    Equivalent (model (center child 0)).1 (V (model (parent.binder 0)).1) ∧
      center child 1 = parent.binder 1 := by
  have names : List.ofFn child.input.center = [compound parent clause.id,parent.binder 1] := by
    rw [input]; exact child_centers parent clause present signature
  simp only [center,names,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  exact ⟨child_value parent declaration clause present signature equations,trivial⟩

theorem emitted_w_values {model : GeneralNominalCommonBridge.Assignment}
    (parent child : Plan roles) (parentDeclaration : parent.packet.declaration = p)
    (childDeclaration : child.packet.declaration = w)
    (input : child.input = parent.childSite wrapChild wrapSignature)
    (parentEquations : parent.Equations model) (childEquations : child.Equations model) :
    Equivalent (model (child.binder 0)).1 (model (parent.binder 0)).1 ∧
      Same model (.source (child.binder 1)) (.source (parent.binder 1)) := by
  have emitted := emitted_input_values parent child parentDeclaration wrapChild (by simp [p]) wrapSignature input parentEquations
  have matched := w_head_value child childDeclaration childEquations
  exact ⟨GeneralNominalSettledIntervalObstruction.variant_cancel
    (equivalent_trans (equivalent_symm matched.1) emitted.1),
    emitted.2 ▸ same_symm matched.2⟩

theorem emitted_p_values {model : GeneralNominalCommonBridge.Assignment}
    (parent child : Plan roles) (parentDeclaration : parent.packet.declaration = p)
    (childDeclaration : child.packet.declaration = p)
    (input : child.input = parent.childSite recurChild recurSignature)
    (parentEquations : parent.Equations model) (childEquations : child.Equations model) :
    Equivalent (model (parent.binder 0)).1 (V (model (child.binder 0)).1) ∧
      Same model (.source (parent.binder 1)) (.source (child.binder 1)) := by
  have emitted := emitted_input_values parent child parentDeclaration recurChild (by simp [p]) recurSignature input parentEquations
  have matched := p_head_value child childDeclaration childEquations
  exact ⟨GeneralNominalSettledIntervalObstruction.variant_cancel
    (equivalent_trans (equivalent_symm emitted.1) matched.1),emitted.2 ▸ matched.2⟩

/-- The actual P/W lineage supplies all three pump equations, including
the common b center and the duplicated output target of each emitted W. -/
theorem recorded_trigger_cycle (p₀ w₀ p₁ w₁ : Plan roles)
    (p₀Member : p₀ ∈ state.plans) (w₀Member : w₀ ∈ state.plans)
    (p₁Member : p₁ ∈ state.plans) (w₁Member : w₁ ∈ state.plans)
    (p₀Declaration : p₀.packet.declaration = p) (w₀Declaration : w₀.packet.declaration = w)
    (p₁Declaration : p₁.packet.declaration = p) (w₁Declaration : w₁.packet.declaration = w)
    (first : w₀.input = p₀.childSite wrapChild wrapSignature)
    (recursive : p₁.input = p₀.childSite recurChild recurSignature)
    (last : w₁.input = p₁.childSite wrapChild wrapSignature)
    (inhabited : ∃ model, Models state model) :
    GeneralNominalCenteredGraph.Cyclic (graph state) (.source (w₀.binder 1)) := by
  have firstOutputs : w₀.packet.site.occurrence.demand.outputs =
      [⟨0,(GeneralNominalPacketSupport.capture p₀.packet).outputs 2⟩,
       ⟨1,(GeneralNominalPacketSupport.capture p₀.packet).outputs 2⟩,
       ⟨2,(GeneralNominalPacketSupport.capture p₀.packet).outputs 3⟩] := by
    rw [← w₀.input_exact,first]; exact wrap_outputs p₀ p₀Declaration
  have lastOutputs : w₁.packet.site.occurrence.demand.outputs =
      [⟨0,(GeneralNominalPacketSupport.capture p₁.packet).outputs 2⟩,
       ⟨1,(GeneralNominalPacketSupport.capture p₁.packet).outputs 2⟩,
       ⟨2,(GeneralNominalPacketSupport.capture p₁.packet).outputs 3⟩] := by
    rw [← w₁.input_exact,last]; exact wrap_outputs p₁ p₁Declaration
  apply two_w_cycle w₀ w₁ w₀Member w₁Member w₀Declaration w₁Declaration firstOutputs lastOutputs ?_ ?_ inhabited
  · intro model valid
    have one := emitted_w_values p₀ w₀ p₀Declaration w₀Declaration first (valid.2.2 _ p₀Member) (valid.2.2 _ w₀Member)
    have two := emitted_p_values p₀ p₁ p₀Declaration p₁Declaration recursive (valid.2.2 _ p₀Member) (valid.2.2 _ p₁Member)
    have three := emitted_w_values p₁ w₁ p₁Declaration w₁Declaration last (valid.2.2 _ p₁Member) (valid.2.2 _ w₁Member)
    exact same_trans one.2 (same_trans two.2 (same_symm three.2))
  · intro model valid
    have one := emitted_w_values p₀ w₀ p₀Declaration w₀Declaration first (valid.2.2 _ p₀Member) (valid.2.2 _ w₀Member)
    have two := emitted_p_values p₀ p₁ p₀Declaration p₁Declaration recursive (valid.2.2 _ p₀Member) (valid.2.2 _ p₁Member)
    have three := emitted_w_values p₁ w₁ p₁Declaration w₁Declaration last (valid.2.2 _ p₁Member) (valid.2.2 _ w₁Member)
    exact equivalent_trans one.1 (equivalent_trans two.1 (tick_congr (equivalent_symm three.1)))


theorem graph_cycle_transport (journal : GeneralNominalCenteredGraph.Journal)
    (cycle : GeneralNominalCenteredGraph.Cyclic journal first)
    (equal : GeneralNominalCenteredGraph.Equal journal first last) :
    GeneralNominalCenteredGraph.Cyclic journal last := by
  have finish {middle target} (path : GeneralNominalCenteredGraph.Path journal middle target)
      (targetEqual : GeneralNominalCenteredGraph.Equal journal target last)
      {start} (edge : GeneralNominalCenteredGraph.Edge journal start middle) :
      ∃ next, GeneralNominalCenteredGraph.Edge journal start next ∧
        GeneralNominalCenteredGraph.Path journal next last := by
    induction path generalizing start with
    | nil =>
      obtain ⟨parent,child,recorded,one,two⟩ := edge
      exact ⟨last,⟨parent,child,recorded,one,fun model valid =>
        same_trans (two model valid) (targetEqual model valid)⟩,.nil _⟩
    | cons nextEdge rest ih =>
      obtain ⟨next,adjusted,tail⟩ := ih targetEqual nextEdge
      exact ⟨_,edge,.cons adjusted tail⟩
  obtain ⟨⟨next,⟨parent,child,recorded,one,two⟩,path⟩,inhabited⟩ := cycle
  exact ⟨finish path equal ⟨parent,child,recorded,fun model valid =>
    same_trans (same_symm (equal model valid)) (one model valid),two⟩,inhabited⟩

theorem recorded_trigger_rejected (p₀ w₀ p₁ w₁ : Plan roles)
    (p₀Member : p₀ ∈ state.plans) (w₀Member : w₀ ∈ state.plans)
    (p₁Member : p₁ ∈ state.plans) (w₁Member : w₁ ∈ state.plans)
    (p₀Declaration : p₀.packet.declaration = p) (w₀Declaration : w₀.packet.declaration = w)
    (p₁Declaration : p₁.packet.declaration = p) (w₁Declaration : w₁.packet.declaration = w)
    (first : w₀.input = p₀.childSite wrapChild wrapSignature)
    (recursive : p₁.input = p₀.childSite recurChild recurSignature)
    (last : w₁.input = p₁.childSite wrapChild wrapSignature)
    (registered : w₀.input ∈ state.sites)
    (known : ¬ (GeneralNominalCenteredBoundary.fields roles).RootPending registry state w₀.input.occurrence)
    (inhabited : ∃ model, Models state model) :
    GeneralNominalCenteredBoundary.Local registry state w₀.input.occurrence .rejected := by
  have cycle := recorded_trigger_cycle p₀ w₀ p₁ w₁ p₀Member w₀Member p₁Member w₁Member
    p₀Declaration w₀Declaration p₁Declaration w₁Declaration first recursive last inhabited
  let index : Fin (roles w₀.input.occurrence.demand.role).arity := ⟨1,by rw [first]; change 1 < 2; decide +kernel⟩
  have centerName : center w₀ 1 = w₀.input.center index := by
    simp [center,List.getElem?_ofFn,index,show 1 < (roles w₀.input.occurrence.demand.role).arity from index.isLt]
  apply GeneralNominalCenteredBoundary.root_cycle_rejected known
  refine ⟨w₀.input,registered,rfl,index,Or.inr (graph_cycle_transport (graph state) cycle ?_)⟩
  intro model valid
  have matched := (w_head_value w₀ w₀Declaration (valid.2.2 _ w₀Member)).2
  rw [centerName] at matched
  exact same_symm matched

end Yulang.GeneralNominalCenteredTriggerReadback
