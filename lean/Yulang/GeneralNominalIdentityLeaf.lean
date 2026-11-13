import Yulang.GeneralNominalSourceFrontier
import Yulang.GeneralNominalSharedPositive
import Yulang.GeneralNominalFiniteAssociatedFacts

/-! Exact producer facts for unary point-input identity leaves. The restriction
is syntactic and independent of reachability, termination or a supplied cover. -/
namespace Yulang.GeneralNominalIdentityLeaf
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

structure Shape (declaration : Declaration) : Prop where
  head : declaration.head = [.var 0]
  terminal : declaration.requirements = []
  outputs : ∀ equation ∈ declaration.associated, equation.rhs = .var 0

def RegistryShape (registry : Registry) : Prop :=
  ∀ declaration ∈ registry.declarations, Shape declaration

/-- The unary point restriction concerns the demand, not unrelated source slots. -/
def Point (root : Occurrence roles) (input : Nat) : Prop :=
  List.ofFn root.demand.arguments = [(input,input)]

theorem located_point (point : Point root input)
    (located : GeneralNominalCandidates.arguments context root = some bounds) :
    ∃ slot : Fin context.state.base.slots, bounds = [(slot,slot)] ∧ context.state.base.source slot = input := by
  unfold GeneralNominalCandidates.arguments at located
  rw [point] at located
  unfold GeneralCandidateBoundaryParts.locate at located
  cases found : GeneralDictionaryBinderLocations.sourceSlot context.state.base input with
  | none => simp [found] at located
  | some slot =>
      refine ⟨slot,?_,(GeneralDictionaryBinderLocations.sourceSlot_exact _ _ _).mp found⟩
      simpa [found] using located.symm

def pointReport (state : GeneralNominalState.State) (slot : Fin state.base.slots) : Report state :=
  { captures := [⟨0,(slot,slot),none⟩], checked := [(slot,slot),(slot,slot)] }

theorem report_exact (shape : Shape declaration) (context : GeneralNominalCandidates.Context)
    (slot : Fin context.state.base.slots) :
    GeneralNominalRecursiveCandidates.report context declaration [(slot,slot)] = pointReport context.state slot := by
  simp [GeneralNominalRecursiveCandidates.report,GeneralNominalInspection.queries,Declaration.normalHead,
    shape.head,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,inspectMany,inspect,Report.append,pointReport]

variable {roles : Roles.RoleDecls} {packet : Packet roles} {slot : Fin packet.context.state.base.slots}

theorem bindings_exact (shape : Shape packet.declaration) (bounds : packet.bounds = [(slot,slot)]) :
    packet.bindings = [(0,(packet.context.state.base.source slot,packet.context.state.base.source slot))] := by
  simp only [Packet.bindings,bounds,report_exact shape,bindings,pointReport,List.map_cons,List.map_nil]

theorem capture_exact (shape : Shape packet.declaration) (bounds : packet.bounds = [(slot,slot)]) :
    (GeneralNominalPacketSupport.capture packet).inputs 0 =
      (packet.context.state.base.source slot,packet.context.state.base.source slot) := by
  simp [GeneralNominalPacketSupport.capture,bindings_exact shape bounds,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences]

theorem children_empty (packet : Packet roles) (terminal : packet.declaration.requirements = []) :
    packet.children = [] := by
  simp [Packet.children,GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,
    GeneralCanonicalChildOrder.canonicalEmit,GeneralDeclarationDemands.emitAll,
    GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,terminal]

def targets (declaration : Declaration) (root : Occurrence roles) : List Nat :=
  (rootRequests declaration root).map Request.target

def outputSchema (targets : List Nat) : Schema :=
  { variables := targets.map fun target => ⟨0,.source target,.actual⟩ }

theorem generated_exact (context : GeneralNominalCandidates.Context) (requests : List Request)
    (plain : ∀ request ∈ requests, request.pattern = .var 0 ∧ request.mode = .actual) :
    generated context.state context.interpretation requests = outputSchema (requests.map Request.target) := by
  induction requests with
  | nil => rfl
  | cons request rest ih =>
      have head := plain request (by simp)
      have tail := ih (fun r hr => plain r (List.mem_cons_of_mem _ hr))
      change (schema _ _ _).append (generated _ _ rest) = _
      rw [tail,head.1,head.2]
      simp [schema,GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
        outputSchema,Schema.append]

theorem named_schema (shape : Shape packet.declaration) :
    GeneralNominalPacketSupport.namedSchema packet = outputSchema (targets packet.declaration packet.site.occurrence) := by
  unfold GeneralNominalPacketSupport.namedSchema GeneralNominalRecursiveCandidates.generated
  rw [GeneralNominalFiniteAssociatedFacts.terminal_requests _ _ _ _ _ _ shape.terminal]
  apply generated_exact
  intro request member
  obtain ⟨output,_,equation,equationMember,_,rfl⟩ :=
    GeneralNominalFiniteAssociatedFacts.root_request_witness _ _ _ member
  exact ⟨shape.outputs equation equationMember,rfl⟩

theorem inputs_valid (shape : Shape packet.declaration) (bounds : packet.bounds = [(slot,slot)])
    (model : Assignment) : GeneralNominalPacketSupport.Inputs packet model := by
  have names : packet.declaration.inputNames = [0] := by
    simp [Declaration.inputNames,shape.head,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables]
  have report : GeneralNominalPacketSupport.report packet = pointReport packet.context.state slot := by
    simp only [GeneralNominalPacketSupport.report,bounds,report_exact shape]
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa [GeneralNominalAllocation.Compatible,bindings_exact shape bounds] using
      subtype_refl (model (packet.context.state.base.source slot)).1
  · simp [GeneralNominalAllocation.merges,names,bindings_exact shape bounds,
      GeneralNominalAllocation.occurrences,PresenceNormalForm.All]
  · simpa [selfChecks,report,pointReport,PresenceNormalForm.All,PresenceNormalForm.Atom.Holds,
      Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model] using
      subtype_refl (model (packet.context.state.base.source slot)).1
  · simp [ProjectionModels,report,pointReport]
  · rw [GeneralNominalSharedPositive.leaf_input_schema packet shape.terminal]
    exact empty_models _ _ _ _ _

theorem outputs_exact (shape : Shape packet.declaration) (bounds : packet.bounds = [(slot,slot)])
    (model : Assignment) : GeneralNominalPacketSupport.Outputs packet model ↔
    ∀ target ∈ targets packet.declaration packet.site.occurrence,
      Equivalent (model target).1 (model (packet.context.state.base.source slot)).1 := by
  have names := GeneralNominalLinearMaterializationFacts.no_output_binders packet.declaration packet.checked shape.terminal
  have report : GeneralNominalPacketSupport.report packet = pointReport packet.context.state slot := by
    simp only [GeneralNominalPacketSupport.report,bounds,report_exact shape]
  unfold GeneralNominalPacketSupport.Outputs
  rw [named_schema shape]
  constructor
  · intro valid target member
    have fits := (valid.2.1 ⟨0,.source target,.actual⟩ (List.mem_map.mpr ⟨target,member,rfl⟩)).2 _ (.source target)
    simp only [VariableHolds,names,List.not_mem_nil,ite_false,capture_exact shape bounds] at fits
    exact ⟨fits.2,fits.1⟩
  · intro equal
    refine ⟨?_,?_,?_,?_⟩
    · intro test member; cases member
    · intro entry member
      obtain ⟨target,targetMember,rfl⟩ := List.mem_map.mp member
      refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen; cases seen
      simp only [VariableHolds,names,List.not_mem_nil,ite_false,capture_exact shape bounds]
      exact ⟨(equal target targetMember).2,(equal target targetMember).1⟩
    · intro first one last two _ _ _ a b seenA seenB
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp one
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp two
      cases seenA; cases seenB
      exact ⟨subtype_trans (equal x hx).1 (equal y hy).2,
        subtype_trans (equal y hy).1 (equal x hx).2⟩
    · intro entry member captured capturedMember _ _ origin found
      rw [report] at capturedMember
      cases List.mem_singleton.mp capturedMember
      cases found

end Yulang.GeneralNominalIdentityLeaf
