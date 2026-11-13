import Yulang.GeneralNominalIdentityLeaf
import Yulang.GeneralNominalHoleFacets

/-! The complete head-relevant producer invariant for identity leaves.
All inspections stay at the original point input, and every output use is an
alias of it. Reserved source slots are absent from both semantic deltas. -/
namespace Yulang.GeneralNominalIdentityProvenance
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSharedSteps GeneralNominalIdentityLeaf
open GeneralNominalDemandMerging GeneralNominalRecursiveInspection
open GeneralNominalMaterialization GeneralNominalOriginTerms
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

variable {roles : Roles.RoleDecls} {root : Occurrence roles} {registry : Registry}

theorem formed_sites (shape : RegistryShape registry) (formed : SourceFormed registry root state) :
    state.current.sites = [pointSite root] := by
  induction formed with
  | initial => rfl
  | update formed step ih =>
      obtain ⟨focus,generated,action⟩ := step
      cases action with
      | administrative _ _ action =>
          cases action with
          | enqueue linked absent =>
              obtain ⟨site,member,equal⟩ := generated_registered formed generated
              exact False.elim (absent site member equal)
          | refresh => exact ih
          | equate => exact ih
          | reobserve => exact ih
      | merge => exact ih
      | install packet support enabled novel guard =>
          have terminal := (shape packet.declaration enabled.1.2.2.2.1).terminal
          change _ ++ packet.children.map (GeneralNominalSharedEmission.childSite packet) = _
          rw [children_empty packet terminal,List.map_nil,List.append_nil]
          exact ih

theorem enabled_site (shape : RegistryShape registry) (formed : SourceFormed registry root state)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet) :
    packet.site = pointSite root := by
  have member := enabled.1.2.2.1
  rw [formed_sites shape formed] at member
  exact List.mem_singleton.mp member

theorem generated_root (shape : RegistryShape registry) (formed : SourceFormed registry root state)
    (generated : Generated state.current root focus) : focus = root := by
  obtain ⟨site,member,equal⟩ := generated_registered formed generated
  rw [formed_sites shape formed] at member
  cases List.mem_singleton.mp member
  exact equal.symm

theorem argument_point (point : Point root input) (index : Fin (roles root.demand.role).arity) :
    root.demand.arguments index = (input,input) := by
  have member : root.demand.arguments index ∈ List.ofFn root.demand.arguments := List.mem_ofFn.mpr ⟨index,rfl⟩
  rw [point] at member
  exact List.mem_singleton.mp member

theorem point_inputs (point : Point root input) : (pointSite root).inputs = [some (.source input)] := by
  have mapped := congrArg (List.map fun bounds : Nat × Nat =>
    if bounds.1 = bounds.2 then some (Origin.source bounds.1) else none) point
  simpa [Point,pointSite,List.map_ofFn,Function.comp_def] using mapped

theorem initial_input (point : Point root input)
    (source : GeneralNominalSourceFormation.InitialSource registry context root) :
    input ∈ GeneralNominalState.sources context.state := by
  have present : (input,input) ∈ List.ofFn root.demand.arguments := by rw [point]; simp
  obtain ⟨index,equal⟩ := List.mem_ofFn.mp present
  have linked := (source.linked.1 index).1
  simpa only [equal] using linked

/-- A duplicate-free list of exactly the initial listed IDs, using its seed. -/
def basis (context : GeneralNominalCandidates.Context) : List Nat :=
  (List.range (context.state.seed+1)).filter fun name => name ∈ GeneralNominalState.sources context.state

theorem basis_distinct (context : GeneralNominalCandidates.Context) : (basis context).Nodup :=
  List.nodup_range.filter _

theorem basis_exact (source : GeneralNominalSourceFormation.InitialSource registry context root) :
    identity ∈ basis context ↔ identity ∈ GeneralNominalState.sources context.state := by
  simp only [basis,List.mem_filter,List.mem_range,decide_eq_true_eq]
  exact ⟨And.right,fun member => ⟨Nat.lt_succ_of_le (source.below_seed identity member),member⟩⟩

theorem initial_frontier (point : Point root input)
    (source : GeneralNominalSourceFormation.InitialSource registry context root) :
    (basis context).Nodup ∧ input ∈ basis context ∧
      ∀ output ∈ root.demand.outputs, output.target ∈ basis context :=
  ⟨basis_distinct context,(basis_exact source).mpr (initial_input point source),
    fun output member => (basis_exact source).mpr (source.linked.2 output member)⟩

variable {packet : Packet roles} {slot : Fin packet.context.state.base.slots}

theorem enabled_bounds (shape : RegistryShape registry) (formed : SourceFormed registry root state)
    (point : Point root input) (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet) :
    ∃ slot : Fin packet.context.state.base.slots, packet.bounds = [(slot,slot)] ∧
      packet.context.state.base.source slot = input := by
  have located := enabled.1.2.2.2.2.2.1
  rw [enabled_site shape formed enabled] at located
  exact located_point point located

theorem inherited_capture (shape : Shape packet.declaration) (bounds : packet.bounds = [(slot,slot)])
    (site : packet.site = pointSite root) (point : Point root input) :
    (GeneralNominalSharedCaptures.inheritedReport packet).captures =
      [⟨0,(slot,slot),some (.source input)⟩] := by
  have inputs : packet.site.inputs = [some (.source input)] := by rw [site]; exact point_inputs point
  simp [GeneralNominalSharedCaptures.inheritedReport,bounds,GeneralNominalInspection.queries,
    Declaration.normalHead,shape.head,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,
    inspectMany,inspect,Report.append,inputs]

theorem reads_empty (shape : Shape declaration) (context : GeneralNominalCandidates.Context)
    (slot : Fin context.state.base.slots) :
    readsMany context.state (GeneralNominalInspection.queries context.state context.interpretation declaration)
      [(slot,slot)] = [] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,shape.head,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,readsMany,reads]

/-- Root uses and reads of this packet's declaration. -/
def HeadUse (packet : Packet roles) (identity : Nat) : Prop :=
  (∃ index, identity = (packet.site.occurrence.demand.arguments index).1) ∨
    ∃ slot ∈ readsMany packet.context.state
      (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration)
      packet.bounds, identity = packet.context.state.base.source slot

theorem head_use_exact (shape : RegistryShape registry) (formed : SourceFormed registry root state)
    (point : Point root input) (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (use : HeadUse packet identity) : identity = input := by
  obtain ⟨slot,bounds,_⟩ := enabled_bounds shape formed point enabled
  rcases use with one | ⟨read,member,_⟩
  · rw [enabled_site shape formed enabled] at one
    obtain ⟨index,rfl⟩ := one
    exact congrArg Prod.fst (argument_point point index)
  · rw [bounds,reads_empty (shape packet.declaration enabled.1.2.2.2.1)] at member
    cases member

theorem reserved_not_head (shape : RegistryShape registry) (formed : SourceFormed registry root state)
    (point : Point root input) (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (different : identity ≠ input) : ¬ HeadUse packet identity :=
  fun use => different (head_use_exact shape formed point enabled use)

/-- All visible alternatives, as quantified by the actual decision guard. -/
def DecisionUse (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (identity : Nat) : Prop :=
  (∃ index, identity = (root.demand.arguments index).1) ∨
    ∃ declaration ∈ registry.declarations, declaration.role = root.demand.role ∧
      ∃ bounds, GeneralNominalCandidates.arguments context root = some bounds ∧
        ∃ slot ∈ readsMany context.state
          (GeneralNominalInspection.queries context.state context.interpretation declaration) bounds,
          identity = context.state.base.source slot

theorem decision_use_exact (shape : RegistryShape registry) (point : Point root input)
    (use : DecisionUse registry context root identity) : identity = input := by
  rcases use with ⟨index,rfl⟩ | ⟨declaration,visible,_,bounds,located,read,member,_⟩
  · exact congrArg Prod.fst (argument_point point index)
  · obtain ⟨slot,rfl,_⟩ := located_point point located
    rw [reads_empty (shape declaration visible)] at member
    cases member

theorem new_id_not_decision (shape : RegistryShape registry) (point : Point root input)
    (different : identity ≠ input) : ¬ DecisionUse registry context root identity :=
  fun use => different (decision_use_exact shape point use)

/-- The two facets collapse because this source argument is point-valued. -/
theorem capture_facets (shape : Shape packet.declaration) (bounds : packet.bounds = [(slot,slot)])
    (source : packet.context.state.base.source slot = input) (model : Assignment) :
    Equivalent (model (GeneralNominalPacketSupport.capture packet |>.inputs 0).1).1
      ((GeneralNominalHoleFacets.Facet.leaf input).eval fun name => (model name).1) ∧
    Equivalent (model (GeneralNominalPacketSupport.capture packet |>.inputs 0).2).1
      ((GeneralNominalHoleFacets.Facet.leaf input).eval fun name => (model name).1) := by
  rw [capture_exact shape bounds,source]
  exact ⟨⟨subtype_refl _,subtype_refl _⟩,⟨subtype_refl _,subtype_refl _⟩⟩

theorem target_requested (member : target ∈ targets declaration root) :
    ∃ output ∈ root.demand.outputs, output.target = target := by
  obtain ⟨request,present,rfl⟩ := List.mem_map.mp member
  obtain ⟨output,outputMember,equation,_,_,rfl⟩ :=
    GeneralNominalFiniteAssociatedFacts.root_request_witness _ _ _ present
  exact ⟨output,outputMember,rfl⟩

theorem target_complete (defined : RootDefined declaration root) (member : output ∈ root.demand.outputs) :
    output.target ∈ targets declaration root := by
  obtain ⟨equation,present,same⟩ := defined output member
  cases found : declaration.associated.find? (fun equation => equation.name == output.name) with
  | none =>
      have absent := List.find?_eq_none.mp found equation present
      simp [same] at absent
  | some selected =>
      apply List.mem_map.mpr
      refine ⟨⟨selected.rhs,output.target,.actual⟩,?_,rfl⟩
      apply List.mem_flatMap.mpr
      exact ⟨output,member,by simp [found]⟩

theorem output_readback (shape : Shape packet.declaration) (bounds : packet.bounds = [(slot,slot)])
    (source : packet.context.state.base.source slot = input)
    (member : target ∈ targets packet.declaration packet.site.occurrence) :
    GeneralNominalHoleReadback.Over packet.Holds [.source input] (.source target) (.leaf (.source input)) := by
  refine ⟨?_,by simp [Expr.leaves]⟩
  intro model valid
  have same := (outputs_exact shape bounds model).mp ((GeneralNominalPacketSupport.packet_exact packet model).mp valid).2.2 target member
  rw [source] at same
  refine ⟨⟨_,.source _⟩,⟨_,.source _⟩,?_⟩
  intro a b one two; cases one; cases two; exact same

end Yulang.GeneralNominalIdentityProvenance
