import Yulang.GeneralNominalHistoricalNodeEvidence

/-! Recover whole nominal output equality from actual recorded materialization
facts, rather than assuming output equality or a current equation path. -/
namespace Yulang.GeneralNominalMaterializedHeadRecovery
open CommonNominalFullCarrier GeneralNominalRecursiveInspection
open GeneralNominalLinearCaptureFacts GeneralNominalLinearMaterializationFacts
open GeneralNominalMaterialization GeneralDeclarations

/-- A nominal test witness agrees with every actual projection observation. -/
theorem observed_argument (model : GeneralNominalCommonBridge.Assignment)
    (source name index : Nat) (args : List Argument)
    (eq : Equivalent (model source).1 (nominal name args))
    (value : Argument) (found : args[index]? = some value)
    (actual : Ty) (seen : Observes model (.nominal (.source source) name index) actual) :
    ArgumentEquivalent value (.inl actual) := by
  cases seen with
  | nominal parent equal located =>
    cases parent
    exact ((nominal_regular_invariant_exact ..).mp (subtype_trans eq.2 equal.1)).2.2 index _ _ found located

/-- A fixed finite nominal head is determined by all its type projections. -/
theorem heads_equivalent (model : GeneralNominalCommonBridge.Assignment)
    (first last name n : Nat)
    (firstTest : (Test.nominal name n).Holds (model first).1)
    (lastTest : (Test.nominal name n).Holds (model last).1)
    (shared : ∀ i : Fin n, ∃ a b,
      Observes model (.nominal (.source first) name i.val) a ∧
      Observes model (.nominal (.source last) name i.val) b ∧ Equivalent a b) :
    Equivalent (model first).1 (model last).1 := by
  obtain ⟨xs,hxs,eqx⟩ := firstTest
  obtain ⟨ys,hys,eqy⟩ := lastTest
  have pointwise : ArgumentsEquivalent xs ys := by
    intro i x y hx hy
    have bound : i < n := by
      rw [← hxs]
      exact (List.getElem?_eq_some_iff.mp hx).1
    obtain ⟨a,b,ha,hb,eq⟩ := shared ⟨i,bound⟩
    have xa := observed_argument model first name i xs eqx x hx a ha
    have yb := observed_argument model last name i ys eqy y hy b hb
    cases x <;> cases y <;> simp only [ArgumentEquivalent] at *
    · exact ⟨subtype_trans xa.1 (subtype_trans eq.1 yb.2),
        subtype_trans yb.1 (subtype_trans eq.2 xa.2)⟩
    all_goals contradiction
  have forward := (nominal_regular_invariant_exact name name xs ys).mpr ⟨rfl,hxs.trans hys.symm,pointwise⟩
  have reverse := (nominal_regular_invariant_exact name name ys xs).mpr ⟨rfl,hys.trans hxs.symm,?_⟩
  · exact ⟨subtype_trans eqx.1 (subtype_trans forward eqy.2),
      subtype_trans eqy.1 (subtype_trans reverse eqx.2)⟩
  · intro i y x hy hx
    have eq := pointwise i x y hx hy
    cases x <;> cases y <;> simp only [ArgumentEquivalent] at *
    · exact ⟨eq.2,eq.1⟩
    · exact eq.symm

/-- A fully materialized nominal request identifies its whole target with the
inspected head. Cross-capture constraints, not just interval fits, are crucial. -/
theorem materialized_head_equivalent (state : GeneralNominalState.State)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (target : Nat) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model)
    (materialized : Models state declaration capture (captured state slot descriptor.declaration.name names bounds)
      (schema (.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])) (.source target) .actual) model) :
    Equivalent (model target).1 (model (state.base.source slot)).1 := by
  rw [GeneralNominalAssociatedSourceTransport.schema_source_exact] at materialized
  apply heads_equivalent model target (state.base.source slot) descriptor.declaration.name n
  · exact (materialized.1 (.source target,.nominal descriptor.declaration.name n) (by simp)).2 _ (.source target)
  · obtain ⟨args,fit,equal⟩ := valid.2.1 slot descriptor recorded
    refine ⟨args,?_,equal⟩
    rw [fitsAll_length state.base model descriptor.arguments args fit,parameters]
    exact List.length_ofFn
  · intro i
    obtain ⟨a,seenA⟩ := (materialized.2.1 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)).1
    obtain ⟨b,seenB⟩ := (nominal_argument_bounds state model valid slot descriptor recorded i.val (bounds i)
      (by rw [parameters]; simp [i.isLt])).1
    refine ⟨a,b,seenA,seenB,?_⟩
    exact materialized.2.2.2 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
      _ (List.mem_ofFn.mpr ⟨i,rfl⟩) rfl rfl _ rfl a b seenA
      (by simpa only [Nat.zero_add] using seenB)

/-- Every component's fields occur in the folded schema; cross-component
constraints may add obligations but cannot remove component obligations. -/
theorem component_membership (schemas : List Schema) (part : Schema) (member : part ∈ schemas) :
    (∀ t ∈ part.tests, t ∈ (schemas.foldr Schema.append {}).tests) ∧
    (∀ v ∈ part.variables, v ∈ (schemas.foldr Schema.append {}).variables) := by
  induction schemas with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨fun _ h => List.mem_append_left _ h,fun _ h => List.mem_append_left _ h⟩
    · have tail := ih later
      exact ⟨fun t h => List.mem_append_right _ (tail.1 t h),
        fun v h => List.mem_append_right _ (tail.2 v h)⟩

/-- Recover a particular actual request from the full generated schema. -/
theorem request_models (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : Report state) (requests : List Request) (request : Request) (member : request ∈ requests)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models state declaration capture report (generated state interpretation requests) model) :
    Models state declaration capture report
      (schema (GeneralNominalInspection.translate state.constructors interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) (.source request.target) request.mode) model := by
  let f := fun r : Request => schema (GeneralNominalInspection.translate state.constructors interpretation
    (GeneralDeclarationPatterns.normalize r.pattern)) (.source r.target) r.mode
  have included := component_membership (requests.map f) (f request) (List.mem_map.mpr ⟨request,member,rfl⟩)
  exact GeneralNominalFiniteAssociatedFacts.models_of_membership state declaration capture report _ _ model
    valid included.1 included.2

/-- Any actual request in a stored packet recovers whole-output equality at
EVERY current journal model. The original BranchModels is read from that journal,
not supplied as a separate semantic premise. -/
theorem packet_request_equivalent (state : GeneralNominalSaturationState.State roles)
    (packet : GeneralNominalSaturationState.Packet roles) (member : packet ∈ state.packets)
    (slot : Fin packet.context.state.base.slots)
    (descriptor : GeneralNominalState.Descriptor packet.context.state.base.slots)
    (recorded : packet.context.state.nominals slot = some descriptor)
    (headBounds : packet.bounds = [(slot,slot)]) {n : Nat} (names : Fin n → Nat)
    (bounds : Fin n → GeneralNominalInspection.Bounds packet.context.state)
    (parameters : descriptor.arguments = List.ofFn fun i => .type (bounds i))
    (query : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i])])
    (request : Request)
    (requested : request ∈ requests packet.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked packet.bindings)
    (actual : request.mode = .actual)
    (translated : GeneralNominalInspection.translate packet.context.state.constructors packet.context.interpretation
      (GeneralDeclarationPatterns.normalize request.pattern) =
      .nominal descriptor.declaration.name (List.ofFn fun i => .variables [names i]))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models state model) :
    Equivalent (model request.target).1 (model (packet.context.state.base.source slot)).1 := by
  have branch := valid.2.1 packet member
  change GeneralNominalRecursiveCandidates.BranchModels packet.registry packet.context packet.site.occurrence
    packet.declaration packet.checked packet.bounds model at branch
  have original := (GeneralNominalRecursiveCandidates.branch_interval_sound packet.registry packet.context
    packet.site.occurrence packet.declaration packet.checked packet.bounds model branch).1
  have one := request_models packet.context.state packet.context.interpretation packet.declaration _ _ _
    request requested model branch.2.2
  rw [translated,actual] at one
  have calculated := report_exact packet.context packet.declaration slot descriptor recorded names bounds parameters query
  rw [headBounds,calculated] at one
  exact materialized_head_equivalent packet.context.state packet.declaration _ slot descriptor recorded
    names bounds parameters request.target model original one

end Yulang.GeneralNominalMaterializedHeadRecovery
