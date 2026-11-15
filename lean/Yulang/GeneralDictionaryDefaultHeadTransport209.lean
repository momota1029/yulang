import Yulang.GeneralDictionaryDefaultFrameSemantics209
import Yulang.GeneralNominalReportTransport188

set_option backward.isDefEq.respectTransparency false

/-! Actual head-schema transport uses semantic observation correspondence and
binder equivalence, not equality of reports or center source names. -/
namespace Yulang.GeneralDictionaryDefaultHeadTransport209
open GeneralNominalCenters GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalOriginTerms GeneralNominalOriginAlias181 CommonNominalFullCarrier
open GeneralDictionaryDefaultExpression209
variable {roles : Roles.RoleDecls} {first last : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

 theorem similar_of_observations (agree : ∀ value, Observes model a value ↔ Observes model b value) :
    Similar model a b :=
  ⟨fun value seen => ⟨value,(agree value).mp seen,equivalent_refl _⟩,
    fun value seen => ⟨value,(agree value).mpr seen,equivalent_refl _⟩⟩

 theorem head_similar (similar : Similar model a b) (held : Head model a test) : Head model b test := by
  obtain ⟨value,seen⟩ := held.1
  obtain ⟨other,observed,_⟩ := similar.1 value seen
  refine ⟨⟨other,observed⟩,?_⟩
  intro value seen
  obtain ⟨old,observed,equal⟩ := similar.2 value seen
  exact GeneralNominalReportTransport188.test_transport test equal (held.2 old observed)

 theorem actual_similar (similar : Similar model a b)
    (binders : Equivalent (model x).1 (model y).1)
    (held : Same model a (.source x)) : Same model b (.source y) := by
  obtain ⟨value,seen⟩ := held.1
  obtain ⟨other,observed,_⟩ := similar.1 value seen
  refine ⟨⟨other,observed⟩,⟨_,.source _⟩,?_⟩
  intro value target seen source
  cases source
  obtain ⟨old,observed,equal⟩ := similar.2 value seen
  exact equivalent_trans equal (equivalent_trans (held.2.2 _ _ observed (.source _)) binders)

 theorem append_iff (plan : Plan roles) (one two : Schema) :
    plan.SchemaHolds (one.append two) model ↔ plan.SchemaHolds one model ∧ plan.SchemaHolds two model := by
  simp only [Plan.SchemaHolds,Schema.append,List.mem_append,forall_and,or_imp]
  exact ⟨fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2,h.2.2⟩,fun h => ⟨⟨h.1.1,h.2.1⟩,h.1.2,h.2.2⟩⟩

 theorem tested_iff (plan : Plan roles) (schema : Schema) (origin : Origin) (test : Test) :
    plan.SchemaHolds {schema with tests := (origin,test)::schema.tests} model ↔
      Head model origin test ∧ plan.SchemaHolds schema model := by
  simp only [Plan.SchemaHolds,List.mem_cons,forall_eq_or_imp]
  exact ⟨fun h => ⟨h.1.1,h.1.2,h.2⟩,fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩⟩

mutual
 theorem schema_transport (query : GeneralNominalInspection.Query)
    (similar : Similar model a b)
    (binders : ∀ name, Equivalent (model (first.binder name)).1 (model (last.binder name)).1)
    (held : first.SchemaHolds (schema query a .actual) model) :
    last.SchemaHolds (schema query b .actual) model := by
  cases query with
  | variables names =>
    simp only [schema] at held ⊢
    constructor
    · intro test member; cases member
    · intro entry member
      obtain ⟨name,present,rfl⟩ := List.mem_map.mp member
      have old := held.2 _ (List.mem_map.mpr ⟨name,present,rfl⟩)
      exact actual_similar similar (binders name) old
  | scalar base =>
    simp only [schema] at held ⊢
    constructor
    · intro test member
      cases List.mem_singleton.mp member
      exact head_similar similar (held.1 _ (List.mem_singleton_self _))
    · intro entry member; cases member
  | deferred =>
    simp only [schema] at held ⊢
    constructor <;> intro entry member <;> cases member
  | node shape children =>
    simp only [schema] at held ⊢
    have old := (tested_iff first _ a (.structural shape)).mp held
    apply (tested_iff last _ b (.structural shape)).mpr
    refine ⟨head_similar similar old.1,?_⟩
    exact schemas_transport children (fun index => similar_of_observations
      (structural_congr model a b similar shape index)) binders old.2
  | nominal name children =>
    simp only [schema] at held ⊢
    have old := (tested_iff first _ a (.nominal name children.length)).mp held
    apply (tested_iff last _ b (.nominal name children.length)).mpr
    refine ⟨head_similar similar old.1,?_⟩
    exact schemas_transport children (fun index => similar_of_observations
      (nominal_congr model a b similar name index)) binders old.2
 termination_by sizeOf query
 theorem schemas_transport (queries : List GeneralNominalInspection.Query)
    (similar : ∀ index, Similar model (a index) (b index))
    (binders : ∀ name, Equivalent (model (first.binder name)).1 (model (last.binder name)).1)
    (held : first.SchemaHolds (schemas queries a .actual offset) model) :
    last.SchemaHolds (schemas queries b .actual offset) model := by
  cases queries with
  | nil =>
    simp only [schemas]
    constructor <;> intro entry member <;> cases member
  | cons query rest =>
    simp only [schemas] at held ⊢
    have old := (append_iff first _ _).mp held
    exact (append_iff last _ _).mpr
      ⟨schema_transport query (similar offset) binders old.1,
        schemas_transport rest similar binders old.2⟩
 termination_by sizeOf queries
end

 theorem head_schema_transport
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (centers : ∀ index : Nat, Equivalent
      (model ((List.ofFn first.input.center)[index]?.getD 0)).1
      (model ((List.ofFn last.input.center)[index]?.getD 0)).1)
    (binders : ∀ name, Equivalent (model (first.binder name)).1 (model (last.binder name)).1)
    (held : first.SchemaHolds first.headSchema model) :
    last.SchemaHolds last.headSchema model := by
  have queries : GeneralNominalInspection.queries first.packet.context.state first.packet.context.interpretation first.packet.declaration =
      GeneralNominalInspection.queries last.packet.context.state last.packet.context.interpretation last.packet.declaration := by
    simp only [GeneralNominalInspection.queries,constructors,interpretation,declaration]
  unfold Plan.headSchema at held ⊢
  rw [← queries]
  apply schemas_transport _ _ binders held
  intro index
  constructor
  · intro value observed; cases observed
    exact ⟨_,.source _,centers index⟩
  · intro value observed; cases observed
    exact ⟨_,.source _,⟨(centers index).2,(centers index).1⟩⟩

/-- Point input centers provide the root comparison even after metadata
reobservation. Binder agreement remains an explicit semantic premise. -/
 theorem point_head_schema_transport
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (occurrence : first.input.occurrence = last.input.occurrence)
    (point : ∀ index, (first.input.occurrence.demand.arguments index).1 =
      (first.input.occurrence.demand.arguments index).2)
    (one : first.input.Holds model) (two : last.input.Holds model)
    (binders : ∀ name, Equivalent (model (first.binder name)).1 (model (last.binder name)).1)
    (held : first.SchemaHolds first.headSchema model) :
    last.SchemaHolds last.headSchema model :=
  head_schema_transport declaration constructors interpretation
    (GeneralDictionaryDefaultPointTransport209.centers_equivalent first.input last.input occurrence point one two)
    binders held

/-- Current selected-witness representatives need no extra binder agreement:
checked declaration keys and identical current frames derive it. -/
 theorem current_frame_schema
    (checked : GeneralDeclarations.Checked registry)
    (one : GeneralNominalCenteredHeadOutputs.Frame registry state focus key first)
    (two : GeneralNominalCenteredHeadOutputs.Frame registry state focus key last)
    (point : ∀ index, (focus.demand.arguments index).1 = (focus.demand.arguments index).2)
    (firstHolds : first.input.Holds model) (lastHolds : last.input.Holds model)
    (held : first.SchemaHolds first.headSchema model) : last.SchemaHolds last.headSchema model := by
  have firstFocus := first.input_exact.trans one.occurrence_eq
  have lastFocus := last.input_exact.trans two.occurrence_eq
  apply point_head_schema_transport
    (GeneralDictionaryDefaultFrameSemantics209.declaration checked one two)
    (congrArg (fun context : GeneralNominalCandidates.Context => context.state.constructors)
      (one.context_eq.trans two.context_eq.symm))
    (congrArg GeneralNominalCandidates.Context.interpretation (one.context_eq.trans two.context_eq.symm))
    (firstFocus.trans lastFocus.symm) (firstFocus.symm ▸ point) firstHolds lastHolds _ held
  intro name
  rw [GeneralDictionaryDefaultFrameSemantics209.binder checked one two name]
  exact equivalent_refl _

end Yulang.GeneralDictionaryDefaultHeadTransport209
