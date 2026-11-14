import Yulang.GeneralNominalHeadSemanticTransport185
import Yulang.GeneralNominalHeadCoreCoverage185
import Yulang.GeneralNominalCompleteNames183
import Yulang.GeneralNominalCenteredCaptureSchema

/-! Semantic transport through the actual recursive head schema. Corresponding
origins may have equal observation sets without being inhabited. At the outer
centers, Same suffices. No syntactic equality of centers is required. -/
namespace Yulang.GeneralNominalHeadSchemaSemantic186
open GeneralNominalRecursiveInspection GeneralNominalMaterialization GeneralNominalOriginTerms
open GeneralNominalInspection (Query)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

variable {model : Assignment}

def Related (model : Assignment) (first last : Origin) : Prop :=
  (∀ value, Observes model first value ↔ Observes model last value) ∨ Same model first last

theorem related_symm (related : Related model first last) : Related model last first := by
  rcases related with equal | same
  · exact .inl (fun value => (equal value).symm)
  · exact .inr (same_symm same)

theorem related_holds (related : Related model first last)
    (valid : Holds model term first) : Holds model term last := by
  rcases related with equal | same
  · exact holds_observations term equal valid
  · exact holds_transport same valid

private theorem equivalent_trans (first : Equivalent a b) (last : Equivalent b c) : Equivalent a c :=
  ⟨subtype_trans first.1 last.1,subtype_trans last.2 first.2⟩

theorem structural_related (related : Related model first last) (shape : GeneralNormalizedObservation.Shape)
    (index : Nat) : Related model (.structural first shape index) (.structural last shape index) := by
  apply Or.inl
  have forward : ∀ {a b}, Related model a b → ∀ value,
      Observes model (.structural a shape index) value → Observes model (.structural b shape index) value := by
    intro a b relation value seen
    cases seen with
    | structural parent length equal found =>
      rcases relation with eqv | same
      · exact .structural ((eqv _).mp parent) length equal found
      · obtain ⟨other,observed⟩ := same.2.1
        exact .structural observed length
          (equivalent_trans ⟨(same.2.2 _ _ parent observed).2,(same.2.2 _ _ parent observed).1⟩ equal) found
  intro value
  exact ⟨forward related value,forward (related_symm related) value⟩

theorem nominal_related (related : Related model first last) (name index : Nat) :
    Related model (.nominal first name index) (.nominal last name index) := by
  apply Or.inl
  have forward : ∀ {a b}, Related model a b → ∀ value,
      Observes model (.nominal a name index) value → Observes model (.nominal b name index) value := by
    intro a b relation value seen
    cases seen with
    | nominal parent equal found =>
      rcases relation with eqv | same
      · exact .nominal ((eqv _).mp parent) equal found
      · obtain ⟨other,observed⟩ := same.2.1
        exact .nominal observed
          (equivalent_trans ⟨(same.2.2 _ _ parent observed).2,(same.2.2 _ _ parent observed).1⟩ equal) found
  intro value
  exact ⟨forward related value,forward (related_symm related) value⟩

mutual
 theorem schema_correspondence (query : Query) (first last : Origin) (mode : Mode)
    (related : Related model first last) (entry : Use)
    (member : entry ∈ (schema query first mode).variables) :
    ∃ other ∈ (schema query last mode).variables,
      entry.name = other.name ∧ entry.mode = other.mode ∧ Related model entry.origin other.origin := by
  cases query with
  | variables names =>
    simp only [schema] at member ⊢
    obtain ⟨name,present,rfl⟩ := List.mem_map.mp member
    exact ⟨⟨name,last,mode⟩,List.mem_map.mpr ⟨name,present,rfl⟩,rfl,rfl,related⟩
  | scalar base => simp [schema] at member
  | deferred reason => simp [schema] at member
  | node shape children =>
    simp only [schema] at member ⊢
    exact schemas_correspondence children _ _ mode 0
      (fun index => structural_related related shape index) entry member
  | nominal name children =>
    simp only [schema] at member ⊢
    exact schemas_correspondence children _ _ .actual 0
      (fun index => nominal_related related name index) entry member
 termination_by sizeOf query

 theorem schemas_correspondence (queries : List Query) (first last : Nat → Origin) (mode : Mode)
    (index : Nat) (related : ∀ i, Related model (first i) (last i)) (entry : Use)
    (member : entry ∈ (schemas queries first mode index).variables) :
    ∃ other ∈ (schemas queries last mode index).variables,
      entry.name = other.name ∧ entry.mode = other.mode ∧ Related model entry.origin other.origin := by
  cases queries with
  | nil => simp [schemas] at member
  | cons query rest =>
    simp only [schemas,Schema.append,List.mem_append] at member ⊢
    rcases member with here | later
    · obtain ⟨other,present,name,modeEq,origins⟩ := schema_correspondence query _ _ mode (related index) entry here
      exact ⟨other,Or.inl present,name,modeEq,origins⟩
    · obtain ⟨other,present,name,modeEq,origins⟩ := schemas_correspondence rest first last mode (index+1) related entry later
      exact ⟨other,Or.inr present,name,modeEq,origins⟩
 termination_by sizeOf queries
end

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters

/-- The two plans need not be syntactically the same site, or the same packet.
Only query configuration and semantic centers are shared. -/
theorem head_correspondence (first last : Plan roles)
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (centers : ∀ index : Nat,
      Same model (.source ((List.ofFn first.input.center)[index]?.getD 0))
        (.source ((List.ofFn last.input.center)[index]?.getD 0)))
    (entry : Use) (member : entry ∈ first.headSchema.variables) :
    ∃ other ∈ last.headSchema.variables,
      entry.name = other.name ∧ entry.mode = other.mode ∧ Related model entry.origin other.origin := by
  have queries : GeneralNominalInspection.queries first.packet.context.state
      first.packet.context.interpretation first.packet.declaration =
      GeneralNominalInspection.queries last.packet.context.state
        last.packet.context.interpretation last.packet.declaration := by
    simp only [GeneralNominalInspection.queries,constructors,interpretation,declaration]
  unfold Plan.headSchema at member ⊢
  rw [← queries]
  exact schemas_correspondence _ _ _ .actual 0 (fun index => Or.inr (centers index)) entry member

/-- Finished head inspection supplies a concrete actual use for each input
name, including a terminal declaration with no where children. -/
theorem input_use (plan : Plan roles)
    (finished : Finished (GeneralNominalQueryProvenance183.headInspection plan))
    (name : Nat) (named : name ∈ plan.packet.declaration.inputNames) :
    ∃ origin, (⟨name,origin,.actual⟩ : Use) ∈ plan.headSchema.variables := by
  obtain ⟨captured,present,equal⟩ := GeneralNominalCompleteNames183.declaration_input_capture
    plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration
    plan.packet.bounds _ 0 finished name named
  obtain ⟨origin,_,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured present
  exact ⟨origin,equal ▸ used⟩

/-- Semantic center agreement yields semantic binder agreement, without equal
capture bounds, equal source names, or equal point/nonpoint decisions. -/
theorem binder_same (first last : Plan roles)
    (declaration : first.packet.declaration = last.packet.declaration)
    (constructors : first.packet.context.state.constructors = last.packet.context.state.constructors)
    (interpretation : first.packet.context.interpretation = last.packet.context.interpretation)
    (centers : ∀ index : Nat,
      Same model (.source ((List.ofFn first.input.center)[index]?.getD 0))
        (.source ((List.ofFn last.input.center)[index]?.getD 0)))
    (one : first.SchemaHolds first.headSchema model)
    (two : last.SchemaHolds last.headSchema model)
    (finished : Finished (GeneralNominalQueryProvenance183.headInspection first))
    (name : Nat) (named : name ∈ first.packet.declaration.inputNames) :
    Same model (.source (first.binder name)) (.source (last.binder name)) := by
  obtain ⟨origin,present⟩ := input_use first finished name named
  obtain ⟨other,found,nameEq,modeEq,related⟩ := head_correspondence first last declaration
    constructors interpretation centers ⟨name,origin,.actual⟩ present
  have original : Same model origin (.source (first.binder name)) := by
    simpa only [ite_true] using one.2 ⟨name,origin,.actual⟩ present
  have transported : Same model other.origin (.source (first.binder name)) :=
    related_holds (term := .leaf (.source (first.binder name))) related original
  have target : Same model other.origin (.source (last.binder name)) := by
    have equation := two.2 other found
    have actual : other.mode = .actual := modeEq.symm
    simpa only [actual,ite_true,← nameEq] using equation
  exact same_trans (same_symm transported) target

end Yulang.GeneralNominalHeadSchemaSemantic186
