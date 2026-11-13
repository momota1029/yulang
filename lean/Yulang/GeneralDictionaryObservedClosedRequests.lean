import Yulang.GeneralDictionaryObservedScalarRequests

/-! Closed observed source trees justify actual nominal materialization requests.
Internal edges are point intervals; variables, rows and fresh targets are excluded
explicitly. Nominal bodies are never traversed. -/
namespace Yulang.GeneralDictionaryObservedClosedRequests
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalSpineFacts GeneralNominalBranchProjection CommonNominalFullCarrier
open GeneralNominalInspection (Query)

inductive Tree (state : GeneralNominalState.State) : Fin state.base.slots → Query → Type where
  | scalar (slot base) (head : state.view.heads slot = .scalar base) : Tree state slot (.scalar base)
  | nil (slot) (descriptor : GeneralNominalState.Descriptor state.base.slots)
      (recorded : state.nominals slot = some descriptor) (parameters : descriptor.arguments = []) :
      Tree state slot (.nominal descriptor.declaration.name [])
  | one (slot child) (descriptor : GeneralNominalState.Descriptor state.base.slots)
      (recorded : state.nominals slot = some descriptor)
      (parameters : descriptor.arguments = [.type (child,child)])
      (rest : Tree state child query) : Tree state slot (.nominal descriptor.declaration.name [query])
  | two (slot left right) (descriptor : GeneralNominalState.Descriptor state.base.slots)
      (recorded : state.nominals slot = some descriptor)
      (parameters : descriptor.arguments = [.type (left,left),.type (right,right)])
      (first : Tree state left one) (last : Tree state right two) :
      Tree state slot (.nominal descriptor.declaration.name [one,two])

def TestValid (model : GeneralNominalCommonBridge.Assignment) (test : Origin × Test) : Prop :=
  (∃ actual, Observes model test.1 actual) ∧
    ∀ actual, Observes model test.1 actual → test.2.Holds actual

def ClosedValid (model : GeneralNominalCommonBridge.Assignment) (value : Schema) : Prop :=
  value.variables = [] ∧ value.unknown = false ∧ ∀ test ∈ value.tests, TestValid model test

theorem empty_valid (model : GeneralNominalCommonBridge.Assignment) : ClosedValid model {} := by
  exact ⟨rfl,rfl,by simp⟩

theorem append_valid (model : GeneralNominalCommonBridge.Assignment) (first last : Schema)
    (one : ClosedValid model first) (two : ClosedValid model last) :
    ClosedValid model (first.append last) := by
  refine ⟨by simp [Schema.append,one.1,two.1],by simp [Schema.append,one.2.1,two.2.1],?_⟩
  intro test member
  rcases List.mem_append.mp member with h | h
  · exact one.2.2 test h
  · exact two.2.2 test h

theorem prepend_valid (model : GeneralNominalCommonBridge.Assignment) (value : Schema)
    (test : Origin × Test) (good : ClosedValid model value) (valid : TestValid model test) :
    ClosedValid model {value with tests := test :: value.tests} := by
  refine ⟨good.1,good.2.1,?_⟩
  intro t member
  rcases List.mem_cons.mp member with rfl | member
  · exact valid
  · exact good.2.2 t member

theorem nominal_valid (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) (arity : Nat)
    (length : descriptor.arguments.length = arity) (origin : Origin)
    (consistent : Matches state model slot origin) :
    TestValid model (origin,.nominal descriptor.declaration.name arity) := by
  refine ⟨consistent.1,?_⟩
  intro actual seen
  have same := consistent.2 actual seen
  obtain ⟨values,fit,equal⟩ := valid.2.1 slot descriptor recorded
  exact ⟨values,(GeneralNominalLinearMaterializationFacts.fitsAll_length state.base model
    descriptor.arguments values fit).trans length,
    subtype_trans same.1 equal.1,subtype_trans equal.2 same.2⟩

theorem tree_schema (state : GeneralNominalState.State) {slot query}
    (tree : Tree state slot query) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (origin : Origin) (mode : Mode)
    (consistent : Matches state model slot origin) : ClosedValid model (schema query origin mode) := by
  induction tree generalizing origin mode with
  | scalar slot base head =>
    simp only [schema]
    refine ⟨rfl,rfl,?_⟩
    intro test member
    have same := List.mem_singleton.mp member
    subst test
    refine ⟨consistent.1,?_⟩
    intro actual seen
    have eq := consistent.2 actual seen
    have scalar := GeneralDictionaryObservedScalarRequests.source_scalar state slot base head model valid
    exact ⟨subtype_trans eq.1 scalar.1,subtype_trans scalar.2 eq.2⟩
  | nil slot descriptor recorded parameters =>
    simp only [schema,schemas,List.length_nil]
    apply prepend_valid model {} _ (empty_valid model)
    exact nominal_valid state model valid slot descriptor recorded 0 (by rw [parameters]; rfl) origin consistent
  | one slot child descriptor recorded parameters rest ih =>
    simp only [schema,schemas,List.length_cons,List.length_nil]
    apply prepend_valid
    · apply append_valid
      · exact ih _ .actual (point_child_matches state model valid slot child descriptor recorded parameters origin consistent)
      · exact empty_valid model
    · exact nominal_valid state model valid slot descriptor recorded 1 (by rw [parameters]; rfl) origin consistent
  | two slot left right descriptor recorded parameters first last ihOne ihTwo =>
    simp only [schema,schemas,List.length_cons,List.length_nil]
    apply prepend_valid
    · apply append_valid
      · exact ihOne _ .actual (point_argument_matches state model valid slot left descriptor recorded 0
          (by rw [parameters]; rfl) origin consistent)
      · apply append_valid
        · exact ihTwo _ .actual (point_argument_matches state model valid slot right descriptor recorded 1
            (by rw [parameters]; rfl) origin consistent)
        · exact empty_valid model
    · exact nominal_valid state model valid slot descriptor recorded 2 (by rw [parameters]; rfl) origin consistent

/-- Purely syntactic readiness: all constructors of Tree have closed queries. -/
theorem tree_shape (state : GeneralNominalState.State) {slot query}
    (tree : Tree state slot query) (origin : Origin) (mode : Mode) :
    (schema query origin mode).variables = [] ∧ (schema query origin mode).unknown = false := by
  induction tree generalizing origin mode with
  | scalar => simp [schema]
  | nil => simp [schema,schemas]
  | one slot child descriptor recorded parameters rest ih =>
    simp only [schema,schemas,Schema.append]
    simp [(ih _ .actual).1,(ih _ .actual).2]
  | two slot left right descriptor recorded parameters first last ihOne ihTwo =>
    simp only [schema,schemas,Schema.append]
    simp [(ihOne _ .actual).1,(ihOne _ .actual).2,(ihTwo _ .actual).1,(ihTwo _ .actual).2]

/-- Syntax/source certificate, not desired materialization Models. -/
def Observed (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request) : Prop :=
  ∀ request ∈ requests, ∃ slot : Fin state.base.slots,
    request.target = state.base.source slot ∧
    Nonempty (Tree state slot (GeneralNominalInspection.translate state.constructors interpretation
      (GeneralDeclarationPatterns.normalize request.pattern)))

theorem generated_shape (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request)
    (observed : Observed state interpretation requests) :
    (generated state interpretation requests).variables = [] ∧
      (generated state interpretation requests).unknown = false := by
  induction requests with
  | nil => exact ⟨rfl,rfl⟩
  | cons request rest ih =>
    obtain ⟨slot,target,⟨tree⟩⟩ := observed request (by simp)
    have first := tree_shape state tree (.source request.target) request.mode
    have last := ih (fun r member => observed r (by simp [member]))
    simp only [generated] at last
    simp only [generated,List.map_cons,List.foldr_cons,Schema.append]
    exact ⟨by simp [first.1,last.1],by simp [first.2,last.2]⟩

theorem generated_valid (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request)
    (observed : Observed state interpretation requests)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model) :
    ClosedValid model (generated state interpretation requests) := by
  induction requests with
  | nil => exact empty_valid model
  | cons request rest ih =>
    obtain ⟨slot,target,⟨tree⟩⟩ := observed request (by simp)
    apply append_valid
    · simp only [target]
      exact tree_schema state tree model valid _ request.mode (source_matches state model slot)
    · exact ih (fun r member => observed r (by simp [member]))

theorem generated_models (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request)
    (observed : Observed state interpretation requests)
    (declaration : GeneralDeclarations.Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : Report state) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) :
    Models state declaration capture report (generated state interpretation requests) model := by
  have good := generated_valid state interpretation requests observed model valid
  refine ⟨good.2.2,?_,?_,?_⟩
  · intro entry member; rw [good.1] at member; cases member
  · intro entry member; rw [good.1] at member; cases member
  · intro entry member; rw [good.1] at member; cases member

/-- Every scalar certificate is also a closed-tree certificate. -/
theorem observed_of_scalar (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request)
    (observed : GeneralDictionaryObservedScalarRequests.Observed state interpretation requests) :
    Observed state interpretation requests := by
  intro request member
  obtain ⟨slot,base,target,head,query⟩ := observed request member
  refine ⟨slot,target,?_⟩
  rw [query]
  exact ⟨.scalar slot base head⟩
end Yulang.GeneralDictionaryObservedClosedRequests
