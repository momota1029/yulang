import Yulang.GeneralDictionaryObservedClosedRequests

/-! Arbitrary finite nominal arity, with exact indexed point source edges.
Only the binary cap is removed; closed queries and existing targets remain. -/
namespace Yulang.GeneralDictionaryObservedFiniteRequests
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralNominalSpineFacts GeneralNominalBranchProjection
open GeneralDictionaryObservedClosedRequests (ClosedValid TestValid empty_valid append_valid prepend_valid nominal_valid)
open GeneralNominalInspection (Query)

inductive Tree (state : GeneralNominalState.State) : Fin state.base.slots → Query → Type where
  | scalar (slot base) (head : state.view.heads slot = .scalar base) : Tree state slot (.scalar base)
  | nominal {n : Nat} (slot) (descriptor : GeneralNominalState.Descriptor state.base.slots)
      (recorded : state.nominals slot = some descriptor)
      (slots : Fin n → Fin state.base.slots) (queries : Fin n → Query)
      (parameters : descriptor.arguments = List.ofFn fun i => .type (slots i,slots i))
      (branches : ∀ i, Tree state (slots i) (queries i)) :
      Tree state slot (.nominal descriptor.declaration.name (List.ofFn queries))

theorem schemas_valid (model : GeneralNominalCommonBridge.Assignment)
    (queries : List Query) (origins : Nat → Origin) (mode : Mode) (start : Nat)
    (good : ∀ index query, queries[index]? = some query →
      ClosedValid model (schema query (origins (start + index)) mode)) :
    ClosedValid model (schemas queries origins mode start) := by
  induction queries generalizing start with
  | nil => simpa only [schemas] using empty_valid model
  | cons query rest ih =>
    simp only [schemas]
    apply append_valid
    · simpa using good 0 query rfl
    · apply ih
      intro index query found
      have result := good (index+1) query (by simpa using found)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

theorem tree_schema (state : GeneralNominalState.State) {slot query}
    (tree : Tree state slot query) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (origin : Origin) (mode : Mode)
    (consistent : Matches state model slot origin) : ClosedValid model (schema query origin mode) := by
  induction tree generalizing origin mode with
  | scalar slot base head =>
    exact GeneralDictionaryObservedClosedRequests.tree_schema state (.scalar slot base head) model valid origin mode consistent
  | @nominal n slot descriptor recorded slots queries parameters branches ih =>
    simp only [schema,List.length_ofFn]
    apply prepend_valid
    · apply schemas_valid
      intro index query found
      have bound : index < n := by
        have h := List.getElem?_eq_some_iff.mp found
        simpa using h.1
      have same : queries ⟨index,bound⟩ = query := by
        obtain ⟨h,eq⟩ := List.getElem?_eq_some_iff.mp found
        simpa using eq
      subst query
      apply ih ⟨index,bound⟩ _ .actual
      simpa using point_argument_matches state model valid slot (slots ⟨index,bound⟩) descriptor recorded index
        (by rw [parameters]; simp [bound]) origin consistent
    · exact nominal_valid state model valid slot descriptor recorded n (by rw [parameters]; simp) origin consistent

theorem schemas_shape (queries : List Query) (origins : Nat → Origin) (mode : Mode) (start : Nat)
    (good : ∀ index query, queries[index]? = some query →
      (schema query (origins (start+index)) mode).variables = [] ∧
      (schema query (origins (start+index)) mode).unknown = false) :
    (schemas queries origins mode start).variables = [] ∧
      (schemas queries origins mode start).unknown = false := by
  induction queries generalizing start with
  | nil => simp [schemas]
  | cons query rest ih =>
    have first := good 0 query rfl
    simp only [Nat.add_zero] at first
    have last := ih (start+1) (by
      intro index query found
      have result := good (index+1) query (by simpa using found)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result)
    simp only [schemas,Schema.append]
    simp [first.1,first.2,last.1,last.2]

theorem tree_shape (state : GeneralNominalState.State) {slot query}
    (tree : Tree state slot query) (origin : Origin) (mode : Mode) :
    (schema query origin mode).variables = [] ∧ (schema query origin mode).unknown = false := by
  induction tree generalizing origin mode with
  | scalar => simp [schema]
  | @nominal n slot descriptor recorded slots queries parameters branches ih =>
    simp only [schema]
    apply schemas_shape
    intro index query found
    obtain ⟨bound,eq⟩ := List.getElem?_eq_some_iff.mp found
    have bound' : index < n := by simpa using bound
    have same : queries ⟨index,bound'⟩ = query := by simpa using eq
    subst query
    simpa using ih ⟨index,bound'⟩ (.nominal origin descriptor.declaration.name index) .actual

/-- Every previous binary certificate embeds; exact child slots are preserved. -/
noncomputable def of_closed (state : GeneralNominalState.State) {slot query}
    (tree : GeneralDictionaryObservedClosedRequests.Tree state slot query) : Tree state slot query := by
  induction tree with
  | scalar slot base head => exact .scalar slot base head
  | nil slot descriptor recorded parameters =>
    exact .nominal slot descriptor recorded (n := 0) Fin.elim0 Fin.elim0
      (by simpa using parameters) (fun i => Fin.elim0 i)
  | @one query slot child descriptor recorded parameters rest ih =>
    exact .nominal slot descriptor recorded (n := 1) (fun _ => child) (fun _ => query)
      (by simpa [List.ofFn_succ] using parameters) (fun _ => ih)
  | @two one two slot left right descriptor recorded parameters first last ihOne ihTwo =>
    exact .nominal slot descriptor recorded (n := 2) (Fin.cases left (fun _ => right))
      (Fin.cases one (fun _ => two)) (by simpa [List.ofFn_succ] using parameters)
      (Fin.cases ihOne (fun _ => ihTwo))

/-- Arbitrary finite point nominal arity, not a generated-model premise. -/
def Observed (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request) : Prop :=
  ∀ request ∈ requests, ∃ slot : Fin state.base.slots,
    request.target = state.base.source slot ∧
    Nonempty (Tree state slot (GeneralNominalInspection.translate state.constructors interpretation
      (GeneralDeclarationPatterns.normalize request.pattern)))

theorem observed_of_closed (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request)
    (observed : GeneralDictionaryObservedClosedRequests.Observed state interpretation requests) :
    Observed state interpretation requests := by
  intro request member
  obtain ⟨slot,target,⟨tree⟩⟩ := observed request member
  exact ⟨slot,target,⟨of_closed state tree⟩⟩

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

end Yulang.GeneralDictionaryObservedFiniteRequests
