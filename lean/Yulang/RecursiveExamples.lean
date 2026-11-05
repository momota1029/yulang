import Yulang.RecursiveInference
import Yulang.Structural

/-!
# Recursive checking with a writable top type

The depth-shaped core recursively replaces `x` by `(x, x)` and keeps an
integer result. Arithmetic and guards are abstracted to literals; no evaluation
or termination claim is made.

A full annotation checks every instance independently. With `any` as the top
type (spec/04-types.md §4.1, decision 36), this example ALSO has the monotype
`any -> int`: the recursive pair argument widens to `any`. The former claim
that every finite monotype is rejected was specific to the old top-free
algebra and is false in the current language. The witnesses below connect the
newly admitted monotype to the existing generated SCC constraints.
-/

namespace Yulang.RecursiveExamples

open Inference RecursiveInference

def depthBody : Expr :=
  .branch (.lit .bool) (.lit .int) (.app (.var 1) (.pair (.var 0) (.var 0)))

def depthFunction : Expr := .lam depthBody

def depthAnnotation : FullAnnotation α 1 where
  type := .arrow (.var (.inl 0)) .empty (.base .int) .empty
  function := rfl
  captured := rfl

def depthAssumption (Key : Type u) : Binding (Structural.model Key) :=
  .signature 1 (fun locals => Comp.pure (Structural.model Key)
    (.arrow (locals 0) [] (.base .int) []))

theorem depth_typing_at_every_instance (Key : Type u) (input : Structural.Ty Key) :
    Typing (Structural.model Key) [depthAssumption Key] depthFunction
      (.arrow input [] (.base .int) [], []) := by
  apply Typing.lam (m := Structural.model Key)
    (a := (input, [])) (b := (.base .int, []))
  · apply Typing.branch (m := Structural.model Key) (eg := [])
      (a := (.base .int, [])) (b := (.base .int, []))
    · exact Typing.lit ⟨.refl _, Structural.row_refl _⟩
    · exact Typing.lit ⟨.refl _, Structural.row_refl _⟩
    · apply Typing.app (m := Structural.model Key)
        (a := (.pair input input, [])) (b := (.base .int, [])) (ef := [])
      · exact Typing.var rfl (BindingTyping.signature (ι := fun _ => .pair input input)
          ⟨.refl _, Structural.row_refl _⟩)
      · apply Typing.pair (m := Structural.model Key) (a := (input, [])) (b := (input, []))
        · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, Structural.row_refl _⟩)
        · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, Structural.row_refl _⟩)
        · exact ⟨.refl _, Structural.row_refl _⟩
      · exact ⟨.refl _, Structural.row_refl _⟩
    · exact ⟨.unionElim (.refl _) (.refl _), Structural.row_refl _⟩
  · exact ⟨.refl _, Structural.row_refl _⟩

def annotatedDepth : List (Declaration Empty) := [.annotated 1 depthAnnotation depthFunction]

theorem annotated_depth_typing (Key : Type u) (ρ : Empty → Comp (Structural.model Key)) :
    SCCTyping (Structural.model Key) [] ρ annotatedDepth := by
  intro member present
  simp only [annotatedDepth, List.mem_singleton] at present
  subst member
  apply DefinitionTyping.annotated
  intro locals
  exact depth_typing_at_every_instance Key (locals 0)

theorem generated_annotated_depth_satisfied (Key : Type u)
    (ρ : Empty → Comp (Structural.model Key)) :
    (generateSCC [] annotatedDepth).Holds (Structural.model Key) ρ :=
  (generateSCC_exact _ ρ [] [] (EnvRel.nil _ _) annotatedDepth).mpr
    (annotated_depth_typing Key ρ)

theorem mono_variable_type {Γ : List (Binding (Structural.model Key))}
    {index : Nat} {assumed result : Comp (Structural.model Key)}
    (lookup : Γ[index]? = some (.mono assumed))
    (typed : Typing (Structural.model Key) Γ (.var index) result) :
    Structural.Subtype assumed.1 result.1 := by
  rcases (Typing.var_iff _ _ _ _).mp typed with ⟨binding, found, checked⟩
  rw [lookup] at found
  cases found
  cases checked with | mono h => exact h.1

/-- The same monotype is used by the definition and by every recursive call.
The pair argument is explicitly forgotten to `any`, as required by top. -/
def depthMonotype (Key : Type u) : Comp (Structural.model Key) :=
  (.arrow .top [] (.base .int) [], [])

theorem unannotated_depth_typable (Key : Type u) :
    Typing (Structural.model Key) [.mono (depthMonotype Key)] depthFunction
      (depthMonotype Key) := by
  apply Typing.lam (m := Structural.model Key)
    (a := (.top, [])) (b := (.base .int, []))
  · apply Typing.branch (m := Structural.model Key) (eg := [])
      (a := (.base .int, [])) (b := (.base .int, []))
    · exact Typing.lit ⟨.refl _, Structural.row_refl _⟩
    · exact Typing.lit ⟨.refl _, Structural.row_refl _⟩
    · apply Typing.app (m := Structural.model Key)
        (a := (.top, [])) (b := (.base .int, [])) (ef := [])
      · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, Structural.row_refl _⟩)
      · apply Typing.pair (m := Structural.model Key) (a := (.top, [])) (b := (.top, []))
        · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, Structural.row_refl _⟩)
        · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, Structural.row_refl _⟩)
        · exact ⟨.top _, Structural.row_refl _⟩
      · exact ⟨.refl _, Structural.row_refl _⟩
    · exact ⟨.unionElim (.refl _) (.refl _), Structural.row_refl _⟩
  · exact ⟨.refl _, Structural.row_refl _⟩

def unannotatedDepth : List (Declaration Unit) := [.inferred () depthFunction]

def depthAssignment (Key : Type u) : Unit → Comp (Structural.model Key) :=
  fun _ => depthMonotype Key

theorem generated_unannotated_depth_satisfied (Key : Type u) :
    (generateSCC [] unannotatedDepth).Holds (Structural.model Key) (depthAssignment Key) := by
  apply (generateSCC_exact _ _ [] [] (EnvRel.nil _ _) unannotatedDepth).mpr
  intro member present
  simp only [unannotatedDepth, List.mem_singleton] at present
  subst member
  exact DefinitionTyping.inferred (unannotated_depth_typable Key)

theorem closed_unannotated_depth_satisfied (Key : Type u)
    (ρ : Empty → Comp (Structural.model Key)) :
    (inferUnannotatedSCC [] (fun _ : Fin 1 => depthFunction)).Holds (Structural.model Key) ρ := by
  apply (inferUnannotatedSCC_exact _ ρ [] [] (EnvRel.nil _ _) _).mpr
  refine ⟨fun _ => depthMonotype Key, ?_⟩
  intro member present
  have present' : member = .inferred (.inl 0) depthFunction := by
    simpa [unannotatedMembers, List.ofFn_succ] using present
  subst member
  exact DefinitionTyping.inferred (unannotated_depth_typable Key)

/-! After-check generalization instantiates the whole checked value block at
each use. The captured environment is the same in both uses. -/

def identityMembers : List (Declaration (Fin 1 ⊕ Empty)) :=
  [.inferred (.inl 0) (.lam (.var 0))]

def identitySlots (Key : Type u) (base : Base) : Fin 1 → Comp (Structural.model Key) :=
  fun _ => (Structural.identityType base, [])

theorem identity_in_recursive_context (Key : Type u) (base : Base) :
    Typing (Structural.model Key) [.mono (Structural.identityType base, [])]
      (.lam (.var 0)) (Structural.identityType base, []) := by
  apply Typing.lam (m := Structural.model Key)
    (a := (.base base, [])) (b := (.base base, []))
  · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, Structural.row_refl _⟩)
  · exact ⟨.refl _, Structural.row_refl _⟩

def identityOut (base : Base) : CompTerm α :=
  CompTerm.pure (.arrow (.base base) .empty (.base base) .empty)

theorem generalized_identity_satisfied (Key : Type u) (base : Base)
    (ρ : Empty → Comp (Structural.model Key)) :
    (generalizeMember [] identityMembers 0 (identityOut base)).Holds (Structural.model Key) ρ := by
  apply (generalizeMember_exact _ ρ [] [] (EnvRel.nil _ _) identityMembers 0 _).mpr
  refine ⟨identitySlots Key base, ?_, ?_⟩
  · intro member present
    simp only [identityMembers, List.mem_singleton] at present
    subst member
    exact ⟨rfl, identity_in_recursive_context Key base⟩
  · refine ⟨rfl, ?_, identity_in_recursive_context Key base, ?_⟩
    · intro member present
      simp only [identityMembers, List.mem_singleton] at present
      subst member
      exact DefinitionTyping.inferred (identity_in_recursive_context Key base)
    · exact BindingTyping.mono ⟨.refl _, Structural.row_refl _⟩

theorem after_scc_independent_instantiations (Key : Type u)
    (ρ : Empty → Comp (Structural.model Key)) :
    (Constraint.and (generalizeMember [] identityMembers 0 (identityOut .int))
      (generalizeMember [] identityMembers 0 (identityOut .str))).Holds (Structural.model Key) ρ :=
  ⟨generalized_identity_satisfied Key .int ρ, generalized_identity_satisfied Key .str ρ⟩

/-- Even when exporting the other, syntactically-value member, a computed
member cannot be hidden among the existentially generalized slots. -/
def computedLocalMembers : List (Declaration (Fin 2 ⊕ Empty)) :=
  [.inferred (.inl 0) (.app (.lam (.var 0)) (.lit .int)),
   .inferred (.inl 1) (.lam (.var 0))]

theorem computed_peer_cannot_be_generalized (m : Model) (ρ : Empty → Comp m) (out : CompTerm Empty) :
    ¬ (generalizeMember [] computedLocalMembers 1 out).Holds m ρ :=
  generalizeMember_rejects_computed_local m ρ [] [] (EnvRel.nil _ _) computedLocalMembers 0
    (.app (.lam (.var 0)) (.lit .int)) (by simp [computedLocalMembers]) rfl 1 out

/-! A genuinely mutual block: annotated `f` calls monomorphic `g`, and `g`
calls the annotated `f` at a pair type. The annotation is available to peers. -/

def mutualFirst : Expr := .lam (.app (.var 2) (.lit .unit))
def mutualSecond : Expr := .lam (.app (.var 1) (.pair (.var 0) (.var 0)))

def mutualMembers : List (Declaration Unit) :=
  [.annotated 1 depthAnnotation mutualFirst, .inferred () mutualSecond]

def mutualAssignment (Key : Type u) : Unit → Comp (Structural.model Key) :=
  fun _ => (.arrow (.base .unit) [] (.base .int) [], [])

def mutualContext (Key : Type u) : List (Binding (Structural.model Key)) :=
  [depthAssumption Key, .mono (.arrow (.base .unit) [] (.base .int) [], [])]

theorem mutual_first_typing (Key : Type u) (input : Structural.Ty Key) :
    Typing (Structural.model Key) (mutualContext Key) mutualFirst
      (.arrow input [] (.base .int) [], []) := by
  apply Typing.lam (m := Structural.model Key) (a := (input, [])) (b := (.base .int, []))
  · apply Typing.app (m := Structural.model Key)
      (a := (.base .unit, [])) (b := (.base .int, [])) (ef := [])
    · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, Structural.row_refl _⟩)
    · exact Typing.lit ⟨.refl _, Structural.row_refl _⟩
    · exact ⟨.refl _, Structural.row_refl _⟩
  · exact ⟨.refl _, Structural.row_refl _⟩

theorem mutual_second_typing (Key : Type u) :
    Typing (Structural.model Key) (mutualContext Key) mutualSecond
      (.arrow (.base .unit) [] (.base .int) [], []) := by
  apply Typing.lam (m := Structural.model Key)
    (a := (.base .unit, [])) (b := (.base .int, []))
  · apply Typing.app (m := Structural.model Key)
      (a := (.pair (.base .unit) (.base .unit), [])) (b := (.base .int, [])) (ef := [])
    · exact Typing.var rfl (BindingTyping.signature (ι := fun _ => .pair (.base .unit) (.base .unit))
        ⟨.refl _, Structural.row_refl _⟩)
    · apply Typing.pair (m := Structural.model Key)
        (a := (.base .unit, [])) (b := (.base .unit, []))
      · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, Structural.row_refl _⟩)
      · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, Structural.row_refl _⟩)
      · exact ⟨.refl _, Structural.row_refl _⟩
    · exact ⟨.refl _, Structural.row_refl _⟩
  · exact ⟨.refl _, Structural.row_refl _⟩

theorem generated_mixed_mutual_satisfied (Key : Type u) :
    (generateSCC [] mutualMembers).Holds (Structural.model Key) (mutualAssignment Key) := by
  apply (generateSCC_exact _ _ [] [] (EnvRel.nil _ _) mutualMembers).mpr
  intro member present
  simp [mutualMembers] at present
  rcases present with rfl | rfl
  · exact DefinitionTyping.annotated (fun locals => mutual_first_typing Key (locals 0))
  · exact DefinitionTyping.inferred (mutual_second_typing Key)

end Yulang.RecursiveExamples
