import Yulang.RecursiveInference
import Yulang.Structural

/-!
# A genuine polymorphic-recursion separation

The depth-shaped core below recursively replaces `x` by `(x, x)` and keeps an
integer result. The arithmetic/guard implementation from the source example is
abstracted to a Boolean literal; no evaluation or termination claim is made.

The positive witness checks every annotation instance in the actual structural
type algebra. The negative witness excludes EVERY finite monotype in that same
algebra, including unions, intersections and bottom; it does not merely fail a
chosen unifier. Recursive types and other models are outside this separation.
-/

namespace Yulang.RecursiveExamples

open Inference RecursiveInference

def pairDepth : StructuralBase.Ty RowType → Nat
  | .union a b => max (pairDepth a) (pairDepth b)
  | .inter a b => min (pairDepth a) (pairDepth b)
  | .pair a b => max (pairDepth a) (pairDepth b) + 1
  | _ => 0

theorem pairDepth_record {record : StructuralBase.Ty RowType}
    (shape : StructuralBase.IsRecord record) : pairDepth record = 0 := by
  cases shape <;> rfl

theorem pairDepth_mono {a b : StructuralBase.Ty RowType}
    (h : StructuralBase.Subtype leRow a b) : pairDepth a ≤ pairDepth b := by
  induction h with
  | refl => exact Nat.le_refl _
  | trans _ _ hab hbc => exact Nat.le_trans hab hbc
  | bottom => exact Nat.zero_le _
  | unionLeft => simp only [pairDepth]; omega
  | unionRight => simp only [pairDepth]; omega
  | unionElim _ _ ha hb => simp only [pairDepth]; omega
  | interLeft => simp only [pairDepth]; omega
  | interRight => simp only [pairDepth]; omega
  | interIntro _ _ ha hb => simp only [pairDepth]; omega
  | pair _ _ ha hb => simp only [pairDepth]; omega
  | variant => exact Nat.le_refl _
  | arrow => exact Nat.le_refl _
  | record sourceShape targetShape _ _ _ =>
      rw [pairDepth_record sourceShape, pairDepth_record targetShape]
      exact Nat.le_refl 0

def ArrowDomainBound (limit : Nat) : StructuralBase.Ty RowType → Prop
  | .union a b => ArrowDomainBound limit a ∨ ArrowDomainBound limit b
  | .inter a b => ArrowDomainBound limit a ∧ ArrowDomainBound limit b
  | .arrow input _ _ _ => pairDepth input ≤ limit
  | _ => False

theorem record_not_arrow {record : StructuralBase.Ty RowType}
    (shape : StructuralBase.IsRecord record) (limit : Nat) : ¬ ArrowDomainBound limit record := by
  cases shape <;> exact fun h => h

theorem arrowDomainBound_mono {a b : StructuralBase.Ty RowType}
    (h : StructuralBase.Subtype leRow a b) :
    ∀ limit, ArrowDomainBound limit a → ArrowDomainBound limit b := by
  induction h with
  | refl => exact fun _ h => h
  | trans _ _ hab hbc => exact fun limit h => hbc limit (hab limit h)
  | bottom => exact fun _ h => False.elim h
  | unionLeft => exact fun _ h => Or.inl h
  | unionRight => exact fun _ h => Or.inr h
  | unionElim _ _ ha hb => exact fun limit h => h.elim (ha limit) (hb limit)
  | interLeft => exact fun _ h => h.1
  | interRight => exact fun _ h => h.2
  | interIntro _ _ ha hb => exact fun limit h => ⟨ha limit h, hb limit h⟩
  | pair => exact fun _ h => False.elim h
  | variant => exact fun _ h => False.elim h
  | arrow inputTypes _ _ _ _ _ =>
      exact fun _ h => Nat.le_trans (pairDepth_mono inputTypes) h
  | record sourceShape _ _ _ _ =>
      exact fun limit h => False.elim (record_not_arrow sourceShape limit h)

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

/-- A single recursive monotype cannot contain its own strictly deeper pair
input. This rejects every candidate type, rather than one guessed signature. -/
theorem unannotated_depth_not_typable (type : Structural.Ty Key) (row : Effects.Row Key) :
    ¬ Typing (Structural.model Key) [.mono (type, [])] depthFunction (type, row) := by
  intro h
  rcases (Typing.lam_iff _ _ _ _).mp h with ⟨argument, returned, bodyTyped, lambdaBound⟩
  rcases (Typing.branch_iff _ _ _ _ _ _).mp bodyTyped with
    ⟨_, _, _, _, _, callTyped, _⟩
  rcases (Typing.app_iff _ _ _ _ _).mp callTyped with
    ⟨callInput, callOutput, _, functionTyped, pairTyped, _⟩
  rcases (Typing.pair_iff _ _ _ _ _).mp pairTyped with
    ⟨left, right, leftTyped, _, pairBound⟩
  have functionBound := mono_variable_type (assumed := (type, [])) rfl functionTyped
  have leftBound := mono_variable_type (assumed := argument) rfl leftTyped
  have domain := arrowDomainBound_mono
    (Structural.Subtype.trans lambdaBound.1 functionBound) (pairDepth argument.1) (Nat.le_refl _)
  have increasing := pairDepth_mono pairBound.1
  have fromArgument := pairDepth_mono leftBound
  change pairDepth callInput.1 ≤ pairDepth argument.1 at domain
  change max (pairDepth left.1) (pairDepth right.1) + 1 ≤ pairDepth callInput.1 at increasing
  omega

def unannotatedDepth : List (Declaration Unit) := [.inferred () depthFunction]

theorem generated_unannotated_depth_rejected (ρ : Unit → Comp (Structural.model Key)) :
    ¬ (generateSCC [] unannotatedDepth).Holds (Structural.model Key) ρ := by
  intro h
  have checked := (generateSCC_exact _ ρ [] [] (EnvRel.nil _ _) unannotatedDepth).mp h
  have member := checked (.inferred () depthFunction) (by simp [unannotatedDepth])
  cases member with
  | inferred typed => exact unannotated_depth_not_typable (ρ ()).1 (ρ ()).2 typed

theorem closed_unannotated_depth_rejected (ρ : Empty → Comp (Structural.model Key)) :
    ¬ (inferUnannotatedSCC [] (fun _ : Fin 1 => depthFunction)).Holds (Structural.model Key) ρ := by
  intro h
  rcases (inferUnannotatedSCC_exact _ ρ [] [] (EnvRel.nil _ _) _).mp h with ⟨slots, checked⟩
  have member := checked (.inferred (.inl 0) depthFunction) (by
    simp [unannotatedMembers])
  cases member with
  | inferred typed => exact unannotated_depth_not_typable (slots 0).1 (slots 0).2 typed

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
