import Yulang.StructuralBase
import Yulang.Inference
import Yulang.Directed
import Yulang.RowInference

/-!
# Structural types with signed occurrence rows

The type constructors and structural subtype rules are exactly those of
`StructuralBase`; this module supplies actual `Directed.Row` values, membership
inclusion, and append as their join. Negative weights remain in the row rather
than disappearing when an unmatched boundary is released.

This is a non-vacuous reference model of generated constraints, not a complete
MLsub solver or a source elaboration. The finite interface `Fin n` is explicit;
the signed coordinate values are unbounded integers. Type-directed transport
of latent callbacks and source origin invariants are separate proof obligations.
-/

namespace Yulang.SignedStructural

open Yulang.Inference

abbrev Ty (n : Nat) (Key : Type u) := StructuralBase.Ty (Directed.Row n Key)

namespace Ty
export StructuralBase.Ty (base bottom union inter pair emptyRecord record variant arrow)
end Ty

def RowLe (a b : Directed.Row n Key) : Prop := ∀ occurrence, occurrence ∈ a → occurrence ∈ b

abbrev Subtype {n : Nat} {Key : Type u} := StructuralBase.Subtype (@RowLe n Key)

abbrev model (n : Nat) (Key : Type u) : Model :=
  StructuralBase.model (Directed.Row n Key) [] List.append RowLe

/-- The shared effect-rule generator sees the actual signed rows unchanged. -/
def rowView (n : Nat) (Key : Type) [DecidableEq Key] :
    RowInference.RowView (model n Key) (RowInference.signedAlgebra n Key) where
  decode := id
  decode_empty := rfl
  decode_join := fun _ _ => rfl
  subtype_iff := fun _ _ => Iff.rfl

theorem row_refl (row : Directed.Row n Key) : RowLe row row := fun _ h => h

theorem row_bottom (row : Directed.Row n Key) : RowLe [] row := by
  intro occurrence impossible
  cases impossible

theorem row_join_left (a b : Directed.Row n Key) : RowLe a (a ++ b) :=
  fun _ h => List.mem_append.mpr (Or.inl h)

theorem row_join_right (a b : Directed.Row n Key) : RowLe b (a ++ b) :=
  fun _ h => List.mem_append.mpr (Or.inr h)

theorem row_join_least {a b c : Directed.Row n Key} (ac : RowLe a c) (bc : RowLe b c) :
    RowLe (a ++ b) c := by
  intro occurrence h
  exact (List.mem_append.mp h).elim (ac occurrence) (bc occurrence)

theorem raw_not_below_empty (key : Key) :
    ¬ RowLe [Directed.raw (n := n) key] [] := by
  intro h
  have impossible := h (Directed.raw key) (by simp)
  cases impossible

theorem int_not_str : ¬ Subtype (Ty.base .int : Ty n Key) (.base .str) :=
  StructuralBase.int_not_str

theorem int_union_str_not_int :
    ¬ Subtype (Ty.union (.base .int) (.base .str) : Ty n Key) (.base .int) :=
  StructuralBase.int_union_str_not_int

theorem record_width :
    Subtype (Ty.record 0 (.base .int) (.record 1 (.base .str) .emptyRecord) : Ty n Key)
      (.record 0 (.base .int) .emptyRecord) := StructuralBase.record_width

theorem arrow_variance (extra : Directed.Row n Key) :
    Subtype
      (Ty.arrow (.union (.base .int) (.base .str)) extra (.base .int) [] : Ty n Key)
      (.arrow (.base .int) [] (.union (.base .int) (.base .str)) extra) :=
  .arrow (.unionLeft _ _) (row_bottom _) (.unionLeft _ _) (row_bottom _)

/-! Concrete instances of the existing core generator already distinguish
an effectful computation variable from a pure result. -/

def effectAssignment (n : Nat) (key : Key) : Unit → Comp (model n Key) :=
  fun _ => (.base .int, [Directed.raw key])

theorem generated_effect_row_satisfied (n : Nat) (key : Key) :
    (generate [Scheme.mono (CompTerm.var ())] (.var 0) (CompTerm.var ())).Holds
      (model n Key) (effectAssignment n key) := by
  change ((Scheme.mono (CompTerm.var ())).instantiate (CompTerm.var ())).Holds _ _
  rw [Scheme.holds_instantiate, Scheme.holds_mono]
  exact ⟨.refl _, row_refl _⟩

theorem generated_absent_effect_rejected (n : Nat) (key : Key) :
    ¬ (generate [Scheme.mono (CompTerm.var ())] (.var 0)
      (CompTerm.pure (.base .int))).Holds (model n Key) (effectAssignment n key) := by
  intro h
  change ((Scheme.mono (CompTerm.var ())).instantiate
    (CompTerm.pure (.base .int))).Holds _ _ at h
  rw [Scheme.holds_instantiate, Scheme.holds_mono] at h
  exact raw_not_below_empty key h.2

/-! The generic resolved-operation generator has inhabited, discriminating
instances in this concrete model. Keys contain family parameters only; these
initial examples use monomorphic signatures; the examples below add local quantifiers. -/

def integerOperation (key : EffectInference.SigKey F O A) :
    EffectInference.Signature Unit F O A where
  key := key
  input := .base .int
  output := .base .int

theorem generated_request_satisfied [DecidableEq (EffectInference.SigKey F O A)]
    (n : Nat) (key : EffectInference.SigKey F O A) :
    (RowInference.requestConstraints [] (integerOperation key) (.lit .int) (CompTerm.var ())).Holds
      (rowView n (EffectInference.SigKey F O A)) (effectAssignment n key) := by
  apply (RowInference.request_constraints_exact _ _ [] [] _ (EnvRel.nil _ _)
    (integerOperation key) (.lit .int) (CompTerm.var ())).mpr
  apply RowInference.RequestTyping.intro (er := [])
  · exact Typing.lit ⟨.refl _, row_refl _⟩
  · exact .refl _
  · exact row_refl _

theorem generated_request_without_effect_rejected [DecidableEq (EffectInference.SigKey F O A)]
    (n : Nat) (key : EffectInference.SigKey F O A) :
    ¬ (RowInference.requestConstraints [] (integerOperation key) (.lit .int)
      (CompTerm.pure (.base .int))).Holds
        (rowView n (EffectInference.SigKey F O A)) (effectAssignment n key) := by
  intro h
  have typed := (RowInference.request_constraints_exact _ _ [] [] _ (EnvRel.nil _ _)
    (integerOperation key) (.lit .int) (CompTerm.pure (.base .int))).mp h
  cases typed with
  | intro _ _ budget =>
    have impossible : Directed.raw (n := n) key ∈ ([] : Directed.Row n _) :=
      budget _ (by simp [RowInference.signedAlgebra, RowInference.keysRow, integerOperation])
    cases impossible

/-! Concrete operation-local polymorphism over actual signed rows. -/

def polyIdentityOperation (key : EffectInference.SigKey F O A) :
    EffectInference.PolySignature α 1 F O A where
  key := key
  input := .var (.inr 0)
  output := .var (.inr 0)

/-- The caller can choose an arbitrary structural type, including compound
and effectful arrow types. The ambient slot is fixed independently of locals. -/
theorem generated_poly_request_at_any_type [DecidableEq (EffectInference.SigKey F O A)]
    (n : Nat) (key : EffectInference.SigKey F O A) (t : Ty n (EffectInference.SigKey F O A)) :
    (RowInference.polyRequestConstraints [Scheme.mono (CompTerm.pure (.var ()))]
      (polyIdentityOperation key) (.var 0) (CompTerm.var ())).Holds
      (rowView n (EffectInference.SigKey F O A)) (fun _ => (t, [Directed.raw key])) := by
  apply (RowInference.poly_request_constraints_exact _ _ _ [.mono (t, [])] _
    ((EnvRel.nil _ _).mono (CompTerm.pure (.var ()))) _ _ _).mpr
  apply RowInference.PolyRequestTyping.intro (fun _ => t)
  apply RowInference.RequestTyping.intro (er := [])
  · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, row_refl _⟩)
  · exact .refl _
  · exact row_refl _

theorem generated_poly_request_literal [DecidableEq (EffectInference.SigKey F O A)]
    (n : Nat) (key : EffectInference.SigKey F O A) (ρ : α → Comp (model n (EffectInference.SigKey F O A)))
    (base : Base) (out : CompTerm α) (hout : out.eval _ ρ = (.base base, [Directed.raw key])) :
    (RowInference.polyRequestConstraints [] (polyIdentityOperation key) (.lit base) out).Holds
      (rowView n (EffectInference.SigKey F O A)) ρ := by
  apply (RowInference.poly_request_constraints_exact _ _ [] [] _ (EnvRel.nil _ _) _ _ _).mpr
  rw [hout]
  apply RowInference.PolyRequestTyping.intro (fun _ => Ty.base base)
  apply RowInference.RequestTyping.intro (er := [])
  · exact Typing.lit ⟨.refl _, row_refl _⟩
  · exact .refl _
  · exact row_refl _

/-- Both calls use one signature and one ambient assignment. Each existential
binder chooses its own local type (int and str, respectively). -/
theorem generated_poly_requests_independent [DecidableEq (EffectInference.SigKey F O A)]
    (n : Nat) (key : EffectInference.SigKey F O A) :
    let ρ : Bool → Comp (model n (EffectInference.SigKey F O A)) :=
      fun b => (.base (if b then .str else .int), [Directed.raw key])
    (RowInference.Constraint.and
      (RowInference.polyRequestConstraints [] (polyIdentityOperation key) (.lit .int) (CompTerm.var false))
      (RowInference.polyRequestConstraints [] (polyIdentityOperation key) (.lit .str) (CompTerm.var true))).Holds
      (rowView n (EffectInference.SigKey F O A)) ρ := by
  constructor
  · exact generated_poly_request_literal n key _ .int _ rfl
  · exact generated_poly_request_literal n key _ .str _ rfl

/-- A rigid payload may be passed to a continuation expecting the same local
type, for every choice of that type. The result remains the fixed int type. -/
theorem generated_poly_handler_resumes_payload [DecidableEq (EffectInference.SigKey F O A)]
    (n : Nat) (key : EffectInference.SigKey F O A)
    (ρ : α → Comp (model n (EffectInference.SigKey F O A))) :
    (RowInference.polyHandlerConstraints [] (polyIdentityOperation key) (.lit .int) (.var 0)
      (.app (.var 1) (.var 0)) (CompTerm.pure (.base .int))).Holds
      (rowView n (EffectInference.SigKey F O A)) ρ := by
  apply (RowInference.poly_handler_constraints_exact _ _ [] [] _ (EnvRel.nil _ _) _ _ _ _ _).mpr
  apply RowInference.PolyHandlerTyping.intro
    (input := (Ty.base .int, [])) (returned := (Ty.base .int, []))
  · exact Typing.lit ⟨.refl _, row_refl _⟩
  · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, row_refl _⟩)
  · intro ι
    refine ⟨(Ty.base .int, []), ?_, .unionElim (.refl _) (.refl _), ?_⟩
    · apply Typing.app (a := (ι 0, [])) (b := (Ty.base .int, [])) (ef := [])
      · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, row_refl _⟩)
      · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, row_refl _⟩)
      · exact ⟨.refl _, row_refl _⟩
    · exact row_refl _

/-- Choosing local := int once would accept this arm. Rigid quantification
also requires local := str, which cannot be returned as the fixed int result. -/
theorem generated_poly_handler_payload_escape_rejected
    [DecidableEq (EffectInference.SigKey F O A)]
    (n : Nat) (key : EffectInference.SigKey F O A)
    (ρ : α → Comp (model n (EffectInference.SigKey F O A))) :
    ¬ (RowInference.polyHandlerConstraints [] (polyIdentityOperation key) (.lit .int) (.var 0)
      (.var 0) (CompTerm.pure (.base .int))).Holds
      (rowView n (EffectInference.SigKey F O A)) ρ := by
  intro h
  have typed := (RowInference.poly_handler_constraints_exact _ _ [] [] _ (EnvRel.nil _ _) _ _ _ _ _).mp h
  rcases (RowInference.polyHandlerTyping_iff _ _ _ _ _ _ _ _ _ _).mp typed with
    ⟨input, returned, _, _, arms⟩
  rcases arms (fun _ => Ty.base .str) with ⟨operated, ho, bound, _⟩
  cases ho with
  | var lookup binding =>
    simp only [EffectInference.semanticArmEnvironment, List.getElem?_cons_zero,
      Option.some.injEq] at lookup
    cases lookup
    cases binding with
    | mono included =>
      exact StructuralBase.str_not_int (.trans included.1 (.trans (.unionRight _ _) bound))

/-! Release-before-protect is genuinely signed in generated boundary rules. -/

def boundaryAssignment (scope : Fin n) (key : Key) : Bool → Comp (model n Key)
  | false => (.base .int, [Directed.raw key])
  | true => (.base .int, [Directed.release scope Directed.allowNone (Directed.raw key)])

theorem boundary_environment_related (scope : Fin n) (key : Key) :
    EnvRel (model n Key) (boundaryAssignment scope key)
      [Scheme.mono (CompTerm.var false)] [.mono (.base .int, [Directed.raw key])] :=
  (EnvRel.nil _ _).mono (CompTerm.var false)

theorem generated_release_retains_debt [DecidableEq Key] (scope : Fin n) (key : Key) :
    (RowInference.boundaryConstraints [Scheme.mono (CompTerm.var false)]
      (.release scope Directed.allowNone) (.var 0) (CompTerm.var true)).Holds
        (rowView n Key) (boundaryAssignment scope key) := by
  apply (RowInference.boundary_constraints_exact _ _ _ _ _
    (boundary_environment_related scope key) _ _ _).mpr
  apply RowInference.BoundaryTyping.intro (m := model n Key)
    (input := (.base .int, [Directed.raw key]))
  · exact Typing.var rfl (BindingTyping.mono ⟨.refl _, row_refl _⟩)
  · exact .refl _
  · exact row_refl _

theorem generated_release_cannot_drop_debt [DecidableEq Key] (scope : Fin n) (key : Key) :
    ¬ (RowInference.boundaryConstraints [Scheme.mono (CompTerm.var false)]
      (.release scope Directed.allowNone) (.var 0) (CompTerm.pure (.base .int))).Holds
        (rowView n Key) (boundaryAssignment scope key) := by
  intro h
  have typed := (RowInference.boundary_constraints_exact _ _ _ _ _
    (boundary_environment_related scope key) _ _ _).mp h
  cases typed with
  | intro bodyTyped _ budget =>
    cases bodyTyped with
    | var lookup binding =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      cases lookup
      cases binding with
      | mono included =>
        have present := included.2 (Directed.raw key) (by simp)
        have moved := List.mem_map.mpr
          ⟨Directed.raw key, present, (rfl : Directed.release scope Directed.allowNone
            (Directed.raw key) = Directed.release scope Directed.allowNone (Directed.raw key))⟩
        have impossible : Directed.release scope Directed.allowNone (Directed.raw key) ∈
            ([] : Directed.Row n Key) := budget _ moved
        cases impossible

end Yulang.SignedStructural
