import Yulang.CommonEffectFormula
import Yulang.CoreEffectTyping

/-! Quantifier and aggregation laws used for finite multi-handler generation.
Outer environments/results are free parameters of these lemmas, never selected
anew per operation-local type. Generic predicates occur only in propositions,
not as formula atoms. -/
namespace Yulang.CommonEffectUniversalArms
open Common (Ty Row Subtype)
open Core.PresenceGeneration (Comp CompTerm extend)
open CommonEffectRequestGeneration (Computation localEnv)

/-- Universal families of independent arms can be checked separately. Both
sides permit the arm result to depend on the local type. -/
theorem joint_locals_iff (locals : Fin count → Nat)
    (predicate : (i : Fin count) → (Fin (locals i) → Ty) → Computation → Prop) :
    (∀ assignment : (i : Fin count) → Fin (locals i) → Ty,
      ∃ operated : Fin count → Computation, ∀ i, predicate i (assignment i) (operated i)) ↔
    (∀ i, ∀ assignment : Fin (locals i) → Ty, ∃ operated, predicate i assignment operated) := by
  constructor
  · intro joint index assignment
    let complete : (i : Fin count) → Fin (locals i) → Ty :=
      fun i => if same : i = index then same.symm ▸ assignment else fun _ => .top
    obtain ⟨operated, valid⟩ := joint complete
    refine ⟨operated index, ?_⟩
    simpa [complete] using valid index
  · intro separate assignment
    have results : ∀ i, ∃ operated, predicate i (assignment i) operated :=
      fun i => separate i (assignment i)
    exact ⟨fun i => Classical.choose (results i), fun i => Classical.choose_spec (results i)⟩

theorem union_le_iff (first last upper : Ty) :
    Subtype (.union first last) upper ↔ Subtype first upper ∧ Subtype last upper := by
  constructor
  · intro below
    exact ⟨fun depth => (CommonFinite.producerLe_union_iff _ _ _).mp (below depth) |>.1,
      fun depth => (CommonFinite.producerLe_union_iff _ _ _).mp (below depth) |>.2⟩
  · rintro ⟨firstLe, lastLe⟩ depth
    exact (CommonFinite.producerLe_union_iff _ _ _).mpr ⟨firstLe depth, lastLe depth⟩

theorem fold_types_le_iff (indices : List α) (value : α → Ty) (returned upper : Ty) :
    Subtype (indices.foldr (fun i rest => .union (value i) rest) returned) upper ↔
      Subtype returned upper ∧ ∀ i ∈ indices, Subtype (value i) upper := by
  induction indices with
  | nil => simp
  | cons first rest ih =>
    simp only [List.foldr_cons, union_le_iff, ih, List.mem_cons, forall_eq_or_imp]
    exact ⟨fun ⟨head, returned, tail⟩ => ⟨returned, head, tail⟩,
      fun ⟨returned, head, tail⟩ => ⟨head, returned, tail⟩⟩

theorem fold_rows_le_iff (indices : List α) (row : α → Row) (upper : Row) :
    Common.rowLe (indices.foldr (fun i rest => Common.rowJoin (row i) rest) Common.rowEmpty) upper ↔
      ∀ i ∈ indices, Common.rowLe (row i) upper := by
  induction indices with
  | nil => simp [Common.rowEmpty_le]
  | cons first rest ih => simp [Common.rowJoin_le_iff, ih]

/-- Finite conjunction of finite formulas, including zero-operation handlers. -/
def andAll (formulas : List (CommonEffectFormula.Formula scopes α)) : CommonEffectFormula.Formula scopes α :=
  formulas.foldr .and (.core .top)

@[simp] theorem andAll_exact (formulas : List (CommonEffectFormula.Formula scopes α)) (assignment : α → Computation) :
    (andAll formulas).Holds assignment ↔ ∀ formula ∈ formulas, formula.Holds assignment := by
  induction formulas <;> simp_all [andAll, CommonEffectFormula.Formula.Holds,
    Core.PresenceGeneration.Formula.Holds]

/-- The actual syntactic universal layer for heterogeneous operation locals.
Bodies are finite syntax, including their result slot; there is no semantic
function contract or Typing leaf in this construction. -/
def universalArms (locals : Fin count → Nat)
    (bodies : (i : Fin count) → CommonEffectFormula.Formula scopes (Option (α ⊕ Fin (locals i)))) :
    CommonEffectFormula.Formula scopes α :=
  andAll ((List.finRange count).map (fun i => .forallTypes (locals i) (.existsSlot (bodies i))))

theorem universalArms_exact (locals : Fin count → Nat)
    (bodies : (i : Fin count) → CommonEffectFormula.Formula scopes (Option (α ⊕ Fin (locals i))))
    (assignment : α → Computation) :
    (universalArms locals bodies).Holds assignment ↔
      ∀ localAssignment : (i : Fin count) → Fin (locals i) → Ty,
        ∃ operated : Fin count → Computation,
          ∀ i, (bodies i).Holds (extend (localEnv assignment (localAssignment i)) (operated i)) := by
  rw [joint_locals_iff locals (fun i types result =>
    (bodies i).Holds (extend (localEnv assignment types) result))]
  simp [universalArms, andAll_exact, CommonEffectFormula.Formula.Holds]
end Yulang.CommonEffectUniversalArms
