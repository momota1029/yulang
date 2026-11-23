import Yulang.GeneralDeclarativeWitnessSparseIntervals357
import Yulang.GeneralNominalCommonBridge

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessFullIntervals357

open Core.PresenceGeneration (TyTerm RowTerm Comp)
open CommonDeclaredNominalInspection (Kind Parameter Declaration Registry)
open CommonDeclaredNominalVariance (Variance)
open CommonRecursiveNominalIntervals hiding ContextDerives ContextDerivesArguments ContextDerivesArgument
  context_derives_argument_exact context_derives_arguments_exact context_derives_ordinary_exact
  context_derives_nominal_exact inspect_context_exact
open PresenceNormalForm (Atom All)

/-- Only row evaluation uses this auxiliary assignment. The type part is
never used: value obligations below compare the actual full type endpoints. -/
def rowPart (m : α → Comp CommonNominalFullCarrier.model) : α → Comp Common.model :=
  fun n => (.bottom,(m n).2)

theorem row_args_exact (m : α → Comp CommonNominalFullCarrier.model) (r : RowTerm α) :
    r.eval Common.model (rowPart m) = r.eval CommonNominalFullCarrier.model m := by
  induction r <;> simp_all [RowTerm.eval,rowPart,Common.model,CommonNominalFullCarrier.model]

mutual
inductive ContextDerives (registry : Registry) (assignment : α → Comp CommonNominalFullCarrier.model) :
    Bool → Endpoint α → Endpoint α → Prop where
  | ordinary {context : Bool} {a b : TyTerm α} :
      CommonNominalFullCarrier.Subtype (a.eval CommonNominalFullCarrier.model assignment) (b.eval CommonNominalFullCarrier.model assignment) →
      ContextDerives registry assignment context (.ordinary a) (.ordinary b)
  | nominal {context : Bool} {name : Nat} {first last : List (Argument α)} {declaration : Declaration} :
      registry[name]? = some declaration →
      ContextDerivesArguments registry assignment context declaration first last →
      ContextDerives registry assignment context (.nominal name first) (.nominal name last)

inductive ContextDerivesArguments (registry : Registry) (assignment : α → Comp CommonNominalFullCarrier.model) :
    Bool → Declaration → List (Argument α) → List (Argument α) → Prop where
  | nil (context : Bool) : ContextDerivesArguments registry assignment context [] [] []
  | cons {context parameter rest first tail last suffix} :
      ContextDerivesArgument registry assignment (childContext context parameter)
        (effectiveParameter context parameter) first last →
      ContextDerivesArguments registry assignment context rest tail suffix →
      ContextDerivesArguments registry assignment context
        (parameter :: rest) (first :: tail) (last :: suffix)

/-- This argument rule receives the already effective direction and the
child context. Their relationship to the original declaration is fixed by
`ContextDerivesArguments.cons`, not chosen by the comparison. -/
inductive ContextDerivesArgument (registry : Registry) (assignment : α → Comp CommonNominalFullCarrier.model) :
    Bool → Parameter → Argument α → Argument α → Prop where
  | covariantValue {context a b} : ContextDerives registry assignment context a b →
      ContextDerivesArgument registry assignment context ⟨.value, .covariant⟩
        (.inl (.point a)) (.inl (.point b))
  | contravariantValue {context a b} : ContextDerives registry assignment context b a →
      ContextDerivesArgument registry assignment context ⟨.value, .contravariant⟩
        (.inl (.point a)) (.inl (.point b))
  | invariantValue {context} {a b : Bounds (Endpoint α)} :
      ContextDerives registry assignment context a.lower a.upper →
      ContextDerives registry assignment context b.lower b.upper →
      ContextDerives registry assignment context a.lower b.upper →
      ContextDerives registry assignment context b.lower a.upper →
      ContextDerivesArgument registry assignment context ⟨.value, .invariant⟩ (.inl a) (.inl b)
  | unusedValue (context) (a b : Bounds (Endpoint α)) :
      ContextDerivesArgument registry assignment context ⟨.value, .unused⟩ (.inl a) (.inl b)
  | covariantRow {context} {a b : RowTerm α} :
      Common.rowLe (a.eval CommonNominalFullCarrier.model assignment) (b.eval CommonNominalFullCarrier.model assignment) →
      ContextDerivesArgument registry assignment context ⟨.row, .covariant⟩
        (.inr (.point a)) (.inr (.point b))
  | contravariantRow {context} {a b : RowTerm α} :
      Common.rowLe (b.eval CommonNominalFullCarrier.model assignment) (a.eval CommonNominalFullCarrier.model assignment) →
      ContextDerivesArgument registry assignment context ⟨.row, .contravariant⟩
        (.inr (.point a)) (.inr (.point b))
  | invariantRow {context} {a b : Bounds (RowTerm α)} :
      Common.rowLe (a.lower.eval CommonNominalFullCarrier.model assignment) (a.upper.eval CommonNominalFullCarrier.model assignment) →
      Common.rowLe (b.lower.eval CommonNominalFullCarrier.model assignment) (b.upper.eval CommonNominalFullCarrier.model assignment) →
      Common.rowLe (a.lower.eval CommonNominalFullCarrier.model assignment) (b.upper.eval CommonNominalFullCarrier.model assignment) →
      Common.rowLe (b.lower.eval CommonNominalFullCarrier.model assignment) (a.upper.eval CommonNominalFullCarrier.model assignment) →
      ContextDerivesArgument registry assignment context ⟨.row, .invariant⟩ (.inr a) (.inr b)
  | unusedRow (context) (a b : Bounds (RowTerm α)) :
      ContextDerivesArgument registry assignment context ⟨.row, .unused⟩ (.inr a) (.inr b)
end

theorem context_derives_argument_exact (registry : Registry) (assignment : α → Comp CommonNominalFullCarrier.model)
    (context : Bool) (parameter : Parameter) (first last : Argument α) :
    ContextDerivesArgument registry assignment context parameter first last ↔
      ArgumentRel (ContextDerives registry assignment context) (rowPart assignment) parameter first last := by
  rcases parameter with ⟨kind, mode⟩
  cases first <;> cases last <;> rename_i first last
  all_goals cases first <;> cases last <;> cases kind <;> cases mode
  all_goals simp only [ArgumentRel,row_args_exact]
  all_goals constructor <;> intro proof
  all_goals solve
    | cases proof <;> simp_all
    | exact .covariantValue proof
    | exact .contravariantValue proof
    | exact .covariantRow proof
    | exact .contravariantRow proof
    | exact .unusedValue _ _ _
    | exact .unusedRow _ _ _
    | exact .invariantValue proof.1 proof.2.1 proof.2.2.1 proof.2.2.2
    | exact .invariantRow proof.1 proof.2.1 proof.2.2.1 proof.2.2.2

theorem context_derives_arguments_exact (registry : Registry) (assignment : α → Comp CommonNominalFullCarrier.model)
    (context : Bool) (declaration : Declaration) (first last : List (Argument α)) :
    ContextDerivesArguments registry assignment context declaration first last ↔
      ContextArgumentsRel (ContextDerives registry assignment) (rowPart assignment) context declaration first last := by
  induction declaration generalizing first last with
  | nil =>
      cases first <;> cases last <;> simp only [ContextArgumentsRel]
      all_goals constructor <;> intro proof
      all_goals solve | cases proof | exact .nil context | trivial
  | cons parameter rest ih =>
      cases first with
      | nil =>
          cases last <;> simp only [ContextArgumentsRel]
          all_goals constructor <;> intro proof <;> cases proof
      | cons first tail =>
          cases last with
          | nil =>
              simp only [ContextArgumentsRel]
              constructor <;> intro proof <;> cases proof
          | cons last suffix =>
              simp only [ContextArgumentsRel]
              constructor
              · intro proof
                cases proof with
                | cons head tail =>
                    exact ⟨(context_derives_argument_exact registry assignment _ _ _ _).mp head,
                      (ih _ _).mp tail⟩
              · rintro ⟨head, tail⟩
                exact .cons ((context_derives_argument_exact registry assignment _ _ _ _).mpr head)
                  ((ih _ _).mpr tail)

theorem context_derives_ordinary_exact (registry : Registry) (assignment : α → Comp CommonNominalFullCarrier.model)
    (context : Bool) (a b : TyTerm α) :
    ContextDerives registry assignment context (.ordinary a) (.ordinary b) ↔
      CommonNominalFullCarrier.Subtype (a.eval CommonNominalFullCarrier.model assignment) (b.eval CommonNominalFullCarrier.model assignment) := by
  constructor
  · intro proof; cases proof; assumption
  · exact ContextDerives.ordinary

theorem context_derives_nominal_exact (registry : Registry) (assignment : α → Comp CommonNominalFullCarrier.model)
    (context : Bool) (name other : Nat) (first last : List (Argument α)) :
    ContextDerives registry assignment context (.nominal name first) (.nominal other last) ↔
      name = other ∧ ∃ declaration, registry[name]? = some declaration ∧
        ContextArgumentsRel (ContextDerives registry assignment) (rowPart assignment) context declaration first last := by
  constructor
  · intro proof
    cases proof with
    | nominal declared arguments =>
        exact ⟨rfl, _, declared,
          (context_derives_arguments_exact registry assignment context _ _ _).mp arguments⟩
  · rintro ⟨rfl, declaration, declared, arguments⟩
    exact .nominal declared
      ((context_derives_arguments_exact registry assignment context _ _ _).mpr arguments)

/-- All finite original descriptions, both inherited contexts, every table
and every independent Common assignment. No depth, success or semantic
oracle is an input to the actual compiler. -/
theorem inspect_context_exact (registry : Registry) (assignment : α → Comp CommonNominalFullCarrier.model)
    (context : Bool) (first last : Endpoint α) :
    ResultHolds (fun atom => atom.Holds CommonNominalFullCarrier.model assignment)
      (inspectContext registry context first last) ↔
        ContextDerives registry assignment context first last := by
  cases first with
  | ordinary a =>
      cases last with
      | ordinary b =>
          rw [inspectContext, context_derives_ordinary_exact]
          simp [ResultHolds, Atom.Holds, CommonNominalFullCarrier.model]
      | nominal other after =>
          rw [inspectContext] <;> try (solve | simp)
          constructor
          · intro impossible; exact False.elim (result_none _ impossible)
          · intro impossible; cases impossible
  | nominal name before =>
      cases last with
      | ordinary b =>
          rw [inspectContext] <;> try (solve | simp)
          constructor
          · intro impossible; exact False.elim (result_none _ impossible)
          · intro impossible; cases impossible
      | nominal other after =>
          by_cases same : name = other
          · subst other
            cases declared : registry[name]? with
            | none =>
                rw [inspectContext]
                simp only [↓reduceIte, declared]
                constructor
                · intro impossible; exact False.elim (result_none _ impossible)
                · intro proof
                  obtain ⟨_, declaration, found, _⟩ :=
                    (context_derives_nominal_exact registry assignment context name name before after).mp proof
                  simp [declared] at found
            | some declaration =>
                cases generated : decomposeContextArguments context declaration before after with
                | none =>
                    have absent : inspectContext registry context
                        (.nominal name before) (.nominal name after) = none := by
                      rw [inspectContext]
                      simp only [↓reduceIte, declared]
                      split <;> simp_all
                    rw [absent]
                    constructor
                    · intro impossible; exact False.elim (result_none _ impossible)
                    · intro proof
                      obtain ⟨_, actual, found, arguments⟩ :=
                        (context_derives_nominal_exact registry assignment context name name before after).mp proof
                      have equal : actual = declaration := Option.some.inj (found.symm.trans declared)
                      subst actual
                      have emitted := (decompose_context_arguments_exact (ContextDerives registry assignment)
                        (rowPart assignment) context declaration before after).mpr arguments
                      rw [generated] at emitted
                      exact False.elim (result_none _ emitted)
                | some obligations =>
                    rw [inspect_context_nominal registry context name before after declaration
                      obligations declared generated, concatenate_exact]
                    simp only [List.forall_mem_map]
                    have each (obligation : ContextObligation α) (present : obligation ∈ obligations) :
                        ResultHolds (fun atom => atom.Holds CommonNominalFullCarrier.model assignment)
                          (inspectContextObligation registry obligation) ↔
                            ContextObligation.Holds (ContextDerives registry assignment) (rowPart assignment) obligation := by
                      rcases obligation with ⟨child, obligation⟩
                      cases obligation with
                      | row a b =>
                          simp [inspectContextObligation, ResultHolds, Atom.Holds,
                            ContextObligation.Holds, Obligation.Holds, row_args_exact, CommonNominalFullCarrier.model]
                      | value a b =>
                          have _smaller := decompose_context_arguments_size_lt context declaration before after
                            obligations generated child a b present
                          exact inspect_context_exact registry assignment child a b
                    have exactArguments := decompose_context_arguments_exact (ContextDerives registry assignment)
                      (rowPart assignment) context declaration before after
                    rw [generated, result_some] at exactArguments
                    calc
                      _ ↔ ∀ obligation ∈ obligations,
                          ContextObligation.Holds (ContextDerives registry assignment) (rowPart assignment) obligation :=
                        forall_congr' fun obligation => forall_congr' fun present => each obligation present
                      _ ↔ ContextArgumentsRel (ContextDerives registry assignment) (rowPart assignment)
                          context declaration before after := exactArguments
                      _ ↔ ContextDerives registry assignment context
                          (.nominal name before) (.nominal name after) := by
                        rw [context_derives_nominal_exact]
                        simp only [true_and, declared, Option.some.injEq, exists_eq_left']
          · rw [inspectContext]
            simp only [same, ↓reduceIte]
            constructor
            · intro impossible; exact False.elim (result_none _ impossible)
            · intro proof
              exact False.elim (same
                ((context_derives_nominal_exact registry assignment context name other before after).mp proof).1)
termination_by max (sizeOf first) (sizeOf last)
decreasing_by
  simp only [Endpoint.nominal.sizeOf_spec]
  omega


theorem compiled_full_exact (table : Registry)
    (m : α → Comp CommonNominalFullCarrier.model) (context : Bool) (lo hi : Endpoint α) :
    ResultHolds (fun atom => atom.Holds CommonNominalFullCarrier.model m) (compileInContext table context lo hi) ↔
      ContextWellFormed table context lo ∧ ContextWellFormed table context hi ∧ ContextDerives table m context lo hi := by
  unfold compileInContext
  by_cases accepted : (admitContext table context lo && admitContext table context hi) = true
  · simp only [accepted,ite_true,inspect_context_exact]
    obtain ⟨l,h⟩ := Bool.and_eq_true_iff.mp accepted
    simp only [(admit_context_exact table context lo).mp l,(admit_context_exact table context hi).mp h,true_and]
  · simp only [accepted,Bool.false_eq_true,ite_false,result_none,false_iff]
    rintro ⟨left,right,_⟩
    exact accepted (Bool.and_eq_true_iff.mpr ⟨(admit_context_exact ..).mpr left,(admit_context_exact ..).mpr right⟩)

theorem in_current_full_model {s : GeneralDeclarativeHead320.State} {e table context lo hi}
    (checked : GeneralDeclarativeWitnessSparseIntervals357.Compiled e table context lo hi)
    (present : ∀ atom ∈ checked.rows,atom ∈ s.normal.ordinary)
    (m : GeneralNominalCommonBridge.Assignment) (fit : GeneralDeclarativeHead320.Models s m) :
    ContextWellFormed table context lo ∧ ContextWellFormed table context hi ∧ ContextDerives table m context lo hi := by
  apply (compiled_full_exact table m context lo hi).mp
  exact ⟨checked.rows,checked.exact,fun atom used => fit.1.1 _ (present atom used)⟩

end Yulang.GeneralDeclarativeWitnessFullIntervals357
