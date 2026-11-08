import Yulang.CommonRecursiveNominalIntervalGeneration

/-!
# Independent finite structural derivations for nested interval compilation

These rules mention ordinary Common subtype/row order and declaration
metadata, not the compiler. Invariant rules retain four recursive premises
for arbitrary open bounds. They do not quantify a chosen actual argument.
The judgment has the finite structural grammar of the descriptions; it is
not claimed to be the full regular nominal carrier's subtype relation.
-/

namespace Yulang.CommonRecursiveNominalIntervals

open Core.PresenceGeneration (TyTerm RowTerm Comp)
open CommonDeclaredNominalInspection (Kind Parameter Declaration Registry)
open CommonDeclaredNominalVariance (Variance)
open PresenceNormalForm (Atom All)

mutual
inductive Derives (registry : Registry) (assignment : α → Comp Common.model) :
    Endpoint α → Endpoint α → Prop where
  | ordinary {a b : TyTerm α} :
      Common.Subtype (a.eval Common.model assignment) (b.eval Common.model assignment) →
      Derives registry assignment (.ordinary a) (.ordinary b)
  | nominal {name : Nat} {first last : List (Argument α)} {declaration : Declaration} :
      registry[name]? = some declaration →
      DerivesArguments registry assignment declaration first last →
      Derives registry assignment (.nominal name first) (.nominal name last)

inductive DerivesArguments (registry : Registry) (assignment : α → Comp Common.model) :
    Declaration → List (Argument α) → List (Argument α) → Prop where
  | nil : DerivesArguments registry assignment [] [] []
  | cons {parameter rest first tail last suffix} :
      DerivesArgument registry assignment parameter first last →
      DerivesArguments registry assignment rest tail suffix →
      DerivesArguments registry assignment (parameter :: rest) (first :: tail) (last :: suffix)

inductive DerivesArgument (registry : Registry) (assignment : α → Comp Common.model) :
    Parameter → Argument α → Argument α → Prop where
  | covariantValue {a b} : Derives registry assignment a b →
      DerivesArgument registry assignment ⟨.value, .covariant⟩ (.inl (.point a)) (.inl (.point b))
  | contravariantValue {a b} : Derives registry assignment b a →
      DerivesArgument registry assignment ⟨.value, .contravariant⟩ (.inl (.point a)) (.inl (.point b))
  | invariantValue {a b : Bounds (Endpoint α)} :
      Derives registry assignment a.lower a.upper → Derives registry assignment b.lower b.upper →
      Derives registry assignment a.lower b.upper → Derives registry assignment b.lower a.upper →
      DerivesArgument registry assignment ⟨.value, .invariant⟩ (.inl a) (.inl b)
  | unusedValue (a b : Bounds (Endpoint α)) :
      DerivesArgument registry assignment ⟨.value, .unused⟩ (.inl a) (.inl b)
  | covariantRow {a b : RowTerm α} :
      Common.rowLe (a.eval Common.model assignment) (b.eval Common.model assignment) →
      DerivesArgument registry assignment ⟨.row, .covariant⟩ (.inr (.point a)) (.inr (.point b))
  | contravariantRow {a b : RowTerm α} :
      Common.rowLe (b.eval Common.model assignment) (a.eval Common.model assignment) →
      DerivesArgument registry assignment ⟨.row, .contravariant⟩ (.inr (.point a)) (.inr (.point b))
  | invariantRow {a b : Bounds (RowTerm α)} :
      Common.rowLe (a.lower.eval Common.model assignment) (a.upper.eval Common.model assignment) →
      Common.rowLe (b.lower.eval Common.model assignment) (b.upper.eval Common.model assignment) →
      Common.rowLe (a.lower.eval Common.model assignment) (b.upper.eval Common.model assignment) →
      Common.rowLe (b.lower.eval Common.model assignment) (a.upper.eval Common.model assignment) →
      DerivesArgument registry assignment ⟨.row, .invariant⟩ (.inr a) (.inr b)
  | unusedRow (a b : Bounds (RowTerm α)) :
      DerivesArgument registry assignment ⟨.row, .unused⟩ (.inr a) (.inr b)
end

theorem derives_argument_exact (registry : Registry) (assignment : α → Comp Common.model)
    (parameter : Parameter) (first last : Argument α) :
    DerivesArgument registry assignment parameter first last ↔
      ArgumentRel (Derives registry assignment) assignment parameter first last := by
  rcases parameter with ⟨kind, mode⟩
  cases first <;> cases last <;> rename_i first last
  all_goals cases first <;> cases last <;> cases kind <;> cases mode
  all_goals simp only [ArgumentRel]
  all_goals constructor <;> intro proof
  all_goals solve
    | cases proof <;> simp_all
    | exact .covariantValue proof
    | exact .contravariantValue proof
    | exact .covariantRow proof
    | exact .contravariantRow proof
    | exact .unusedValue _ _
    | exact .unusedRow _ _
    | exact .invariantValue proof.1 proof.2.1 proof.2.2.1 proof.2.2.2
    | exact .invariantRow proof.1 proof.2.1 proof.2.2.1 proof.2.2.2

theorem derives_arguments_exact (registry : Registry) (assignment : α → Comp Common.model)
    (declaration : Declaration) (first last : List (Argument α)) :
    DerivesArguments registry assignment declaration first last ↔
      ArgumentsRel (Derives registry assignment) assignment declaration first last := by
  induction declaration generalizing first last with
  | nil =>
      cases first <;> cases last <;> simp only [ArgumentsRel]
      all_goals constructor <;> intro proof
      all_goals solve | cases proof | exact .nil | trivial
  | cons parameter rest ih =>
      cases first with
      | nil =>
          cases last <;> simp only [ArgumentsRel]
          all_goals constructor <;> intro proof <;> cases proof
      | cons first tail =>
          cases last with
          | nil =>
              simp only [ArgumentsRel]
              constructor <;> intro proof <;> cases proof
          | cons last suffix =>
              simp only [ArgumentsRel]
              constructor
              · intro proof
                cases proof with
                | cons head tail =>
                    exact ⟨(derives_argument_exact registry assignment _ _ _).mp head,
                      (ih _ _).mp tail⟩
              · rintro ⟨head, tail⟩
                exact .cons ((derives_argument_exact registry assignment _ _ _).mpr head)
                  ((ih _ _).mpr tail)

theorem derives_ordinary_exact (registry : Registry) (assignment : α → Comp Common.model)
    (a b : TyTerm α) :
    Derives registry assignment (.ordinary a) (.ordinary b) ↔
      Common.Subtype (a.eval Common.model assignment) (b.eval Common.model assignment) := by
  constructor
  · intro proof; cases proof; assumption
  · exact Derives.ordinary

theorem derives_nominal_exact (registry : Registry) (assignment : α → Comp Common.model)
    (name other : Nat) (first last : List (Argument α)) :
    Derives registry assignment (.nominal name first) (.nominal other last) ↔
      name = other ∧ ∃ declaration, registry[name]? = some declaration ∧
        ArgumentsRel (Derives registry assignment) assignment declaration first last := by
  constructor
  · intro proof
    cases proof with
    | nominal declared arguments =>
        exact ⟨rfl, _, declared, (derives_arguments_exact registry assignment _ _ _).mp arguments⟩
  · rintro ⟨rfl, declaration, declared, arguments⟩
    exact .nominal declared ((derives_arguments_exact registry assignment _ _ _).mpr arguments)

def inspectObligation (registry : Registry) : Obligation α → Option (List (Atom α))
  | .value first last => inspect registry first last
  | .row first last => some [.rowLe first last]

theorem inspect_nominal (registry : Registry) (name : Nat)
    (first last : List (Argument α)) (declaration : Declaration) (obligations : List (Obligation α))
    (declared : registry[name]? = some declaration)
    (generated : decomposeArguments declaration first last = some obligations) :
    inspect registry (.nominal name first) (.nominal name last) =
      concatenate (obligations.map (inspectObligation registry)) := by
  rw [inspect]
  simp only [↓reduceIte, declared]
  split
  · rename_i absent
    simp [absent] at generated
  · rename_i parts returned
    have same : parts = obligations := Option.some.inj (returned.symm.trans generated)
    subst parts
    congr 1
    calc
      _ = obligations.attach.map (fun obligation => inspectObligation registry obligation.val) := by
        apply List.map_congr_left
        intro obligation _
        cases obligation.val <;> rfl
      _ = _ := List.attach_map_val


/-- Every finite pair of descriptions, every declaration registry and every
original Common assignment. The compiler performs every nested comparison;
no semantic condition is supplied to its recursion. This is exactness of the
local structural grammar, prior to recursive syntactic admission. -/
theorem inspect_exact (registry : Registry) (assignment : α → Comp Common.model)
    (first last : Endpoint α) :
    ResultHolds (fun atom => atom.Holds Common.model assignment) (inspect registry first last) ↔
      Derives registry assignment first last := by
  cases first with
  | ordinary a =>
      cases last with
      | ordinary b =>
          rw [inspect, derives_ordinary_exact]
          simp [ResultHolds, Atom.Holds, Common.model]
      | nominal other after =>
          rw [inspect] <;> try (solve | simp)
          constructor
          · intro impossible; exact False.elim (result_none _ impossible)
          · intro impossible; cases impossible
  | nominal name before =>
      cases last with
      | ordinary b =>
          rw [inspect] <;> try (solve | simp)
          constructor
          · intro impossible; exact False.elim (result_none _ impossible)
          · intro impossible; cases impossible
      | nominal other after =>
          by_cases same : name = other
          · subst other
            cases declared : registry[name]? with
            | none =>
                rw [inspect]
                simp only [↓reduceIte, declared]
                constructor
                · intro impossible; exact False.elim (result_none _ impossible)
                · intro proof
                  obtain ⟨_, declaration, found, _⟩ :=
                    (derives_nominal_exact registry assignment name name before after).mp proof
                  simp [declared] at found
            | some declaration =>
                cases generated : decomposeArguments declaration before after with
                | none =>
                    have absent : inspect registry (.nominal name before) (.nominal name after) = none := by
                      rw [inspect]
                      simp only [↓reduceIte, declared]
                      split <;> simp_all
                    rw [absent]
                    constructor
                    · intro impossible; exact False.elim (result_none _ impossible)
                    · intro proof
                      obtain ⟨_, actual, found, arguments⟩ :=
                        (derives_nominal_exact registry assignment name name before after).mp proof
                      have equal : actual = declaration := Option.some.inj (found.symm.trans declared)
                      subst actual
                      have emitted := (decompose_arguments_exact (Derives registry assignment)
                        assignment declaration before after).mpr arguments
                      rw [generated] at emitted
                      exact False.elim (result_none _ emitted)
                | some obligations =>
                    rw [inspect_nominal registry name before after declaration obligations declared generated]
                    rw [concatenate_exact]
                    simp only [List.forall_mem_map]
                    have each (obligation : Obligation α) (present : obligation ∈ obligations) :
                        ResultHolds (fun atom => atom.Holds Common.model assignment)
                          (inspectObligation registry obligation) ↔
                            obligation.Holds (Derives registry assignment) assignment := by
                      cases obligation with
                      | row a b => simp [inspectObligation, ResultHolds, Atom.Holds, Obligation.Holds, Common.model]
                      | value a b =>
                          have _smaller := decompose_arguments_size_lt declaration before after obligations
                            generated a b present
                          exact inspect_exact registry assignment a b
                    have exactArguments := decompose_arguments_exact (Derives registry assignment)
                      assignment declaration before after
                    rw [generated, result_some] at exactArguments
                    calc
                      _ ↔ ∀ obligation ∈ obligations,
                          obligation.Holds (Derives registry assignment) assignment :=
                        forall_congr' fun obligation => forall_congr' fun present => each obligation present
                      _ ↔ ArgumentsRel (Derives registry assignment) assignment declaration before after :=
                        exactArguments
                      _ ↔ Derives registry assignment (.nominal name before) (.nominal name after) := by
                        rw [derives_nominal_exact]
                        simp only [true_and, declared, Option.some.injEq, exists_eq_left']
          · rw [inspect]
            simp only [same, ↓reduceIte]
            constructor
            · intro impossible; exact False.elim (result_none _ impossible)
            · intro proof
              exact False.elim (same ((derives_nominal_exact registry assignment name other before after).mp proof).1)
termination_by max (sizeOf first) (sizeOf last)
decreasing_by
  simp only [Endpoint.nominal.sizeOf_spec]
  omega

end Yulang.CommonRecursiveNominalIntervals
