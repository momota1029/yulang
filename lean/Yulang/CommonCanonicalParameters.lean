import Yulang.CommonCanonicalNames

/-!
# Removal of unused generalized parameters across different arities

The finite `Form` syntax admits uniform scalar substitutions. Compaction
keeps exactly its used generalized slots, in first-occurrence order, and
removes every unused slot, including the zero-slot case. Projection and
extension of assignments recover every concrete type by literal equality.

After the independent constructor/lattice normalization, this also removes
slots eliminated by that normalization. Exact demand-equivalent instance
families and their upward subtype closures are preserved in both directions.
No same-arity permutation hypothesis is required.

This is not a complete canonical code for arbitrary instance families.
General reparameterizations can merge even used slots. Weak-variable metadata,
row renaming and the larger public interface grammar remain outside `Form`.
-/

namespace Yulang.CommonCanonicalParameters

open ProducerCanonicalOpen (Expr Atom)
open CommonCanonicalInterface (Form)
open CommonCanonicalNames (occurrencesExpr occurrences used unique mem_unique unique_nodup)

variable {n m : Nat}

def substituteExpr (replacement : Fin n → Expr m) : Expr n → Expr m
  | .atom (.var index) => replacement index
  | .atom (.base scalar) => .atom (.base scalar)
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (substituteExpr replacement first) (substituteExpr replacement last)
  | .inter first last => .inter (substituteExpr replacement first) (substituteExpr replacement last)

/-- A single replacement is used for every occurrence, including arrow
domains. This preserves the original sharing across positive/negative uses. -/
def substitute (replacement : Fin n → Expr m) : Form n → Form m
  | .scalar expression => .scalar (substituteExpr replacement expression)
  | .pair first last => .pair (substitute replacement first) (substitute replacement last)
  | .required label payload => .required label (substitute replacement payload)
  | .variant label payload => .variant label (substitute replacement payload)
  | .arrow incoming outgoing input output =>
      .arrow incoming outgoing (substituteExpr replacement input) (substitute replacement output)

theorem instantiate_substituteExpr (replacement : Fin n → Expr m) (parameters : Fin m → Common.Ty)
    (expression : Expr n) :
    CommonCanonicalOpen.instantiate parameters (substituteExpr replacement expression) =
      CommonCanonicalOpen.instantiate
        (fun index => CommonCanonicalOpen.instantiate parameters (replacement index)) expression := by
  induction expression with
  | atom entry => cases entry <;> rfl
  | _ => simp_all [substituteExpr, CommonCanonicalOpen.instantiate]

theorem instantiate_substitute (replacement : Fin n → Expr m) (rows : Nat → Common.Row)
    (parameters : Fin m → Common.Ty) (expression : Form n) :
    (substitute replacement expression).instantiate rows parameters =
      expression.instantiate rows (fun index => CommonCanonicalOpen.instantiate parameters (replacement index)) := by
  induction expression <;>
    simp_all [substitute, Form.instantiate, instantiate_substituteExpr]

/-- Two finite scalar substitutions can witness equality of instance
families across arbitrary arities. They need not be permutations, injections
or inverses on all assignments. The hypotheses are the existing independent
pointwise demand equivalences, each decidable by its finite canonical code. -/
theorem reparameterization_instances_exact (first : Form n) (last : Form m)
    (forward : Fin n → Expr m) (backward : Fin m → Expr n)
    (firstLast : CommonCanonicalInterface.Equivalent (substitute forward first) last)
    (lastFirst : CommonCanonicalInterface.Equivalent (substitute backward last) first)
    (rows : Nat → Common.Row) (target : Common.Ty) :
    (∃ parameters : Fin n → Common.Ty, Common.Equivalent (first.instantiate rows parameters) target) ↔
      ∃ parameters : Fin m → Common.Ty, Common.Equivalent (last.instantiate rows parameters) target := by
  constructor
  · rintro ⟨parameters, same⟩
    refine ⟨fun index => CommonCanonicalOpen.instantiate parameters (backward index), ?_⟩
    have converted := lastFirst rows parameters
    rw [instantiate_substitute] at converted
    exact Common.equivalent_trans converted same
  · rintro ⟨parameters, same⟩
    refine ⟨fun index => CommonCanonicalOpen.instantiate parameters (forward index), ?_⟩
    have converted := firstLast rows parameters
    rw [instantiate_substitute] at converted
    exact Common.equivalent_trans converted same

theorem reparameterization_subtype_instances_exact (first : Form n) (last : Form m)
    (forward : Fin n → Expr m) (backward : Fin m → Expr n)
    (firstLast : CommonCanonicalInterface.Equivalent (substitute forward first) last)
    (lastFirst : CommonCanonicalInterface.Equivalent (substitute backward last) first)
    (rows : Nat → Common.Row) (target : Common.Ty) :
    (∃ parameters : Fin n → Common.Ty, Common.Subtype (first.instantiate rows parameters) target) ↔
      ∃ parameters : Fin m → Common.Ty, Common.Subtype (last.instantiate rows parameters) target := by
  constructor
  · rintro ⟨parameters, below⟩
    refine ⟨fun index => CommonCanonicalOpen.instantiate parameters (backward index), ?_⟩
    have converted := lastFirst rows parameters
    rw [instantiate_substitute] at converted
    exact Common.subtype_trans converted.1 below
  · rintro ⟨parameters, below⟩
    refine ⟨fun index => CommonCanonicalOpen.instantiate parameters (forward index), ?_⟩
    have converted := firstLast rows parameters
    rw [instantiate_substitute] at converted
    exact Common.subtype_trans converted.1 below

theorem instantiateExpr_agrees (expression : Expr n) (first last : Fin n → Common.Ty)
    (agree : ∀ index ∈ occurrencesExpr expression, first index = last index) :
    CommonCanonicalOpen.instantiate first expression = CommonCanonicalOpen.instantiate last expression := by
  induction expression with
  | atom entry =>
      cases entry with
      | var index => exact agree index List.mem_cons_self
      | base => rfl
  | bottom | top => rfl
  | union before after ihb iha | inter before after ihb iha =>
      have left := ihb (fun index member => agree index (List.mem_append_left _ member))
      have right := iha (fun index member => agree index (List.mem_append_right _ member))
      simp only [CommonCanonicalOpen.instantiate, left, right]

theorem instantiate_agrees (expression : Form n) (rows : Nat → Common.Row)
    (first last : Fin n → Common.Ty)
    (agree : ∀ index ∈ occurrences expression, first index = last index) :
    expression.instantiate rows first = expression.instantiate rows last := by
  induction expression with
  | scalar expression => exact instantiateExpr_agrees expression first last agree
  | pair before after ihb iha =>
      have left := ihb (fun index member => agree index (List.mem_append_left _ member))
      have right := iha (fun index member => agree index (List.mem_append_right _ member))
      simp only [Form.instantiate, left, right]
  | required label payload ih | variant label payload ih =>
      simp only [Form.instantiate, ih agree]
  | arrow incoming outgoing input output ih =>
      have domain := instantiateExpr_agrees input first last
        (fun index member => agree index (List.mem_append_left _ member))
      have result := ih (fun index member => agree index (List.mem_append_right _ member))
      simp only [Form.instantiate, domain, result]

def replacement (expression : Form n) (index : Fin n) : Expr (used expression).length :=
  if present : index ∈ used expression then
    .atom (.var ⟨(used expression).idxOf index, List.idxOf_lt_length_of_mem present⟩)
  else .bottom

def compact (expression : Form n) : Form (used expression).length :=
  substitute (replacement expression) expression

def project (expression : Form n) (parameters : Fin n → Common.Ty) :
    Fin (used expression).length → Common.Ty :=
  fun index => parameters (used expression)[index.val]

/-- Unused old slots receive bottom only to make the extension total. Any
fixed common type would give the same instantiated form, by `instantiate_agrees`. -/
def expand (expression : Form n) (parameters : Fin (used expression).length → Common.Ty) :
    Fin n → Common.Ty :=
  fun index => CommonCanonicalOpen.instantiate parameters (replacement expression index)

theorem expand_project_used (expression : Form n) (parameters : Fin n → Common.Ty)
    (index : Fin n) (member : index ∈ used expression) :
    expand expression (project expression parameters) index = parameters index := by
  simp only [expand, replacement, member, ↓reduceDIte, CommonCanonicalOpen.instantiate,
    CommonCanonicalOpen.atomType, project]
  exact congrArg parameters (List.getElem_idxOf _)

/-- Every old assignment has a compact assignment with literally the same
common type. Rows, regular parameter types and repeated negative uses remain
unchanged by the projection. -/
theorem compact_project_exact (expression : Form n) (rows : Nat → Common.Row)
    (parameters : Fin n → Common.Ty) :
    (compact expression).instantiate rows (project expression parameters) =
      expression.instantiate rows parameters := by
  rw [compact, instantiate_substitute]
  apply instantiate_agrees
  intro index member
  exact expand_project_used expression parameters index ((mem_unique _ _).mpr member)

/-- Every compact assignment extends to an old assignment with literally
the same common type. No extra conditions are imposed on the new parameters. -/
theorem compact_expand_exact (expression : Form n) (rows : Nat → Common.Row)
    (parameters : Fin (used expression).length → Common.Ty) :
    (compact expression).instantiate rows parameters =
      expression.instantiate rows (expand expression parameters) :=
  instantiate_substitute _ rows parameters expression

theorem compact_instances_exact (expression : Form n) (rows : Nat → Common.Row) (target : Common.Ty) :
    (∃ parameters : Fin n → Common.Ty, Common.Equivalent (expression.instantiate rows parameters) target) ↔
      ∃ parameters : Fin (used expression).length → Common.Ty,
        Common.Equivalent ((compact expression).instantiate rows parameters) target := by
  constructor
  · rintro ⟨parameters, same⟩
    refine ⟨project expression parameters, ?_⟩
    simpa only [compact_project_exact] using same
  · rintro ⟨parameters, same⟩
    refine ⟨expand expression parameters, ?_⟩
    simpa only [compact_expand_exact] using same

theorem compact_subtype_instances_exact (expression : Form n) (rows : Nat → Common.Row)
    (target : Common.Ty) :
    (∃ parameters : Fin n → Common.Ty, Common.Subtype (expression.instantiate rows parameters) target) ↔
      ∃ parameters : Fin (used expression).length → Common.Ty,
        Common.Subtype ((compact expression).instantiate rows parameters) target := by
  constructor
  · rintro ⟨parameters, below⟩
    refine ⟨project expression parameters, ?_⟩
    simpa only [compact_project_exact] using below
  · rintro ⟨parameters, below⟩
    refine ⟨expand expression parameters, ?_⟩
    simpa only [compact_expand_exact] using below

theorem compact_parameter_count_le (expression : Form n) : (used expression).length ≤ n := by
  have bound := (unique_nodup (occurrences expression)).length_le_of_subset
    (l₂ := List.finRange n) (fun _ _ => List.mem_finRange _)
  simpa only [used, List.length_finRange] using bound

theorem occurrence_substituteExpr (replacement : Fin n → Expr m) (expression : Expr n)
    (original : Fin n) (member : original ∈ occurrencesExpr expression)
    (index : Fin m) (inserted : index ∈ occurrencesExpr (replacement original)) :
    index ∈ occurrencesExpr (substituteExpr replacement expression) := by
  induction expression with
  | atom entry =>
      cases entry with
      | var actual =>
          have same := List.mem_singleton.mp member
          subst actual
          exact inserted
      | base => cases member
  | bottom | top => cases member
  | union first last ihf ihl | inter first last ihf ihl =>
      exact (List.mem_append.mp member).elim
        (fun inside => List.mem_append_left _ (ihf inside))
        (fun inside => List.mem_append_right _ (ihl inside))

theorem occurrence_substitute (replacement : Fin n → Expr m) (expression : Form n)
    (original : Fin n) (member : original ∈ occurrences expression)
    (index : Fin m) (inserted : index ∈ occurrencesExpr (replacement original)) :
    index ∈ occurrences (substitute replacement expression) := by
  induction expression with
  | scalar expression => exact occurrence_substituteExpr replacement expression original member index inserted
  | pair first last ihf ihl =>
      exact (List.mem_append.mp member).elim
        (fun inside => List.mem_append_left _ (ihf inside))
        (fun inside => List.mem_append_right _ (ihl inside))
  | required _ payload ih | variant _ payload ih => exact ih member
  | arrow _ _ input output ih =>
      exact (List.mem_append.mp member).elim
        (fun inside => List.mem_append_left _
          (occurrence_substituteExpr replacement input original inside index inserted))
        (fun inside => List.mem_append_right _ (ih inside))

/-- Every slot of the compact result actually appears. This includes the
zero-slot case without retaining an artificial dummy parameter. -/
theorem compact_all_parameters_used (expression : Form n) (index : Fin (used expression).length) :
    index ∈ used (compact expression) := by
  let original := (used expression)[index.val]
  have member : original ∈ used expression := List.getElem_mem index.isLt
  apply (mem_unique _ _).mpr
  apply occurrence_substitute (replacement expression) expression original
    ((mem_unique _ _).mp member) index
  simp only [replacement, member, ↓reduceDIte, occurrencesExpr, List.mem_singleton]
  apply Fin.ext
  exact (unique_nodup (occurrences expression)).idxOf_getElem index.val index.isLt |>.symm

def normalizedCompact (expression : Form n) :
    Form (used (CommonCanonicalInterface.normalize expression)).length :=
  compact (CommonCanonicalInterface.normalize expression)

theorem normalizedCompact_instances_exact (expression : Form n) (rows : Nat → Common.Row)
    (target : Common.Ty) :
    (∃ parameters : Fin n → Common.Ty, Common.Equivalent (expression.instantiate rows parameters) target) ↔
      ∃ parameters : Fin (used (CommonCanonicalInterface.normalize expression)).length → Common.Ty,
        Common.Equivalent ((normalizedCompact expression).instantiate rows parameters) target := by
  rw [normalizedCompact, ← compact_instances_exact]
  constructor
  · rintro ⟨parameters, same⟩
    exact ⟨parameters, Common.equivalent_trans
      (CommonCanonicalInterface.normalize_equivalent expression rows parameters) same⟩
  · rintro ⟨parameters, same⟩
    exact ⟨parameters, Common.equivalent_trans
      (Common.equivalent_symm (CommonCanonicalInterface.normalize_equivalent expression rows parameters)) same⟩

theorem normalizedCompact_subtype_instances_exact (expression : Form n) (rows : Nat → Common.Row)
    (target : Common.Ty) :
    (∃ parameters : Fin n → Common.Ty, Common.Subtype (expression.instantiate rows parameters) target) ↔
      ∃ parameters : Fin (used (CommonCanonicalInterface.normalize expression)).length → Common.Ty,
        Common.Subtype ((normalizedCompact expression).instantiate rows parameters) target := by
  rw [normalizedCompact, ← compact_subtype_instances_exact]
  constructor
  · rintro ⟨parameters, below⟩
    exact ⟨parameters, Common.subtype_trans
      (CommonCanonicalInterface.normalize_equivalent expression rows parameters).1 below⟩
  · rintro ⟨parameters, below⟩
    exact ⟨parameters, Common.subtype_trans
      (CommonCanonicalInterface.normalize_equivalent expression rows parameters).2 below⟩

namespace Examples

def twoUsed : Form 2 := .scalar (.union (.atom (.var 0)) (.atom (.var 1)))
def oneUsed : Form 1 := .scalar (.atom (.var 0))

/-- Even genuinely used parameters may merge under instance semantics.
Unused-slot removal and same-arity alpha normalization alone cannot be a
complete decision procedure for equality of these families. -/
theorem union_parameters_merge (rows : Nat → Common.Row) (target : Common.Ty) :
    (∃ parameters : Fin 2 → Common.Ty, Common.Equivalent (twoUsed.instantiate rows parameters) target) ↔
      ∃ parameters : Fin 1 → Common.Ty, Common.Equivalent (oneUsed.instantiate rows parameters) target := by
  apply reparameterization_instances_exact twoUsed oneUsed
    (fun _ => .atom (.var 0)) (fun _ => .union (.atom (.var 0)) (.atom (.var 1)))
  · intro _ parameters
    change Common.Equivalent (.union (parameters 0) (parameters 0)) (parameters 0)
    exact ⟨(Common.common_union_is_join _ _ _).mpr
      ⟨Common.subtype_refl _, Common.subtype_refl _⟩,
      ((Common.common_union_is_join _ _ _).mp (Common.subtype_refl (.union (parameters 0) (parameters 0)))).1⟩
  · intro _ _
    exact Common.equivalent_refl _

theorem both_parameters_used : used twoUsed = [0, 1] := by decide +kernel

end Examples

end Yulang.CommonCanonicalParameters
