import Yulang.CommonCanonicalParameters
import Yulang.CommonBoundCoalescing

/-!
# One-polarity parameter removal over the common constructor grammar

This finite pass computes the positive and negative occurrences of each
parameter in the existing `Form` grammar. An unfrozen parameter used only
positively becomes bottom; one used only negatively becomes top. Parameters
shared between both polarities, and every frozen parameter, retain their
original identity. Weak/ambient slots can therefore be frozen explicitly.

The instance theorem fixes all frozen values on both sides, and quantifies
every remaining parameter over the full common carrier. Rows are held fixed
and arbitrary. No structural-type embedding, fixed record-spine hypothesis,
or semantic subtype checker is used. Role-dependent slots must also be kept
when this pass is placed beneath qualifier interpretation; this module does
not erase any role requirement or claim complete interface canonicalization.
-/

namespace Yulang.CommonCanonicalPolarity

open ProducerCanonicalOpen (Expr)
open CommonCanonicalInterface (Form)
open CommonCanonicalNames (occurrencesExpr)
open CommonCanonicalOpen (instantiate)
open CommonCanonicalParameters (substitute instantiate_substitute)
open Common (Ty Row Subtype)

variable {n : Nat}

/-- Arrow domains are scalar expressions in this grammar; every one of
their parameter occurrences is negative. Arrow results retain polarity. -/
def variables (positive : Bool) : Form n → List (Fin n)
  | .scalar expression => if positive then occurrencesExpr expression else []
  | .pair first last => variables positive first ++ variables positive last
  | .required _ payload | .variant _ payload => variables positive payload
  | .arrow _ _ input output =>
      (if positive then [] else occurrencesExpr input) ++ variables positive output

theorem scalar_ordered (expression : Expr n) (first last : Fin n → Ty)
    (below : ∀ index ∈ occurrencesExpr expression, Subtype (first index) (last index)) :
    Subtype (instantiate first expression) (instantiate last expression) := by
  induction expression with
  | atom entry =>
      cases entry with
      | var index => exact below index List.mem_cons_self
      | base => exact Common.subtype_refl _
  | bottom | top => exact Common.subtype_refl _
  | union _ _ ihf ihl =>
      exact Common.common_union_mono
        (ihf (fun index member => below index (List.mem_append_left _ member)))
        (ihl (fun index member => below index (List.mem_append_right _ member)))
  | inter _ _ ihf ihl =>
      exact Common.common_inter_mono
        (ihf (fun index member => below index (List.mem_append_left _ member)))
        (ihl (fun index member => below index (List.mem_append_right _ member)))

/-- Every shared parameter is compared in every polarity where it occurs.
Mixed parameters consequently require both directions of the comparison. -/
theorem instantiate_ordered (expression : Form n) (rows : Nat → Row)
    (first last : Fin n → Ty)
    (positive : ∀ index ∈ variables true expression, Subtype (first index) (last index))
    (negative : ∀ index ∈ variables false expression, Subtype (last index) (first index)) :
    Subtype (expression.instantiate rows first) (expression.instantiate rows last) := by
  induction expression with
  | scalar expression => exact scalar_ordered expression first last positive
  | pair before after ihb iha =>
      exact (Common.common_pair_iff _ _ _ _).mpr
        ⟨ihb (fun index member => positive index (List.mem_append_left _ member))
            (fun index member => negative index (List.mem_append_left _ member)),
          iha (fun index member => positive index (List.mem_append_right _ member))
            (fun index member => negative index (List.mem_append_right _ member))⟩
  | required label payload ih =>
      exact Common.common_record_mono label (ih positive negative) (Common.subtype_refl _)
  | variant label payload ih =>
      exact (Common.common_variant_iff label _ _).mpr (ih positive negative)
  | arrow incoming outgoing input output ih =>
      have argument := scalar_ordered input last first
        (fun index member => negative index (List.mem_append_left _ member))
      have result := ih
        (fun index member => positive index (List.mem_append_right _ member))
        (fun index member => negative index (List.mem_append_right _ member))
      exact (Common.common_arrow_iff _ _ _ _ _ _ _ _).mpr
        ⟨argument, Common.rowLe_refl _, result, Common.rowLe_refl _⟩

def replacement (frozen : Fin n → Bool) (expression : Form n) (index : Fin n) : Expr n :=
  if frozen index then .atom (.var index)
  else if index ∈ variables false expression then
    if index ∈ variables true expression then .atom (.var index) else .top
  else .bottom

def simplify (frozen : Fin n → Bool) (expression : Form n) : Form n :=
  substitute (replacement frozen expression) expression

def selected (frozen : Fin n → Bool) (expression : Form n) (parameters : Fin n → Ty) : Fin n → Ty :=
  fun index => if frozen index then parameters index
    else if index ∈ variables false expression then
      if index ∈ variables true expression then parameters index else .top
    else .bottom

theorem replacement_eval (frozen : Fin n → Bool) (expression : Form n)
    (parameters : Fin n → Ty) (index : Fin n) :
    instantiate parameters (replacement frozen expression index) = selected frozen expression parameters index := by
  by_cases kept : frozen index = true <;>
    by_cases negative : index ∈ variables false expression <;>
    by_cases positive : index ∈ variables true expression <;>
    simp [replacement, selected, kept, negative, positive, instantiate, CommonCanonicalOpen.atomType]

theorem instantiate_simplify (frozen : Fin n → Bool) (expression : Form n)
    (rows : Nat → Row) (parameters : Fin n → Ty) :
    (simplify frozen expression).instantiate rows parameters =
      expression.instantiate rows (selected frozen expression parameters) := by
  rw [simplify, instantiate_substitute]
  congr 1
  funext index
  exact replacement_eval frozen expression parameters index

theorem selected_frozen (frozen : Fin n → Bool) (expression : Form n)
    (parameters : Fin n → Ty) (index : Fin n) (kept : frozen index = true) :
    selected frozen expression parameters index = parameters index := by
  simp [selected, kept]

theorem selected_mixed (frozen : Fin n → Bool) (expression : Form n)
    (parameters : Fin n → Ty) (index : Fin n)
    (positive : index ∈ variables true expression) (negative : index ∈ variables false expression) :
    selected frozen expression parameters index = parameters index := by
  simp [selected, positive, negative]

theorem simplified_below (frozen : Fin n → Bool) (expression : Form n)
    (rows : Nat → Row) (parameters : Fin n → Ty) :
    Subtype ((simplify frozen expression).instantiate rows parameters) (expression.instantiate rows parameters) := by
  rw [instantiate_simplify]
  apply instantiate_ordered
  · intro index positive
    by_cases kept : frozen index = true
    · rw [selected_frozen frozen expression parameters index kept]
      exact Common.subtype_refl _
    · by_cases negative : index ∈ variables false expression
      · rw [selected_mixed frozen expression parameters index positive negative]
        exact Common.subtype_refl _
      · simpa [selected, kept, negative] using
          CommonBoundCoalescing.bottom_le (parameters index)
  · intro index negative
    by_cases kept : frozen index = true
    · rw [selected_frozen frozen expression parameters index kept]
      exact Common.subtype_refl _
    · by_cases positive : index ∈ variables true expression
      · rw [selected_mixed frozen expression parameters index positive negative]
        exact Common.subtype_refl _
      · simpa [selected, kept, negative, positive] using
          CommonBoundCoalescing.le_top (parameters index)

def Fixed (frozen : Fin n → Bool) (ambient parameters : Fin n → Ty) : Prop :=
  ∀ index, frozen index = true → parameters index = ambient index

theorem selected_fixed (frozen : Fin n → Bool) (expression : Form n) (ambient parameters : Fin n → Ty)
    (fixed : Fixed frozen ambient parameters) : Fixed frozen ambient (selected frozen expression parameters) := by
  intro index kept
  exact (selected_frozen frozen expression parameters index kept).trans (fixed index kept)

def Instances (frozen : Fin n → Bool) (ambient : Fin n → Ty) (rows : Nat → Row)
    (expression : Form n) (target : Ty) : Prop :=
  ∃ parameters : Fin n → Ty, Fixed frozen ambient parameters ∧
    Subtype (expression.instantiate rows parameters) target

/-- For every fixed ambient assignment, arbitrary rows and arbitrary common
target, the pass preserves the entire upward instance family. Generalized
values are unrestricted; the only fixed values are the explicitly frozen
slots, kept literally by the concrete witnessing reparameterization. -/
theorem simplify_instances_exact (frozen : Fin n → Bool) (ambient : Fin n → Ty) (rows : Nat → Row)
    (expression : Form n) (target : Ty) :
    Instances frozen ambient rows expression target ↔
      Instances frozen ambient rows (simplify frozen expression) target := by
  constructor
  · rintro ⟨parameters, fixed, below⟩
    exact ⟨parameters, fixed, Common.subtype_trans (simplified_below frozen expression rows parameters) below⟩
  · rintro ⟨parameters, fixed, below⟩
    refine ⟨selected frozen expression parameters, selected_fixed frozen expression ambient parameters fixed, ?_⟩
    simpa only [instantiate_simplify] using below

def normalize (frozen : Fin n → Bool) (expression : Form n) : Form n :=
  CommonCanonicalInterface.normalize (simplify frozen expression)

theorem normalize_instances_exact (frozen : Fin n → Bool) (ambient : Fin n → Ty) (rows : Nat → Row)
    (expression : Form n) (target : Ty) :
    Instances frozen ambient rows expression target ↔
      Instances frozen ambient rows (normalize frozen expression) target := by
  rw [simplify_instances_exact frozen ambient rows expression target]
  constructor
  · rintro ⟨parameters, fixed, below⟩
    exact ⟨parameters, fixed, Common.subtype_trans
      (CommonCanonicalInterface.normalize_equivalent (simplify frozen expression) rows parameters).1 below⟩
  · rintro ⟨parameters, fixed, below⟩
    exact ⟨parameters, fixed, Common.subtype_trans
      (CommonCanonicalInterface.normalize_equivalent (simplify frozen expression) rows parameters).2 below⟩

namespace Examples

theorem positive_generalized_removed :
    simplify (n := 1) (fun _ => false) (.scalar (.atom (.var 0))) = .scalar .bottom := by decide +kernel

theorem negative_generalized_removed :
    simplify (n := 1) (fun _ => false) (.arrow 0 1 (.atom (.var 0)) (.scalar (.atom (.base .int)))) =
      .arrow 0 1 .top (.scalar (.atom (.base .int))) := by decide +kernel

theorem shared_identity_retained :
    simplify (n := 1) (fun _ => false) (.arrow 0 1 (.atom (.var 0)) (.scalar (.atom (.var 0)))) =
      .arrow 0 1 (.atom (.var 0)) (.scalar (.atom (.var 0))) := by decide +kernel

theorem positive_weak_retained :
    simplify (n := 1) (fun _ => true) (.scalar (.atom (.var 0))) = .scalar (.atom (.var 0)) := by decide +kernel

end Examples

end Yulang.CommonCanonicalPolarity
