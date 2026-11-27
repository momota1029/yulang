import Yulang.GeneralDeclarativeI65I74NamedProjection464
import Yulang.GeneralDeclarativeEntailment320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464.ReturnAudit
open GeneralDeclarativeHead320 (Equation Models)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonNominalFullCarrier (Ty Equivalent record)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeK2Graph321 (Shape Descends Path)
open GeneralDeclarativeK2Graph321.AddAtOneSource
open Derivation
open GeneralDeclarativeEntailment320 (Holds Entails)
open GeneralNominalCommonBridge (Assignment)
open List410 (ExactEscapeWire)

def empty : Expr := .primitive .emptyRecord []
def recState (field : Nat) : CommonNominalSyntax.State Common.Row :=
  .block [.record field (.inl 0) .emptyRecord] 0
def mu (field : Nat) : Ty := .record field (recState field) .emptyRecord
theorem unfold_mu455 (f : Nat) :
    Equivalent (mu f) (record f (mu f) .emptyRecord) := by
  have each (k : Nat) : CommonNominalFullCarrier.observeTy k (mu f) =
      CommonNominalFullCarrier.observeTy k (record f (mu f) .emptyRecord) := by
    cases k <;> rfl
  constructor
  · intro k
    rw [←each k]
    exact CommonNominalFullDemand.producerLe_refl _
  · intro k
    rw [each k]
    exact CommonNominalFullDemand.producerLe_refl _

def twiceInline : Equation := ⟨4,.record 30 (.record 30 (.variable 4) empty) empty⟩
def returnByName : Equation := ⟨5,.record 30 (.variable 4) empty⟩
def returningOld : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[twiceInline,returnByName]⟩
def returningProposed : Equation := ⟨4,.record 30 (.variable 5) empty⟩

theorem equivalent_named_projection_can_be_entailed_before_any_graph_insertion :
    Entails returningOld returningProposed := by
  intro m fit
  have h₁ := fit.2 twiceInline (by simp [returningOld])
  have h₂ := fit.2 returnByName (by simp [returningOld])
  change Equivalent (m 4).1 (record 30 (record 30 (m 4).1 .emptyRecord) .emptyRecord) at h₁
  change Equivalent (m 5).1 (record 30 (m 4).1 .emptyRecord) at h₂
  change Equivalent (m 4).1 (record 30 (m 5).1 .emptyRecord)
  exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans h₁
    (GeneralNominalCenteredHeadMatPatternSemantics.record_congr 30 ⟨h₂.2,h₂.1⟩
      (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _))

def returnModel : Assignment := fun _ => (mu 30,Common.rowEmpty)

theorem original_entailment_is_not_vacuous : Models returningOld returnModel := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  intro r h
  rcases List.mem_cons.mp h with first | second
  · subst r
    change Equivalent (mu 30) (record 30 (record 30 (mu 30) .emptyRecord) .emptyRecord)
    exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans (unfold_mu455 30)
      (GeneralNominalCenteredHeadMatPatternSemantics.record_congr 30 (unfold_mu455 30)
        (GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _))
  · obtain rfl := List.mem_singleton.mp second
    exact unfold_mu455 30

private theorem return_bound_is_refl {a b : Nat} (d : Bound returningOld.normal a b) : a=b := by
  induction d with
  | interval mem => cases mem
  | constraint mem => cases mem
  | refl => rfl
  | trans _ _ i j => exact i.trans j

private theorem returning_old_alias_is_refl {a b : Nat}
    (d : GeneralDeclarativeLowerKnown321.Alias returningOld a b) : a=b := by
  induction d with
  | bounds h _ => exact return_bound_is_refl h
  | forward h =>
    change _ ∈ [twiceInline,returnByName] at h
    rcases List.mem_cons.mp h with h | h
    · cases h
    · have h := List.mem_singleton.mp h
      cases h
  | backward h =>
    change _ ∈ [twiceInline,returnByName] at h
    rcases List.mem_cons.mp h with h | h
    · cases h
    · have h := List.mem_singleton.mp h
      cases h
  | trans _ _ i j => exact i.trans j

private theorem old_4_has_no_observed_shape :
    ¬ AliasCycle returningOld (observed returningOld) 4 := by
  apply GeneralDeclarativeK2Alias321.no_nonempty_alias_only
  rintro a alias shape ⟨expr,seen,parsed⟩
  have eq := returning_old_alias_is_refl alias
  subst a
  rcases List.mem_cons.mp seen with first | second
  · have eq := congrArg Equation.right first
    dsimp at eq
    subst expr
    change none=some shape at parsed
    cases parsed
  · have eq := congrArg Equation.left (List.mem_singleton.mp second)
    change (4:Nat)=5 at eq
    cases eq

theorem genuine_old_return_means_new_raw_cycle_despite_model_entailment :
    (¬AliasCycle returningOld (observed returningOld) 4) ∧
      AliasCycle (extendedRows returningOld returningProposed)
        (observed (extendedRows returningOld returningProposed)) 4 ∧
    (∀ w, checksNamedProjectionCut returningOld 4 returningProposed.right w = false) := by
  refine ⟨old_4_has_no_observed_shape,?_,?_⟩
  · apply (physical_new_row_root_cycle_exactly_old_or_old_return_from_child
      (s := returningOld) (site := 4) (term := returningProposed.right) (form := .record [(30,5)]) rfl).mpr
    refine .inr ⟨5,by simp [Shape.children],4,GeneralDeclarativeLowerKnown321.alias_refl _,.next ?_ (.refl _)⟩
    exact ⟨.record [(30,4)],GeneralDeclarativeGraphRows321.literal_head
        (exp := returnByName.right)
        (show returnByName ∈ returningOld.equations from by simp [returningOld]) rfl,
      by simp [Shape.children]⟩
  · intro w
    cases yes : checksNamedProjectionCut returningOld 4 returningProposed.right w with
    | false => rfl
    | true =>
      exfalso
      have contradictionWitness := (original_projection_cut_has_finite_wire_exactly_when_safe
        (s := returningOld) (site := 4) (term := returningProposed.right) (form := .record [(30,5)]) rfl).mp ⟨w,yes⟩
      exact contradictionWitness.2 5 (by simp [Shape.children]) 4
        (GeneralDeclarativeLowerKnown321.alias_refl _) (.next
        ⟨.record [(30,4)],GeneralDeclarativeGraphRows321.literal_head
          (exp := returnByName.right)
          (show returnByName ∈ returningOld.equations from by simp [returningOld]) rfl,
         by simp [Shape.children]⟩ (.refl _))

def equalInOld : EqWire :=
  .compose (.old (.currentRow 0))
    (.record 30 (.reverse (.old (.currentRow 1))) (.old (.refl empty)))

theorem same_ordinary_models_and_explicit_old_derivation_still_do_not_permit_projection :
    (∀ m, Models returningOld m ↔ Models (extendedRows returningOld returningProposed) m) ∧
    checkEq returningOld (.variable 4) returningProposed.right equalInOld = true ∧
    ∀ w, checkProjection returningOld (extendedRows returningOld returningProposed) 4 w = false := by
  refine ⟨fun m => ⟨?_,?_⟩,by decide +kernel,?_⟩
  · intro fits
    refine ⟨fits.1,?_⟩
    intro r present
    change r ∈ returningOld.equations ++ [returningProposed] at present
    rcases List.mem_append.mp present with old | extra
    · exact fits.2 r old
    · obtain rfl := List.mem_singleton.mp extra
      exact equivalent_named_projection_can_be_entailed_before_any_graph_insertion m fits
  · intro h
    exact ⟨h.1,fun r seen => h.2 r (List.mem_append_left _ seen)⟩
  · intro w
    cases result : checkProjection returningOld (extendedRows returningOld returningProposed) 4 w with
    | false => rfl
    | true =>
      have eqIndex : (extendedRows returningOld returningProposed).equations[returningOld.equations.length]? =
          some returningProposed := rfl
      have wanted := genuine_old_return_means_new_raw_cycle_despite_model_entailment.2.2 w.cut
      simp [checkProjection,eqIndex,wanted] at result

#print axioms equivalent_named_projection_can_be_entailed_before_any_graph_insertion
#print axioms original_entailment_is_not_vacuous
#print axioms genuine_old_return_means_new_raw_cycle_despite_model_entailment
#print axioms same_ordinary_models_and_explicit_old_derivation_still_do_not_permit_projection

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464.ReturnAudit
