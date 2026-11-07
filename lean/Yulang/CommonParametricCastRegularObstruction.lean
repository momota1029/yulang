import Yulang.ParametricCastRules
import Yulang.CommonListNil
import Yulang.PureCasts

/-!
# Accepted non-growing cast endpoints need not form a finite regular universe

The real size/count checker accepts F(G a,b) -> F(a,G b). A one-state nominal
regular type A = G A gives infinitely many demand-inequivalent reachable
endpoints F(A,G^n C), using only one declaration and fixed nominal identities.
The step also has a concrete executable finite-pattern matcher.

This refutes extending finite-tree endpoint enumeration to arbitrary regular
nominal arguments. It does not refute symbolic reachability decidability or
B5's entire cast theorem, and does not claim original source-body validation.
-/

namespace Yulang.CommonParametricCastRegularObstruction

open CommonNominalCarrier
open Roles (Term)

def declaration : ParametricCasts.Rule :=
  ⟨.app 0 [.app 1 [.var 0], .var 1], .app 0 [.var 0, .app 1 [.var 1]]⟩

theorem declaration_accepted : declaration.check = true := by decide +kernel

theorem declaration_valid : declaration.Valid := (ParametricCasts.Rule.check_exact declaration).mp declaration_accepted

def wrap (type : Ty) : Ty := nominal 1 [.inl type]
def two (first last : Ty) : Ty := nominal 0 [.inl first, .inl last]

def interpret (assignment : Nat → Ty) : Term → Option Ty
  | .var index => some (assignment index)
  | .app 0 [first, last] => do return two (← interpret assignment first) (← interpret assignment last)
  | .app 1 [type] => do return wrap (← interpret assignment type)
  | _ => none

def loopState : CommonNominalSyntax.State Row := .block [.nominal 1 [.inl (.inl 0)]] 0
def loop : Ty := CommonNominalSyntax.graph Row loopState

private theorem loop_observe (depth : Nat) : observeTy depth loop = observeTy depth (wrap loop) := by
  cases depth <;> rfl

theorem loop_unfold : Equivalent loop (wrap loop) :=
  ⟨fun depth => by rw [loop_observe]; exact CommonNominalFinite.producerLe_refl _,
    fun depth => by rw [loop_observe]; exact CommonNominalFinite.producerLe_refl _⟩

private theorem equivalent_refl (type : Ty) : Equivalent type type := ⟨subtype_refl _, subtype_refl _⟩
private theorem equivalent_symm {first last : Ty} (same : Equivalent first last) : Equivalent last first :=
  ⟨same.2, same.1⟩
private theorem equivalent_trans {first middle last : Ty}
    (before : Equivalent first middle) (after : Equivalent middle last) : Equivalent first last :=
  ⟨subtype_trans before.1 after.1, subtype_trans after.2 before.2⟩

private theorem wrap_below_iff (first last : Ty) :
    CommonNominalCarrier.Subtype (wrap first) (wrap last) ↔ Equivalent first last := by
  simpa only [wrap, CommonListNil.listType, true_and] using
    CommonListNil.list_invariant_exact ⟨1⟩ ⟨1⟩ first last

private theorem two_congr {first first' last last' : Ty}
    (left : Equivalent first first') (right : Equivalent last last') :
    Equivalent (two first last) (two first' last') := by
  have direction (first first' last last' : Ty)
      (left : Equivalent first first') (right : Equivalent last last') :
      CommonNominalCarrier.Subtype (two first last) (two first' last') := by
    apply (nominal_regular_invariant_exact _ _ _ _).mpr
    refine ⟨rfl, rfl, ?_⟩
    intro index a b before after
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at before after
        subst a; subst b; exact left
    | succ index =>
        cases index with
        | zero =>
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at before after
            subst a; subst b; exact right
        | succ index => simp at before
  exact ⟨direction _ _ _ _ left right,
    direction _ _ _ _ (equivalent_symm left) (equivalent_symm right)⟩

def growing : Nat → Ty
  | 0 => nominal 2 []
  | count + 1 => wrap (growing count)

def chain (count : Nat) : Ty := two loop (growing count)

/-- One executable pattern unfolding; it never enumerates an endpoint universe. -/
def fire : Ty → Option Ty
  | .nominal 0 [.inl first, .inl last] =>
      match CommonNominalSyntax.graph Row first with
      | .nominal 1 [.inl argument] =>
          some (two (CommonNominalSyntax.graph Row argument) (wrap (CommonNominalSyntax.graph Row last)))
      | _ => none
  | _ => none

theorem fire_chain (count : Nat) : fire (chain count) = some (chain (count + 1)) := rfl

def Step (source target : Ty) : Prop :=
  ∃ assignment first last,
    interpret assignment declaration.source = some first ∧
    interpret assignment declaration.target = some last ∧
    Equivalent first source ∧ Equivalent last target

theorem chain_step (count : Nat) : Step (chain count) (chain (count + 1)) := by
  refine ⟨(fun index => if index = 0 then loop else growing count),
    two (wrap loop) (growing count), chain (count + 1), rfl, rfl, ?_, equivalent_refl _⟩
  exact two_congr (equivalent_symm loop_unfold) (equivalent_refl _)

private theorem zero_not_wrap (type : Ty) : ¬ Equivalent (nominal 2 []) (wrap type) := by
  intro same
  have identity := ((nominal_regular_invariant_exact _ _ _ _).mp same.1).1
  contradiction

theorem growing_equivalent_iff (first last : Nat) : Equivalent (growing first) (growing last) ↔ first = last := by
  constructor
  · intro same
    induction first generalizing last with
    | zero =>
        cases last with
        | zero => rfl
        | succ last => exact False.elim (zero_not_wrap _ same)
    | succ first ih =>
        cases last with
        | zero => exact False.elim (zero_not_wrap _ (equivalent_symm same))
        | succ last => exact congrArg Nat.succ (ih last ((wrap_below_iff _ _).mp same.1))
  · rintro rfl
    exact equivalent_refl _

theorem chain_equivalent_iff (first last : Nat) : Equivalent (chain first) (chain last) ↔ first = last := by
  constructor
  · intro same
    have arguments := ((nominal_regular_invariant_exact _ _ _ _).mp same.1).2.2
    exact (growing_equivalent_iff first last).mp
      (arguments 1 (.inl (growing first)) (.inl (growing last)) rfl rfl)
  · rintro rfl
    exact equivalent_refl _

inductive Reach (source : Ty) : Ty → Prop where
  | refl : Reach source source
  | step : Reach source middle → Step middle target → Reach source target

theorem chain_reachable (count : Nat) : Reach (chain 0) (chain count) := by
  induction count with
  | zero => exact .refl
  | succ count ih => exact .step ih (chain_step count)

private noncomputable def candidateLimit (candidate : Ty) : Nat := by
  classical
  exact if found : ∃ index, Equivalent candidate (chain index) then Classical.choose found + 1 else 0

private theorem candidate_bounded (candidate : Ty) (index : Nat) (same : Equivalent candidate (chain index)) :
    index < candidateLimit candidate := by
  classical
  have found : ∃ index, Equivalent candidate (chain index) := ⟨index, same⟩
  have chosen := Classical.choose_spec found
  have identity := (chain_equivalent_iff (Classical.choose found) index).mp
    (equivalent_trans (equivalent_symm chosen) same)
  simp only [candidateLimit, found, ↓reduceDIte]
  omega

private noncomputable def universeLimit : List Ty → Nat
  | [] => 0
  | candidate :: rest => max (candidateLimit candidate) (universeLimit rest)

private theorem limit_member (candidates : List Ty) (candidate : Ty) (present : candidate ∈ candidates) :
    candidateLimit candidate ≤ universeLimit candidates := by
  induction candidates with
  | nil => cases present
  | cons head tail ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih later) (Nat.le_max_right ..)

/-- A finite list cannot cover all reachable endpoints, even after arbitrary
demand-equivalence normalization. One checked non-growing declaration suffices. -/
theorem no_finite_regular_endpoint_universe :
    ¬ ∃ candidates : List Ty, ∀ target, Reach (chain 0) target →
      ∃ candidate ∈ candidates, Equivalent candidate target := by
  rintro ⟨candidates, covers⟩
  obtain ⟨candidate, present, same⟩ := covers _ (chain_reachable (universeLimit candidates))
  have below := candidate_bounded candidate (universeLimit candidates) same
  have above := limit_member candidates candidate present
  omega

end Yulang.CommonParametricCastRegularObstruction
