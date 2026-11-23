import Yulang.GeneralDeclarativeWitnessRecursiveSeed358
import Yulang.GeneralDeclarativeWitnessReifiedViews357

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 55000
set_option maxHeartbeats 62000000
namespace Yulang.GeneralDeclarativeWitnessRecursiveModel358
open GeneralDeclarativeWitnessRecursiveSeed358 (Data data)
open GeneralDeclarativeWitnessDeclaredState357 (ModelsCurrent AuthoredNominal)
open GeneralDeclarativeWitnessReifiedViews357 (models_extend modelViews)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm)
open GeneralNominalCommonBridge (Assignment variant_merge)
open CommonNominalFullCarrier (Ty Equivalent Subtype variant)
open PresenceNormalForm (Atom)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

inductive Kind where
  | int | bool | merged | taggedInt | taggedBool | taggedMerged
  deriving DecidableEq

def cat (n : Nat) : Kind :=
  if n = 1 then .int else if n = 2 then .bool else
  if n = 7 then .taggedInt else if n = 8 then .taggedBool else
  if n = 10 ∨ n = 41 ∨ (60 ≤ n ∧ n ≤ 64) then .taggedMerged else .merged

def whole : Ty := .union (.base .int) (.base .bool)
def denotation : Kind → Ty
  | .int => .base .int
  | .bool => .base .bool
  | .merged => whole
  | .taggedInt => variant 7 (.base .int)
  | .taggedBool => variant 7 (.base .bool)
  | .taggedMerged => variant 7 whole

def model : Assignment := fun n => (denotation (cat n),Common.rowEmpty)

def variantKind : Kind → Option Kind
  | .int => some .taggedInt
  | .bool => some .taggedBool
  | .merged => some .taggedMerged
  | _ => none

theorem variant_exact {srcKind to : Kind} (written : variantKind srcKind = some to) :
    denotation to = variant 7 (denotation srcKind) := by
  cases srcKind <;> cases written <;> rfl

def eqOK (e : Equation) : Bool :=
  match e.right with
  | .variable n => decide (cat e.left = cat n)
  | .variant 7 (.variable n) => decide (variantKind (cat n) = some (cat e.left))
  | .join (.variable 1) (.variable 2) => decide (cat e.left = .merged)
  | .join (.variable 7) (.variable 8) => decide (cat e.left = .taggedMerged)
  | _ => false

theorem eq_checked {e : Equation} (good : eqOK e = true) : Holds model e := by
  unfold eqOK at good
  split at good
  · rename_i n right
    have same : cat e.left = cat n := of_decide_eq_true good
    change Equivalent (denotation (cat e.left)) _
    rw [right]
    change Equivalent (denotation (cat e.left)) (denotation (cat n))
    rw [same]
    exact eqv_refl _
  · rename_i n right
    have same := variant_exact (of_decide_eq_true good : variantKind (cat n) = some (cat e.left))
    change Equivalent (denotation (cat e.left)) _
    rw [right,same]
    exact eqv_refl _
  · rename_i right
    have same : cat e.left = .merged := of_decide_eq_true good
    change Equivalent (denotation (cat e.left)) _
    rw [right,same]
    exact eqv_refl _
  · rename_i right
    have same : cat e.left = .taggedMerged := of_decide_eq_true good
    change Equivalent (denotation (cat e.left)) _
    rw [right,same]
    exact eqv_symm (variant_merge 7 (.base .int) (.base .bool))
  · cases good

def atomOK : Atom Nat → Bool
  | .tyLe (.var a) (.var b) => decide (cat a = cat b)
  | _ => false

theorem atom_checked {a : Atom Nat} (good : atomOK a = true) :
    a.Holds CommonNominalFullCarrier.model model := by
  cases a with
  | rowLe a b => cases good
  | tyLe a b =>
    cases a <;> cases b <;> try cases good
    rename_i n p
    have same : cat n = cat p := of_decide_eq_true good
    change Subtype (denotation (cat n)) (denotation (cat p))
    rw [same]
    exact (eqv_refl _).1

def covers (d : Data) : Bool :=
  (d.current.ordinary.normal.ordinary.all atomOK &&
    d.current.ordinary.normal.intervals.isEmpty &&
    d.current.ordinary.equations.all eqOK) &&
  decide (d.current.visible.map AuthoredNominal.place).Nodup

theorem actual_model_checked : (data.map covers).getD false = true := by decide +kernel

theorem fits {d : Data} (found : data = some d) :
    ModelsCurrent d.current model (modelViews d.current model) := by
  have yes := actual_model_checked
  rw [found] at yes
  have covered : covers d = true := yes
  obtain ⟨truth,views⟩ := splitAnd covered
  obtain ⟨normal,rows⟩ := splitAnd truth
  obtain ⟨atoms,noIntervals⟩ := splitAnd normal
  apply models_extend (of_decide_eq_true views)
  refine ⟨⟨?_ ,?_⟩,?_⟩
  · intro a present
    exact atom_checked (List.all_eq_true.mp atoms _ present)
  · intro e present
    rw [List.isEmpty_iff.mp noIntervals] at present
    cases present
  · intro row present
    exact eq_checked (List.all_eq_true.mp rows _ present)

end Yulang.GeneralDeclarativeWitnessRecursiveModel358
