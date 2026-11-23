import Yulang.GeneralDeclarativeWitnessSiblingSeed358
import Yulang.GeneralDeclarativeWitnessRecursiveModel358

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 62000
set_option maxHeartbeats 77000000
namespace Yulang.GeneralDeclarativeWitnessSiblingModel358
open GeneralDeclarativeWitnessSiblingSeed358 (Data data)
open GeneralDeclarativeWitnessRecursiveModel358 (eqOK eq_checked atomOK atom_checked)
open GeneralDeclarativeWitnessDeclaredState357 (ModelsCurrent AuthoredNominal)
open GeneralDeclarativeWitnessReifiedViews357 (modelViews models_extend)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open PresenceNormalForm (Atom)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

def original (n : Nat) : Nat := if n = 42 then 41 else n

def model : Assignment := fun n => GeneralDeclarativeWitnessRecursiveModel358.model (original n)

def rhs : Expr → Option Expr
  | .variable x => some (.variable (original x))
  | .variant tag (.variable x) => some (.variant tag (.variable (original x)))
  | .join (.variable l) (.variable r) => some (.join (.variable (original l)) (.variable (original r)))
  | _ => none

theorem rhs_exact {e result} (translated : rhs e = some result) :
    value (GeneralDeclarativeHead320.environment model) .actual e =
      value (GeneralDeclarativeHead320.environment GeneralDeclarativeWitnessRecursiveModel358.model) .actual result := by
  unfold rhs at translated
  split at translated <;> cases translated <;> rfl

def equationOK (eq : Equation) : Bool :=
  ((rhs eq.right).map (fun e => eqOK ⟨original eq.left,e⟩)).getD false

theorem covers_equation {eq : Equation} (verified : equationOK eq = true) : Holds model eq := by
  cases translated : rhs eq.right with
  | none => simp [equationOK,translated] at verified
  | some expression =>
    have held := eq_checked (show eqOK ⟨original eq.left,expression⟩ = true from
      by simpa only [equationOK,translated,Option.map_some,Option.getD_some] using verified)
    change CommonNominalFullCarrier.Equivalent (model eq.left).1
      (value (GeneralDeclarativeHead320.environment model) .actual eq.right)
    rw [rhs_exact translated]
    exact held

def atomTrace : Atom Nat → Option (Atom Nat)
  | .tyLe (.var a) (.var b) => some (.tyLe (.var (original a)) (.var (original b)))
  | _ => none

theorem atomTrace_exact {a b : Atom Nat} (found : atomTrace a = some b) :
    b.Holds CommonNominalFullCarrier.model GeneralDeclarativeWitnessRecursiveModel358.model →
    a.Holds CommonNominalFullCarrier.model model := by
  cases a with
  | rowLe l r => cases found
  | tyLe l r =>
    cases l <;> cases r <;> try cases found
    exact id

def atomTest (a : Atom Nat) : Bool := ((atomTrace a).map atomOK).getD false

theorem covers_atom {a : Atom Nat} (verified : atomTest a = true) :
    a.Holds CommonNominalFullCarrier.model model := by
  cases trace : atomTrace a with
  | none => simp [atomTest,trace] at verified
  | some originalAtom =>
    exact atomTrace_exact trace (atom_checked (by simpa [atomTest,trace] using verified))

def test (d : Data) : Bool :=
  (d.current.ordinary.normal.ordinary.all atomTest &&
    d.current.ordinary.normal.intervals.isEmpty &&
    d.current.ordinary.equations.all equationOK) &&
  decide (d.current.visible.map AuthoredNominal.place).Nodup

theorem actual_siblings_model_checked : (data.map test).getD false = true := by decide +kernel

theorem same_actual_models {d : Data} (found : data = some d) :
    ModelsCurrent d.current model (modelViews d.current model) := by
  have known := actual_siblings_model_checked
  rw [found] at known
  obtain ⟨all,unique⟩ := splitAnd (show test d = true from known)
  obtain ⟨facts,rows⟩ := splitAnd all
  obtain ⟨atoms,closed⟩ := splitAnd facts
  apply models_extend (of_decide_eq_true unique)
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro a actual
    exact covers_atom (List.all_eq_true.mp atoms a actual)
  · intro bound actual
    rw [List.isEmpty_iff.mp closed] at actual
    cases actual
  · intro row actual
    exact covers_equation (List.all_eq_true.mp rows row actual)

end Yulang.GeneralDeclarativeWitnessSiblingModel358
