import Yulang.GeneralDeclarativeWitnessBound349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessEquation349
open GeneralDeclarativeHead320 (State Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralCandidateInspection (Primitive)
open GeneralDeclarativeEqualities322 (Derives Forest)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open GeneralDeclarativeWitnessBound349 (Shared tied alias_sound)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

mutual
inductive Code where
  | currentRow (index : Nat)
  | refl (value : Expr)
  | reverse (before : Code)
  | compose (first last : Code)
  | variableBounds (a b : Nat) (witness : Shared)
  | primitive (kind : Primitive) (args : Args)
  | nominal (id : Nat) (args : Args)
  | record (label : Nat) (payload tail : Code)
  | variant (label : Nat) (payload : Code)
  | join (first last : Code)

inductive Args where
  | nil
  | cons (first : Code) (rest : Args)
end

structure Checked (s : State) where
  left : Expr
  right : Expr
  derivation : Derives s left right

structure CheckedArgs (s : State) where
  left : List Expr
  right : List Expr
  derivation : Forest s left right

mutual
/-- Every constructor uses a rule of ordinary derivability. In
particular an integer is only an index into the fixed current state;
there is no instruction for marking a row as authored or released. -/
def replay (s : State) : Code → Option (Checked s)
  | .currentRow ix =>
    match same : s.equations[ix]? with
    | none => none
    | some e =>
      some ⟨.variable e.left,e.right,.row (List.mem_iff_getElem?.mpr ⟨ix,same⟩)⟩
  | .refl e => some ⟨e,e,.refl e⟩
  | .reverse p => (replay s p).map (fun q => ⟨q.right,q.left,.symm q.derivation⟩)
  | .compose p q => do
    let a ← replay s p
    let b ← replay s q
    if linked : eqExpr a.right b.left = true then
      let middle := (eq_expr _ _).mp linked
      some ⟨a.left,b.right,.trans a.derivation (middle.symm ▸ b.derivation)⟩
    else none
  | .variableBounds a b p =>
    if linked : tied s a b p = true then
      some ⟨.variable a,.variable b,.congruent (.variable (alias_sound linked))⟩
    else none
  | .primitive k inputs => do
    let found ← replayArgs s inputs
    pure ⟨.primitive k found.left,.primitive k found.right,.primitive found.derivation⟩
  | .nominal k inputs => do
    let found ← replayArgs s inputs
    pure ⟨.nominal k found.left,.nominal k found.right,.nominal found.derivation⟩
  | .record k payload tail => do
    let left ← replay s payload
    let right ← replay s tail
    pure ⟨.record k left.left right.left,.record k left.right right.right,.record left.derivation right.derivation⟩
  | .variant k body => (replay s body).map (fun q => ⟨.variant k q.left,.variant k q.right,.variant q.derivation⟩)
  | .join p q => do
    let a ← replay s p
    let b ← replay s q
    pure ⟨.join a.left b.left,.join a.right b.right,.join a.derivation b.derivation⟩
termination_by proof => sizeOf proof

def replayArgs (s : State) : Args → Option (CheckedArgs s)
  | .nil => some ⟨[],[],.nil⟩
  | .cons first last => do
    let a ← replay s first
    let rest ← replayArgs s last
    pure ⟨a.left::rest.left,a.right::rest.right,.cons a.derivation rest.derivation⟩
termination_by proof => sizeOf proof
end

def check (s : State) (a b : Expr) (p : Code) : Bool :=
  ((replay s p).map (fun found => eqExpr found.left a && eqExpr found.right b)).getD false

theorem sound {s : State} {a b : Expr} {p : Code} (yes : check s a b p = true) :
    Derives s a b := by
  unfold check at yes
  cases run : replay s p with
  | none => simp [run] at yes
  | some got =>
    rw [run] at yes
    change (eqExpr got.left a && eqExpr got.right b) = true at yes
    have two := splitAnd yes
    exact (eq_expr ..).mp two.1 ▸ (eq_expr ..).mp two.2 ▸ got.derivation

theorem in_every_model {s : State} {a b : Expr} {p : Code} (checked : check s a b p = true)
    (m : GeneralNominalCommonBridge.Assignment) (fit : GeneralDeclarativeHead320.Models s m) :
    CommonNominalFullCarrier.Equivalent
      (GeneralNominalCenteredHeadMatExpressions.value (GeneralDeclarativeHead320.environment m) .actual a)
      (GeneralNominalCenteredHeadMatExpressions.value (GeneralDeclarativeHead320.environment m) .actual b) :=
  GeneralDeclarativeEqualities322.semantic (sound checked) m fit

end Yulang.GeneralDeclarativeWitnessEquation349
