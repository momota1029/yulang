import Std

/-!
# A finite tree programming language and its halting diagonal

This module formalizes computation separately from role semantics. Programs
and input trees are finite syntax; evaluation is an independent finite
big-step derivation. The diagonal theorem is generic in a program encoding.
It is not itself an undecidability theorem about Yulang role resolution: a
later compiler must connect this evaluation relation to actual checked role
declarations and dictionaries.
-/

namespace Yulang.CommonRoleComputation

inductive Tree where
  | leaf
  | node : Tree → Tree → Tree
  deriving DecidableEq, Repr

inductive Code where
  | const : Tree → Code
  | id
  | left
  | right
  | pair : Code → Code → Code
  | seq : Code → Code → Code
  | cond : Code → Code → Code → Code
  | whileE : Code → Code → Code
  deriving DecidableEq, Repr

/-- Leaf is false and every node is true. -/
def IsNode : Tree → Prop
  | .leaf => False
  | .node _ _ => True

/-- Both pair branches and both conditional branches receive the original
input. The sequence and loop body pass their computed output onward. -/
inductive Eval : Code → Tree → Tree → Prop where
  | const (value input : Tree) : Eval (.const value) input value
  | id (input : Tree) : Eval .id input input
  | leftLeaf : Eval .left .leaf .leaf
  | leftNode (first last : Tree) : Eval .left (.node first last) first
  | rightLeaf : Eval .right .leaf .leaf
  | rightNode (first last : Tree) : Eval .right (.node first last) last
  | pair {first last : Code} {input a b : Tree}
      (left : Eval first input a) (right : Eval last input b) :
      Eval (.pair first last) input (.node a b)
  | seq {first last : Code} {input middle output : Tree}
      (before : Eval first input middle) (after : Eval last middle output) :
      Eval (.seq first last) input output
  | condLeaf {test yes no : Code} {input output : Tree}
      (tested : Eval test input .leaf) (branch : Eval yes input output) :
      Eval (.cond test yes no) input output
  | condNode {test yes no : Code} {input a b output : Tree}
      (tested : Eval test input (.node a b)) (branch : Eval no input output) :
      Eval (.cond test yes no) input output
  | whileLeaf {test body : Code} {input : Tree}
      (tested : Eval test input .leaf) : Eval (.whileE test body) input input
  | whileNode {test body : Code} {input a b middle output : Tree}
      (tested : Eval test input (.node a b)) (step : Eval body input middle)
      (rest : Eval (.whileE test body) middle output) :
      Eval (.whileE test body) input output

def Halts (code : Code) (input : Tree) : Prop := ∃ output, Eval code input output

theorem Eval.deterministic {code : Code} {input output : Tree}
    (evaluation : Eval code input output) :
    ∀ {other}, Eval code input other → output = other := by
  induction evaluation with
  | const => intro other second; cases second; rfl
  | id => intro other second; cases second; rfl
  | leftLeaf => intro other second; cases second; rfl
  | leftNode => intro other second; cases second; rfl
  | rightLeaf => intro other second; cases second; rfl
  | rightNode => intro other second; cases second; rfl
  | pair first last ihFirst ihLast =>
      intro other second
      cases second with
      | pair first' last' =>
          have leftEqual := ihFirst first'
          have rightEqual := ihLast last'
          cases leftEqual
          cases rightEqual
          rfl
  | seq before after ihBefore ihAfter =>
      intro other second
      cases second with
      | seq before' after' =>
          have middle := ihBefore before'
          cases middle
          exact ihAfter after'
  | condLeaf tested branch ihTest ihBranch =>
      intro other second
      cases second with
      | condLeaf tested' branch' => exact ihBranch branch'
      | condNode tested' _ => cases ihTest tested'
  | condNode tested branch ihTest ihBranch =>
      intro other second
      cases second with
      | condLeaf tested' _ => cases ihTest tested'
      | condNode _ branch' => exact ihBranch branch'
  | whileLeaf tested ihTest =>
      intro other second
      cases second with
      | whileLeaf => rfl
      | whileNode tested' _ _ => cases ihTest tested'
  | whileNode tested step rest ihTest ihStep ihRest =>
      intro other second
      cases second with
      | whileLeaf tested' => cases ihTest tested'
      | whileNode _ step' rest' =>
          have middle := ihStep step'
          cases middle
          exact ihRest rest'

def diverge : Code := .whileE (.const (.node .leaf .leaf)) .id

/-- The always-true loop has no finite evaluation at any input or output. -/
theorem diverge_no_eval (input output : Tree) : ¬ Eval diverge input output := by
  intro evaluation
  generalize same : diverge = code at evaluation
  induction evaluation with
  | whileLeaf tested =>
      cases same
      cases tested
  | whileNode tested step rest _ _ ihRest =>
      cases same
      exact ihRest rfl
  | _ => cases same

theorem diverge_not_halts (input : Tree) : ¬ Halts diverge input := by
  rintro ⟨output, evaluation⟩
  exact diverge_no_eval input output evaluation

/-- Duplicate the input, consult the alleged classifier, halt on false and
diverge on true. The classifier sees the pair (input,input). -/
def diagonal (classifier : Code) : Code :=
  .cond (.seq (.pair .id .id) classifier) (.const .leaf) diverge

/-- A total classifier must produce an actual finite evaluation on every
encoded program/input pair. Its truth value describes the independent Eval
judgment, not a Boolean chosen by classical excluded middle. -/
def HaltingClassifier (encode : Code → Tree) (classifier : Code) : Prop :=
  ∀ code input, ∃ result,
    Eval classifier (.node (encode code) input) result ∧
      (IsNode result ↔ Halts code input)

/-- No program in this finite language is a total halting classifier, for
any program encoding whatsoever. No injectivity or internal interpreter is
needed: the diagonal program is supplied its own encoded syntax as input. -/
theorem no_halting_classifier (encode : Code → Tree) :
    ¬ ∃ classifier : Code, HaltingClassifier encode classifier := by
  rintro ⟨classifier, classifies⟩
  let program := diagonal classifier
  let input := encode program
  obtain ⟨result, evaluated, correct⟩ := classifies program input
  have tested : Eval (.seq (.pair .id .id) classifier) input result :=
    .seq (.pair (.id input) (.id input)) evaluated
  cases result with
  | leaf =>
      have halts : Halts program input := ⟨.leaf, .condLeaf tested (.const .leaf input)⟩
      exact correct.mpr halts
  | node a b =>
      obtain ⟨output, evaluation⟩ := correct.mp True.intro
      change Eval (.cond (.seq (.pair .id .id) classifier) (.const .leaf) diverge)
        input output at evaluation
      cases evaluation with
      | condLeaf other _ => cases tested.deterministic other
      | condNode _ branch => exact diverge_no_eval input output branch

end Yulang.CommonRoleComputation
