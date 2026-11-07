import Yulang.CommonRoleComputation
import Yulang.CommonRoleLinearClock

/-!
# A linear copying machine for finite tree programs

The copying zipper below makes duplication explicit. A completed-copy state
stores one mathematical tree, but its concrete representation contains two
equal, physically separate trees. Its rules only move variables; they never
duplicate an RHS variable. Program syntax is fixed in the finite entry rules.
-/

namespace Yulang.CommonRoleLinearInterpreter

open CommonRoleComputation (Tree Code Eval Halts)
open CommonRoleLinearClock (Ground Pattern Rule Configuration)

inductive Kont where
  | halt
  | seq : Code → Kont → Kont
  | pairLeft : Code → Tree → Kont → Kont
  | pairRight : Tree → Kont → Kont
  | cond : Code → Code → Tree → Kont → Kont
  | loop : Code → Code → Tree → Kont → Kont
  deriving DecidableEq, Repr

inductive Resume where
  | pair : Code → Code → Kont → Resume
  | cond : Code → Code → Code → Kont → Resume
  | loop : Code → Code → Kont → Resume
  deriving DecidableEq, Repr

inductive CopyKont where
  | done : Resume → CopyKont
  | left : Tree → CopyKont → CopyKont
  | right : Tree → CopyKont → CopyKont
  deriving DecidableEq, Repr

inductive State where
  | run : Code → Tree → Kont → State
  | ret : Tree → Kont → State
  | copy : Tree → CopyKont → State
  | copied : Tree → CopyKont → State
  | halted : Tree → State
  deriving DecidableEq, Repr

def next : State → State
  | .run (.const value) _ k => .ret value k
  | .run .id input k => .ret input k
  | .run .left .leaf k => .ret .leaf k
  | .run .left (.node first _) k => .ret first k
  | .run .right .leaf k => .ret .leaf k
  | .run .right (.node _ last) k => .ret last k
  | .run (.pair first last) input k => .copy input (.done (.pair first last k))
  | .run (.seq first last) input k => .run first input (.seq last k)
  | .run (.cond test yes no) input k => .copy input (.done (.cond test yes no k))
  | .run (.whileE test body) input k => .copy input (.done (.loop test body k))
  | .ret output .halt => .halted output
  | .ret output (.seq code k) => .run code output k
  | .ret first (.pairLeft last original k) => .run last original (.pairRight first k)
  | .ret last (.pairRight first k) => .ret (.node first last) k
  | .ret .leaf (.cond yes _ original k) => .run yes original k
  | .ret (.node _ _) (.cond _ no original k) => .run no original k
  | .ret .leaf (.loop _ _ original k) => .ret original k
  | .ret (.node _ _) (.loop test body original k) =>
      .run body original (.seq (.whileE test body) k)
  | .copy .leaf k => .copied .leaf k
  | .copy (.node first last) k => .copy first (.left last k)
  | .copied first (.left last k) => .copy last (.right first k)
  | .copied last (.right first k) => .copied (.node first last) k
  | .copied input (.done (.pair first last k)) =>
      .run first input (.pairLeft last input k)
  | .copied input (.done (.cond test yes no k)) =>
      .run test input (.cond yes no input k)
  | .copied input (.done (.loop test body k)) =>
      .run test input (.loop test body input k)
  | .halted output => .halted output

inductive Steps : State → State → Prop where
  | refl (state : State) : Steps state state
  | step {state last : State} : Steps (next state) last → Steps state last

theorem Steps.trans {first middle last : State} (before : Steps first middle)
    (after : Steps middle last) : Steps first last := by
  induction before with
  | refl => exact after
  | step _ ih => exact .step (ih after)

theorem one_step (state : State) : Steps state (next state) := .step (.refl _)

theorem copy_steps (tree : Tree) (k : CopyKont) : Steps (.copy tree k) (.copied tree k) := by
  induction tree generalizing k with
  | leaf => exact .step (.refl _)
  | node first last ihFirst ihLast =>
      exact .step ((ihFirst (.left last k)).trans
        (.step ((ihLast (.right first k)).trans (.step (.refl _)))))

theorem evaluation_steps {code : Code} {input output : Tree}
    (evaluation : Eval code input output) (k : Kont) :
    Steps (.run code input k) (.ret output k) := by
  induction evaluation generalizing k with
  | const | id | leftLeaf | leftNode | rightLeaf | rightNode => exact .step (.refl _)
  | @pair first last input a b firstEval lastEval ihFirst ihLast =>
      exact .step ((copy_steps input (.done (.pair first last k))).trans
        (.step ((ihFirst (.pairLeft last input k)).trans
          (.step ((ihLast (.pairRight a k)).trans (.step (.refl _)))))))
  | @seq first last input middle output before after ihFirst ihLast =>
      exact .step ((ihFirst (.seq last k)).trans (.step (ihLast k)))
  | @condLeaf test yes no input output tested branch ihTest ihBranch =>
      exact .step ((copy_steps input (.done (.cond test yes no k))).trans
        (.step ((ihTest (.cond yes no input k)).trans (.step (ihBranch k)))))
  | @condNode test yes no input a b output tested branch ihTest ihBranch =>
      exact .step ((copy_steps input (.done (.cond test yes no k))).trans
        (.step ((ihTest (.cond yes no input k)).trans (.step (ihBranch k)))))
  | @whileLeaf test body input tested ihTest =>
      exact .step ((copy_steps input (.done (.loop test body k))).trans
        (.step ((ihTest (.loop test body input k)).trans (.step (.refl _)))))
  | @whileNode test body input a b middle output tested bodyEval rest ihTest ihBody ihRest =>
      exact .step ((copy_steps input (.done (.loop test body k))).trans
        (.step ((ihTest (.loop test body input k)).trans
          (.step ((ihBody (.seq (.whileE test body) k)).trans (.step (ihRest k)))))))

def Kont.Outcome : Kont → Tree → Tree → Prop
  | .halt, value, output => value = output
  | .seq code k, value, output => ∃ result, Eval code value result ∧ k.Outcome result output
  | .pairLeft code original k, value, output =>
      ∃ result, Eval code original result ∧ k.Outcome (.node value result) output
  | .pairRight first k, value, output => k.Outcome (.node first value) output
  | .cond yes _ original k, .leaf, output =>
      ∃ result, Eval yes original result ∧ k.Outcome result output
  | .cond _ no original k, .node _ _, output =>
      ∃ result, Eval no original result ∧ k.Outcome result output
  | .loop _ _ original k, .leaf, output => k.Outcome original output
  | .loop test body original k, .node _ _, output =>
      ∃ middle result, Eval body original middle ∧ Eval (.whileE test body) middle result ∧
        k.Outcome result output

def Resume.Outcome : Resume → Tree → Tree → Prop
  | .pair first last k, input, output =>
      ∃ result, Eval (.pair first last) input result ∧ k.Outcome result output
  | .cond test yes no k, input, output =>
      ∃ result, Eval (.cond test yes no) input result ∧ k.Outcome result output
  | .loop test body k, input, output =>
      ∃ result, Eval (.whileE test body) input result ∧ k.Outcome result output

def CopyKont.Outcome : CopyKont → Tree → Tree → Prop
  | .done resume, input, output => resume.Outcome input output
  | .left last k, input, output => k.Outcome (.node input last) output
  | .right first k, input, output => k.Outcome (.node first input) output

def State.Outcome : State → Tree → Prop
  | .run code input k, output => ∃ result, Eval code input result ∧ k.Outcome result output
  | .ret input k, output => k.Outcome input output
  | .copy input k, output => k.Outcome input output
  | .copied input k, output => k.Outcome input output
  | .halted input, output => input = output

theorem predecessor_outcome (state : State) (output : Tree) :
    (next state).Outcome output → state.Outcome output := by
  cases state with
  | run code input k =>
      cases code with
      | const value => intro outcome; exact ⟨value, .const value input, outcome⟩
      | id => intro outcome; exact ⟨input, .id input, outcome⟩
      | left =>
          cases input with
          | leaf => intro outcome; exact ⟨.leaf, .leftLeaf, outcome⟩
          | node first last => intro outcome; exact ⟨first, .leftNode first last, outcome⟩
      | right =>
          cases input with
          | leaf => intro outcome; exact ⟨.leaf, .rightLeaf, outcome⟩
          | node first last => intro outcome; exact ⟨last, .rightNode first last, outcome⟩
      | pair first last => exact id
      | seq first last =>
          rintro ⟨middle, before, result, after, rest⟩
          exact ⟨result, .seq before after, rest⟩
      | cond test yes no => exact id
      | whileE test body => exact id
  | ret input k =>
      cases k with
      | halt => exact id
      | seq code k => exact id
      | pairLeft code original k => exact id
      | pairRight first k => exact id
      | cond yes no original k => cases input <;> exact id
      | loop test body original k =>
          cases input with
          | leaf => exact id
          | node first last =>
              rintro ⟨middle, evaluated, result, loopEval, rest⟩
              exact ⟨middle, result, evaluated, loopEval, rest⟩
  | copy input k => cases input <;> exact id
  | copied input k =>
      cases k with
      | left last k => exact id
      | right first k => exact id
      | done resume =>
          cases resume with
          | pair first last k =>
              rintro ⟨a, firstEval, b, lastEval, rest⟩
              exact ⟨.node a b, .pair firstEval lastEval, rest⟩
          | cond test yes no k =>
              rintro ⟨tested, testEval, rest⟩
              cases tested with
              | leaf =>
                  obtain ⟨result, branch, rest⟩ := rest
                  exact ⟨result, .condLeaf testEval branch, rest⟩
              | node first last =>
                  obtain ⟨result, branch, rest⟩ := rest
                  exact ⟨result, .condNode testEval branch, rest⟩
          | loop test body k =>
              rintro ⟨tested, testEval, rest⟩
              cases tested with
              | leaf => exact ⟨input, .whileLeaf testEval, rest⟩
              | node first last =>
                  obtain ⟨middle, result, step, loopEval, rest⟩ := rest
                  exact ⟨result, .whileNode testEval step loopEval, rest⟩
  | halted input => exact id

theorem outcome_of_steps {first last : State} (steps : Steps first last) (output : Tree)
    (outcome : last.Outcome output) : first.Outcome output := by
  induction steps with
  | refl => exact outcome
  | step _ ih => exact predecessor_outcome _ _ (ih outcome)

theorem machine_exact (code : Code) (input output : Tree) :
    Steps (.run code input .halt) (.halted output) ↔ Eval code input output := by
  constructor
  · intro steps
    obtain ⟨result, evaluated, same⟩ := outcome_of_steps steps output rfl
    cases same
    exact evaluated
  · intro evaluated
    exact (evaluation_steps evaluated .halt).trans (.step (.refl _))

def _root_.Yulang.CommonRoleComputation.Tree.encode : Tree → Ground
  | .leaf => .int
  | .node first last => .pair first.encode last.encode

def _root_.Yulang.CommonRoleComputation.Code.encode : Code → Ground
  | .const value => .variant 0 value.encode
  | .id => .variant 1 .int
  | .left => .variant 2 .int
  | .right => .variant 3 .int
  | .pair first last => .variant 4 (.pair first.encode last.encode)
  | .seq first last => .variant 5 (.pair first.encode last.encode)
  | .cond test yes no => .variant 6 (.pair test.encode (.pair yes.encode no.encode))
  | .whileE test body => .variant 7 (.pair test.encode body.encode)

def Kont.encode : Kont → Ground
  | .halt => .variant 0 .int
  | .seq code k => .variant 1 (.pair code.encode k.encode)
  | .pairLeft code original k => .variant 2 (.pair code.encode (.pair original.encode k.encode))
  | .pairRight first k => .variant 3 (.pair first.encode k.encode)
  | .cond yes no original k => .variant 4 (.pair yes.encode (.pair no.encode (.pair original.encode k.encode)))
  | .loop test body original k =>
      .variant 5 (.pair body.encode (.pair (Code.whileE test body).encode (.pair original.encode k.encode)))

def Resume.encode : Resume → Ground
  | .pair first last k => .variant 0 (.pair first.encode (.pair last.encode k.encode))
  | .cond test yes no k => .variant 1 (.pair test.encode (.pair yes.encode (.pair no.encode k.encode)))
  | .loop test body k =>
      .variant 2 (.pair test.encode (.pair body.encode (.pair (Code.whileE test body).encode k.encode)))

def CopyKont.encode : CopyKont → Ground
  | .done resume => .variant 0 resume.encode
  | .left last k => .variant 1 (.pair last.encode k.encode)
  | .right first k => .variant 2 (.pair first.encode (.pair first.encode k.encode))

def State.encode : State → Configuration
  | .run code input k => ⟨1, .pair code.encode (.pair input.encode k.encode)⟩
  | .ret input k => ⟨2, .pair input.encode k.encode⟩
  | .copy input k => ⟨3, .pair input.encode k.encode⟩
  | .copied input k => ⟨4, .pair input.encode (.pair input.encode k.encode)⟩
  | .halted input => ⟨0, input.encode⟩

end Yulang.CommonRoleLinearInterpreter
