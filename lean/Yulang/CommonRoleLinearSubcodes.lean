import Yulang.CommonRoleLinearInterpreter

/-! Finite source-code closure and injective concrete interpreter encodings. -/

namespace Yulang.CommonRoleLinearSubcodes

open CommonRoleComputation (Tree Code)

def subcodes : Code → List Code
  | code@(.const _) | code@(.id) | code@(.left) | code@(.right) => [code]
  | code@(.pair first last) | code@(.seq first last) => code :: (subcodes first ++ subcodes last)
  | code@(.cond test yes no) => code :: (subcodes test ++ (subcodes yes ++ subcodes no))
  | code@(.whileE test body) => code :: (subcodes test ++ subcodes body)

theorem self_mem_subcodes (code : Code) : code ∈ subcodes code := by
  cases code <;> simp [subcodes]

theorem pair_first_subcodes {code first last : Code} (member : code ∈ subcodes first) :
    code ∈ subcodes (.pair first last) := by simp [subcodes, member]

theorem pair_last_subcodes {code first last : Code} (member : code ∈ subcodes last) :
    code ∈ subcodes (.pair first last) := by simp [subcodes, member]

theorem seq_first_subcodes {code first last : Code} (member : code ∈ subcodes first) :
    code ∈ subcodes (.seq first last) := by simp [subcodes, member]

theorem seq_last_subcodes {code first last : Code} (member : code ∈ subcodes last) :
    code ∈ subcodes (.seq first last) := by simp [subcodes, member]

theorem cond_test_subcodes {code test yes no : Code} (member : code ∈ subcodes test) :
    code ∈ subcodes (.cond test yes no) := by simp [subcodes, member]

theorem cond_yes_subcodes {code test yes no : Code} (member : code ∈ subcodes yes) :
    code ∈ subcodes (.cond test yes no) := by simp [subcodes, member]

theorem cond_no_subcodes {code test yes no : Code} (member : code ∈ subcodes no) :
    code ∈ subcodes (.cond test yes no) := by simp [subcodes, member]

theorem while_test_subcodes {code test body : Code} (member : code ∈ subcodes test) :
    code ∈ subcodes (.whileE test body) := by simp [subcodes, member]

theorem while_body_subcodes {code test body : Code} (member : code ∈ subcodes body) :
    code ∈ subcodes (.whileE test body) := by simp [subcodes, member]

theorem pair_first_mem (first last : Code) : first ∈ subcodes (.pair first last) :=
  pair_first_subcodes (self_mem_subcodes _)

theorem pair_last_mem (first last : Code) : last ∈ subcodes (.pair first last) :=
  pair_last_subcodes (self_mem_subcodes _)

theorem seq_first_mem (first last : Code) : first ∈ subcodes (.seq first last) :=
  seq_first_subcodes (self_mem_subcodes _)

theorem seq_last_mem (first last : Code) : last ∈ subcodes (.seq first last) :=
  seq_last_subcodes (self_mem_subcodes _)

theorem cond_test_mem (test yes no : Code) : test ∈ subcodes (.cond test yes no) :=
  cond_test_subcodes (self_mem_subcodes _)

theorem cond_yes_mem (test yes no : Code) : yes ∈ subcodes (.cond test yes no) :=
  cond_yes_subcodes (self_mem_subcodes _)

theorem cond_no_mem (test yes no : Code) : no ∈ subcodes (.cond test yes no) :=
  cond_no_subcodes (self_mem_subcodes _)

theorem while_test_mem (test body : Code) : test ∈ subcodes (.whileE test body) :=
  while_test_subcodes (self_mem_subcodes _)

theorem while_body_mem (test body : Code) : body ∈ subcodes (.whileE test body) :=
  while_body_subcodes (self_mem_subcodes _)

theorem subcodes_trans {first middle last : Code}
    (before : first ∈ subcodes middle) (after : middle ∈ subcodes last) :
    first ∈ subcodes last := by
  induction last generalizing middle with
  | const | id | left | right =>
      simp only [subcodes, List.mem_singleton] at after
      subst middle
      exact before
  | pair a b ihA ihB =>
      simp only [subcodes, List.mem_cons, List.mem_append] at after
      rcases after with same | inA | inB
      · subst middle; exact before
      · exact pair_first_subcodes (ihA before inA)
      · exact pair_last_subcodes (ihB before inB)
  | seq a b ihA ihB =>
      simp only [subcodes, List.mem_cons, List.mem_append] at after
      rcases after with same | inA | inB
      · subst middle; exact before
      · exact seq_first_subcodes (ihA before inA)
      · exact seq_last_subcodes (ihB before inB)
  | cond test yes no ihTest ihYes ihNo =>
      simp only [subcodes, List.mem_cons, List.mem_append] at after
      rcases after with same | inTest | inYes | inNo
      · subst middle; exact before
      · exact cond_test_subcodes (ihTest before inTest)
      · exact cond_yes_subcodes (ihYes before inYes)
      · exact cond_no_subcodes (ihNo before inNo)
  | whileE test body ihTest ihBody =>
      simp only [subcodes, List.mem_cons, List.mem_append] at after
      rcases after with same | inTest | inBody
      · subst middle; exact before
      · exact while_test_subcodes (ihTest before inTest)
      · exact while_body_subcodes (ihBody before inBody)

theorem tree_encode_injective {first last : Tree} (same : first.encode = last.encode) :
    first = last := by
  induction first generalizing last with
  | leaf => cases last <;> simp_all [Tree.encode]
  | node a b ihFirst ihLast =>
      cases last with
      | leaf => cases same
      | node c d =>
          have parts := CommonRoleLinearClock.Ground.pair.inj same
          have leftEqual := ihFirst parts.1
          have rightEqual := ihLast parts.2
          cases leftEqual
          cases rightEqual
          rfl

theorem code_encode_injective {first last : Code} (same : first.encode = last.encode) :
    first = last := by
  induction first generalizing last with
  | const value =>
      cases last <;> simp [Code.encode] at same
      exact congrArg Code.const (tree_encode_injective same)
  | id | left | right => cases last <;> simp_all [Code.encode]
  | pair a b ihFirst ihLast =>
      cases last <;> simp [Code.encode] at same
      have leftEqual := ihFirst same.1
      have rightEqual := ihLast same.2
      cases leftEqual
      cases rightEqual
      rfl
  | seq a b ihFirst ihLast =>
      cases last <;> simp [Code.encode] at same
      have leftEqual := ihFirst same.1
      have rightEqual := ihLast same.2
      cases leftEqual
      cases rightEqual
      rfl
  | cond test yes no ihTest ihYes ihNo =>
      cases last <;> simp [Code.encode] at same
      have testEqual := ihTest same.1
      have yesEqual := ihYes same.2.1
      have noEqual := ihNo same.2.2
      cases testEqual
      cases yesEqual
      cases noEqual
      rfl
  | whileE test body ihTest ihBody =>
      cases last <;> simp [Code.encode] at same
      have testEqual := ihTest same.1
      have bodyEqual := ihBody same.2
      cases testEqual
      cases bodyEqual
      rfl

end Yulang.CommonRoleLinearSubcodes
