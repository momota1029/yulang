import Yulang.CommonRoleLinearProgram

/-! Exact finite halting of the compiled linear root machine. -/

namespace Yulang.CommonRoleLinearExecution

open CommonRoleComputation (Tree Code Eval Halts)
open CommonRoleLinearClock (Ground Pattern Rule Configuration Step)
open CommonRoleLinearInterpreter (Kont Resume CopyKont State next)
open CommonRoleLinearInterpreterRules
open CommonRoleLinearSubcodes
open CommonRoleLinearProgram

inductive RawHalts (program : Code) : Configuration → Prop where
  | done {configuration : Configuration} (finished : configuration.role = 0) : RawHalts program configuration
  | step {source target : Configuration} (transition : Step (rules program) source target)
      (rest : RawHalts program target) : RawHalts program source

theorem run_step {program code : Code} (member : code ∈ subcodes program) (input : Tree) (k : Kont) :
    Step (rules program) (State.run code input k).encode (next (.run code input k)).encode := by
  obtain ⟨rule, selected, transition⟩ := entry_step code input k
  exact ⟨rule, entry_member member selected, transition⟩

theorem other_step (program : Code) (state : State)
    (notRun : ∀ code input k, state ≠ .run code input k)
    (notHalted : ∀ input, state ≠ .halted input) :
    Step (rules program) state.encode (next state).encode := by
  obtain ⟨rule, member, transition⟩ := generic_step state notRun notHalted
  exact ⟨rule, generic_member program member, transition⟩

theorem ret_step (program : Code) (input : Tree) (k : Kont) :
    Step (rules program) (State.ret input k).encode (next (.ret input k)).encode :=
  other_step program (.ret input k) (by intro _ _ _ impossible; cases impossible)
    (by intro _ impossible; cases impossible)

theorem copy_step (program : Code) (input : Tree) (k : CopyKont) :
    Step (rules program) (State.copy input k).encode (next (.copy input k)).encode :=
  other_step program (.copy input k) (by intro _ _ _ impossible; cases impossible)
    (by intro _ impossible; cases impossible)

theorem copied_step (program : Code) (input : Tree) (k : CopyKont) :
    Step (rules program) (State.copied input k).encode (next (.copied input k)).encode :=
  other_step program (.copied input k) (by intro _ _ _ impossible; cases impossible)
    (by intro _ impossible; cases impossible)

theorem run_code_present {program code : Code} {input : Tree} {k : Kont} {target : Configuration}
    (transition : Step (rules program) (State.run code input k).encode target) : code ∈ subcodes program := by
  obtain ⟨rule, member, σ, sourceRole, _, head, _⟩ := transition
  rcases List.mem_append.mp member with generic | entries
  · exact False.elim ((generic_source generic).2 sourceRole.symm)
  · obtain ⟨other, present, selected⟩ := List.mem_flatMap.mp entries
    obtain ⟨rest, control⟩ := entry_control other selected σ
    have same : other.encode = code.encode := (Ground.pair.inj (control.symm.trans head)).1
    have sameCode := code_encode_injective same
    subst other
    exact present

/-- Every actual rule from an encoded valid state reflects the unique typed
next state. No arbitrary decoder and no assumption on the returned state is used. -/
theorem step_reflect (program : Code) (state : State) {target : Configuration}
    (transition : Step (rules program) state.encode target) : target = (next state).encode := by
  cases state with
  | run code input k =>
      exact step_deterministic program transition (run_step (run_code_present transition) input k)
  | ret input k => exact step_deterministic program transition (ret_step program input k)
  | copy input k => exact step_deterministic program transition (copy_step program input k)
  | copied input k => exact step_deterministic program transition (copied_step program input k)
  | halted input =>
      obtain ⟨rule, member, _, sourceRole, _, _, _⟩ := transition
      exact False.elim (no_terminal_source program member sourceRole.symm)

theorem raw_halting_outcome {program : Code} {configuration : Configuration}
    (halting : RawHalts program configuration) :
    ∀ state : State, configuration = state.encode → ∃ output, state.Outcome output := by
  induction halting with
  | @done configuration finished =>
      intro state same
      subst configuration
      cases state <;> simp_all [State.encode, State.Outcome]
  | @step source target transition rest ih =>
      intro state same
      subst source
      obtain ⟨output, outcome⟩ := ih (next state) (step_reflect program state transition)
      exact ⟨output, CommonRoleLinearInterpreter.predecessor_outcome state output outcome⟩

theorem copy_halting (program : Code) (input : Tree) (k : CopyKont)
    (rest : RawHalts program (State.copied input k).encode) :
    RawHalts program (State.copy input k).encode := by
  induction input generalizing k with
  | leaf => exact .step (copy_step program .leaf k) rest
  | node first last ihFirst ihLast =>
      exact .step (copy_step program (.node first last) k)
        (ihFirst (.left last k) (.step (copied_step program first (.left last k))
          (ihLast (.right first k) (.step (copied_step program last (.right first k)) rest))))

theorem evaluation_halting {code : Code} {input output : Tree}
    (evaluation : Eval code input output) (program : Code) (present : code ∈ subcodes program)
    (k : Kont) (rest : RawHalts program (State.ret output k).encode) :
    RawHalts program (State.run code input k).encode := by
  induction evaluation generalizing k with
  | const | id | leftLeaf | leftNode | rightLeaf | rightNode =>
      exact .step (run_step present _ k) rest
  | @pair first last input a b firstEval lastEval ihFirst ihLast =>
      exact .step (run_step present input k)
        (copy_halting program input (.done (.pair first last k))
          (.step (copied_step program input (.done (.pair first last k)))
            (ihFirst (subcodes_trans (pair_first_mem first last) present) (.pairLeft last input k)
              (.step (ret_step program a (.pairLeft last input k))
                (ihLast (subcodes_trans (pair_last_mem first last) present) (.pairRight a k)
                  (.step (ret_step program b (.pairRight a k)) rest))))))
  | @seq first last input middle output before after ihFirst ihLast =>
      exact .step (run_step present input k)
        (ihFirst (subcodes_trans (seq_first_mem first last) present) (.seq last k)
          (.step (ret_step program middle (.seq last k))
            (ihLast (subcodes_trans (seq_last_mem first last) present) k rest)))
  | @condLeaf test yes no input output tested branch ihTest ihBranch =>
      exact .step (run_step present input k)
        (copy_halting program input (.done (.cond test yes no k))
          (.step (copied_step program input (.done (.cond test yes no k)))
            (ihTest (subcodes_trans (cond_test_mem test yes no) present) (.cond yes no input k)
              (.step (ret_step program .leaf (.cond yes no input k))
                (ihBranch (subcodes_trans (cond_yes_mem test yes no) present) k rest)))))
  | @condNode test yes no input a b output tested branch ihTest ihBranch =>
      exact .step (run_step present input k)
        (copy_halting program input (.done (.cond test yes no k))
          (.step (copied_step program input (.done (.cond test yes no k)))
            (ihTest (subcodes_trans (cond_test_mem test yes no) present) (.cond yes no input k)
              (.step (ret_step program (.node a b) (.cond yes no input k))
                (ihBranch (subcodes_trans (cond_no_mem test yes no) present) k rest)))))
  | @whileLeaf test body input tested ihTest =>
      exact .step (run_step present input k)
        (copy_halting program input (.done (.loop test body k))
          (.step (copied_step program input (.done (.loop test body k)))
            (ihTest (subcodes_trans (while_test_mem test body) present) (.loop test body input k)
              (.step (ret_step program .leaf (.loop test body input k)) rest))))
  | @whileNode test body input a b middle output tested bodyEval recurse ihTest ihBody ihRest =>
      exact .step (run_step present input k)
        (copy_halting program input (.done (.loop test body k))
          (.step (copied_step program input (.done (.loop test body k)))
            (ihTest (subcodes_trans (while_test_mem test body) present) (.loop test body input k)
              (.step (ret_step program (.node a b) (.loop test body input k))
                (ihBody (subcodes_trans (while_body_mem test body) present) (.seq (.whileE test body) k)
                  (.step (ret_step program middle (.seq (.whileE test body) k))
                    (ihRest present k rest)))))))

/-- Halting of the concrete finite linear root-rewrite program is exactly
finite evaluation of the independent source program. -/
theorem halts_exact (code : Code) (input : Tree) :
    RawHalts code (State.run code input .halt).encode ↔ Halts code input := by
  constructor
  · intro halting
    obtain ⟨output, result, evaluated, _⟩ := raw_halting_outcome halting (.run code input .halt) rfl
    exact ⟨result, evaluated⟩
  · rintro ⟨output, evaluated⟩
    apply evaluation_halting evaluated code (self_mem_subcodes code) .halt
    exact .step (ret_step code output .halt) (.done rfl)

end Yulang.CommonRoleLinearExecution
