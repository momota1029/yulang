import Yulang.CommonRoleComputation

/-!
# Finite deterministic Turing machines compiled to the tree language

The tape alphabet is Bool, with false as blank; tapes have unbounded finite
left and right lists. A missing transition halts. A finite transition table
uses its first matching entry, making the machine deterministic even if a
table contains repeated keys. The compiler below uses only the finite Code
constructors, never an external evaluator or semantic oracle.
-/

namespace Yulang.CommonRoleTuringBridge

open CommonRoleComputation (Tree Code Eval)

def truth : Tree := .node .leaf .leaf

def left : Tree → Tree
  | .leaf => .leaf
  | .node first _ => first

def right : Tree → Tree
  | .leaf => .leaf
  | .node _ last => last

theorem eval_left (input : Tree) : Eval .left input (left input) := by
  cases input with
  | leaf => exact .leftLeaf
  | node first last => exact .leftNode first last

theorem eval_right (input : Tree) : Eval .right input (right input) := by
  cases input with
  | leaf => exact .rightLeaf
  | node first last => exact .rightNode first last

/-- False in a path chooses the left component; true chooses the right. -/
def project : List Bool → Code
  | [] => .id
  | false :: path => .seq .left (project path)
  | true :: path => .seq .right (project path)

def projection : List Bool → Tree → Tree
  | [], input => input
  | false :: path, input => projection path (left input)
  | true :: path, input => projection path (right input)

theorem eval_project (path : List Bool) (input : Tree) :
    Eval (project path) input (projection path input) := by
  induction path generalizing input with
  | nil => exact .id input
  | cons direction path ih =>
      cases direction with
      | false => exact .seq (eval_left input) (ih _)
      | true => exact .seq (eval_right input) (ih _)

/-- Equality tests return leaf for equality and a fixed node otherwise. -/
def eqConst : Tree → Code
  | .leaf => .cond .id (.const .leaf) (.const truth)
  | .node first last =>
      .cond .id (.const truth)
        (.cond (.seq .left (eqConst first)) (.seq .right (eqConst last)) (.const truth))

theorem eval_eqConst (target input : Tree) :
    Eval (eqConst target) input (if input = target then .leaf else truth) := by
  induction target generalizing input with
  | leaf =>
      cases input with
      | leaf => exact .condLeaf (.id _) (.const _ _)
      | node first last => exact .condNode (.id _) (.const _ _)
  | node first last ihFirst ihLast =>
      cases input with
      | leaf => exact .condLeaf (.id _) (.const _ _)
      | node a b =>
          apply Eval.condNode (.id _)
          by_cases firstEq : a = first
          · subst a
            have tested := ihFirst first
            simp only [ite_true] at tested
            by_cases lastEq : b = last
            · subst b
              simp only [ite_true]
              have result := ihLast last
              simp only [ite_true] at result
              exact .condLeaf (.seq (eval_left _) tested) (.seq (eval_right _) result)
            · simp only [Tree.node.injEq, true_and, lastEq, ite_false]
              have result := ihLast b
              simp only [lastEq, ite_false] at result
              exact .condLeaf (.seq (eval_left _) tested) (.seq (eval_right _) result)
          · simp only [Tree.node.injEq, firstEq, false_and, ite_false]
            have tested := ihFirst a
            simp only [firstEq, ite_false] at tested
            exact .condNode (.seq (eval_left _) tested) (.const _ _)

def encodeNat : Nat → Tree
  | 0 => .leaf
  | n + 1 => .node .leaf (encodeNat n)

theorem encodeNat_injective {first last : Nat} (same : encodeNat first = encodeNat last) :
    first = last := by
  induction first generalizing last with
  | zero => cases last <;> simp_all [encodeNat]
  | succ first ih =>
      cases last with
      | zero => simp [encodeNat] at same
      | succ last => exact congrArg Nat.succ (ih (Tree.node.inj same).2)

def encodeBool : Bool → Tree
  | false => .leaf
  | true => truth

theorem encodeBool_injective {first last : Bool} (same : encodeBool first = encodeBool last) :
    first = last := by
  cases first <;> cases last <;> simp_all [encodeBool, truth]

def encodeList : List Bool → Tree
  | [] => .leaf
  | first :: rest => .node (encodeBool first) (encodeList rest)

def tapeHead (tape : List Bool) : Bool := tape.headD false
def tapeTail (tape : List Bool) : List Bool := tape.tail

theorem encode_head (tape : List Bool) : left (encodeList tape) = encodeBool (tapeHead tape) := by
  cases tape <;> rfl

theorem encode_tail (tape : List Bool) : right (encodeList tape) = encodeList (tapeTail tape) := by
  cases tape <;> rfl

inductive Move where
  | left | right | stay
  deriving DecidableEq, Repr

structure Config where
  state : Nat
  leftTape : List Bool
  current : Bool
  rightTape : List Bool
  deriving DecidableEq, Repr

structure Transition where
  state : Nat
  read : Bool
  next : Nat
  write : Bool
  move : Move
  deriving DecidableEq, Repr

abbrev Machine := List Transition

def encodeConfig (config : Config) : Tree :=
  .node (encodeNat config.state)
    (.node (encodeList config.leftTape) (.node (encodeBool config.current) (encodeList config.rightTape)))

def update (transition : Transition) (config : Config) : Config :=
  match transition.move with
  | .left => ⟨transition.next, tapeTail config.leftTape, tapeHead config.leftTape,
      transition.write :: config.rightTape⟩
  | .right => ⟨transition.next, transition.write :: config.leftTape,
      tapeHead config.rightTape, tapeTail config.rightTape⟩
  | .stay => ⟨transition.next, config.leftTape, transition.write, config.rightTape⟩

def Matches (transition : Transition) (config : Config) : Prop :=
  config.state = transition.state ∧ config.current = transition.read

instance (transition : Transition) (config : Config) : Decidable (Matches transition config) :=
  inferInstanceAs (Decidable (_ ∧ _))

def lookup : Machine → Config → Option Transition
  | [], _ => none
  | transition :: rest, config =>
      if Matches transition config then some transition else lookup rest config

def step (machine : Machine) (config : Config) : Option Config :=
  (lookup machine config).map (fun transition => update transition config)

/-- Independent finite machine execution terminating at a missing transition. -/
inductive Runs (machine : Machine) : Config → Config → Prop where
  | halt {config : Config} (stopped : step machine config = none) : Runs machine config config
  | step {config next final : Config}
      (transition : step machine config = some next) (rest : Runs machine next final) :
      Runs machine config final

def stateCode : Code := project [false]
def leftTapeCode : Code := project [true, false]
def currentCode : Code := project [true, true, false]
def rightTapeCode : Code := project [true, true, true]

theorem eval_state (config : Config) :
    Eval stateCode (encodeConfig config) (encodeNat config.state) := eval_project _ _

theorem eval_leftTape (config : Config) :
    Eval leftTapeCode (encodeConfig config) (encodeList config.leftTape) := eval_project _ _

theorem eval_current (config : Config) :
    Eval currentCode (encodeConfig config) (encodeBool config.current) := eval_project _ _

theorem eval_rightTape (config : Config) :
    Eval rightTapeCode (encodeConfig config) (encodeList config.rightTape) := eval_project _ _

def frame (state leftTape current rightTape : Code) : Code :=
  .pair state (.pair leftTape (.pair current rightTape))

def updateCode (transition : Transition) : Code :=
  match transition.move with
  | .left => frame (.const (encodeNat transition.next))
      (.seq leftTapeCode .right) (.seq leftTapeCode .left)
      (.pair (.const (encodeBool transition.write)) rightTapeCode)
  | .right => frame (.const (encodeNat transition.next))
      (.pair (.const (encodeBool transition.write)) leftTapeCode)
      (.seq rightTapeCode .left) (.seq rightTapeCode .right)
  | .stay => frame (.const (encodeNat transition.next)) leftTapeCode
      (.const (encodeBool transition.write)) rightTapeCode

theorem eval_updateCode (transition : Transition) (config : Config) :
    Eval (updateCode transition) (encodeConfig config) (encodeConfig (update transition config)) := by
  cases direction : transition.move with
  | left =>
      simp only [updateCode, update, direction, encodeConfig, frame, encodeList]
      refine .pair (.const _ _) (.pair ?_ (.pair ?_ ?_))
      · simpa only [encode_tail, encodeConfig] using
          Eval.seq (eval_leftTape config) (eval_right (encodeList config.leftTape))
      · simpa only [encode_head, encodeConfig] using
          Eval.seq (eval_leftTape config) (eval_left (encodeList config.leftTape))
      · exact .pair (.const _ _) (eval_rightTape config)
  | right =>
      simp only [updateCode, update, direction, encodeConfig, frame, encodeList]
      refine .pair (.const _ _) (.pair ?_ (.pair ?_ ?_))
      · exact .pair (.const _ _) (eval_leftTape config)
      · simpa only [encode_head, encodeConfig] using
          Eval.seq (eval_rightTape config) (eval_left (encodeList config.rightTape))
      · simpa only [encode_tail, encodeConfig] using
          Eval.seq (eval_rightTape config) (eval_right (encodeList config.rightTape))
  | stay =>
      simp only [updateCode, update, direction, encodeConfig, frame]
      exact .pair (.const _ _) (.pair (eval_leftTape config)
        (.pair (.const _ _) (eval_rightTape config)))

def matchCode (transition : Transition) : Code :=
  .cond (.seq stateCode (eqConst (encodeNat transition.state)))
    (.seq currentCode (eqConst (encodeBool transition.read))) (.const truth)

theorem eval_matchCode (transition : Transition) (config : Config) :
    Eval (matchCode transition) (encodeConfig config)
      (if Matches transition config then .leaf else truth) := by
  have stateTest := Eval.seq (eval_state config)
    (eval_eqConst (encodeNat transition.state) (encodeNat config.state))
  have readTest := Eval.seq (eval_current config)
    (eval_eqConst (encodeBool transition.read) (encodeBool config.current))
  by_cases stateEqual : config.state = transition.state
  · simp only [stateEqual, ite_true] at stateTest
    by_cases readEqual : config.current = transition.read
    · simp only [readEqual, ite_true] at readTest
      simp only [Matches, stateEqual, readEqual, and_self, ite_true]
      exact .condLeaf stateTest readTest
    · have encodedDifferent : encodeBool config.current ≠ encodeBool transition.read :=
        fun same => readEqual (encodeBool_injective same)
      simp only [encodedDifferent, ite_false] at readTest
      simp only [Matches, stateEqual, readEqual, and_false, ite_false]
      exact .condLeaf stateTest readTest
  · have encodedDifferent : encodeNat config.state ≠ encodeNat transition.state :=
      fun same => stateEqual (encodeNat_injective same)
    simp only [encodedDifferent, ite_false] at stateTest
    simp only [Matches, stateEqual, false_and, ite_false]
    exact .condNode stateTest (.const _ _)

def runningCode : Machine → Code
  | [] => .const .leaf
  | transition :: rest => .cond (matchCode transition) (.const truth) (runningCode rest)

def stepCode : Machine → Code
  | [] => .id
  | transition :: rest => .cond (matchCode transition) (updateCode transition) (stepCode rest)

theorem eval_runningCode (machine : Machine) (config : Config) :
    Eval (runningCode machine) (encodeConfig config)
      (if (lookup machine config).isSome then truth else .leaf) := by
  induction machine with
  | nil => exact .const _ _
  | cons transition rest ih =>
      have tested := eval_matchCode transition config
      by_cases matched : Matches transition config
      · simp only [matched, ite_true] at tested
        simpa only [runningCode, lookup, matched, ite_true, Option.isSome_some]
          using Eval.condLeaf (no := runningCode rest) tested (.const truth (encodeConfig config))
      · simp only [matched, ite_false] at tested
        simpa only [runningCode, lookup, matched, ite_false] using
          Eval.condNode (yes := .const truth) tested ih

theorem eval_stepCode (machine : Machine) (config : Config) :
    Eval (stepCode machine) (encodeConfig config)
      (encodeConfig ((step machine config).getD config)) := by
  induction machine with
  | nil => exact .id _
  | cons transition rest ih =>
      have tested := eval_matchCode transition config
      by_cases matched : Matches transition config
      · simp only [matched, ite_true] at tested
        simpa only [stepCode, step, lookup, matched, ite_true, Option.map_some, Option.getD_some]
          using Eval.condLeaf (no := stepCode rest) tested (eval_updateCode transition config)
      · simp only [matched, ite_false] at tested
        simpa only [stepCode, step, lookup, matched, ite_false] using
          Eval.condNode (yes := updateCode transition) tested ih

def compile (machine : Machine) : Code := .whileE (runningCode machine) (stepCode machine)

theorem eval_running_stopped (machine : Machine) (config : Config)
    (stopped : step machine config = none) :
    Eval (runningCode machine) (encodeConfig config) .leaf := by
  have tested := eval_runningCode machine config
  cases found : lookup machine config with
  | none => simpa only [found, Option.isSome_none, Bool.false_eq_true, ite_false] using tested
  | some transition => simp [step, found] at stopped

theorem eval_running_transition (machine : Machine) (config next : Config)
    (transition : step machine config = some next) :
    Eval (runningCode machine) (encodeConfig config) truth := by
  have tested := eval_runningCode machine config
  cases found : lookup machine config with
  | none => simp [step, found] at transition
  | some rule => simpa only [found, Option.isSome_some, ite_true] using tested

theorem eval_step_transition (machine : Machine) (config next : Config)
    (transition : step machine config = some next) :
    Eval (stepCode machine) (encodeConfig config) (encodeConfig next) := by
  simpa only [transition, Option.getD_some] using eval_stepCode machine config

theorem compile_of_runs {machine : Machine} {config final : Config}
    (execution : Runs machine config final) :
    Eval (compile machine) (encodeConfig config) (encodeConfig final) := by
  induction execution with
  | halt stopped => exact .whileLeaf (eval_running_stopped _ _ stopped)
  | step transition _ ih =>
      exact .whileNode (eval_running_transition _ _ _ transition)
        (eval_step_transition _ _ _ transition) ih

private theorem machine_of_eval {code : Code} {input output : Tree}
    (evaluation : Eval code input output) :
    ∀ machine config, code = compile machine → input = encodeConfig config →
      ∃ final, Runs machine config final ∧ output = encodeConfig final := by
  induction evaluation with
  | @whileLeaf test body input tested _ =>
      intro machine config codeEqual inputEqual
      simp only [compile, Code.whileE.injEq] at codeEqual
      rcases codeEqual with ⟨rfl, rfl⟩
      subst input
      cases transition : step machine config with
      | none => exact ⟨config, .halt transition, rfl⟩
      | some next =>
          have impossible := (eval_running_transition machine config next transition).deterministic tested
          cases impossible
  | @whileNode test body input a b middle output tested evaluated _ _ _ ihRest =>
      intro machine config codeEqual inputEqual
      simp only [compile, Code.whileE.injEq] at codeEqual
      rcases codeEqual with ⟨rfl, rfl⟩
      subst input
      cases transition : step machine config with
      | none =>
          have impossible := (eval_running_stopped machine config transition).deterministic tested
          cases impossible
      | some next =>
          have middleEqual := (eval_step_transition machine config next transition).deterministic evaluated
          subst middle
          obtain ⟨final, execution, result⟩ := ihRest machine next rfl rfl
          exact ⟨final, .step transition execution, result⟩
  | _ => intro machine config impossible _; cases impossible

/-- Every finite evaluation of the compiled program is an actual finite
machine execution. This does not assume that the machine terminates. -/
theorem runs_of_compile {machine : Machine} {config : Config} {output : Tree}
    (evaluation : Eval (compile machine) (encodeConfig config) output) :
    ∃ final, Runs machine config final ∧ output = encodeConfig final :=
  machine_of_eval evaluation machine config rfl rfl

/-- Exact simulation for every finite machine, every initial tape/state and
every output tree, with no halting or fuel premise. -/
theorem compile_exact (machine : Machine) (config : Config) (output : Tree) :
    Eval (compile machine) (encodeConfig config) output ↔
      ∃ final, Runs machine config final ∧ output = encodeConfig final := by
  constructor
  · exact runs_of_compile
  · rintro ⟨final, execution, rfl⟩
    exact compile_of_runs execution

theorem compile_halts_iff (machine : Machine) (config : Config) :
    CommonRoleComputation.Halts (compile machine) (encodeConfig config) ↔
      ∃ final, Runs machine config final := by
  constructor
  · rintro ⟨output, evaluation⟩
    obtain ⟨final, execution, _⟩ := runs_of_compile evaluation
    exact ⟨final, execution⟩
  · rintro ⟨final, execution⟩
    exact ⟨encodeConfig final, compile_of_runs execution⟩

/-- A binary serialization: reverse preorder, with false for a leaf and true
for a node. The reversal lets the evaluator accumulate bits by cons alone. -/
def serialize : Tree → List Bool
  | .leaf => [false]
  | .node first last => serialize last ++ serialize first ++ [true]

def decodeBits : List Bool → List Tree → Option (List Tree)
  | [], stack => some stack
  | false :: bits, stack => decodeBits bits (.leaf :: stack)
  | true :: bits, first :: last :: stack => decodeBits bits (.node first last :: stack)
  | true :: _, _ => none

theorem decodeBits_append (first last : List Bool) (stack : List Tree) :
    decodeBits (first ++ last) stack =
      (decodeBits first stack).bind (decodeBits last) := by
  induction first generalizing stack with
  | nil => rfl
  | cons bit rest ih =>
      cases bit with
      | false => exact ih _
      | true =>
          cases stack with
          | nil => rfl
          | cons first stack =>
              cases stack with
              | nil => rfl
              | cons last stack => exact ih _

/-- The binary tape encoding has a concrete decoder and loses no tree data. -/
theorem decode_serialize (input : Tree) (stack : List Tree) :
    decodeBits (serialize input) stack = some (input :: stack) := by
  induction input generalizing stack with
  | leaf => rfl
  | node first last ihFirst ihLast =>
      simp only [serialize, decodeBits_append, ihLast, Option.bind_some, ihFirst]
      rfl

theorem serialize_injective {first last : Tree} (same : serialize first = serialize last) :
    first = last := by
  have decoded := congrArg (fun bits => decodeBits bits []) same
  rw [decode_serialize, decode_serialize] at decoded
  exact (List.cons.inj (Option.some.inj decoded)).1

def serializeTasks : List Tree → List Bool
  | [] => []
  | task :: rest => serializeTasks rest ++ serialize task

def encodeStack : List Tree → Tree
  | [] => .leaf
  | task :: rest => .node task (encodeStack rest)

def treeSize : Tree → Nat
  | .leaf => 1
  | .node first last => 1 + treeSize first + treeSize last

def workSize : List Tree → Nat
  | [] => 0
  | task :: rest => treeSize task + workSize rest

def serializeBody : Code :=
  .cond (project [false, false])
    (.pair (project [false, true])
      (.pair (.const (encodeBool false)) (project [true])))
    (.pair
      (.pair (project [false, false, false])
        (.pair (project [false, false, true]) (project [false, true])))
      (.pair (.const (encodeBool true)) (project [true])))

def serializeLoop : Code := .whileE .left serializeBody

theorem eval_serializeBody_leaf (rest : List Tree) (bits : List Bool) :
    Eval serializeBody (.node (encodeStack (.leaf :: rest)) (encodeList bits))
      (.node (encodeStack rest) (encodeList (false :: bits))) :=
  .condLeaf (eval_project _ _)
    (.pair (eval_project _ _) (.pair (.const _ _) (eval_project _ _)))

theorem eval_serializeBody_node (first last : Tree) (rest : List Tree) (bits : List Bool) :
    Eval serializeBody (.node (encodeStack (.node first last :: rest)) (encodeList bits))
      (.node (encodeStack (first :: last :: rest)) (encodeList (true :: bits))) :=
  .condNode (eval_project _ _)
    (.pair (.pair (eval_project _ _) (.pair (eval_project _ _) (eval_project _ _)))
      (.pair (.const _ _) (eval_project _ _)))

/-- The serializer's loop terminates by the number of unvisited tree nodes,
and preserves the entire serialized bit string, not only a halting flag. -/
theorem eval_serializeLoop (tasks : List Tree) (bits : List Bool) :
    Eval serializeLoop (.node (encodeStack tasks) (encodeList bits))
      (.node .leaf (encodeList (serializeTasks tasks ++ bits))) := by
  cases tasks with
  | nil => exact .whileLeaf (eval_left _)
  | cons task rest =>
      cases task with
      | leaf =>
          have tail := eval_serializeLoop rest (false :: bits)
          have result := Eval.whileNode (eval_left (.node (encodeStack (.leaf :: rest)) (encodeList bits)))
            (eval_serializeBody_leaf rest bits) tail
          simpa only [serializeLoop, serializeTasks, serialize, List.append_assoc, List.cons_append,
            List.nil_append] using result
      | node first last =>
          have tail := eval_serializeLoop (first :: last :: rest) (true :: bits)
          have result := Eval.whileNode
            (eval_left (.node (encodeStack (.node first last :: rest)) (encodeList bits)))
            (eval_serializeBody_node first last rest bits) tail
          simpa only [serializeLoop, serializeTasks, serialize, List.append_assoc, List.cons_append,
            List.nil_append] using result
termination_by workSize tasks
decreasing_by all_goals simp [workSize, treeSize] <;> omega

def serializeCode : Code :=
  .seq (.pair (.pair .id (.const .leaf)) (.const .leaf)) (.seq serializeLoop .right)

theorem eval_serializeCode (input : Tree) :
    Eval serializeCode input (encodeList (serialize input)) := by
  have loop := eval_serializeLoop [input] []
  simp only [serializeTasks, List.nil_append, List.append_nil] at loop
  exact .seq (.pair (.pair (.id input) (.const _ _)) (.const _ _))
    (.seq loop (eval_right _))

/-- Standard input convention: state 0, blank current cell, serialized finite
input to its right and blanks beyond either end of the finite tape lists. -/
def initial (input : Tree) : Config := ⟨0, [], false, serialize input⟩

def initialCode : Code :=
  frame (.const (encodeNat 0)) (.const (encodeList [])) (.const (encodeBool false)) serializeCode

theorem eval_initialCode (input : Tree) : Eval initialCode input (encodeConfig (initial input)) :=
  .pair (.const _ _) (.pair (.const _ _) (.pair (.const _ _) (eval_serializeCode input)))

/-- Run a finite tape machine on serialized input and read its final current
bit. The output is exactly leaf/true-node, with no assumed computation oracle. -/
def classifierCode (machine : Machine) : Code := .seq initialCode (.seq (compile machine) currentCode)

theorem classifier_of_runs (machine : Machine) (input : Tree) (final : Config)
    (execution : Runs machine (initial input) final) :
    Eval (classifierCode machine) input (encodeBool final.current) :=
  .seq (eval_initialCode input) (.seq (compile_of_runs execution) (eval_current final))

theorem classifier_exact (machine : Machine) (input output : Tree) :
    Eval (classifierCode machine) input output ↔
      ∃ final, Runs machine (initial input) final ∧ output = encodeBool final.current := by
  constructor
  · intro evaluation
    cases evaluation with
    | seq initialized after =>
        have initialEqual := (eval_initialCode input).deterministic initialized
        cases initialEqual
        cases after with
        | seq execution returned =>
            obtain ⟨final, actual, result⟩ := runs_of_compile execution
            subst result
            exact ⟨final, actual, (eval_current final).deterministic returned |>.symm⟩
  · rintro ⟨final, actual, rfl⟩
    exact classifier_of_runs machine input final actual

/-- A conventional tape-machine halting classifier for the finite Code
language, using the explicit binary input convention above. -/
def TuringHaltingClassifier (encode : Code → Tree) (machine : Machine) : Prop :=
  ∀ code input, ∃ final,
    Runs machine (initial (.node (encode code) input)) final ∧
      (final.current = true ↔ CommonRoleComputation.Halts code input)

theorem no_turing_halting_classifier (encode : Code → Tree) :
    ¬ ∃ machine : Machine, TuringHaltingClassifier encode machine := by
  rintro ⟨machine, classifies⟩
  apply CommonRoleComputation.no_halting_classifier encode
  refine ⟨classifierCode machine, ?_⟩
  intro code input
  obtain ⟨final, execution, correct⟩ := classifies code input
  refine ⟨encodeBool final.current, classifier_of_runs machine _ final execution, ?_⟩
  cases symbol : final.current <;>
    simpa only [symbol, encodeBool, truth, CommonRoleComputation.IsNode, Bool.false_eq_true] using correct

end Yulang.CommonRoleTuringBridge
