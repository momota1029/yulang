import Yulang.CommonRoleTuringBridge

/-!
# A self-delimiting binary tape interface for the halting obstruction

Raw finite-list serialization is not by itself a faithful Turing input
convention when false is the blank symbol: trailing false cells cannot be
distinguished from the infinite blank suffix. Here every payload bit is
preceded by true, and a false marker terminates the frame. The decoder below
reads only tape cells, never finite-list length or EOF.
-/

namespace Yulang.CommonRoleTuringDelimited

open CommonRoleComputation (Tree Code Eval)
open CommonRoleTuringBridge (Machine Config Runs encodeNat encodeBool encodeList encodeConfig
  project eval_project eval_left eval_right serialize serializeCode eval_serializeCode
  compile compile_of_runs runs_of_compile currentCode eval_current)

def frameOnto : List Bool → List Bool → List Bool
  | [], suffix => suffix
  | bit :: rest, suffix => true :: bit :: frameOnto rest suffix

def frameBits (bits : List Bool) : List Bool := frameOnto bits [false]

theorem frameOnto_append (first last suffix : List Bool) :
    frameOnto (first ++ last) suffix = frameOnto first (frameOnto last suffix) := by
  induction first <;> simp_all [frameOnto]

def stream : List Bool → (Nat → Bool) → Nat → Bool
  | [], suffix, position => suffix position
  | first :: _, _, 0 => first
  | _ :: rest, suffix, position + 1 => stream rest suffix position

/-- Read a frame from an infinite tape view. Each rule inspects only the
marker and, for a true marker, its next payload cell. No EOF test exists. -/
inductive ReadsFrame : (Nat → Bool) → List Bool → Nat → Prop where
  | stop {tape : Nat → Bool} (marker : tape 0 = false) : ReadsFrame tape [] 1
  | bit {tape : Nat → Bool} {bits : List Bool} {consumed : Nat}
      (marker : tape 0 = true)
      (rest : ReadsFrame (fun position => tape (position + 2)) bits consumed) :
      ReadsFrame tape (tape 1 :: bits) (consumed + 2)

theorem reads_frameBits (bits : List Bool) (suffix : Nat → Bool) :
    ReadsFrame (stream (frameBits bits) suffix) bits (2 * bits.length + 1) := by
  induction bits with
  | nil => exact .stop rfl
  | cons bit rest ih =>
      have amount : (2 * rest.length + 1) + 2 = 2 * (bit :: rest).length + 1 := by
        simp only [List.length_cons]
        omega
      rw [← amount]
      exact .bit rfl ih

theorem ReadsFrame.deterministic {tape : Nat → Bool} {bits : List Bool} {consumed : Nat}
    (first : ReadsFrame tape bits consumed) :
    ∀ {other amount}, ReadsFrame tape other amount → bits = other ∧ consumed = amount := by
  induction first with
  | stop marker =>
      intro other amount last
      cases last with
      | stop => exact ⟨rfl, rfl⟩
      | bit opposite _ => rw [marker] at opposite; cases opposite
  | bit marker rest ih =>
      intro other amount last
      cases last with
      | stop opposite => rw [marker] at opposite; cases opposite
      | bit _ tail =>
          obtain ⟨sameBits, sameAmount⟩ := ih tail
          cases sameBits
          cases sameAmount
          exact ⟨rfl, rfl⟩

/-- Even with arbitrary tape after the terminator, different framed payloads
cannot become the same infinite tape. This is stronger than list injectivity. -/
theorem frame_stream_prefix_free (first last : List Bool) (afterFirst afterLast : Nat → Bool)
    (same : stream (frameBits first) afterFirst = stream (frameBits last) afterLast) : first = last := by
  have left := reads_frameBits first afterFirst
  have right := reads_frameBits last afterLast
  rw [same] at left
  exact (left.deterministic right).1

theorem stream_blank (bits : List Bool) (position : Nat) :
    stream bits (fun _ => false) position = (bits[position]?).getD false := by
  induction bits generalizing position with
  | nil => rfl
  | cons bit rest ih =>
      cases position with
      | zero => rfl
      | succ position => exact ih position

def inputBits (input : Tree) : List Bool := frameBits (serialize input).reverse

def initial (input : Tree) : Config := ⟨0, [], false, inputBits input⟩

/-- The actual infinite blank-extended input tapes distinguish every source
tree; the receiver does not need access to finite-list length metadata. -/
theorem initial_tape_injective {first last : Tree}
    (same : ∀ position : Nat,
      ((initial first).rightTape[position]?).getD false =
        ((initial last).rightTape[position]?).getD false) : first = last := by
  have streams : stream (inputBits first) (fun _ => false) = stream (inputBits last) (fun _ => false) := by
    funext position
    rw [stream_blank, stream_blank]
    exact same position
  have reversed := frame_stream_prefix_free (serialize first).reverse (serialize last).reverse
    (fun _ => false) (fun _ => false) streams
  have serialized := congrArg List.reverse reversed
  simp only [List.reverse_reverse] at serialized
  exact CommonRoleTuringBridge.serialize_injective serialized

def frameBody : Code :=
  .pair (project [false, true])
    (.pair (.const (encodeBool true))
      (.pair (project [false, false]) (project [true])))

def frameLoop : Code := .whileE .left frameBody

theorem eval_frameBody (bit : Bool) (rest suffix : List Bool) :
    Eval frameBody (.node (encodeList (bit :: rest)) (encodeList suffix))
      (.node (encodeList rest) (encodeList (true :: bit :: suffix))) :=
  .pair (eval_project _ _)
    (.pair (.const _ _) (.pair (eval_project _ _) (eval_project _ _)))

theorem eval_frameLoop (bits suffix : List Bool) :
    Eval frameLoop (.node (encodeList bits) (encodeList suffix))
      (.node .leaf (encodeList (frameOnto bits.reverse suffix))) := by
  induction bits generalizing suffix with
  | nil => exact .whileLeaf (eval_left _)
  | cons bit rest ih =>
      have result := Eval.whileNode
        (eval_left (.node (encodeList (bit :: rest)) (encodeList suffix)))
        (eval_frameBody bit rest suffix) (ih (true :: bit :: suffix))
      simpa only [frameLoop, List.reverse_cons, frameOnto_append, frameOnto] using result

def frameCode : Code :=
  .seq (.pair .id (.const (encodeList [false]))) (.seq frameLoop .right)

theorem eval_frameCode (bits : List Bool) :
    Eval frameCode (encodeList bits) (encodeList (frameBits bits.reverse)) :=
  .seq (.pair (.id _) (.const _ _)) (.seq (eval_frameLoop bits [false]) (eval_right _))

def initialCode : Code :=
  CommonRoleTuringBridge.frame (.const (encodeNat 0)) (.const (encodeList []))
    (.const (encodeBool false)) (.seq serializeCode frameCode)

theorem eval_initialCode (input : Tree) : Eval initialCode input (encodeConfig (initial input)) :=
  .pair (.const _ _) (.pair (.const _ _)
    (.pair (.const _ _) (.seq (eval_serializeCode input) (eval_frameCode (serialize input)))))

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

def TuringHaltingClassifier (encode : Code → Tree) (machine : Machine) : Prop :=
  ∀ code input, ∃ final,
    Runs machine (initial (.node (encode code) input)) final ∧
      (final.current = true ↔ CommonRoleComputation.Halts code input)

/-- No finite standard tape machine classifies all Code halting queries under
the concrete self-delimiting input convention. No domain or success oracle is
assumed, and the tape representation has the prefix-free theorem above. -/
theorem no_turing_halting_classifier (encode : Code → Tree) :
    ¬ ∃ machine : Machine, TuringHaltingClassifier encode machine := by
  rintro ⟨machine, classifies⟩
  apply CommonRoleComputation.no_halting_classifier encode
  refine ⟨classifierCode machine, ?_⟩
  intro code input
  obtain ⟨final, execution, correct⟩ := classifies code input
  refine ⟨encodeBool final.current, classifier_of_runs machine _ final execution, ?_⟩
  cases symbol : final.current <;>
    simpa only [symbol, encodeBool, CommonRoleTuringBridge.truth,
      CommonRoleComputation.IsNode, Bool.false_eq_true] using correct

end Yulang.CommonRoleTuringDelimited
