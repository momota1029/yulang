import Yulang.Common

/-!
# Finite inspection of common presence observations

The executable inspector traverses an entire finite outer layer, including
same-depth tails, default sources and masks. Its alternatives contain only
proper payload-reference observations, negative argument comparisons, row
comparisons and role membership. In particular an uninspected whole-default
comparison is not an atomic obligation.

Exactness below is for one arbitrary observation and one arbitrary payload
assignment. Turning all target observations and all constructor depths into
one finite subtype problem, then solving its obligations simultaneously,
remains a separate compiler theorem.
-/

namespace Yulang.CommonPresenceInspection

open CommonSyntax (Layer)
open CommonFinite (Ty Observation Environment)
open ProducerContextual (Head)

universe u v
variable {Row : Type u} {Index : Type v}

/-- Each payload atom names a proper constructor child. The grammar contains
no source-layer comparison or default observation oracle. -/
inductive Obligation (Row : Type u) (Index : Type v) where
  | child : Index → Observation Row → Obligation Row Index
  | argument : Nat → Index → Obligation Row Index
  | rowBelow : Row → Row → Obligation Row Index
  | role : Head → Nat → Obligation Row Index

def Obligation.Holds (leRow : Row → Row → Prop) (env : Environment Row)
    (argumentOrder : Ty Row → Ty Row → Prop) (assignment : Index → Ty Row) :
    Obligation Row Index → Prop
  | .child index obs => CommonFinite.ProbeStep leRow env argumentOrder (assignment index) obs
  | .argument name index => argumentOrder (env.types name) (assignment index)
  | .rowBelow first last => leRow first last
  | .role head name => head ∈ env.roles name

abbrev Branch (Row : Type u) (Index : Type v) := List (Obligation Row Index)
abbrev Alternatives (Row : Type u) (Index : Type v) := List (Branch Row Index)

def Branch.Holds (holds : Obligation Row Index → Prop) (branch : Branch Row Index) : Prop :=
  ∀ obligation ∈ branch, holds obligation

def Alternatives.Holds (holds : Obligation Row Index → Prop)
    (alternatives : Alternatives Row Index) : Prop :=
  ∃ branch ∈ alternatives, Branch.Holds holds branch

def truth : Alternatives Row Index := [[]]
def falsity : Alternatives Row Index := []
def atom (obligation : Obligation Row Index) : Alternatives Row Index := [[obligation]]
def disjoin (first last : Alternatives Row Index) : Alternatives Row Index := first ++ last
def conjoin (first last : Alternatives Row Index) : Alternatives Row Index :=
  first.flatMap fun left => last.map fun right => left ++ right
def constant (value : Bool) : Alternatives Row Index := if value then truth else falsity

@[simp] theorem holds_truth (holds : Obligation Row Index → Prop) :
    Alternatives.Holds holds truth := by
  simp [Alternatives.Holds, Branch.Holds, truth]

@[simp] theorem holds_falsity (holds : Obligation Row Index → Prop) :
    ¬ Alternatives.Holds holds falsity := by
  simp [Alternatives.Holds, falsity]

@[simp] theorem holds_atom (holds : Obligation Row Index → Prop)
    (obligation : Obligation Row Index) :
    Alternatives.Holds holds (atom obligation) ↔ holds obligation := by
  simp [Alternatives.Holds, Branch.Holds, atom]

@[simp] theorem holds_constant (holds : Obligation Row Index → Prop) (value : Bool) :
    Alternatives.Holds holds (constant value) ↔ value = true := by
  cases value <;> simp [constant]

@[simp] theorem holds_disjoin (holds : Obligation Row Index → Prop)
    (first last : Alternatives Row Index) :
    Alternatives.Holds holds (disjoin first last) ↔
      Alternatives.Holds holds first ∨ Alternatives.Holds holds last := by
  simp only [Alternatives.Holds, disjoin, List.mem_append, or_and_right, exists_or]

@[simp] theorem branch_holds_append (holds : Obligation Row Index → Prop)
    (first last : Branch Row Index) :
    Branch.Holds holds (first ++ last) ↔ Branch.Holds holds first ∧ Branch.Holds holds last := by
  simp only [Branch.Holds, List.mem_append, or_imp, forall_and]

@[simp] theorem holds_conjoin (holds : Obligation Row Index → Prop)
    (first last : Alternatives Row Index) :
    Alternatives.Holds holds (conjoin first last) ↔
      Alternatives.Holds holds first ∧ Alternatives.Holds holds last := by
  constructor
  · rintro ⟨branch, member, valid⟩
    simp only [conjoin, List.mem_flatMap, List.mem_map] at member
    obtain ⟨left, leftMember, right, rightMember, rfl⟩ := member
    exact ⟨⟨left, leftMember, (branch_holds_append holds left right).mp valid |>.1⟩,
      ⟨right, rightMember, (branch_holds_append holds left right).mp valid |>.2⟩⟩
  · rintro ⟨⟨left, leftMember, leftValid⟩, ⟨right, rightMember, rightValid⟩⟩
    refine ⟨left ++ right, ?_, (branch_holds_append holds left right).mpr ⟨leftValid, rightValid⟩⟩
    simp only [conjoin, List.mem_flatMap, List.mem_map]
    exact ⟨left, leftMember, right, rightMember, rfl⟩

def isTrivial : Observation Row → Bool
  | .trivial => true
  | _ => false

@[simp] theorem isTrivial_exact (obs : Observation Row) :
    isTrivial obs = true ↔ obs = .trivial := by
  cases obs <;> simp [isTrivial]

/-- All branching is finite syntax traversal. Mask accumulation stays at the
outer layer, while every emitted child obligation starts with an empty mask. -/
def inspect (depth : Nat) (hidden : List Nat) :
    Layer Row Index → Observation Row → Alternatives Row Index
  | _, .trivial => truth
  | .bottom, _ => truth
  | .top, _ => falsity
  | .union first last, obs => conjoin (inspect depth hidden first obs) (inspect depth hidden last obs)
  | .inter first last, obs => disjoin (inspect depth hidden first obs) (inspect depth hidden last obs)
  | .mask more source, obs => inspect depth (hidden ++ more) source obs
  | .base actual, .base expected => constant (decide (actual = expected))
  | .base actual, .role name => atom (.role (.base actual) name)
  | .pair _ _, .role name => atom (.role .pair name)
  | .emptyRecord, .role name => atom (.role .records name)
  | .exactEmpty, .role name => atom (.role .records name)
  | .record _ _ _, .role name => atom (.role .records name)
  | .recordDefault _ _ _, .role name => atom (.role .records name)
  | .variant label _, .role name => atom (.role (.variant label) name)
  | .arrow _ _ _ _, .role name => atom (.role .arrow name)
  | .pair first _, .pairFirst obs => atom (.child first obs)
  | .pair _ last, .pairLast obs => atom (.child last obs)
  | .emptyRecord, .records => truth
  | .exactEmpty, .records => truth
  | .record _ _ _, .records => truth
  | .recordDefault _ _ _, .records => truth
  | .emptyRecord, .optional _ obs => constant (isTrivial obs)
  | .exactEmpty, .optional label obs => constant (decide (label ∉ hidden) || isTrivial obs)
  | .record current payload rest, .field label obs =>
      if label = current ∧ current ∉ hidden then atom (.child payload obs)
      else inspect depth hidden rest (.field label obs)
  | .record current payload rest, .optional label obs =>
      if label = current ∧ current ∉ hidden then atom (.child payload obs)
      else disjoin (inspect depth hidden rest (.optional label obs)) (constant (isTrivial obs))
  | .recordDefault current source fallback, .field label obs =>
      if label = current ∧ current ∉ hidden then
        match depth with
        | 0 => truth
        | _ + 1 => conjoin (inspect depth hidden source (.optional label obs))
            (disjoin (inspect depth hidden source (.field label .trivial)) (atom (.child fallback obs)))
      else inspect depth hidden source (.field label obs)
  | .recordDefault current source fallback, .optional label obs =>
      disjoin (if label = current ∧ current ∉ hidden then
        match depth with
        | 0 => truth
        | _ + 1 => conjoin (inspect depth hidden source (.optional label obs))
            (disjoin (inspect depth hidden source (.field label .trivial)) (atom (.child fallback obs)))
      else inspect depth hidden source (.optional label obs)) (constant (isTrivial obs))
  | .variant actual payload, .variant expected obs =>
      if actual = expected then atom (.child payload obs) else falsity
  | .arrow input _ _ _, .arrowArgument name => atom (.argument name input)
  | .arrow _ _ output _, .arrowResult obs => atom (.child output obs)
  | .arrow _ inputRow _ _, .arrowInputRow expected => atom (.rowBelow expected inputRow)
  | .arrow _ _ _ outputRow, .arrowOutputRow expected => atom (.rowBelow outputRow expected)
  | _, _ => falsity

/-- Independent denotation for the finite obligations produced by inspection. -/
def ObligationsHold (leRow : Row → Row → Prop) (env : Environment Row)
    (argumentOrder : Ty Row → Ty Row → Prop) (assignment : Index → Ty Row)
    (alternatives : Alternatives Row Index) : Prop :=
  Alternatives.Holds (Obligation.Holds leRow env argumentOrder assignment) alternatives

private theorem masked_bottom (leRow : Row → Row → Prop) (env : Environment Row)
    (argumentOrder : Ty Row → Ty Row → Prop) (hidden : List Nat) (obs : Observation Row) :
    CommonFinite.MaskedProbeStep leRow env argumentOrder hidden .bottom obs := by
  cases obs <;> trivial

/-- Exact finite outer inspection at an arbitrary observation, arbitrary
negative-comparison relation and arbitrary assignment of all payload children. -/
theorem inspect_exact (leRow : Row → Row → Prop) (env : Environment Row)
    (argumentOrder : Ty Row → Ty Row → Prop) (assignment : Index → Ty Row)
    (depth : Nat) (hidden : List Nat) (source : Layer Row Index) (obs : Observation Row) :
    CommonFinite.MaskedProbeStep leRow env argumentOrder hidden (source.evalAt depth assignment) obs ↔
      ObligationsHold leRow env argumentOrder assignment (inspect depth hidden source obs) := by
  unfold ObligationsHold
  induction source generalizing depth hidden obs <;> cases obs <;>
    simp_all [inspect, Layer.evalAt, CommonFinite.MaskedProbeStep, CommonFinite.ProbeStep,
      Obligation.Holds]
  all_goals cases depth <;>
    try simp_all [CommonFinite.MaskedProbeStep, masked_bottom]
  all_goals split <;>
    simp_all [Obligation.Holds, CommonFinite.ProbeStep]

/-- The existing negative-context interpretation at a fixed rank. It is
defined from lower-rank observations, independently of the inspector. -/
def argumentOrderAt (leRow : Row → Row → Prop) : Nat → Ty Row → Ty Row → Prop
  | 0, _, _ => True
  | rank + 1, expected, input =>
      ∀ env obs, CommonFinite.ProbeAt leRow rank env input obs →
        CommonFinite.ProbeAt leRow rank env expected obs

theorem inspect_at_exact (leRow : Row → Row → Prop) (rank : Nat) (env : Environment Row)
    (assignment : Index → Ty Row) (depth : Nat) (hidden : List Nat)
    (source : Layer Row Index) (obs : Observation Row) :
    CommonFinite.MaskedProbeAt leRow rank env hidden (source.evalAt depth assignment) obs ↔
      ObligationsHold leRow env (argumentOrderAt leRow rank) assignment
        (inspect depth hidden source obs) := by
  cases rank <;> exact inspect_exact leRow env _ assignment depth hidden source obs

/-- The same finite algorithm observes arbitrary regular common syntax and
the actual unrestricted common environment. Every branch uses only proper
child states; source tails and masks have already been traversed. -/
theorem common_inspect_exact (depth rank : Nat) (env : Common.Environment)
    (source : Common.Ty) (obs : Common.Observation) :
    Common.AcceptAt depth rank env source (.atom obs) ↔
      ObligationsHold Common.rowLe (env.atDepth depth) (argumentOrderAt Common.rowLe rank)
        (CommonSyntax.observe (CommonSyntax.graph Common.Row) depth)
        (inspect depth [] source obs) := by
  unfold Common.AcceptAt
  rw [CommonFinite.acceptAt_atom]
  cases rank <;> exact inspect_exact Common.rowLe _ _ _ depth [] source obs

def inspectDefault (depth : Nat) (hidden : List Nat) (label : Nat)
    (source : Layer Row Index) (fallback : Index) (obs : Observation Row) : Alternatives Row Index :=
  inspect depth hidden (.recordDefault label source fallback) obs

/-- Whole-default exactness for each arbitrary observation, with the entire
source expanded into independent finite obligations. This is not yet the
all-target subtype/solver compiler contract. -/
theorem default_inspect_at_exact (depth rank : Nat) (env : Common.Environment)
    (label : Nat) (source fallback : Common.Ty) (obs : Common.Observation) :
    Common.AcceptAt depth rank env (Common.recordDefault label source fallback) (.atom obs) ↔
      ObligationsHold Common.rowLe (env.atDepth depth) (argumentOrderAt Common.rowLe rank)
        (CommonSyntax.observe (CommonSyntax.graph Common.Row) depth)
        (inspectDefault depth [] label source (.node fallback) obs) :=
  common_inspect_exact depth rank env (Common.recordDefault label source fallback) obs

/-- The selected-field expansion keeps the optional-payload obligation and
both alternatives for presence/fallback. Both source tests are recursively
inspected, while the fallback is a proper child observation. -/
theorem inspectDefault_successor_field (depth label : Nat) (source : Layer Row Index)
    (fallback : Index) (obs : Observation Row) :
    inspectDefault (depth + 1) [] label source fallback (.field label obs) =
      conjoin (inspect (depth + 1) [] source (.optional label obs))
        (disjoin (inspect (depth + 1) [] source (.field label .trivial)) (atom (.child fallback obs))) := by
  simp [inspectDefault, inspect]

/-- At the constructor cutoff the selected payload is bottom, matching the
ordinary record approximation; the source's unrelated fields remain intact. -/
theorem inspectDefault_zero_field (label : Nat) (source : Layer Row Index)
    (fallback : Index) (obs : Observation Row) :
    inspectDefault 0 [] label source fallback (.field label obs) = truth := by
  simp [inspectDefault, inspect]

end Yulang.CommonPresenceInspection
