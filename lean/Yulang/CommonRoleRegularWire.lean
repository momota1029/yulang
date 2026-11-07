import Yulang.CommonRoleRegularRegistry
import Yulang.CommonRoleTuringDelimited

/-!
# A concrete finite wire format for the regular registry reduction

Every declaration field is serialized from the actual visible environment.
The finite goal syntax has a one-node regular clock and finite pair/int tree
literals. The latter are an explicit syntax constructor, not a supplied
semantic decoder. A fixed finite Code program constructs the complete query
from a program descriptor and an input tree.
-/

namespace Yulang.CommonRoleRegularWire

open CommonRoleComputation (Tree Code Eval)
open CommonRoleLinearClock
open CommonRoleLinearInterpreter (Kont State)
open CommonRoleRegularRegistry (registry environment roles roleDeclarations)
open CommonRoleTuringBridge (encodeNat project projection eval_project)

def tagged (tag : Nat) (payload : Tree) : Tree := .node (encodeNat tag) payload

def listWire {α : Type} (encode : α → Tree) : List α → Tree
  | [] => .leaf
  | first :: rest => .node (encode first) (listWire encode rest)

mutual
  def termWire : Roles.Term → Tree
    | .var name => tagged 0 (encodeNat name)
    | .app name args => tagged 1 (.node (encodeNat name) (termsWire args))
  def termsWire : List Roles.Term → Tree
    | [] => .leaf
    | first :: rest => .node (termWire first) (termsWire rest)
end

theorem termsWire_list (terms : List Roles.Term) :
    termsWire terms = listWire termWire terms := by
  induction terms <;> simp_all [termsWire, listWire]

def goalPatternWire (goal : Roles.Goal) : Tree :=
  .node (encodeNat goal.role) (termsWire goal.args)

/-- Role, every head pattern, every recursive where goal, and declaration ID. -/
def implWire (implementation : Roles.Impl) : Tree :=
  .node (encodeNat implementation.role)
    (.node (termsWire implementation.head)
      (.node (listWire goalPatternWire implementation.constraints) (encodeNat implementation.key)))

def associatedBodyWire (body : Nat × Roles.Term) : Tree :=
  .node (encodeNat body.1) (termWire body.2)

def assocImplWire (implementation : Roles.AssocImpl) : Tree :=
  .node (implWire implementation.impl) (listWire associatedBodyWire implementation.assoc)

def optionTermWire : Option Roles.Term → Tree
  | none => .leaf
  | some term => .node .leaf (termWire term)

/-- A genuinely finite signature, including both required names and defaults. -/
structure Signature where
  arity : Nat
  associated : List (Nat × Option Roles.Term)
  deriving DecidableEq, Repr

def Signature.wire (signature : Signature) : Tree :=
  .node (encodeNat signature.arity)
    (listWire (fun body => .node (encodeNat body.1) (optionTermWire body.2)) signature.associated)

def requiredSignature : Signature := ⟨2, [(0, none)]⟩
def emptySignature : Signature := ⟨0, []⟩
def signatures : List Signature := List.replicate 5 requiredSignature
def signatureAt (name : Nat) : Signature := (signatures[name]?).getD emptySignature

theorem signatureAt_exact (role name : Nat) :
    (signatureAt role).arity = (roles role).arity ∧
      (signatureAt role).associated.lookup name = (roles role).assoc name := by
  by_cases bound : role < 5
  · rw [CommonRoleRegularRegistry.roles_lt bound]
    simp only [signatureAt, signatures, List.getElem?_replicate, bound, ite_true, Option.getD_some]
    constructor
    · rfl
    · by_cases zero : name = 0
      · subst name; rfl
      · simp [requiredSignature, CommonRoleRegularRegistry.requiredRole, zero]
  · simp [signatureAt, signatures, CommonRoleRegularRegistry.roles,
      roleDeclarations, bound, emptySignature,
      CommonRoleRegularRegistry.undeclaredRole]

def databaseWire (code : Code) : Tree :=
  .node (listWire Signature.wire signatures) (listWire assocImplWire (environment code).impls)

theorem databaseWire_actual (code : Code) :
    databaseWire code = .node (listWire Signature.wire signatures)
      (listWire assocImplWire
        ((CommonRoleLinearEvidence.visible (registry code) 0).map CommonRoleRegularRegistry.annotate)) :=
  rfl

def groundWire : Ground → Tree
  | .int => tagged 0 .leaf
  | .pair first last => tagged 1 (.node (groundWire first) (groundWire last))
  | .variant tag payload => tagged 2 (.node (encodeNat tag) (groundWire payload))

/-- A finite graph table: a node stores its variant label and local successor. -/
structure ClockGraph where
  nodes : List (Nat × Nat)
  root : Nat
  deriving DecidableEq, Repr

def ClockGraph.state (graph : ClockGraph) : CommonSyntax.State Common.Row :=
  .block (graph.nodes.map (fun node => .variant node.1 (.inl node.2))) graph.root

def ClockGraph.wire (graph : ClockGraph) : Tree :=
  .node (listWire (fun node => .node (encodeNat node.1) (encodeNat node.2)) graph.nodes)
    (encodeNat graph.root)

def clockGraph : ClockGraph := ⟨[(7, 0)], 0⟩

theorem clockGraph_actual :
    clockGraph.state = CommonRoleRegularObstructions.loopState := rfl

theorem clockGraph_denotes :
    CommonSyntax.graph Common.Row clockGraph.state = clock := rfl

/-- `data` stores finite pair/int syntax directly. Every constructor below has
a fixed interpretation and contains no row predicate or semantic type leaf. -/
inductive TypeDescription where
  | data : Tree → TypeDescription
  | ground : Ground → TypeDescription
  | pair : TypeDescription → TypeDescription → TypeDescription
  | clock
  deriving DecidableEq, Repr

def TypeDescription.eval : TypeDescription → Common.Ty
  | .data input => input.encode.eval
  | .ground literal => literal.eval
  | .pair first last => Common.pair first.eval last.eval
  | .clock => CommonSyntax.graph Common.Row clockGraph.state

def TypeDescription.wire : TypeDescription → Tree
  | .data input => tagged 0 input
  | .ground literal => tagged 1 (groundWire literal)
  | .pair first last => tagged 2 (.node first.wire last.wire)
  | .clock => tagged 3 clockGraph.wire

theorem data_denotes (input : Tree) : (TypeDescription.data input).eval = input.encode.eval := rfl

structure GoalDescription where
  role : Nat
  clock : TypeDescription
  value : TypeDescription
  deriving DecidableEq, Repr

def GoalDescription.eval (goal : GoalDescription) : SemanticGoal :=
  ⟨goal.role, goal.clock.eval, goal.value.eval⟩

def GoalDescription.wire (goal : GoalDescription) : Tree :=
  .node (encodeNat goal.role) (.node goal.clock.wire goal.value.wire)

def startGoal (code : Code) (input : Tree) : GoalDescription :=
  ⟨1, .clock, .pair (.ground code.encode) (.pair (.data input) (.ground Kont.halt.encode))⟩

theorem startGoal_denotes (code : Code) (input : Tree) :
    (startGoal code input).eval = goalOf (State.run code input .halt).encode := rfl

def descriptor (code : Code) : Tree := .node (databaseWire code) (groundWire code.encode)

def queryWire (code : Code) (input : Tree) : Tree :=
  .node (databaseWire code) (startGoal code input).wire

def taggedCode (tag : Nat) (payload : Code) : Code := .pair (.const (encodeNat tag)) payload

theorem eval_taggedCode (tag : Nat) {payload : Code} {input output : Tree}
    (evaluation : Eval payload input output) :
    Eval (taggedCode tag payload) input (tagged tag output) :=
  .pair (.const _ _) evaluation

/-- This one finite program is independent of both the input and the program
whose declarations the descriptor stores. It copies all actual declarations
and constructs the concrete initial regular goal, preserving each field. -/
def queryCode : Code :=
  .pair (project [false, false])
    (.pair (.const (encodeNat 1))
      (.pair (.const (TypeDescription.clock.wire))
        (taggedCode 2 (.pair (taggedCode 1 (project [false, true]))
          (taggedCode 2 (.pair (taggedCode 0 .right)
            (taggedCode 1 (.const (groundWire Kont.halt.encode)))))))))

theorem eval_queryCode (code : Code) (input : Tree) :
    Eval queryCode (.node (descriptor code) input) (queryWire code input) := by
  apply Eval.pair
  · exact eval_project [false, false] _
  · apply Eval.pair (.const _ _)
    apply Eval.pair (.const _ _)
    apply eval_taggedCode
    apply Eval.pair
    · exact eval_taggedCode 1 (eval_project [false, true] _)
    · apply eval_taggedCode
      apply Eval.pair
      · exact eval_taggedCode 0 (.rightNode _ _)
      · exact eval_taggedCode 1 (.const _ _)

theorem queryCode_exact (code : Code) (input output : Tree) :
    Eval queryCode (.node (descriptor code) input) output ↔ output = queryWire code input := by
  constructor
  · intro evaluated
    exact evaluated.deterministic (eval_queryCode code input)
  · rintro rfl
    exact eval_queryCode code input

theorem tagged_eq_iff (first last : Nat) (a b : Tree) :
    tagged first a = tagged last b ↔ first = last ∧ a = b := by
  constructor
  · intro same
    exact ⟨CommonRoleTuringBridge.encodeNat_injective (Tree.node.inj same).1,
      (Tree.node.inj same).2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem congrArg2 {α β γ : Type} (f : α → β → γ) {a b : α} {c d : β}
    (first : a = b) (last : c = d) : f a c = f b d := by
  cases first
  cases last
  rfl

theorem listWire_injective {α : Type} (encode : α → Tree)
    (injective : ∀ {a b}, encode a = encode b → a = b)
    {first last : List α} (same : listWire encode first = listWire encode last) : first = last := by
  induction first generalizing last with
  | nil => cases last <;> simp_all [listWire]
  | cons first rest ih =>
    cases last with
    | nil => cases same
    | cons last tail =>
      have parts := Tree.node.inj same
      exact congrArg2 List.cons (injective parts.1) (ih parts.2)

mutual
  theorem termWire_injective (first last : Roles.Term)
      (same : termWire first = termWire last) : first = last := by
    cases first with
    | var first =>
      cases last with
      | var last =>
        exact congrArg Roles.Term.var
          (CommonRoleTuringBridge.encodeNat_injective (Tree.node.inj same).2)
      | app last args =>
        have impossible := ((tagged_eq_iff _ _ _ _).mp same).1
        cases impossible
    | app first args =>
      cases last with
      | var last =>
        have impossible := ((tagged_eq_iff _ _ _ _).mp same).1
        cases impossible
      | app last more =>
        have parts := Tree.node.inj (Tree.node.inj same).2
        exact congrArg2 Roles.Term.app
          (CommonRoleTuringBridge.encodeNat_injective parts.1)
          (termsWire_injective args more parts.2)
  theorem termsWire_injective (first last : List Roles.Term)
      (same : termsWire first = termsWire last) : first = last := by
    cases first with
    | nil => cases last <;> simp_all [termsWire]
    | cons first rest =>
      cases last with
      | nil => cases same
      | cons last tail =>
        have parts := Tree.node.inj same
        exact congrArg2 List.cons (termWire_injective first last parts.1)
          (termsWire_injective rest tail parts.2)
end

theorem goalPatternWire_injective {first last : Roles.Goal}
    (same : goalPatternWire first = goalPatternWire last) : first = last := by
  have parts := Tree.node.inj same
  have role := CommonRoleTuringBridge.encodeNat_injective parts.1
  have args := termsWire_injective _ _ parts.2
  cases first; cases last; simp_all

theorem implWire_injective {first last : Roles.Impl}
    (same : implWire first = implWire last) : first = last := by
  have a := Tree.node.inj same
  have b := Tree.node.inj a.2
  have c := Tree.node.inj b.2
  have role := CommonRoleTuringBridge.encodeNat_injective a.1
  have head := termsWire_injective _ _ b.1
  have constraints := listWire_injective goalPatternWire goalPatternWire_injective c.1
  have key := CommonRoleTuringBridge.encodeNat_injective c.2
  cases first; cases last; simp_all

theorem associatedBodyWire_injective {first last : Nat × Roles.Term}
    (same : associatedBodyWire first = associatedBodyWire last) : first = last := by
  have parts := Tree.node.inj same
  exact Prod.ext (CommonRoleTuringBridge.encodeNat_injective parts.1)
    (termWire_injective _ _ parts.2)

theorem assocImplWire_injective {first last : Roles.AssocImpl}
    (same : assocImplWire first = assocImplWire last) : first = last := by
  have parts := Tree.node.inj same
  have implementation := implWire_injective parts.1
  have associated := listWire_injective associatedBodyWire associatedBodyWire_injective parts.2
  cases first; cases last; simp_all

theorem groundWire_injective {first last : Ground}
    (same : groundWire first = groundWire last) : first = last := by
  induction first generalizing last with
  | int =>
    cases last with
    | int => rfl
    | pair a b => cases ((tagged_eq_iff _ _ _ _).mp same).1
    | variant tag payload => cases ((tagged_eq_iff _ _ _ _).mp same).1
  | pair first rest ihFirst ihRest =>
    cases last with
    | int => cases ((tagged_eq_iff _ _ _ _).mp same).1
    | pair last tail =>
      have parts := Tree.node.inj (Tree.node.inj same).2
      exact congrArg2 Ground.pair (ihFirst parts.1) (ihRest parts.2)
    | variant tag payload => cases ((tagged_eq_iff _ _ _ _).mp same).1
  | variant tag payload ih =>
    cases last with
    | int => cases ((tagged_eq_iff _ _ _ _).mp same).1
    | pair a b => cases ((tagged_eq_iff _ _ _ _).mp same).1
    | variant other rest =>
      have parts := Tree.node.inj (Tree.node.inj same).2
      exact congrArg2 Ground.variant (CommonRoleTuringBridge.encodeNat_injective parts.1) (ih parts.2)

end Yulang.CommonRoleRegularWire
