import Yulang.GeneralNominalCenteredHeadWFSource

/-! Output expressions preserve unions and arbitrary record tails. Inspection
queries remain a separate language: a union of output values is not a list of
captures required to denote the same value. -/
namespace Yulang.GeneralNominalCenteredHeadMatExpressions
open GeneralDeclarationPatterns GeneralCandidateInspection
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource
open CommonNominalFullCarrier
open GeneralNominalMaterialization (Mode)
open GeneralNominalCommonBridge (Assignment)

inductive Expr where
  | variable (name : Nat)
  | primitive (constructor : Primitive) (arguments : List Expr)
  | nominal (name : Nat) (arguments : List Expr)
  | record (label : Nat) (payload tail : Expr)
  | variant (tag : Nat) (payload : Expr)
  | join (first last : Expr)

def primitiveValue : Primitive → List Ty → Ty
  | .scalar base, [] => .base base
  | .pair, [first,last] => pair first last
  | .emptyRecord, [] => .emptyRecord
  | .exactEmpty, [] => .exactEmpty
  | _, _ => .bottom

mutual
  def value (variables : Mode → Nat → Ty) (mode : Mode) : Expr → Ty
    | .variable name => variables mode name
    | .primitive constructor arguments => primitiveValue constructor (values variables mode arguments)
    | .nominal name arguments => nominal name ((values variables .actual arguments).map Sum.inl)
    | .record label payload tail => record label (value variables mode payload) (value variables mode tail)
    | .variant tag payload => variant tag (value variables mode payload)
    | .join first last => .union (value variables mode first) (value variables mode last)
  def values (variables : Mode → Nat → Ty) (mode : Mode) : List Expr → List Ty
    | [] => []
    | first :: rest => value variables mode first :: values variables mode rest
end

def application (catalogue : Constructors) (interpretation : Interpretation)
    (name : Nat) (arguments : List Expr) : Option Expr := do
  let declaration ← catalogue name
  if declaration.parameters.length = arguments.length then
    match interpretation.primitives name with
    | some primitive =>
        if declaration.parameters = primitive.parameters then some (.primitive primitive arguments) else none
    | none =>
        if interpretation.invariantNominal name = true ∧
            declaration.parameters = List.replicate arguments.length .type then
          some (.nominal declaration.name arguments)
        else none
  else none

mutual
  def translate (catalogue : Constructors) (interpretation : Interpretation) : Pattern → Option Expr
    | .var name => some (.variable name)
    | .app name arguments => do
        let expressions ← translateMany catalogue interpretation arguments
        application catalogue interpretation name expressions
    | .record label payload tail => do
        pure (.record label (← translate catalogue interpretation payload) (← translate catalogue interpretation tail))
    | .variant tag payload => do pure (.variant tag (← translate catalogue interpretation payload))
    | .join first last => do
        pure (.join (← translate catalogue interpretation first) (← translate catalogue interpretation last))
  def translateMany (catalogue : Constructors) (interpretation : Interpretation) : List Pattern → Option (List Expr)
    | [] => some []
    | first :: rest => do
        pure ((← translate catalogue interpretation first) :: (← translateMany catalogue interpretation rest))
end

mutual
  def translateDefault (catalogue : Constructors) (interpretation : Interpretation) : Roles.Term → Option Expr
    | .var name => some (.variable name)
    | .app name arguments => do
        let expressions ← translateDefaults catalogue interpretation arguments
        application catalogue interpretation name expressions
  def translateDefaults (catalogue : Constructors) (interpretation : Interpretation) : List Roles.Term → Option (List Expr)
    | [] => some []
    | first :: rest => do
        pure ((← translateDefault catalogue interpretation first) :: (← translateDefaults catalogue interpretation rest))
end

theorem application_complete (covered : ConstructorUse catalogue interpretation name arguments.length) :
    ∃ expression, application catalogue interpretation name arguments = some expression := by
  obtain ⟨declaration,present,arity,⟨primitive,found,parameters⟩ | ⟨nominal,parameters⟩⟩ := covered
  · have arity' : primitive.parameters.length = arguments.length := parameters ▸ arity
    exact ⟨.primitive primitive arguments,by simp [application,present,found,parameters,arity']⟩
  · exact ⟨.nominal declaration.name arguments,by
      simp [application,present,interpretation.disjoint name nominal,nominal,parameters]⟩

mutual
  theorem translate_complete (covered : PatternCovered catalogue interpretation pattern) :
      ∃ expression, translate catalogue interpretation pattern = some expression := by
    cases pattern with
    | var name => exact ⟨.variable name,rfl⟩
    | app name arguments =>
        obtain ⟨expressions,translated,length⟩ := translateMany_complete covered.2
        obtain ⟨expression,compiled⟩ := application_complete (arguments := expressions) (length ▸ covered.1)
        exact ⟨expression,by simp [translate,translated,compiled]⟩
    | record label payload tail =>
        obtain ⟨first,one⟩ := translate_complete covered.1
        obtain ⟨last,two⟩ := translate_complete covered.2
        exact ⟨.record label first last,by simp [translate,one,two]⟩
    | variant tag payload =>
        obtain ⟨expression,translated⟩ := translate_complete (pattern := payload) covered
        exact ⟨.variant tag expression,by simp [translate,translated]⟩
    | join first last =>
        obtain ⟨a,one⟩ := translate_complete covered.1
        obtain ⟨b,two⟩ := translate_complete covered.2
        exact ⟨.join a b,by simp [translate,one,two]⟩
  theorem translateMany_complete (covered : PatternsCovered catalogue interpretation patterns) :
      ∃ expressions, translateMany catalogue interpretation patterns = some expressions ∧
        expressions.length = patterns.length := by
    cases patterns with
    | nil => exact ⟨[],rfl,rfl⟩
    | cons first rest =>
        obtain ⟨expression,one⟩ := translate_complete covered.1
        obtain ⟨expressions,two,length⟩ := translateMany_complete covered.2
        exact ⟨expression :: expressions,by simp [translateMany,one,two],by simp [length]⟩
end

mutual
  theorem translateDefault_complete (covered : TermCovered catalogue interpretation term) :
      ∃ expression, translateDefault catalogue interpretation term = some expression := by
    cases term with
    | var name => exact ⟨.variable name,rfl⟩
    | app name arguments =>
        obtain ⟨expressions,translated,length⟩ := translateDefaults_complete covered.2
        obtain ⟨expression,compiled⟩ := application_complete (arguments := expressions) (length ▸ covered.1)
        exact ⟨expression,by simp [translateDefault,translated,compiled]⟩
  theorem translateDefaults_complete (covered : TermsCovered catalogue interpretation terms) :
      ∃ expressions, translateDefaults catalogue interpretation terms = some expressions ∧
        expressions.length = terms.length := by
    cases terms with
    | nil => exact ⟨[],rfl,rfl⟩
    | cons first rest =>
        obtain ⟨expression,one⟩ := translateDefault_complete covered.1
        obtain ⟨expressions,two,length⟩ := translateDefaults_complete covered.2
        exact ⟨expression :: expressions,by simp [translateDefaults,one,two],by simp [length]⟩
end

theorem join_value (variables mode first last) :
    value variables mode (.join first last) = .union (value variables mode first) (value variables mode last) := rfl

theorem nominal_actual (variables mode name arguments) :
    value variables mode (.nominal name arguments) =
      nominal name ((values variables .actual arguments).map Sum.inl) := rfl

theorem record_tail (variables mode label payload tail) :
    value variables mode (.record label payload tail) =
      record label (value variables mode payload) (value variables mode tail) := rfl

end Yulang.GeneralNominalCenteredHeadMatExpressions
