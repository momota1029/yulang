import Yulang.GeneralDeclarativeLinear320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13000
set_option maxHeartbeats 3300000
namespace Yulang.GeneralDeclarativeLeaf320
open GeneralDeclarations (Declaration Registry Checked)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand Bounds head_args bounds_sound sourceValue)
open GeneralDeclarativeLocal320 (NodeMeaning)
open GeneralDeclarativeOutputs320 (bodyCapture bodyPattern compile compile_exact OutputMeaning)
open GeneralDeclarativeSubstitution320 (logical EquationRead equation_read)
open GeneralDeclarativeLinear320 (table captures produce)
open GeneralDictionaryAssociatedProvenance (lookup lookup_exact)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Output)

theorem variable_inputs (names : List Nat) :
    variablesArgs (normalizeArgs (names.map Pattern.var)) = names := by
  induction names with
  | nil => rfl
  | cons n ns ih =>
    change n :: variablesArgs (normalizeArgs (ns.map Pattern.var)) = n :: ns
    rw [ih]

/-- This is a positive finished fragment, not a classifier for an arbitrary
signature or unresolved candidate. Each observable unnamed root is
already a scalar and the sole visible same-role head is linear and where-free.
The last field records ordinary completed output constraints; it does not
assume semantic evidence or alter the global readiness rules. -/
structure LeafSelection (s : State) (r : Registry) (interp : Interpretation)
    (d : Demand) (key : Nat) (decl : Declaration) (names : List Nat) : Prop where
  visible : decl ∈ r.declarations
  role : decl.role = d.role
  key_eq : decl.id = key
  sole : ∀ other ∈ r.declarations, other.role = d.role → other = decl
  named : decl.head = names.map Pattern.var
  linear : names.Nodup
  arity : names.length = d.arguments.length
  noWhere : decl.requirements = []
  lower_scalar : ∀ arg ∈ d.arguments, ∃ base,
    ⟨arg.lower,.primitive (.scalar base) []⟩ ∈ s.equations
  bounded : ∀ arg ∈ d.arguments, Bounds s arg
  committed : ∀ out ∈ d.outputs, ∃ body code,
    lookup r.roles decl out.name = some body ∧ compile r.constructors interp body = some code ∧
      ⟨out.target,logical (bodyCapture d (captures (table names d.arguments)) body) .actual code⟩ ∈ s.equations

theorem supplied_output {s r interp d key decl names} (checked : Checked r)
    (selected : LeafSelection s r interp d key decl names) (m : Assignment) (valid : Models s m)
    (out : Output) (asked : out ∈ d.outputs) :
    OutputMeaning r.roles r.constructors interp decl d (captures (table names d.arguments)) m out := by
  obtain ⟨body,expr,known,compiled,materialized⟩ := selected.committed out asked
  have unique := (checked.2 decl selected.visible).identified.2.2.1
  have fact : EquationRead s (bodyCapture d (captures (table names d.arguments)) body) .actual out.target expr :=
    .whole materialized
  exact ⟨body,(lookup_exact r.roles decl unique out.name body).mp known,
    eqv_trans (equation_read fact m valid)
      (compiled_normalized ((compile_exact r.constructors interp body).trans compiled))⟩

/-- In this fragment the ordered head evidence and all capture bounds are
produced from distinct positional variables, not supplied by a semantic premise. -/
theorem selected_leaf {s r interp d key decl names} (checked : Checked r)
    (selected : LeafSelection s r interp d key decl names) (m : Assignment) (valid : Models s m) :
    NodeMeaning r interp m d decl (captures (table names d.arguments)) [] := by
  obtain ⟨captureBounds,head⟩ := produce (s := s) (c := r.constructors) (interp := interp)
    selected.linear selected.arity selected.bounded
  refine ⟨selected.visible,selected.role,?_,?_,?_,supplied_output checked selected m valid⟩
  · intro name input
    have inNames : name ∈ names := by
      change name ∈ variablesArgs (normalizeArgs decl.head) at input
      rwa [selected.named,variable_inputs] at input
    exact bounds_sound (captureBounds name inNames) m valid
  · rw [selected.named]
    exact head_args head m valid
  · rw [selected.noWhere]
    exact .nil

end Yulang.GeneralDeclarativeLeaf320
