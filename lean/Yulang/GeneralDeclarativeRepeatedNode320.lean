import Yulang.GeneralDeclarativeRepeatedHead320
import Yulang.GeneralDeclarativeLeaf320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14500
set_option maxHeartbeats 4350000
namespace Yulang.GeneralDeclarativeRepeatedNode320
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarationPatterns (Pattern normalizeArgs variablesArgs)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand Bounds HeadArg head_args)
open GeneralDeclarativeAssembly320 (Meaning named_sound)
open GeneralDeclarativeEntailment320 (Entails appendFacts conservative_append)
open GeneralDeclarativeCaptureClosure320 (Origin capture_fits withOrdinary compilation conservative_capture available_bounds)
open GeneralDeclarativeBatch320 (zipFacts collect)
open GeneralDeclarativeNodeFacts320 (clauseFacts compiled_clauses)
open GeneralDeclarativeOutputFacts320 (rootFact compiled_root_outputs)
open GeneralDeclarativeRepeatedHead320 (CentersAgree capture occurrences repeated_head repeated_origins)
open GeneralDeclarativeMerge320 (EqualTerm lower upper)
open GeneralDeclarativeLinear320 (table)
open CommonRoleOutermostResolver (All₂)

def afterHeadFacts (r : Registry) (interp : Interpretation) (capture : Nat → Capture)
    (decl : Declaration) (d : Demand) (kids : List Demand) : Option (List Equation) := do
  let req ← zipFacts (clauseFacts r interp capture) decl.requirements kids
  let out ← collect (rootFact r interp decl d capture) d.outputs
  pure (req ++ out)

/-- A direct source head proof and the downstream compiler compose without
requiring a duplicate ordinary equation for the head itself. Repeated
capture bounds and emitted equations can be semantic ordinary consequences. -/
theorem downstream_sound {s r interp capture decl d kids facts}
    (checked : Checked r) (visible : decl ∈ r.declarations) (role : decl.role = d.role)
    (origins : ∀ n ∈ decl.inputNames, Origin s (capture n))
    (head : All₂ (HeadArg s r.constructors interp capture) d.arguments decl.head)
    (generated : afterHeadFacts r interp capture decl d kids = some facts)
    (settled : ∀ row ∈ facts, Entails s row)
    (m : Assignment) (valid : Models s m) : Meaning r interp m d decl capture kids := by
  cases cq : zipFacts (clauseFacts r interp capture) decl.requirements kids with
  | none => simp [afterHeadFacts,cq] at generated
  | some cf =>
    cases oq : collect (rootFact r interp decl d capture) d.outputs with
    | none => simp [afterHeadFacts,cq,oq] at generated
    | some ofacts =>
      have batch : cf ++ ofacts = facts := by simpa [afterHeadFacts,cq,oq] using generated
      subst facts
      let extra := withOrdinary s (compilation decl capture)
      let extended := appendFacts extra (cf ++ ofacts)
      have derived : ∀ row ∈ cf ++ ofacts, Entails extra row :=
        fun row present model v => settled row present model ((conservative_capture origins model).mp v)
      have old : Models extra m := (conservative_capture origins m).mpr valid
      have same : Models extended m := (conservative_append derived m).mpr old
      have has (row) (placed : row ∈ cf ++ ofacts) : row ∈ extended.equations :=
        List.mem_append_right _ placed
      have capBounds : ∀ i ∈ decl.inputNames, Bounds extended (capture i) :=
        available_bounds s decl capture
      exact ⟨visible,role,fun i h => capture_fits (origins i h) m valid,head_args head m valid,
        compiled_clauses (s := extended) (checked.2 decl visible) capBounds cq
          (fun row placed => has row (List.mem_append_left _ placed)) m same,
        fun out asked => named_sound (s := extended) checked visible
          (compiled_root_outputs oq (fun row placed => has row (List.mem_append_right _ placed)) out asked) m same⟩

/-- All variable-only heads are treated, including repeated variables.
The first actual occurrence supplies the center; any additional lower and
upper names must be justified by their ordinary join/meet equations. -/
theorem repeated_source_node {s r interp decl d kids names lo hi facts}
    (checked : Checked r) (visible : decl ∈ r.declarations) (role : decl.role = d.role)
    (head : decl.head = names.map Pattern.var) (arity : names.length = d.arguments.length)
    (bound : ∀ arg ∈ d.arguments, Bounds s arg)
    (shared : CentersAgree s (table names d.arguments))
    (merges : ∀ name ∈ names, ∀ first rest,
      occurrences (table names d.arguments) name = first :: rest →
      EqualTerm s (lo name) (lower first rest) ∧ EqualTerm s (hi name) (upper first rest))
    (generated : afterHeadFacts r interp (capture (table names d.arguments) lo hi) decl d kids = some facts)
    (settled : ∀ row ∈ facts, Entails s row)
    (m : Assignment) (valid : Models s m) :
    Meaning r interp m d decl (capture (table names d.arguments) lo hi) kids := by
  apply downstream_sound checked visible role ?_ ?_ generated settled m valid
  · intro name used
    change name ∈ variablesArgs (normalizeArgs decl.head) at used
    rw [head,GeneralDeclarativeLeaf320.variable_inputs] at used
    exact repeated_origins arity bound shared merges name used
  · rw [head]
    exact repeated_head arity bound shared

end Yulang.GeneralDeclarativeRepeatedNode320
