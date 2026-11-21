import Yulang.GeneralDeclarativeCenterEntails321
import Yulang.GeneralDeclarativeWhereProducer321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNodeProducer321
open GeneralDeclarations (Declaration Checked Registry)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeCenterEntails321 (HeadDerivation actual_head_row)
open GeneralDeclarativeOrdinaryReads321 (Reads entails_read)
open GeneralDeclarativeWhereProducer321 (Child child_result)
open GeneralDeclarativeCompileLists321 (Result zip_result collect_result)
open GeneralDeclarativeEntailment320 (BatchRecipe)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeNodeFacts320 (clauseFacts nodeFacts)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeOutputs320 (bodyCapture bodyPattern compile compile_exact)
open GeneralDictionaryAssociatedProvenance (Supplies lookup_exact)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalInspection (Interpretation)
open GeneralSourceState (Output)
open CommonRoleOutermostResolver (All₂)

/-- The body provenance is the source rule, not equality with compiled
lookup. The ordinary read may use facts which cannot justify expansion. -/
def ReturnRead (s : State) (r : Registry) (interp : Interpretation)
    (decl : Declaration) (d : Demand) (capture : Nat → Capture) (out : Output) : Prop :=
  ∃ body code, Supplies r.roles decl out.name body ∧
    translate r.constructors interp (bodyPattern body) = some code ∧
    Reads s (bodyCapture d capture body) .actual out.target code

theorem return_result (checked : Checked r) (visible : decl ∈ r.declarations)
    (read : ReturnRead s r interp decl d capture out) :
    Result s (rootFact r interp decl d capture out) := by
  obtain ⟨body,code,fromSource,translated,read⟩ := read
  have unique := (checked.2 decl visible).identified.2.2.1
  have found := (lookup_exact r.roles decl unique _ body).mpr fromSource
  have compiled := (compile_exact r.constructors interp body).symm.trans translated
  refine ⟨[⟨out.target,logical (bodyCapture d capture body) .actual code⟩],
    by simp [rootFact,found,compiled],?_⟩
  intro row included
  cases List.mem_singleton.mp included
  exact entails_read read

/-- Independent syntactic construction for a fixed source branch. The head,
where inputs, and associated outputs retain their exact logical names and
their occurrence order. It does not require that the compiler has run,
any entailment hypothesis, or that a child already has a dictionary. -/
structure Derivation (s : State) (r : Registry) (interp : Interpretation)
    (p : Supported s completed) (d : Demand) (decl : Declaration)
    (capture : Nat → Capture) (kids : List Demand) : Prop where
  captures : ∀ binder ∈ decl.inputNames, Bounds s (capture binder)
  bounds : ∀ arg ∈ d.arguments, Bounds s arg
  head : All₂ (HeadDerivation (restriction p) r.constructors interp capture) d.arguments decl.head
  children : All₂ (Child s r interp capture) decl.requirements kids
  results : ∀ out ∈ d.outputs, ReturnRead s r interp decl d capture out

theorem attach_head {s : State} {capture : Nat → Capture}
    (checked : Checked r) (visible : decl ∈ r.declarations) (role : decl.role = d.role)
    (captures : ∀ binder ∈ decl.inputNames, Bounds s (capture binder))
    (bounds : ∀ arg ∈ d.arguments, Bounds s arg)
    (headResult : All₂ (fun arg pattern => Result s (headFact r.constructors interp capture arg pattern))
      d.arguments decl.head)
    (children : All₂ (Child s r interp capture) decl.requirements kids)
    (results : ∀ out ∈ d.outputs, ReturnRead s r interp decl d capture out) :
    BatchRecipe s r interp d decl.id kids := by
  obtain ⟨head,hc,he⟩ := zip_result headResult
  obtain ⟨requirements,cc,ce⟩ := zip_result (f := clauseFacts r interp capture)
    (GeneralDeclarativeNormalized320.ordered_map children (fun _ _ _ _ h => child_result h))
  obtain ⟨outputs,oc,oe⟩ := collect_result (f := rootFact r interp decl d capture)
    (fun out used => return_result checked visible (results out used))
  refine ⟨decl,capture,head ++ requirements ++ outputs,rfl,visible,captures,bounds,
    by simp [nodeFacts,role,hc,cc,oc],?_⟩
  intro row there
  rcases List.mem_append.mp there with within|output
  · exact (List.mem_append.mp within).elim (he row) (ce row)
  · exact oe row output

theorem derivation_batch (checked : Checked r) (visible : decl ∈ r.declarations)
    (role : decl.role = d.role) (read : Derivation s r interp p d decl capture kids) :
    BatchRecipe s r interp d decl.id kids :=
  attach_head checked visible role read.captures read.bounds
    (GeneralDeclarativeNormalized320.ordered_map read.head (fun _ _ _ _ h => actual_head_row p h))
    read.children read.results

end Yulang.GeneralDeclarativeNodeProducer321
