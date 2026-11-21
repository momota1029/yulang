import Yulang.GeneralDeclarativeSourceCodes321
import Yulang.GeneralDeclarativeNormalizedCompiler321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeConstruct321
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEntailment320 (Entails Holds BatchRecipe appendFacts model_append)
open GeneralDeclarativeNormalizedCompiler321 (HeadWalk normalized_result)
open GeneralDeclarativeCompileLists321 (Result zip_result collect_result)
open GeneralDeclarativeWhereProducer321 (Child child_result)
open GeneralDeclarativeNodeProducer321 (ReturnRead return_result)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeNodeFacts320 (nodeFacts clauseFacts)
open GeneralDeclarativeSourceCodes321 (clauseCodes forest_exact)
open GeneralDeclarativeFreshForest321 (all_children_extension allCodes children)
open GeneralDeclarativeFreshCalls321 (seed)
open GeneralDeclarativeNewNames321 (supply)
open GeneralDeclarativeFresh321 (extend)
open GeneralDeclarations (Checked)
open CommonRoleOutermostResolver (All₂)

theorem lift_result {s : State} {defs : List Equation} (result : Result s code) :
    Result (appendFacts s defs) code := by
  obtain ⟨rows,selected,preserved⟩ := result
  exact ⟨rows,selected,fun row there model fitted =>
    preserved row there model ((model_append model).mp fitted).1⟩

theorem attach {s : State} {capture : Nat → Capture}
    (visible : decl ∈ r.declarations) (role : decl.role = d.role)
    (captures : ∀ binder ∈ decl.inputNames, Bounds s (capture binder))
    (bounds : ∀ arg ∈ d.arguments, Bounds s arg)
    (head : Result s (GeneralDeclarativeBatch320.zipFacts
      (headFact r.constructors interp capture) d.arguments decl.head))
    (children : All₂ (Child s r interp capture) decl.requirements kids)
    (outputs : Result s (GeneralDeclarativeBatch320.collect (rootFact r interp decl d capture) d.outputs)) :
    BatchRecipe s r interp d decl.id kids := by
  obtain ⟨hRows,hCode,hTrue⟩ := head
  obtain ⟨cRows,cCode,cTrue⟩ := zip_result (f := clauseFacts r interp capture)
    (GeneralDeclarativeNormalized320.ordered_map children (fun _ _ _ _ read => child_result read))
  obtain ⟨oRows,oCode,oTrue⟩ := outputs
  refine ⟨decl,capture,hRows++cRows++oRows,rfl,visible,captures,bounds,by simp [nodeFacts,role,hCode,cCode,oCode],?_⟩
  intro row there
  rcases List.mem_append.mp there with before|after
  · exact (List.mem_append.mp before).elim (hTrue row) (cTrue row)
  · exact oTrue row after

/-- Real ordered where names can be constructed instead of postulated,
over a conservative extension of any state. The parent head and root
associated output obligations are independent of this construction. -/
theorem compiled_with_fresh_children {s : State} {p : Supported s completed} (checked : Checked r)
    (visible : decl ∈ r.declarations) (role : decl.role = d.role)
    (head : HeadWalk s p r interp d decl capture seen)
    (captures : ∀ binder ∈ decl.inputNames, Bounds s (capture binder))
    (bounds : ∀ arg ∈ d.arguments, Bounds s arg)
    (outputs : ∀ out ∈ d.outputs, ReturnRead s r interp decl d capture out)
    (compiled : clauseCodes r interp decl.requirements = some tables)
    (old : GeneralNominalCommonBridge.Assignment) (fits : Models s old) (extra : List Nat) :
    let expr := allCodes capture tables
    let defs := supply s extra expr
    let s' := appendFacts s defs
    let kids := children capture (seed s extra expr) decl.requirements tables
    Models s' (extend old defs) ∧
      (∀ name ∈ GeneralDeclarativeFootprint321.stateNames s ++ extra, extend old defs name = old name) ∧
      BatchRecipe s' r interp d decl.id kids := by
  dsimp only
  have untilNow := all_children_extension (s := s) (capture := capture) (extra := extra)
    (forest_exact compiled) old fits
  have hResult := zip_result (f := headFact r.constructors interp capture)
    (s := s) (GeneralDeclarativeNormalized320.ordered_map head.walks (by
      rintro arg _ pat _ ⟨original,normalized,used,h₁,h₂,walk,sub⟩
      exact normalized_result p h₁ h₂ walk (fun occ there => head.shared occ (sub there))))
  have oResult := collect_result (f := rootFact r interp decl d capture) (s := s)
    (fun out used => return_result checked visible (outputs out used))
  exact ⟨untilNow.1,untilNow.2.1,attach visible role captures bounds (lift_result hResult)
    untilNow.2.2 (lift_result oResult)⟩

end Yulang.GeneralDeclarativeConstruct321
