import Yulang.GeneralDeclarativeTraceCompiler321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNormalizedCompiler321
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models)
open GeneralDeclarativeTrace321 (Occurrence Links)
open GeneralDeclarativeTraceHead321 (Read read_model)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeEntailment320 (Holds BatchRecipe)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeWhereProducer321 (Child)
open GeneralDeclarativeNodeProducer321 (ReturnRead attach_head)
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized translate_value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open CommonRoleOutermostResolver (All₂)

/-- The compiler's original head spelling need not be the spelling the
candidate inspects. It is sound to inspect only the normalized live fields
and then justify the original source equation by semantic normalization. -/
theorem normalized_result (p : Supported s completed)
    (original : translate catalogue interp pattern = some originalCode)
    (normalized : translate catalogue interp (normalize pattern) = some normalizedCode)
    (proof : Read (restriction p) capture arg normalizedCode seen)
    (links : Links (restriction p) capture seen) :
    Result s (headFact catalogue interp capture arg pattern) := by
  refine ⟨[⟨arg.center,logical capture .actual originalCode⟩],by simp [headFact,original],?_⟩
  intro row present m valid
  cases List.mem_singleton.mp present
  simp only [Holds,logical_value]
  have witness := read_model proof links m (restrict_models p m valid)
  rw [translate_value (normalize pattern) normalized] at witness
  have erase := compiled_normalized (variables := variables capture m) original
  exact eqv_trans witness ⟨erase.2,erase.1⟩

structure HeadWalk (s : State) (p : Supported s completed) (r : Registry) (interp)
    (d : Demand) (decl : Declaration) (capture : Nat → Capture) (seen : List Occurrence) : Prop where
  walks : All₂ (fun a pat => ∃ original normalized used,
    translate r.constructors interp pat = some original ∧
    translate r.constructors interp (normalize pat) = some normalized ∧
    Read (restriction p) capture a normalized used ∧ used ⊆ seen) d.arguments decl.head
  shared : Links (restriction p) capture seen

theorem normalized_batch {s : State} {p : Supported s completed} (checked : Checked r)
    (visible : decl ∈ r.declarations) (role : decl.role = d.role)
    (captures : ∀ binder ∈ decl.inputNames, Bounds s (capture binder))
    (bounds : ∀ arg ∈ d.arguments, Bounds s arg)
    (head : HeadWalk s p r interp d decl capture seen)
    (children : All₂ (Child s r interp capture) decl.requirements kids)
    (results : ∀ out ∈ d.outputs, ReturnRead s r interp decl d capture out) :
    BatchRecipe s r interp d decl.id kids := by
  refine attach_head checked visible role captures bounds ?_ children results
  apply GeneralDeclarativeNormalized320.ordered_map head.walks
  rintro a _ pat _ ⟨originalCode,normCode,used,original,normalized,walk,sub⟩
  exact normalized_result p original normalized walk (fun occ h => head.shared occ (sub h))

end Yulang.GeneralDeclarativeNormalizedCompiler321
