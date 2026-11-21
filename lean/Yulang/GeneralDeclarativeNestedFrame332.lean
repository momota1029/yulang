import Yulang.GeneralDeclarativeNestedMaterial332
import Yulang.GeneralDeclarativeNestedBody332
import Yulang.GeneralDeclarativeNestedDecl332
import Yulang.GeneralDeclarativeVisibleCode325

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDeclarativeNestedFrame332
open GeneralDeclarativeNestedExample332
open GeneralDeclarativeNestedDecl332
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeNestedDecode332 (normalized_sound)
open GeneralDeclarativeNestedMaterial332 (assemble computed_frame)
open GeneralDeclarativeNestedBody332 (compileBody compiler_exact)
open GeneralDeclarativeInlineMaterial331 (named ordinary)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeStableReads329 (One Heads weakened)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeGrowth327 (Extends trans facts)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeStableTies329 (pairOf)
open GeneralDeclarativeOpaqueBatch328 (check)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeVisibleCode325 (codes_were_covered)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarationExamples (constructors roles outputRole)
open GeneralDeclarations (Clause)

abbrev keep := [5,6]
abbrev namedStage := named state (point 0) keep (uses .actual)
abbrev capturedExpr : Expr := .record 7 (.variant 4
  (.primitive .pair [.variable 3,.record 3 (.nominal 0 [.variable 11]) (.variable 16)])) (.variable 17)
abbrev stage := appendFacts namedStage [⟨0,capturedExpr⟩]
abbrev spans : List (Nat × Capture) := [(0,point 3),(3,point 11),(4,point 16),(1,point 17)]
abbrev rootWrite : Equation := ⟨6,.variable 17⟩
abbrev childWrite : Equation := ⟨5,.variable 3⟩
def fallback (_ : Nat) : Capture := point 3
def targets (_ : Clause) (_ : Nat) : Nat := 5

abbrev grouped := GeneralDeclarativeStableAssemble329.merged stage keep spans fallback
abbrev rootStage := appendFacts grouped.state [rootWrite]
abbrev final := appendFacts rootStage [childWrite]

theorem exact_stage :
    assemble state (point 0) keep normalizedExpr (uses .actual) = some (stage,spans) := rfl

theorem actual_read (done : Nat → Prop) :
    Read (restriction (supports done)) .actual (.variable 0) normalizedExpr (uses .actual) := by
  obtain ⟨code,written,source⟩ := normalized_sound (actual_center done)
  have eq := Option.some.inj (written.symm.trans normal)
  exact eq ▸ source

theorem exact_observed (done : Nat → Prop) :
    Retains state stage keep ∧ One stage constructors interpretation (point 0) pat spans ∧
    ordinary state (point 0) keep (uses .actual) ⊆ stage.equations ∧
    (∀ o ∈ spans, Bounds stage o.2) ∧
    ∀ m, Models stage m ↔ Models namedStage m :=
  computed_frame (point_bounded _ _) normal (actual_read done) exact_stage

theorem heads (done : Nat → Prop) : Heads stage constructors interpretation root.arguments decl.head spans :=
  .cons (rest := []) (exact_observed done).2.1 .nil

theorem covered : Coverage registry interpretation := by
  constructor
  · intro d visible
    rcases List.mem_cons.mp visible with rfl|last
    · refine ⟨(codes_were_covered (xs := [normalizedExpr])
        (show GeneralNominalCenteredHeadMatExpressions.translateMany constructors interpretation [pat] = _ from rfl)).1,?_,?_⟩
      · intro cl known
        cases List.mem_singleton.mp known
        refine ⟨⟨trivial,trivial⟩,?_⟩
        intro eq member
        cases List.mem_singleton.mp member
        trivial
      · intro eq member
        cases List.mem_singleton.mp member
        trivial
    · cases List.mem_singleton.mp last
      exact ⟨⟨trivial,trivial⟩,fun _ absent => False.elim (List.not_mem_nil absent),
        fun eq found => by cases List.mem_singleton.mp found; trivial⟩
  · intro role name term h
    by_cases isP : role = 1
    · subst role
      by_cases eq : name = 0 <;> simp [roles,outputRole,eq] at h
    by_cases isC : role = 2
    · subst role
      by_cases eq : name = 1 <;> simp [roles,outputRole,eq] at h
    by_cases isB : role = 4 <;>
      simp [roles,GeneralDeclarationExamples.bareRole,GeneralDeclarationExamples.binaryRole,isP,isC,isB] at h

theorem declared : Declared registry root := by
  intro out wanted
  cases List.mem_singleton.mp wanted
  exact ⟨none,rfl⟩

theorem exact_children_and_writes :
    compileBody registry interpretation root decl stage spans keep fallback targets =
      some (rootStage,[child]) := rfl

theorem no_target_swap : check [child] [⟨2,[⟨18,3,19⟩],[⟨1,6⟩]⟩] = false := rfl

theorem root_frame (done : Nat → Prop) : Nonempty (Frame rootStage registry interpretation root decl [child]) := by
  obtain ⟨actual,kids,frame,computed,_,_,_,_,_,_⟩ := compiler_exact checked covered
    (show decl ∈ registry.declarations from List.mem_cons_self)
    rfl declared keep fallback targets (heads done) (exact_observed done).2.2.2.1
  have exact := Option.some.inj (computed.symm.trans exact_children_and_writes)
  cases exact
  exact ⟨frame⟩

end Yulang.GeneralDeclarativeNestedFrame332
