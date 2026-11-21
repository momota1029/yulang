import Yulang.GeneralDeclarativeInlineCompiler331
import Yulang.GeneralDeclarativeInlineDecl331

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeInlineFixture331
open GeneralDeclarativeInlineDecl331
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeInlineSpine331 (Closed)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeRecordPoints330 (Layout observed usesFrom seed expressions)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeInlineEndpoint331 (Matches)
open GeneralDeclarativeInlineCompiler331 (Source)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeStableReads329 (Heads One weakened)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeGrowth327 (Extends trans facts)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeStableTies329 (rows pairOf)
open GeneralDeclarativeOpaqueCapture328 (choose)
open GeneralDeclarativeClauseBatch327 (prepare Port make)
open GeneralDeclarativeAppliedClause327 (targetsOnly)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativePairDecl326 (clause)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarations (Clause)

abbrev compound : Expr := .primitive .pair [.variable 4,.variable 17]
abbrev terminal : Expr := .primitive .exactEmpty []
abbrev raw : List (Nat × Expr) :=
  [(7,.variable 3),(7,.variable 17),(8,compound),(9,.variable 15)]
abbrev chosen : List (Nat × Expr) := [(7,.variable 3),(8,compound)]
abbrev recorded : List (Nat × Expr) := [(7,.variable 0),(8,.variable 3)]
abbrev rawRow : Equation := ⟨0,withTail raw terminal⟩
abbrev scalar : Equation := ⟨3,.primitive (.scalar .int) []⟩
abbrev sourceRows : List Equation := [rawRow,scalar]
abbrev sourceState : State := ⟨⟨[],[]⟩,sourceRows⟩
abbrev keep : List Nat := [5,6]
abbrev remainder := tailExpr raw [7,8] terminal
abbrev rebuilt := GeneralDeclarativeRecordPoints330.ready sourceState 0 keep chosen remainder
abbrev spans : List (Nat × Capture) := [(0,point 3),(3,point 18),(1,point 19)]
abbrev storedReads : List Equation :=
  [⟨18,compound⟩,⟨19,remainder⟩,⟨0,.record 7 (.variable 3) (.record 8 (.variable 18) (.variable 19))⟩]
abbrev rootWrite : Equation := ⟨6,.variable 19⟩
abbrev leafWrite : Equation := ⟨5,.variable 3⟩
abbrev final := appendFacts (appendFacts rebuilt [rootWrite]) [leafWrite]

def before (done : Nat → Prop) : Supported sourceState done :=
  ⟨fun e origin => e ∈ sourceRows ∧ origin = .source,fun h => h.1⟩

theorem raw_closed (done : Nat → Prop) : Spine (restriction (before done)) 0 raw terminal :=
  .inline (alias_refl _) .exactEnd (from_source _ ⟨List.mem_cons_self,rfl⟩)

def seen (mode : GeneralNominalMaterialization.Mode) : List Occurrence :=
  [⟨0,mode,.variable 3⟩,⟨3,mode,compound⟩,⟨1,mode,remainder⟩]

theorem original (done : Nat → Prop) (mode) :
    Read (restriction (before done)) mode (.variable 0) normalizedExpr (seen mode) :=
  .record (.name (raw_closed done)) (keys := [7,8]) (selected := chosen) (by decide) (by decide) rfl
    (.cons .capture (.cons .capture .nil)) .binder .capture

theorem original_source (done : Nat → Prop) :
    Source (before done) catalogue interpretation root.arguments decl.head :=
  .inline (point_bounded _ _) normal (original done .actual) .nil

theorem exact_material_logic :
    GeneralDeclarativeInlineMaterial331.ordinary sourceState (point 0) keep (seen .actual)
      = [⟨18,compound⟩,⟨19,.record 9 (.variable 15) terminal⟩] ∧
    GeneralDeclarativeInlineAllocation331.captures
      (GeneralDeclarativeInlineMaterial331.seed sourceState (point 0) keep (seen .actual))
      (seen .actual) = spans := ⟨rfl,rfl⟩

theorem actual_heads : Retains sourceState rebuilt keep ∧ Heads rebuilt catalogue interpretation root.arguments decl.head spans := by
  have view := observed (p := before (fun _ => False)) (arg := point 0) (fields := [7,8]) (raw := raw)
    (terminal := terminal) (picked := chosen) (pattern := recorded) (binders := [0,3]) (tailBinder := 1)
    (raw_closed _) (point_bounded _ _) (by decide) rfl (.cons (.cons .nil)) normal keep
  exact ⟨view.1,.cons (rest := []) view.2 .nil⟩

def fallback (_ : Nat) : Capture := point 3
def targets (_ : Clause) (_ : Nat) : Nat := 5
abbrev base (n : Nat) : Capture := choose fallback n spans
abbrev cap := (sourceNames decl (targetsOnly targets) base).input
abbrev ports : List Port := [make rebuilt keep cap clause [.variable 0]]
abbrev place := placement decl.requirements ports targets
abbrev named := sourceNames decl place base

theorem calc_children : children decl named place = [child] := rfl
theorem only_output : collect (one registry interpretation decl root named.input) root.outputs = some [rootWrite] := rfl
theorem prepare_exact : prepare catalogue interpretation keep cap rebuilt decl.requirements = some (rebuilt,ports) := rfl
theorem grows : Extends rebuilt final := trans (facts _ _) (facts _ _)

theorem literal_frame : final.equations = sourceRows ++ storedReads ++ [rootWrite,leafWrite] := rfl

def frame : Frame final registry interpretation root decl [child] :=
  ⟨base,spans,weakened grows actual_heads.2,(by intro _ absent; cases absent),(by
    intro n known
    have who : n ∈ [0,3,1] := known
    simp only [List.mem_cons,List.not_mem_nil,or_false] at who
    rcases who with h|h|h <;> cases h <;> exact point_bounded _ _),
    targets,keep,rebuilt,rebuilt,ports,prepare_exact,grows,[],rfl,
    fun _ h => False.elim (List.not_mem_nil h),[rootWrite],only_output,
    fun _ h => List.mem_append_left _ (List.mem_append_right _ h),rfl⟩

theorem covered : Coverage registry interpretation := by
  constructor
  · intro d inRegistry
    rcases List.mem_cons.mp inRegistry with rfl|rest
    · refine ⟨⟨⟨trivial,⟨trivial,trivial⟩⟩,trivial⟩,?_,?_⟩
      · intro cl needed
        cases List.mem_singleton.mp needed
        refine ⟨⟨trivial,trivial⟩,?_⟩
        intro eq wanted
        cases List.mem_singleton.mp wanted
        trivial
      · intro eq present
        cases List.mem_singleton.mp present
        trivial
    · cases List.mem_singleton.mp rest
      exact ⟨⟨trivial,trivial⟩,fun _ absent => False.elim (List.not_mem_nil absent),
        fun eq found => by cases List.mem_singleton.mp found; trivial⟩
  · intro role name term h
    by_cases isP : role = 1
    · subst role
      by_cases eq : name = 0 <;>
        simp [GeneralDeclarationExamples.roles,GeneralDeclarationExamples.outputRole,eq] at h
    by_cases isC : role = 2
    · subst role
      by_cases eq : name = 1 <;>
        simp [GeneralDeclarationExamples.roles,GeneralDeclarationExamples.outputRole,eq] at h
    by_cases isB : role = 4 <;> simp [GeneralDeclarationExamples.roles,GeneralDeclarationExamples.bareRole,
      GeneralDeclarationExamples.binaryRole,isP,isC,isB] at h

theorem declared : Declared registry root := by
  intro output wanted
  cases List.mem_singleton.mp wanted
  exact ⟨none,rfl⟩

end Yulang.GeneralDeclarativeInlineFixture331
