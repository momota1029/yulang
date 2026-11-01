import YulangClosure.OriginalSourceSyntax

/-!
R218 conditional representation result, not an annotation semantics or resolver.

Source locators: the original source manuscript `docs/yulang-source-type-safety-ja.tex`
§1 (`sec:source`) and §3 (`sec:all-source`, Lambda); selected SG source-rule
construction `2026-10-08-source-generalize-definition-and-proof.md` §§3–5;
`OriginalSourceGeneration.sourceRules`, Lambda's `sourceFormalRole` atom.
The correction in `2026-11-02-source-annotation-elaboration-r217.md`, "Exact
coverage mismatch", separates a value's Effectful wrapper from the TypeRow
directly owned by TypeArrow. The research manuscript/correction is not new
semantic authority.

Only the constructors needed to exhibit that distinction are represented here:
Int, a value wrapper, and a Function with two independently owned arrow rows.
Other annotation constructors, scope resolution, declaration formation, effect
identity arguments, source typing, solving and native execution are omitted.
The two readouts are explicitly external alternatives; neither is claimed to
be the original Yulang meaning or a supported source instance. Thus the result
does not show that actual Yulang annotation resolution is impossible. It only
rules out simultaneously agreeing with these different external choices on
one identical raw source.

The unchanged parent `YulangClosure.SourceProblem.InferenceSoundness`
(`Contracts.lean:128–130`) still needs an independently justified source
annotation interpretation connected to the original Lambda sourceFormalRole
premise. Nothing here constructs that premise or changes `supported`, any
parent quantifier, or the parent's shared witness.
-/
namespace YulangClosure.OriginalAnnotationReconstructionR218

open OriginalSource

/-- A representation fragment with explicit wrapper versus arrow-row ownership. -/
inductive AnnotationTree where
  | int
  | effectful (row : List Nat) (value : AnnotationTree)
  | function (argument : AnnotationTree) (argumentRow resultRow : List Nat)
      (result : AnnotationTree)
  deriving DecidableEq, Repr

/-- One concrete effect-family identity, used only in the external examples. -/
def effectE : Nat := 11

def concreteFormal : Formal :=
  { site := 2, name := 3, annotation := some 7, outerComputation := false }

/-- Actual original syntax, without an added signature or annotation-tree field. -/
def concreteLambda : Source .expression :=
  .lambda { site := 1 } concreteFormal (.varPattern 4 3) (.name { site := 5 } 3)

/-- External alternative A: `([E] int) -> int`, with empty arrow rows. -/
def wrapperArgumentTree : AnnotationTree :=
  .function (.effectful [effectE] .int) [] [] .int

/-- External alternative B: `int -> [E] int`, with a result arrow row. -/
def resultArrowRowTree : AnnotationTree :=
  .function .int [] [effectE] .int

/-- An external table choice, not an implemented original source resolver. -/
def externalReadoutA (annotation : Annotation) : Option AnnotationTree :=
  if annotation = 7 then some wrapperArgumentTree else none

/-- A second external table choice on exactly the same annotation identity. -/
def externalReadoutB (annotation : Annotation) : Option AnnotationTree :=
  if annotation = 7 then some resultArrowRowTree else none

theorem original_lambda_formal_unchanged :
    concreteLambda =
      .lambda { site := 1 } concreteFormal (.varPattern 4 3) (.name { site := 5 } 3) ∧
    concreteFormal.annotation = some 7 ∧ concreteFormal.entry = .value :=
  ⟨rfl, rfl, rfl⟩

/-- These equations retain all three row locations rather than merging them. -/
theorem external_readouts_preserve_row_ownership :
    externalReadoutA 7 =
      some (.function (.effectful [effectE] .int) [] [] .int) ∧
    externalReadoutB 7 =
      some (.function .int [] [effectE] .int) :=
  ⟨rfl, rfl⟩

theorem annotation_trees_distinct : wrapperArgumentTree ≠ resultArrowRowTree := by
  decide

theorem same_annotation_id_distinct_external_readouts :
    externalReadoutA 7 ≠ externalReadoutB 7 := by
  decide

/-- Conditional on incompatible external readouts, no one source-only function
can return both. This does not identify either readout with original semantics. -/
theorem conditional_no_common_source_resolver
    (first second : Annotation → Option AnnotationTree)
    (different : first 7 ≠ second 7) :
    ¬ ∃ resolver : Source .expression → Option AnnotationTree,
      resolver concreteLambda = first 7 ∧ resolver concreteLambda = second 7 := by
  intro ⟨_, agreesFirst, agreesSecond⟩
  exact different (agreesFirst.symm.trans agreesSecond)

theorem no_source_resolver_agrees_with_both_external_readouts :
    ¬ ∃ resolver : Source .expression → Option AnnotationTree,
      resolver concreteLambda = externalReadoutA 7 ∧
      resolver concreteLambda = externalReadoutB 7 :=
  conditional_no_common_source_resolver externalReadoutA externalReadoutB
    same_annotation_id_distinct_external_readouts

end YulangClosure.OriginalAnnotationReconstructionR218
