import Yulang.GeneralDeclarativeWitnessAllocation350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRecordHead350
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeLowerKnown321 (Tag Knows constructorTag)
open GeneralDeclarativeWitnessManifest349 (Manifest Attached support Link link authored)
open GeneralDeclarativeWitnessProjection349 (Checked)
open GeneralDeclarativeInlineTrace331 (Read Fields TailCode)
open GeneralDeclarativeEndpointProgram336 (template)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarationPatterns (Pattern normalize Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeTermWalk322 (Occurrence)
open CommonRoleCanonicalRows (Row normalize residual)

def written (shape : List (Nat × Nat)) : Row Expr :=
  shape.map (fun (key,binder) => (key,.variable binder))

theorem renders (c : Constructors) (i : Interpretation) (shape : List (Nat × Nat)) (tail : Nat) :
    translate c i (template shape tail) = some (withTail (written shape) (.variable tail)) := by
  induction shape with
  | nil => rfl
  | cons item rest ih =>
    obtain ⟨k,b⟩ := item
    simp [template,translate,written,withTail,ih]

theorem fields {s : State} {mode : Mode} {shape : List (Nat × Nat)} {row : Row Expr}
    (labels : row.map Prod.fst = shape.map Prod.fst) :
    ∃ uses, Fields s mode row (written shape) uses := by
  induction shape generalizing row with
  | nil =>
    cases row with
    | nil => exact ⟨[],.nil⟩
    | cons item rest => cases labels
  | cons item rest ih =>
    obtain ⟨key,binder⟩ := item
    cases row with
    | nil => cases labels
    | cons field more =>
      obtain ⟨label,raw⟩ := field
      have parts : label = key ∧ more.map Prod.fst = rest.map Prod.fst := List.cons.inj labels
      obtain ⟨next,holds⟩ := ih parts.2
      cases parts.1
      exact ⟨_ , .cons .capture holds⟩

theorem head {s : State} {manifest : Manifest} {a : Attached s manifest}
    {arg : Capture} {pat : Pattern} (out : Checked a arg pat) (nonempty : out.shape ≠ [])
    (c : Constructors) (i : Interpretation) :
    GeneralDeclarativeTaggedElection340.Head (support a) c i arg pat := by
  have different : out.shape.map Prod.fst ≠ [] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  obtain ⟨lo,knownLo⟩ := fields (mode := .lower) (s := restriction (support a))
    (GeneralDeclarativeWitnessRecord349.exact_labels out.source).1
  obtain ⟨hi,knownHi⟩ := fields (mode := .upper) (s := restriction (support a))
    (GeneralDeclarativeWitnessRecord349.exact_labels out.source).2
  apply GeneralDeclarativeTaggedElection340.Head.old
  refine ⟨out.source.fact.valid,withTail (written out.shape) (.variable out.tail),
    lo ++ [⟨out.tail,.lower,tailExpr out.source.lower (out.shape.map Prod.fst) out.source.lowerEnd⟩],
    hi ++ [⟨out.tail,.upper,tailExpr out.source.upper (out.shape.map Prod.fst) out.source.upperEnd⟩],?_,?_,?_⟩
  · rw [out.pattern]
    exact renders c i out.shape out.tail
  · exact .record (.name out.source.fact.lo) out.source.fact.distinct different
      out.source.fact.displayedLow knownLo .binder .capture
  · exact .record (.name out.source.fact.hi) out.source.fact.distinct different
      out.source.fact.displayedHigh knownHi .binder .capture

structure Seen {s : State} {manifest : Manifest} (a : Attached s manifest) (n : Nat) where
  tag : Tag
  known : Knows (restriction (support a)) n tag

/-- A positive readiness certificate is a genuine authored row, at
a constructor-bearing root and an independently checked alias. -/
def know {s : State} {manifest : Manifest} (a : Attached s manifest) (n idx : Nat)
    (aliased : Link) : Option (Seen a n) := do
  match seen : manifest.sourceRows[idx]? with
  | none => none
  | some e =>
    let proof ← link a n e.left aliased
    match tag : constructorTag e.right with
    | none => none
    | some t => pure ⟨t,e,authored a seen,proof.property,tag⟩

end Yulang.GeneralDeclarativeWitnessRecordHead350
