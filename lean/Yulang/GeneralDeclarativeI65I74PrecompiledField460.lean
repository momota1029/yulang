import Yulang.GeneralDeclarativeI65I74CompiledChild460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open GeneralNominalCenteredHeadMatExpressions (Expr)
open AuthoredInspectQuery456 (AuthoredQuery)
open RecordTraversal455.MixedQA (MixedPath)
open GeneralDeclarativeInspect321 (Inspects)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open InlineStructuralPolicy458 (policy)
open RoutedMixed456 (endsAtField)

/-- Independent state-indexed trace: the selected syntax/query pair stays
aligned down to the terminal. The code of an unvisited sibling is not an
additional input to the path checker. -/
inductive CompiledTrail (s : CoreState) :
    Nat → Term → Expr → MixedPath → Nat → Term → Bool → Prop
  | stop : AuthoredQuery s (writeTerm t) e → Inspects e →
      CompiledTrail s root t e [] root t false
  | down : AuthoredQuery s (writeTerm t) e →
      ¬ AliasCycle s.current.ordinary (observed s.current.ordinary) root →
      AuthenticatedHop458.AtStep s.current.ordinary (policy s) root e a child q used →
      Step (queryKeys s) t (writtenAddress a) u →
      CompiledTrail s child u q rest terminal last other →
      CompiledTrail s root t e ((a,child)::rest) terminal last (used || other)

theorem descend_actual_compiler_alignment {s align root t e path terminal last used}
    (compiled : AuthoredQuery s (writeTerm t) e)
    (pathProof : JointTrail s.current.ordinary (policy s) (fun _ => queryKeys s)
        align root t e path terminal last used) :
    CompiledTrail s root t e path terminal last used := by
  induction pathProof with
  | stop _ rigid => exact .stop compiled rigid
  | down _ safe raw written _ ih =>
    have copied := raw
    obtain ⟨_,_,_,_,_,rawChild,_⟩ := copied
    have child := same_authored_compilation_at_selected_child compiled written rawChild
    exact .down compiled safe raw written (ih child)

/-- This alignment adapter carries no claims; actual compiled alignment
comes only from the independently supplied root compiler derivation. The
wire has no per-node translation program and runs no recursive recompilation. -/
def inheritedCompilerPlacement : Alignment where
  Token := Unit
  exactAt := fun _ _ _ => True
  checks := fun _ _ _ _ => true
  reflects := fun _ _ _ => ⟨fun _ => trivial,fun _ => ⟨(),rfl⟩⟩

theorem compiled_trace_has_structural_joint_trace {s root t e path terminal last used}
    (trace : CompiledTrail s root t e path terminal last used) :
    JointTrail s.current.ordinary (policy s) (fun _ => queryKeys s)
      inheritedCompilerPlacement root t e path terminal last used := by
  induction trace with
  | stop _ rigid => exact .stop trivial rigid
  | down _ safe raw selected _ ih => exact .down trivial safe raw selected ih

abbrev CompilerFieldWire (s : CoreState) := JointFieldWire (policy s) inheritedCompilerPlacement

def readAlreadyCompiledField (s : CoreState) (root : Nat) (t : Term) (e : Expr)
    (w : CompilerFieldWire s) : Option (MixedPath × Nat × Term) :=
  readJointField s.current.ordinary (policy s) (fun _ => queryKeys s)
    inheritedCompilerPlacement root t e w

def CompiledField (s : CoreState) (root : Nat) (t : Term) (e : Expr)
    (path : MixedPath) (terminal : Nat) (last : Term) : Prop :=
  (∃ used, CompiledTrail s root t e path terminal last used) ∧
  endsAtField path terminal = true ∧ AliasCycle s.current.ordinary (observed s.current.ordinary) terminal

theorem precompiled_field_iff_exact_finite_path {s root t e path terminal last}
    (rootCompile : AuthoredQuery s (writeTerm t) e) :
    (∃ w, readAlreadyCompiledField s root t e w = some (path,terminal,last)) ↔
      CompiledField s root t e path terminal last := by
  unfold readAlreadyCompiledField CompiledField
  rw [read_joint_field_exact]
  constructor
  · rintro ⟨⟨used,walk⟩,field,raw⟩
    exact ⟨⟨used,descend_actual_compiler_alignment rootCompile walk⟩,field,raw⟩
  · rintro ⟨⟨used,walk⟩,field,raw⟩
    exact ⟨⟨used,compiled_trace_has_structural_joint_trace walk⟩,field,raw⟩
theorem compiled_field_keeps_same_fit {s : I72.FullState} {root t e path terminal last}
    (found : CompiledField s.base.core root t e path terminal last)
    (m : I72.Model) (fit : I72.FitsFull s m) :
    ∃ used, RoutedInlineStructural458.ModelTrail s.base.core m root e path terminal used ∧
      CoordinateWalk (fun _ => queryKeys s.base.core) root t path terminal last ∧
      AliasCycle s.base.core.current.ordinary (observed s.base.core.current.ordinary) terminal := by
  obtain ⟨⟨used,trace⟩,ends,raw⟩ := found
  refine exact_joint_field_has_same_fit_evidence (align := inheritedCompilerPlacement) ?_ m fit
  exact ⟨⟨used,compiled_trace_has_structural_joint_trace trace⟩,ends,raw⟩

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
