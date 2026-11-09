import Yulang.CommonRoleNormalizedDiagnostic
import Yulang.CommonRoleDiagnosticCanonicalBoundary
import Yulang.CommonRoleNormalizedGlobalChoices

/-! Regression for the semantically equal direct/indirect scalar presentations.
The claim is the full ordered tree, for every registry, source root and table,
not a claim that arbitrary semantically equivalent states share this decoder. -/
namespace Yulang.CommonRoleNormalizedDiagnosticCheck
open CommonRoleDiagnosticCanonicalBoundary
open CommonRoleEvidenceNormalization (normalize)
open CommonRoleEvidenceSaturation (Derived)

 theorem indirect_derived (i : Fin 2) : Derived indirect (i,.int) := by
  apply (CommonRoleEvidenceSaturation.saturate_exact indirect _).mp
  revert i
  decide

 theorem direct_derived (i : Fin 2) : Derived direct (i,.int) := by
  apply (CommonRoleEvidenceSaturation.saturate_exact direct _).mp
  revert i
  decide

/-- The earlier direct-evidence counterexample is repaired for all source trees. -/
theorem repaired_tree (registry : CommonRoleOpenProducer.Registry)
    (root : CommonRoleMaterializedDomain.SourceRequest 2)
    (table : CommonRoleGlobalChoices.Table registry root) :
    CommonRoleDiagnosticTree.diagnose registry root table (normalize indirect) =
      CommonRoleDiagnosticTree.diagnose registry root table (normalize direct) := by
  obtain ⟨a,hi,hd⟩ := consistent
  exact CommonRoleNormalizedDiagnostic.tree_derived registry root table table (fun _ => Iff.rfl)
    indirect direct (fun i => ⟨fun _ => direct_derived i, fun _ => indirect_derived i⟩)
    a a hi hd

def leaf : CommonRoleSettledSyntax.Declaration := ⟨0, 0, .atom .int, []⟩
def registry : CommonRoleOpenProducer.Registry := ⟨[leaf], by
  intro d h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  subst d
  decide, by decide⟩
def root : CommonRoleMaterializedDomain.SourceRequest 2 := ⟨0, .slot 0, .slot 0⟩
def table : CommonRoleGlobalChoices.Table registry root :=
  [(CommonRoleCorrelatedPaths.start registry root,leaf)]

/-- The actual candidate guard now recognizes the int leaf through the
ordinary equality chain. This is not itself a language classification. -/
theorem normalized_candidate_repairs :
    CommonRoleGuardedEquations.candidate indirect root leaf = false ∧
    CommonRoleGuardedEquations.candidate (normalize indirect) root leaf = true := by
  decide
end Yulang.CommonRoleNormalizedDiagnosticCheck
