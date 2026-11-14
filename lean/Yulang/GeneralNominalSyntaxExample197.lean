import Yulang.GeneralNominalSyntaxRefresh197
import Yulang.GeneralNominalTraceEvidence197

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalSyntaxExample197
open GeneralNominalFinishedObservation197
open GeneralNominalSyntaxRefresh197
open GeneralNominalTraceRefreshExample197
open GeneralNominalExecutableView196 (next start finish certificate)
open GeneralNominalRefreshFork (context)
open GeneralDeclarationExamples (roles)

theorem query_syntax : Syntax query := by
  apply Syntax.nominal
  intro q member
  have equal := List.mem_singleton.mp member
  subst q
  apply Syntax.nominal
  intro q member
  have equal := List.mem_singleton.mp member
  subst q
  exact .variables

theorem registry_syntax : RegistrySyntax registry (context none) := by
  intro decl member q present
  have equal := List.mem_singleton.mp member
  subst decl
  rw [computed_query] at present
  have equal := List.mem_singleton.mp present
  subst q
  exact query_syntax

/-- Only syntactic query membership is supplied: Finished comes from the actual
source dictionary, and nominal preservation from the actual refresh certificate. -/
theorem final_payload (wide : Bool) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredHeadStepEffects.Models (finish wide) model) :
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry (finish wide)
      model focus payload :=
  universal_refresh (state := start) (next := next wide) (certificate wide) registry_syntax
    GeneralNominalTraceEvidence197.source_payload model valid

/-- This complete-payload transport is not a vacuous implication. -/
theorem inhabited (wide : Bool) :
    GeneralNominalCenteredHeadStepEffects.Models (finish wide) GeneralNominalRefreshFork.model ∧
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry (finish wide)
      GeneralNominalRefreshFork.model focus payload :=
  ⟨(GeneralNominalExecutableView196.inhabited wide).2,
    final_payload wide _ (GeneralNominalExecutableView196.inhabited wide).2⟩

/-- A deferred query is not silently included by the syntactic check. -/
theorem deferred_excluded (label : GeneralDeclarationPatterns.Pattern) : ¬ Syntax (.deferred label) := by
  intro given
  cases given
end Yulang.GeneralNominalSyntaxExample197
