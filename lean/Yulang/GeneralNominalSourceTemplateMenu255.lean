import Yulang.GeneralNominalRawOutputBudget254
import Yulang.GeneralNominalTemplateNormal255
namespace Yulang.GeneralNominalSourceTemplateMenu255
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open Core.PresenceGeneration (TyTerm)
open GeneralNominalMaterialization (Mode)
open GeneralNominalTemplateChoices255 (Raw Materialized choices reads)
open GeneralPresenceCheckedNormal252 (Side)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {state : State roles}

def menu (registry : Registry) (context : GeneralNominalCandidates.Context)
 (root : Occurrence roles) (pool : List (TyTerm Nat)) : List Materialized :=
 (GeneralNominalRawOutputBudget254.templates registry context root).flatMap (choices pool)

/-- Finite materialized output syntax from an actual reachable frame. The
only additional premise is on the finitely many leaf values actually read.
No model or Evidence tree appears in this enumeration theorem. -/
theorem source_compiled
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
 (requested : output ∈ focus.demand.outputs)
 (supplied : Supplies roles plan.packet.declaration output.name body)
 (compiled : GeneralNominalCenteredHeadMatEffects.compileBody plan body = some expression)
 (pool : List (TyTerm Nat)) (variables : Mode → Nat → TyTerm Nat) (mode : Mode)
 (supported : ∀ entry ∈ reads mode expression, variables entry.1 entry.2 ∈ pool) :
 GeneralNominalRebaseEffectView243.compile variables mode expression ∈ menu registry context root pool :=
 List.mem_flatMap.mpr ⟨expression,GeneralNominalRawOutputBudget254.source_template path frame requested supplied compiled,
   GeneralNominalTemplateChoices255.compiled_mem pool variables mode expression supported⟩

theorem source_normalized
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
 (requested : output ∈ focus.demand.outputs)
 (supplied : Supplies roles plan.packet.declaration output.name body)
 (compiled : GeneralNominalCenteredHeadMatEffects.compileBody plan body = some expression)
 (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Mode → Nat → TyTerm Nat) (mode : Mode) :
 GeneralNominalTemplateNormal255.rewrite policy basis variables mode expression ∈
 menu registry context root (GeneralNominalTemplateNormal255.leafCandidates basis) :=
 source_compiled path frame requested supplied compiled _ _ mode
   (fun entry _ => GeneralNominalTemplateNormal255.normalized_candidate policy basis variables entry.1 entry.2)

/-- The check cannot be omitted: normalization can silently discard unsupported
atoms. Actual successful preparation supplies both finite syntax and semantic
preservation for every assignment, not merely a selected witness model. -/
theorem source_prepared
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
 (requested : output ∈ focus.demand.outputs)
 (supplied : Supplies roles plan.packet.declaration output.name body)
 (compiled : GeneralNominalCenteredHeadMatEffects.compileBody plan body = some expression)
 (policy : Mode → Side) (basis : List (TyTerm Nat)) (variables : Mode → Nat → TyTerm Nat) (mode : Mode) (result : Materialized)
 (success : GeneralNominalTemplateNormal255.prepare policy basis variables mode expression = some result)
 (assignment : GeneralNominalCommonBridge.Assignment) :
 result ∈ menu registry context root (GeneralNominalTemplateNormal255.leafCandidates basis) ∧
 Equivalent (GeneralNominalRebaseEffectView243.eval assignment result)
 (GeneralNominalRebaseEffectView243.eval assignment (GeneralNominalRebaseEffectView243.compile variables mode expression)) := by
 obtain ⟨_,rfl⟩ := (GeneralNominalTemplateNormal255.prepare_exact ..).mp success
 exact ⟨source_normalized path frame requested supplied compiled policy basis variables mode,
   (GeneralNominalTemplateNormal255.prepare_safe policy basis variables mode expression _ success assignment).2⟩
end Yulang.GeneralNominalSourceTemplateMenu255
