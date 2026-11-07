import Yulang.CommonLegacyTyping
import Yulang.CoreCommonInference
import Yulang.CoreSourceInference

/-!
# Actual legacy inference instances survive the new solved common entry

The premise is an instance of the existing executable legacy result. Its
independent typing preservation is followed by the actual new source graph
solver, recovering a returned finite scheme and unrestricted parameters.
The instantiated result row is literally the requested old row, and the value
is demand equivalent to the embedded old result.

This is the preservation direction of decision 46. Reflection of arbitrary
new instances into legacy syntax is a separate theorem; it is not assumed
here and is not encoded into the new scheme or its parameter domain.
-/

namespace Yulang.CommonSolvedLegacyPreservation

open Inference (Expr)
open Core.PresenceGeneration (Comp Typing)
open CommonSolvedSource (Scheme inferSource inferCore ofClause)
open CommonLegacyTyping (oldModel)

/-- A consequence of generated-model retraction that retains both sides of
value equivalence and literal result-row equality, rather than only subsumption. -/
theorem source_typing_retraction (expression : Expr) (result : Comp Common.model)
    (typed : Typing Common.model [] expression result) :
    ∃ scheme ∈ inferSource expression, ∃ parameters : scheme.Parameters,
      Common.Equivalent (scheme.instantiate parameters).1 result.1 ∧
        (scheme.instantiate parameters).2 = result.2 := by
  obtain ⟨clause, generated, assignment, output, accepted⟩ :=
    (PresenceNormalForm.closed_source_exact Common.model expression result).mp typed
  obtain ⟨solution, returned, parameters, same, rowSame⟩ :=
    CommonSolvedSource.source_parameter_retraction expression clause generated assignment accepted
  refine ⟨ofClause clause solution,
    List.mem_flatMap.mpr ⟨clause, generated, List.mem_map.mpr ⟨solution, returned, rfl⟩⟩,
    parameters, ?_, ?_⟩
  · simpa only [output] using same
  · simpa only [output] using rowSame

/-- Every instance of the actual old supported source entry is represented
by a returned new source scheme, with all original result rows unchanged. -/
theorem legacy_source_parameters (expression : Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (result : Inference.Comp oldModel)
    (accepted : (SourcePrincipalInference.infer expression).Instance Common.rowAlgebra result) :
    ∃ scheme ∈ inferSource expression, ∃ parameters : scheme.Parameters,
      Common.Equivalent (scheme.instantiate parameters).1 (Common.embedOld result.1) ∧
        (scheme.instantiate parameters).2 = result.2 :=
  source_typing_retraction expression (Common.embedComp result)
    (CommonLegacyTyping.legacy_instances_preserved expression supported result accepted)

/-- The same recovery lands in the actual public `Core.infer` result. -/
theorem legacy_core_parameters (expression : Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (result : Inference.Comp oldModel)
    (accepted : (SourcePrincipalInference.infer expression).Instance Common.rowAlgebra result) :
    ∃ scheme ∈ Core.infer (Core.Required.embed expression), ∃ parameters : scheme.Parameters,
      Common.Equivalent (scheme.instantiate parameters).1 (Common.embedOld result.1) ∧
        (scheme.instantiate parameters).2 = result.2 := by
  obtain ⟨scheme, member, parameters, same, rowSame⟩ :=
    legacy_source_parameters expression supported result accepted
  refine ⟨scheme, ?_, parameters, same, rowSame⟩
  simpa only [Core.infer_embed, Core.CommonInference.Result.mem_schemes,
    Core.CommonInference.finish_schemes] using member

theorem legacy_instances_preserved (expression : Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (result : Inference.Comp oldModel)
    (accepted : (SourcePrincipalInference.infer expression).Instance Common.rowAlgebra result) :
    (Core.infer (Core.Required.embed expression)).Instance (Common.embedComp result) := by
  obtain ⟨scheme, member, parameters, same, rowSame⟩ :=
    legacy_core_parameters expression supported result accepted
  refine ⟨scheme, member, parameters, same.1, ?_⟩
  change Common.rowLe (scheme.instantiate parameters).2 result.2
  rw [rowSame]
  exact Common.rowLe_refl _

/-- The premise can also name the old executable Core entry itself. -/
theorem legacy_core_entry_parameters (expression : Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (result : Inference.Comp oldModel)
    (accepted : (Core.RequiredInference.infer (Core.Required.embed expression)).Instance
      Common.rowAlgebra result) :
    ∃ scheme ∈ Core.infer (Core.Required.embed expression), ∃ parameters : scheme.Parameters,
      Common.Equivalent (scheme.instantiate parameters).1 (Common.embedOld result.1) ∧
        (scheme.instantiate parameters).2 = result.2 :=
  legacy_core_parameters expression supported result
    ((Core.RequiredInference.legacy_instances_exact Common.rowAlgebra expression result).mp accepted)

theorem legacy_core_entry_preserved (expression : Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (result : Inference.Comp oldModel)
    (accepted : (Core.RequiredInference.infer (Core.Required.embed expression)).Instance
      Common.rowAlgebra result) :
    (Core.infer (Core.Required.embed expression)).Instance (Common.embedComp result) :=
  legacy_instances_preserved expression supported result
    ((Core.RequiredInference.legacy_instances_exact Common.rowAlgebra expression result).mp accepted)

end Yulang.CommonSolvedLegacyPreservation
