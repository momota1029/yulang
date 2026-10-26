import YulangClosure.OriginalFormalAdmission
import YulangClosure.OriginalForcedParameter
import YulangClosure.OriginalSourceClosure
import YulangClosure.OriginalReturnWorld
import YulangClosure.OriginalPrincipalityResolution
import YulangClosure.OriginalInferenceTerminationResolution

/-!
Explicit default-build entry for the 2026-10-27 original-source proof work.

The constructive modules interpret source-owned formal declarations, preserve
their selected contract through the actual body consumer, and compute the
world produced by actual forced Return and native binding. The independent
principality module diagnoses missing interface choices; the inference module
constructs raw allocation/Replay chronology. Neither is a whole-language
principality or termination instance.

No original SourceProblem instance is synthesized by these imports. The
remaining original source/primitive interpretation, recursive callable
realization, whole scoped instance order and native inference machine remain
explicit obligations. AuditOriginalClosureProgress.lean checks every originating
theorem, including generated and private declarations, in these six modules.
-/
