import Yulang.CommonDeclarationVarianceTable
import Yulang.CommonDeclarationVarianceLowering

/-!
# Nominal metadata computed from the original declaration equations

Original declaration headers contain only ordered kinds and formal parameter
identities. The occurrence and recursive-use analyses compute every variance
mode; no independently supplied variance table is trusted. The resulting
registry is the exact input type of the existing nominal inspector.

The source judgment below retains each header position and uses the independent
source `Mode` judgment. It does not mention the computed analyses or their
outputs. Assembling the source equations from a whole resolved declaration
collection, and full nominal source construction, are separate obligations.
-/

namespace Yulang.CommonDeclarationVarianceRegistry

open CommonDeclarationVarianceSyntax (Program)
open CommonDeclarationVarianceOccurrences (Universe occurrences)
open CommonDeclarationVarianceGraph (analyze)
open CommonDeclarationVarianceTable (Mode modeFrom mode_from_exact)
open CommonDeclarationVarianceLowering (Header)
open CommonDeclaredNominalInspection (Kind Declaration Registry)

variable {Index Formal : Type} [DecidableEq Index] [DecidableEq Formal]

/-- Compute both finite analyses once and preserve the original formal identity
when selecting its mode. No mode is read from a source header. -/
def modes (program : Program Index Formal) (pool : Universe Index Formal) :
    Formal → CommonDeclaredNominalVariance.Variance :=
  modeFrom program (occurrences program false pool) (analyze program pool)

theorem modes_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (formal : Formal) (mode : CommonDeclaredNominalVariance.Variance) :
    modes program pool formal = mode ↔ Mode program formal mode :=
  mode_from_exact program pool formal mode

def declaration (program : Program Index Formal) (pool : Universe Index Formal)
    (header : Header Formal) : Declaration :=
  header.map fun entry => ⟨entry.1, modes program pool entry.2⟩

def registry (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) : Registry :=
  headers.map (declaration program pool)

def DeclarationJudgment (program : Program Index Formal) :
    Header Formal → Declaration → Prop
  | [], [] => True
  | (kind, formal) :: header, parameter :: rest =>
      kind = parameter.kind ∧ Mode program formal parameter.variance ∧
        DeclarationJudgment program header rest
  | _, _ => False

def RegistryJudgment (program : Program Index Formal) :
    List (Header Formal) → Registry → Prop
  | [], [] => True
  | header :: headers, entry :: entries =>
      DeclarationJudgment program header entry ∧ RegistryJudgment program headers entries
  | _, _ => False

theorem declaration_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (header : Header Formal) (entry : Declaration) :
    declaration program pool header = entry ↔ DeclarationJudgment program header entry := by
  induction header generalizing entry with
  | nil => cases entry <;> simp [declaration, DeclarationJudgment]
  | cons original rest ih =>
      obtain ⟨kind, formal⟩ := original
      cases entry with
      | nil => simp [declaration, DeclarationJudgment]
      | cons parameter tail =>
          obtain ⟨targetKind, mode⟩ := parameter
          simp only [declaration, List.map_cons, List.cons.injEq,
            CommonDeclaredNominalInspection.Parameter.mk.injEq]
          change (kind = targetKind ∧ modes program pool formal = mode) ∧
            declaration program pool rest = tail ↔ _
          rw [modes_exact, ih]
          exact and_assoc

/-- Every proposed registry agrees with the executable producer exactly when
its entire original ordered header has the independently derived source mode.
This includes unused parameters, whose kind and position are still retained. -/
theorem registry_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (result : Registry) :
    registry program pool headers = result ↔ RegistryJudgment program headers result := by
  induction headers generalizing result with
  | nil => cases result <;> simp [registry, RegistryJudgment]
  | cons header headers ih =>
      cases result with
      | nil => simp [registry, RegistryJudgment]
      | cons entry rest =>
          simp only [registry, List.map_cons, List.cons.injEq, declaration_exact,
            RegistryJudgment]
          change DeclarationJudgment program header entry ∧ registry program pool headers = rest ↔ _
          rw [ih]

theorem declaration_preserves_kinds (program : Program Index Formal) (pool : Universe Index Formal)
    (header : Header Formal) :
    (declaration program pool header).map CommonDeclaredNominalInspection.Parameter.kind =
      header.map Prod.fst := by
  simp [declaration, List.map_map, Function.comp_def]

theorem registry_preserves_arity (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) :
    (registry program pool headers).map List.length = headers.map List.length := by
  simp [registry, declaration, List.map_map, Function.comp_def]

end Yulang.CommonDeclarationVarianceRegistry
