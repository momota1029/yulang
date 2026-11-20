import Yulang.GeneralMixedDiagnosticCompiler304
import Yulang.GeneralRebaseArchiveConflict280

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedDiagnosticArchive304
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralDeferredLadderResnapshot304 (HeadView)
open GeneralMixedDiagnosticSlice304 (Semantics)
open GeneralMixedDiagnosticHead304 (boundary8)
open GeneralRebaseArchiveTrust280 (Correspond changeEffects archive)

variable {roles : Roles.RoleDecls} {s : State roles} {replacement : List (Effect roles)}

theorem head (pair : Correspond s.effects replacement) :
    HeadView s (changeEffects s replacement) :=
  ⟨⟨rfl,rfl,rfl,(archive s pair).models⟩,rfl,rfl⟩

theorem slices (pair : Correspond s.effects replacement) : Semantics s (changeEffects s replacement) :=
  ⟨GeneralRebaseArchiveConflict280.history pair,fun focus m _ =>
    GeneralRebaseArchiveConflict280.class_equations pair focus m⟩

/-- Existing C280 archive compression now discharges the current-head
observer contract for the entire V8 priority classifier and recursive tree. -/
theorem same_tree (pair : Correspond s.effects replacement) (reg : Registry)
    (o : Occurrence roles) (tree : Tree) :
    Resolves (B4TargetV8.Local (boundary8 roles) reg s) o tree ↔
      Resolves (B4TargetV8.Local (boundary8 roles) reg (changeEffects s replacement)) o tree :=
  GeneralMixedDiagnosticCompiler304.recursive_iff (head pair) (slices pair) reg o tree

theorem reuse_compiler (pair : Correspond s.effects replacement) (reg : Registry)
    (o : Occurrence roles) (x : GeneralRebaseDiagnosticData268.Inputs (Occurrence roles))
    (valid : GeneralRebaseDiagnosticData268.Valid (boundary8 roles) reg s o x)
    (complete : GeneralRebaseDiagnosticV8268.Complete x) (result : Frontier (Occurrence roles)) :
    GeneralRebaseDiagnosticV8268.run x = some result ↔
      B4TargetV8.Local (boundary8 roles) reg (changeEffects s replacement) o result :=
  GeneralMixedDiagnosticCompiler304.compiler_exact (head pair) (slices pair) reg o x valid complete result

end Yulang.GeneralMixedDiagnosticArchive304
