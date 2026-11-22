import Yulang.GeneralDeclarativeWitnessCovariant352
import Yulang.GeneralDeclarativeWitnessLiteral349

namespace Yulang.GeneralDeclarativeWitnessCovariantFixture352
open GeneralDeclarativeWitnessCovariant352
open Core.PresenceGeneration (TyTerm)
open CommonDeclaredNominalInspection (Registry)

def registry : Registry := [covariant]
def arms : List (Arm Nat) := [⟨13,unary 0 (.var 7)⟩,⟨13,unary 0 (.var 8)⟩]
def pattern : GeneralDeclarationPatterns.Pattern := .variant 13 (.app 0 [.join (.var 31) (.var 32)])
def payload : TyTerm Nat := .union (.var 7) (.var 8)
def correct : List (Nat × TyTerm Nat) := [(31,payload),(32,payload)]
def split : List (Nat × TyTerm Nat) := [(31,.var 7),(32,.var 8)]

def checks {α : Type} [DecidableEq α] (r : Registry) (a : List (Arm α))
    (i j tag : Nat) (p : GeneralDeclarationPatterns.Pattern)
    (claimed : List (Nat × TyTerm α)) : Bool := decide (witnessed r a i j tag p = some claimed)

theorem checks_exact {α : Type} [DecidableEq α] (r : Registry) (a : List (Arm α))
    (i j tag : Nat) (p : GeneralDeclarationPatterns.Pattern) (claimed : List (Nat × TyTerm α)) :
    checks r a i j tag p claimed = true ↔ witnessed r a i j tag p = some claimed := decide_eq_true_iff

theorem actual_two_whole_bindings : checks registry arms 0 1 13 pattern correct = true := by decide +kernel

theorem rejects_split_capture : checks registry arms 0 1 13 pattern split = false := by decide +kernel

theorem rejects_same_shape_without_declared_covariance :
    checks [[⟨.value,.invariant⟩]] arms 0 1 13 pattern correct = false := by decide +kernel

theorem rejects_other_tag : checks registry arms 0 1 12 pattern correct = false := by decide +kernel

theorem rejects_unauthored_arm : checks registry arms 0 2 13 pattern correct = false := by decide +kernel

theorem rejects_other_nominal :
    checks registry [⟨13,unary 0 (.var 7)⟩,⟨13,unary 1 (.var 8)⟩] 0 1 13 pattern correct = false := by
  decide +kernel

end Yulang.GeneralDeclarativeWitnessCovariantFixture352
