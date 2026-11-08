import Yulang.CommonDeclarationVarianceTable
import Yulang.CommonDeclarationVarianceLowering

/-!
# Actual declaration-variance computations

These witnesses start with the existing finite `Body` source syntax. Every
lowered node is checked to succeed, then the actual finite table producer is
evaluated in the kernel. Constructor alternatives contribute all payloads;
the source graph retains concrete arguments, function boundaries, parameter
permutations and internal references. No variance metadata is supplied.

The approved box/box2/reset/stream, chain/mutual recursion and phantom cases
are distinguished. The two regular-reference examples also guard the gap
that a graph containing only named nominal calls would miss.
-/

namespace Yulang.CommonDeclarationVarianceExamples

open CommonDeclarationVarianceSyntax CommonDeclarationVarianceOccurrences CommonDeclarationVarianceTable
open CommonDeclarationVarianceLowering
open CommonNominalFieldTemplates (Body)
open CommonDeclaredNominalVariance (Variance)

deriving instance DecidableEq for Expr

def pool (nodes parameters : Nat) : Universe (Fin nodes) (Fin parameters) where
  indices := List.finRange nodes
  parameters := List.finRange parameters
  indices_complete := List.mem_finRange
  parameters_complete := List.mem_finRange

def scope (nodes parameters : Nat) : Scope (Fin nodes) (Fin parameters) nodes parameters 0 :=
  ⟨id, id, Fin.elim0⟩

def oneHeader : Resolver (Fin 1) := fun name => if name = 0 then some [(.value, 0)] else none

def twoHeaders : Resolver (Fin 2)
  | 0 => some [(.value, 0)]
  | 1 => some [(.value, 1)]
  | _ => none

def fromBodies (bodies : Fin nodes → Body nodes parameters 0) (roots : Fin parameters → Fin nodes)
    (resolve : Resolver (Fin parameters)) : Program (Fin nodes) (Fin parameters) where
  body index := (lower (scope nodes parameters) resolve (bodies index)).getD .empty
  root := roots

def LoweringVerified (bodies : Fin nodes → Body nodes parameters 0) (roots : Fin parameters → Fin nodes)
    (resolve : Resolver (Fin parameters)) : Prop :=
  ∀ index, lower (scope nodes parameters) resolve (bodies index) =
    some ((fromBodies bodies roots resolve).body index)

def boxBody : Fin 1 → Body 1 1 0 := fun _ => .parameter 0
def box := fromBodies boxBody (fun _ => 0) oneHeader

theorem box_checked : LoweringVerified boxBody (fun _ => 0) oneHeader ∧
    deriveVariance box (pool 1 1) = [(0, .covariant)] := by
  unfold LoweringVerified
  decide

def phantomBody : Fin 1 → Body 1 1 0 := fun _ =>
  .union .emptyRecord (.nominal 0 [.inl (.inr 0)])
def phantom := fromBodies phantomBody (fun _ => 0) oneHeader

theorem phantom_checked : LoweringVerified phantomBody (fun _ => 0) oneHeader ∧
    deriveVariance phantom (pool 1 1) = [(0, .unused)] := by
  unfold LoweringVerified
  decide

end Yulang.CommonDeclarationVarianceExamples
