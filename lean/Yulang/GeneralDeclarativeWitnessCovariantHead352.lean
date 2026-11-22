import Yulang.GeneralDeclarativeWitnessCovariantFixture352

namespace Yulang.GeneralDeclarativeWitnessCovariantHead352
open GeneralDeclarationPatterns (Pattern normalize)
open CommonDeclaredNominalInspection (Registry)
open GeneralDeclarativeWitnessCovariant352 (Bindings covariant matchBindings witnessed)
open GeneralDeclarativeWitnessCovariantFixture352 (registry arms correct split payload pattern)

structure JoinedHead (r : Registry) (raw : Pattern) where
  tag : Nat
  box : Nat
  left : Pattern
  right : Pattern
  extracted : normalize raw =
    .variant tag (.join (.app box [left]) (.app box [right]))
  declared : r[box]? = some covariant

/-- A declaration-directed *additional* head read for the approved unary
covariant case. First use the real base normalizer and check two separate
whole tagged arms; combine the binder patterns only for the same declared
covariant constructor. This is not a change to the global normalizer. -/
def joinedHead (r : Registry) (raw : Pattern) : Option (JoinedHead r raw) :=
  match actual : normalize raw with
  | .variant tag (.join (.app first [left]) (.app last [right])) =>
    if names : first = last then
      if declared : r[first]? = some covariant then
        some ⟨tag,first,left,right,by simpa only [← names] using actual,declared⟩
      else none
    else none
  | _ => none

def JoinedHead.pattern {r : Registry} {raw : Pattern} (h : JoinedHead r raw) : Pattern :=
  .variant h.tag (.app h.box [.join h.left h.right])

def fromWritten {α : Type} (r : Registry) (authors : List (GeneralDeclarativeWitnessCovariant352.Arm α))
    (a b : Nat) (actual : Pattern) : Option (List (Nat × Core.PresenceGeneration.TyTerm α)) := do
  let head ← joinedHead r actual
  witnessed r authors a b head.tag head.pattern

def rawPattern : Pattern :=
  .join (.variant 13 (.app 0 [.var 31])) (.variant 13 (.app 0 [.var 32]))

theorem basic_normalizer_keeps_two_boxes :
    normalize rawPattern = .variant 13 (.join (.app 0 [.var 31]) (.app 0 [.var 32])) := by
  decide +kernel

theorem not_yet_lowered_by_base_normalizer :
    (matchBindings rawPattern 13 0).isNone = true := by decide +kernel

theorem actual_written_head_checked :
    fromWritten registry arms 0 1 rawPattern = some correct := by decide +kernel

theorem cannot_split_written_head :
    fromWritten registry arms 0 1 rawPattern ≠ some split := by decide +kernel

theorem no_nominal_without_declared_covariance :
    fromWritten [[⟨.value,.invariant⟩]] arms 0 1 rawPattern = none := by decide +kernel

theorem unequal_nominal_names :
    fromWritten registry arms 0 1 (.join (.variant 13 (.app 0 [.var 31]))
      (.variant 13 (.app 1 [.var 32]))) = none := by decide +kernel

end Yulang.GeneralDeclarativeWitnessCovariantHead352
