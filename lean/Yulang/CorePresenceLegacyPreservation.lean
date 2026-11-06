import Yulang.CorePresenceGenerationCore
import Yulang.InferenceModelMap
import Yulang.SourcePrincipalInference

/-!
# Preservation of legacy instances under a presence extension

Changing the empty-record expression from the width bound to `exactEmpty`
does not preserve its generating term by literal equality.  The two judgments
are related directly instead: exact emptiness lies below the width bound, and
the legacy singleton-field demand agrees with `required`.

The result below covers every original typing derivation, both value-let
alternatives, captured polymorphic environments, and explicit signatures.
Together with an actual model embedding it preserves every instance of the
legacy solved inference entry.  A concrete embedding and reflection modulo
demand equivalence are separate obligations, not premises hidden in an
instance definition.
-/

namespace Yulang.Core.PresenceGeneration.LegacyPreservation

open Inference (Expr)

universe u v w

variable (m : Model.{u, v})

/-- These are the two additional compatibility laws needed by the changed
source rules.  The inherited width record is not redefined as exact empty. -/
structure Compatible : Prop where
  trans {a b c : m.Ty} : m.subTy a b → m.subTy b c → m.subTy a c
  exactEmpty_width : m.subTy m.exactEmpty m.emptyRecord
  required_eq (label : Nat) (payload : m.Ty) :
    m.record label payload m.emptyRecord = m.required label payload

def binding (m : Model.{u, v}) : Inference.Binding m.toModel → Binding m
  | .mono computation => .mono computation
  | .poly expression environment => .poly expression (environment.map (binding m))
  | .signature count instantiate => .signature count instantiate

/-- Every old derivation over the inherited carrier survives the additional
presence source rules.  No syntax fragment or solver-success premise occurs. -/
theorem typing_preserved (compatible : Compatible m)
    {environment : List (Inference.Binding m.toModel)} {expression : Inference.Expr}
    {result : Inference.Comp m.toModel}
    (typed : Inference.Typing m.toModel environment expression result) :
    Typing m (environment.map (binding m)) expression result := by
  induction typed using Inference.Typing.rec
    (motive_2 := fun b c _ => BindingTyping m (binding m b) c) with
  | var found _ ih => exact .var (by simp [List.getElem?_map, found]) ih
  | lit bounded => exact .lit bounded
  | lam _ bounded body =>
      exact .lam (by simpa [binding] using body) bounded
  | app _ _ bounded function argument => exact .app function argument bounded
  | letValue value _ _ definition body =>
      exact .letValue value definition (by simpa [binding] using body)
  | letComputed _ _ bounded definition body =>
      exact .letComputed definition (by simpa [binding, Comp.pure, Inference.Comp.pure] using body)
        bounded
  | branch _ _ _ bounded condition yes no => exact .branch condition yes no bounded
  | pair _ _ bounded left right => exact .pair left right bounded
  | fst _ bounded pair => exact .fst pair bounded
  | snd _ bounded pair => exact .snd pair bounded
  | emptyRecord bounded =>
      exact .emptyRecord ⟨compatible.trans compatible.exactEmpty_width bounded.1, bounded.2⟩
  | record _ _ admissible bounded head tail => exact .record head tail admissible bounded
  | field _ bounded record =>
      exact .field (by simpa only [compatible.required_eq] using record) bounded
  | variant _ bounded payload => exact .variant payload bounded
  | mono bounded => simpa only [binding] using BindingTyping.mono bounded
  | poly _ row body => simpa only [binding] using BindingTyping.poly body row
  | signature bounded => simpa only [binding] using BindingTyping.signature bounded

theorem closed_typing_preserved (compatible : Compatible m) (expression : Inference.Expr)
    (result : Inference.Comp m.toModel)
    (typed : Inference.Typing m.toModel [] expression result) :
    Typing m [] expression result :=
  typing_preserved m compatible typed

/-- A constructor-preserving map supplies the old subtype preservation; only
the two changed source rules then need the compatibility laws above. -/
theorem closed_typing_mapped {old : Inference.Model.{w, v}}
    (map : Inference.ModelMap old m.toModel) (compatible : Compatible m)
    (expression : Inference.Expr) (result : Inference.Comp old)
    (typed : Inference.Typing old [] expression result) :
    Typing m [] expression (map.comp result) :=
  closed_typing_preserved m compatible expression _
    (map.closed_typing_preserved expression result typed)

/-- One-way preservation for the actual legacy inference entry, every old
supported source and every old result value/row.  The conclusion is the
independent new judgment; it is not defined as a closure of old instances.
The concrete model map is an explicit remaining integration dependency. -/
theorem legacy_instances_preserved {Row : Type v}
    (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {a b}, algebra.le a b → algebra.le b a → a = b)
    (map : Inference.ModelMap (SourcePrincipalInference.model algebra) m.toModel)
    (compatible : Compatible m) (expression : Inference.Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (result : Inference.Comp (SourcePrincipalInference.model algebra))
    (accepted : (SourcePrincipalInference.infer expression).Instance algebra result) :
    Typing m [] expression (map.comp result) :=
  closed_typing_mapped m map compatible expression result
    ((SourcePrincipalInference.infer_instances_exact algebra rowAntisymm expression supported result).mp
      accepted)

theorem legacy_core_instances_preserved (m : Model.{0, 0}) {Row : Type}
    (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {a b}, algebra.le a b → algebra.le b a → a = b)
    (map : Inference.ModelMap (SourcePrincipalInference.model algebra) m.toModel)
    (compatible : Compatible m) (expression : Inference.Expr)
    (supported : SourcePrincipalInference.supported expression = true)
    (result : Inference.Comp (SourcePrincipalInference.model algebra))
    (accepted : (SourcePrincipalInference.infer expression).Instance algebra result) :
    Core.Typing (CoreRules.model m) [] (Required.embed expression) (map.comp result) := by
  exact CoreRules.preserved
    (legacy_instances_preserved m algebra rowAntisymm map compatible expression supported result accepted)

end Yulang.Core.PresenceGeneration.LegacyPreservation
