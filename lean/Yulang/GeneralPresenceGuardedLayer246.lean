import Yulang.CommonNominalFullGuardedClosure
import Yulang.GeneralPresenceModelCongruence245
import Yulang.GeneralPresenceUsedSupport245

/-! A guarded fragment compiled into actual Presence type terms. References
occur only in payload positions. Row expressions remain actual Presence rows.
This is not an encoding of all source terms or a source acceptance restriction. -/
namespace Yulang.GeneralPresenceGuardedLayer246
open Core.PresenceGeneration

inductive Layer (Name Ref : Type) where
  | base : Inference.Base → Layer Name Ref
  | bottom : Layer Name Ref
  | top : Layer Name Ref
  | union : Layer Name Ref → Layer Name Ref → Layer Name Ref
  | inter : Layer Name Ref → Layer Name Ref → Layer Name Ref
  | pair : Ref → Ref → Layer Name Ref
  | emptyRecord : Layer Name Ref
  | exactEmpty : Layer Name Ref
  | required : Nat → Ref → Layer Name Ref
  | record : Nat → Ref → Layer Name Ref → Layer Name Ref
  | recordDefault : Nat → Layer Name Ref → Ref → Layer Name Ref
  | variant : Nat → Ref → Layer Name Ref
  | arrow : Ref → RowTerm Name → Ref → RowTerm Name → Layer Name Ref

def translate (rename : Ref → Name) : Layer Name Ref → TyTerm Name
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union a b => .union (translate rename a) (translate rename b)
  | .inter a b => .inter (translate rename a) (translate rename b)
  | .pair a b => .pair (.var (rename a)) (.var (rename b))
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .required label child => .required label (.var (rename child))
  | .record label child rest => .record label (.var (rename child)) (translate rename rest)
  | .recordDefault label source fallback =>
      .recordDefault label (translate rename source) (.var (rename fallback))
  | .variant label child => .variant label (.var (rename child))
  | .arrow a incoming b outgoing => .arrow (.var (rename a)) incoming (.var (rename b)) outgoing

def lower (assignment : Name → Comp CommonNominalFullCarrier.model) :
    Layer Name Ref → CommonNominalSyntax.Layer Common.Row Ref
  | .base scalar => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union a b => .union (lower assignment a) (lower assignment b)
  | .inter a b => .inter (lower assignment a) (lower assignment b)
  | .pair a b => .pair a b
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .required label child => .record label child .emptyRecord
  | .record label child rest => .record label child (lower assignment rest)
  | .recordDefault label source fallback => .recordDefault label (lower assignment source) fallback
  | .variant label child => .variant label child
  | .arrow a incoming b outgoing =>
      .arrow a (incoming.eval CommonNominalFullCarrier.model assignment)
        b (outgoing.eval CommonNominalFullCarrier.model assignment)

theorem eval_bridge (rename : Ref → Name)
    (assignment : Name → Comp CommonNominalFullCarrier.model) (layer : Layer Name Ref) :
    (translate rename layer).eval CommonNominalFullCarrier.model assignment =
      (lower assignment layer).map
        (fun ref => CommonNominalSyntax.State.node (assignment (rename ref)).1) := by
  induction layer <;>
    simp_all only [translate,lower,TyTerm.eval,CommonNominalSyntax.Layer.map,
      CommonNominalFullCarrier.model,CommonNominalFullCarrier.pair,
      CommonNominalFullCarrier.required,CommonNominalFullCarrier.record,
      CommonNominalFullCarrier.recordDefault,CommonNominalFullCarrier.variant,
      CommonNominalFullCarrier.arrow]

theorem lower_rows (first last : Name → Comp CommonNominalFullCarrier.model)
    (equal : ∀ name, (first name).2 = (last name).2) (layer : Layer Name Ref) :
    lower first layer = lower last layer := by
  induction layer <;> simp_all only [lower,
    GeneralPresenceModelCongruence245.row_eval_equal _ first last equal]

/-- Payload references, with multiplicity and left-to-right order. -/
def references : Layer Name Ref → List Ref
  | .union a b | .inter a b => references a ++ references b
  | .pair a b | .arrow a _ b _ => [a,b]
  | .required _ child | .variant _ child => [child]
  | .record _ child rest => [child] ++ references rest
  | .recordDefault _ source fallback => references source ++ [fallback]
  | _ => []

def rowReferences : Layer Name Ref → List Name
  | .union a b | .inter a b => rowReferences a ++ rowReferences b
  | .record _ _ rest => rowReferences rest
  | .recordDefault _ source _ => rowReferences source
  | .arrow _ incoming _ outgoing =>
      GeneralPresenceSubstitutionSupport244.rowSources incoming ++
      GeneralPresenceSubstitutionSupport244.rowSources outgoing
  | _ => []

theorem typed_reads_translate (rename : Ref → Name) (layer : Layer Name Ref) :
    GeneralPresenceUsedSupport245.typedReads (translate rename layer) =
      (references layer).map rename := by
  induction layer <;> simp_all [translate,references,GeneralPresenceUsedSupport245.typedReads]

theorem row_reads_translate (rename : Ref → Name) (layer : Layer Name Ref) :
    GeneralPresenceUsedSupport245.rowReads (translate rename layer) = rowReferences layer := by
  induction layer <;> simp_all [translate,rowReferences,GeneralPresenceUsedSupport245.rowReads]

theorem sources_translate (rename : Ref → Name) (layer : Layer Name Ref) (name : Name) :
    name ∈ GeneralPresenceSubstitutionSupport244.typeSources (translate rename layer) ↔
      name ∈ (references layer).map rename ∨ name ∈ rowReferences layer := by
  rw [GeneralPresenceUsedSupport245.sources_split,typed_reads_translate,row_reads_translate]

end Yulang.GeneralPresenceGuardedLayer246
