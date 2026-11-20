import Yulang.GeneralRebaseDepthPublic285

/-! A mapped source expression can acquire a read of the row field without
reading any type at that coordinate. The mapping is a compiler test, not an
assertion that the fixture's raw input is an arrow. -/
namespace Yulang.GeneralRebaseSourceRowRegression285
open Core.PresenceGeneration (TyTerm CompTerm)
open GeneralDictionaryOutputDepth252 (plan rhs)
open GeneralRebaseDepthReads285 (explicit translated equation_emitted)
open GeneralRebaseCoordinateProfile285 (Profile ofBody ofEquation)
open GeneralNominalRebaseEffectView243 (body eval Equation)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)

abbrev arr : TyTerm Nat := .arrow .top (.var 7) .top .empty

def mapping (n : Nat) : CompTerm Nat :=
  if n = 2 then ⟨arr,.var 2⟩ else CompTerm.var n

abbrev arrowEquation : Equation := ⟨.var 3,.nominal 0 [.nominal 0 [.source arr]]⟩

theorem materialized : body plan mapping 3 explicit = some arrowEquation := by
  have mapBody : GeneralNominalRebaseEffectView243.bodyVariables plan mapping explicit .actual 0 = arr := by
    change GeneralNominalRebaseEffectView243.variables plan mapping .actual 0 = arr
    have bind : plan.binder 0 = 2 :=
      (GeneralNominalVersionedFrame231.binder_eq plan 0).symm.trans GeneralDictionaryOutputDepth252.binder_exact
    unfold GeneralNominalRebaseEffectView243.variables
    split <;> rw [bind] <;> rfl
  unfold body
  rw [translated]
  simp only [Option.map_some,GeneralNominalRebaseEffectView243.compile,
    GeneralNominalRebaseEffectView243.compileMany,mapBody]
  rfl

theorem coordinate_separation : ofEquation plan mapping 3 explicit = some ⟨[3],[7]⟩ := by
  rw [GeneralRebaseCoordinateProfile285.ofEquation_exact,materialized]
  rfl

def first : Assignment := fun _ => (.top,Common.rowEmpty)
def changed : Assignment := fun n => (.top,if n = 7 then (fun _ => True) else Common.rowEmpty)

theorem arrow_changes :
    arr.eval model first ≠ arr.eval model changed := by
  intro bad
  change CommonNominalSyntax.Layer.arrow (CommonNominalSyntax.State.node (Row := Common.Row) .top) Common.rowEmpty (CommonNominalSyntax.State.node (Row := Common.Row) .top) Common.rowEmpty =
      CommonNominalSyntax.Layer.arrow (CommonNominalSyntax.State.node (Row := Common.Row) .top) (fun _ => True) (CommonNominalSyntax.State.node (Row := Common.Row) .top) Common.rowEmpty at bad
  have wrong := congrFun (CommonNominalSyntax.Layer.arrow.inj bad).2.1 (0,[])
  exact Eq.mp wrong.symm True.intro

theorem nested_changes :
    eval first arrowEquation.expression ≠ eval changed arrowEquation.expression := by
  intro bad
  have inject (a b : CommonNominalFullCarrier.Ty)
      (h : CommonNominalFullCarrier.nominal 0 [.inl a] =
        CommonNominalFullCarrier.nominal 0 [.inl b]) : a = b := by
    simpa [CommonNominalFullCarrier.nominal] using h
  apply arrow_changes
  exact inject _ _ (inject _ _ bad)

theorem no_type_only_profile :
    (∀ n, (first n).1 = (changed n).1) ∧ arr.eval model first ≠ arr.eval model changed :=
  ⟨fun _ => rfl,arrow_changes⟩

end Yulang.GeneralRebaseSourceRowRegression285
