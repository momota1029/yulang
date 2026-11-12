import Yulang.GeneralNominalCycleK2

/-! Actual recurrence edges for different nominal endpoints. Invariance
identifies the actual argument with each endpoint; overlap alone does not.
No nominal body or substituted search value is introduced. -/
namespace Yulang.GeneralNominalCycleEdges

open CommonNominalFullCarrier
open GeneralNominalState

theorem nominal_interval_actual (state : State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models state model) (lower upper : Fin state.base.slots)
    (left right : Descriptor state.base.slots)
    (one : state.nominals lower = some left) (two : state.nominals upper = some right)
    (actual : Ty) (fits : Subtype (model (state.base.source lower)).1 actual ∧
      Subtype actual (model (state.base.source upper)).1) :
    Equivalent actual (model (state.base.source lower)).1 ∧ Equivalent actual (model (state.base.source upper)).1 := by
  obtain ⟨a,_,ha⟩ := valid.2.1 lower left one
  obtain ⟨b,_,hb⟩ := valid.2.1 upper right two
  have sandwiched := GeneralNominalIntervalLaws.nominal_sandwich _ _ a b actual
    (subtype_trans ha.2 fits.1) (subtype_trans fits.2 hb.1)
  exact ⟨⟨subtype_trans sandwiched.1.1 ha.2,subtype_trans ha.1 sandwiched.1.2⟩,
    ⟨subtype_trans sandwiched.2.1 hb.2,subtype_trans hb.1 sandwiched.2.2⟩⟩

theorem nominal_interval_edge (state : State) (parent lower upper : Fin state.base.slots)
    (descriptor left right : Descriptor state.base.slots)
    (recorded : state.nominals parent = some descriptor)
    (one : state.nominals lower = some left) (two : state.nominals upper = some right)
    (index : Nat) (parameter : descriptor.arguments[index]? = some (.type (lower,upper))) :
    GeneralNominalMixedRecurrence.ActualArgument state parent lower ∧
      GeneralNominalMixedRecurrence.ActualArgument state parent upper := by
  have argument (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :=
    GeneralNominalProjections.parameter_binding_valid state model valid parent descriptor recorded index 0
      (.type (lower,upper)) parameter
  constructor
  all_goals
    refine ⟨descriptor,recorded,index,?_⟩
    intro model valid
    obtain ⟨value,seen,fits⟩ := argument model valid
    cases value with
    | inr => cases fits
    | inl actual =>
      have equal := nominal_interval_actual state model valid lower upper left right one two actual fits
      first | exact ⟨actual,seen,equal.1⟩ | exact ⟨actual,seen,equal.2⟩

end Yulang.GeneralNominalCycleEdges
