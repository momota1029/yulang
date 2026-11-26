import Yulang.GeneralDeclarativeI65I74MixedFixedTypedRead442
import Yulang.GeneralNominalState

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedFixed442
open GeneralDeclarativeI65
open CommonNominalFullCarrier (Ty Equivalent Subtype nominal subtype_refl subtype_trans)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Descriptor Denotes FitsAll)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

/-- The existing older descriptor semantics genuinely preserves heterogeneous
nominal arguments. Row equality is not equality of the type at its name. -/
theorem two_kind_ref_equivalent_iff442 {k l : Nat} {a b : Common.Row} {x y : Ty} :
    Equivalent (nominal k [.inr a,.inl x]) (nominal l [.inr b,.inl y]) ↔
      k = l ∧ a = b ∧ Equivalent x y := by
  constructor
  · intro eq
    have args := (CommonNominalFullCarrier.nominal_regular_invariant_exact _ _ _ _).mp eq.1
    exact ⟨args.1,args.2.2 0 (.inr a) (.inr b) rfl rfl,
      args.2.2 1 (.inl x) (.inl y) rfl rfl⟩
  · rintro ⟨rfl,rfl,eq⟩
    have below (first last : Ty) (same : Equivalent first last) :
        Subtype (nominal k [.inr a,.inl first]) (nominal k [.inr a,.inl last]) := by
      apply (CommonNominalFullCarrier.nominal_regular_invariant_exact _ _ _ _).mpr
      refine ⟨rfl,rfl,?_⟩
      intro i u v hu hv
      cases i with
      | zero =>
        have hu := Option.some.inj hu
        have hv := Option.some.inj hv
        subst u; subst v
        rfl
      | succ i =>
        cases i with
        | zero =>
          have hu := Option.some.inj hu
          have hv := Option.some.inj hv
          subst u; subst v
          exact same
        | succ i => simp at hu
    exact ⟨below x y eq,below y x ⟨eq.2,eq.1⟩⟩

/-- An exact adapter lemma for an actually recorded mixed point descriptor.
This old relation holds at the assignment target and not merely the View,
but its separate State/Models are not a field or consequence of I72.Fits. -/
theorem existing_mixed_descriptor_point_exact442 (base : GeneralSourceState.State)
    (m : Assignment) (root e a : Fin base.slots) (descriptor : Descriptor base.slots)
    (typed : descriptor.arguments = [.row (e,e),.type (a,a)]) :
    Denotes base m root descriptor ↔ Equivalent (m (base.source root)).1
      (nominal descriptor.declaration.name [.inr (m (base.rowSource e)).2,.inl (m (base.source a)).1]) := by
  constructor
  · rintro ⟨xs,found,rootEq⟩
    rw [typed] at found
    cases found with
    | cons he rest =>
      cases rest with
      | cons ha tail =>
        cases tail
        rename_i row value
        cases row with
        | inl _ => exact False.elim he
        | inr row =>
          cases value with
          | inr _ => exact False.elim ha
          | inl value =>
            have sameRow := Common.rowLe_antisymm he.2 he.1
            have sameValue : Equivalent value (m (base.source a)).1 := ⟨ha.2,ha.1⟩
            have equiv := (two_kind_ref_equivalent_iff442 (k := descriptor.declaration.name)
              (l := descriptor.declaration.name)).mpr ⟨rfl,sameRow,sameValue⟩
            exact ⟨subtype_trans rootEq.1 equiv.1,subtype_trans equiv.2 rootEq.2⟩
  · intro eq
    refine ⟨[.inr (m (base.rowSource e)).2,.inl (m (base.source a)).1], ?_, eq⟩
    rw [typed]
    exact .cons ⟨Common.rowLe_refl _,Common.rowLe_refl _⟩
      (.cons ⟨subtype_refl _,subtype_refl _⟩ .nil)

/-- If a producer's existing legacy nominal-state *typed descriptor* is retained,
its physical names have to be proven to be precisely the original target
and the two original captures. The distinct rowSource projection matters. -/
structure ExistingMixedCompanion {s : I72.State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} {i : Fin q.demand.outputs.length}
    (output : OriginalOutput (s := s) f i) (companion : GeneralNominalState.State) where
  root : Fin companion.base.slots
  rowPosition : Fin companion.base.slots
  valuePosition : Fin companion.base.slots
  descriptor : Descriptor companion.base.slots
  actual : companion.nominals root = some descriptor
  catalogue : companion.constructors = (authoredRegistry s.core.current).constructors
  constructorKey : descriptor.constructor = output.key
  nominalKey : descriptor.declaration.name = output.key
  ordered : descriptor.arguments = [.row (rowPosition,rowPosition),.type (valuePosition,valuePosition)]
  target : companion.base.source root = q.demand.outputs[i].target
  rowCenter : companion.base.rowSource rowPosition = output.rowCap.center
  valueCenter : companion.base.source valuePosition = output.valueCap.center

theorem existing_companion_has_independent_typed_fixed_equality442
    {s : I72.State} {q : Request} {f : AuthoredBodyFrame393 s.core q}
    {i : Fin q.demand.outputs.length} {out : OriginalOutput (s := s) f i} {graph}
    (kept : ExistingMixedCompanion out graph) (m : I72.Model)
    (valid : GeneralNominalState.Models graph m.assignment) :
    ∃ v, out.named.receipt.actualEquation m = some (q.demand.outputs[i].target,v) ∧
      Equivalent (m.assignment q.demand.outputs[i].target).1 v := by
  apply (original_output_fixed_iff_same_target_equals_mixed_value442 out m).mpr
  have real := GeneralNominalState.nominal_models graph m.assignment valid _ _ kept.actual
  have exactEq := (existing_mixed_descriptor_point_exact442 graph.base m.assignment
    kept.root kept.rowPosition kept.valuePosition kept.descriptor kept.ordered).mp real
  simpa only [kept.target,kept.rowCenter,kept.valueCenter,kept.nominalKey,OriginalOutput.actualValue]
    using exactEq

theorem existing_companion_and_original_Fits_are_separate442
    {s : I72.State} {q : Request} {f : AuthoredBodyFrame393 s.core q}
    {i : Fin q.demand.outputs.length} {out : OriginalOutput (s := s) f i}
    (bad : I72.Model) (fit : I72.Fits s bad)
    (missing : ¬Equivalent (bad.assignment q.demand.outputs[i].target).1 (out.actualValue bad))
    {graph} (kept : ExistingMixedCompanion out graph) :
    ¬∀ m, I72.Fits s m → GeneralNominalState.Models graph m.assignment := by
  intro all
  obtain ⟨v,receipt,eq⟩ := existing_companion_has_independent_typed_fixed_equality442 kept bad (all bad fit)
  exact missing ((original_output_fixed_iff_same_target_equals_mixed_value442 out bad).mp ⟨v,receipt,eq⟩)

end Yulang.GeneralDeclarativeI65.I72.MixedFixed442
