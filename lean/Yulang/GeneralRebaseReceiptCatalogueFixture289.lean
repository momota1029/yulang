import Yulang.GeneralRebaseReceiptCatalogue289

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29200
set_option maxHeartbeats 19000000
namespace Yulang.GeneralRebaseReceiptCatalogueFixture289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseReceiptFixture289 (wire request endpoint_decision)
open GeneralRebaseReceiptCollision289 (removed removed_checked no_current_frame)
open GeneralRebaseReceiptCatalogue289
open GeneralRebaseReceiptExtract289 (extract effectSummary)
open GeneralNominalVersionedJournal232 (State Effect)

theorem before_footprint : constructorKeys raw = [6,0] := by decide +kernel

theorem after_footprint (choice : Bool) : constructorKeys (current choice).state = [6,0] := by
  cases choice <;> decide +kernel

theorem sealed_before (choice : Bool) :
    boundedWire (registry choice) before (child choice) = some (wire choice before) := by
  unfold boundedWire wire
  change (if agreement (constructorKeys raw) constructors constructors then _ else _) = _
  rw [agreement_refl,ite_eq_left rfl]
  rfl

theorem sealed_after (choice : Bool) :
    boundedWire (registry choice) (after choice) (child choice) = some (wire choice (after choice)) := by
  unfold boundedWire wire
  change (if agreement (constructorKeys (current choice).state) constructors constructors then _ else _) = _
  rw [agreement_refl,ite_eq_left rfl]
  change some { extract (registry choice) (after choice) (child choice) with
      producers := (([effect choice] : List _).filter (fun candidate : Effect roles =>
        agreement (constructorKeys (current choice).state) constructors candidate.registry.constructors)).map effectSummary } = _
  have selector : (fun candidate : Effect roles => agreement (constructorKeys (current choice).state)
      constructors candidate.registry.constructors) (effect choice) = true :=
    agreement_refl _ _
  simp only [List.filter_cons,selector,List.filter_nil]
  rfl

theorem guarded_actual (choice : Bool) {s : State roles} (path : GeneralRebaseReceiptWitness289.ActualPath choice s)
    (ask : GeneralRebaseReceiptWire289.Offer) :
    guarded (registry choice) s (child choice) ask = GeneralRebaseReceiptWire289.check (wire choice s) ask := by
  rcases GeneralRebaseRowActualPaths287.one_or_zero choice s path with rfl | rfl
  · unfold guarded
    rw [sealed_before]
  · unfold guarded
    rw [sealed_after]

theorem observed_collision_blocked :
    guarded (removed 6) (after true) (child true) (request true) = .wrongWorld := by
  have no : ¬ agreement (constructorKeys (current true).state) (removed 6).constructors constructors = true := by
    intro test
    have member : 6 ∈ constructorKeys (current true).state := (after_footprint true).symm ▸ List.mem_cons_self
    have bad := (agreement_exact _ _ _).mp test 6 member
    change none = some (⟨[.row],6⟩ : GeneralDeclarationPatterns.Constructor) at bad
    cases bad
  have empty : boundedWire (removed 6) (after true) (child true) = none := by
    unfold boundedWire
    exact ite_eq_right no
  unfold guarded
  rw [empty]

theorem outside_agrees :
    agreement (constructorKeys (current true).state) (removed 8).constructors constructors = true := by
  apply (agreement_exact _ _ _).mpr
  intro key member
  rw [after_footprint] at member
  rcases List.mem_cons.mp member with rfl | left
  · rfl
  · cases List.mem_singleton.mp left
    rfl

theorem finite_footprint_not_global :
    GeneralDeclarations.Checked (removed 8) ∧
      guarded (removed 8) (after true) (child true) (request true) = .ready ∧
      ∀ key p, ¬ GeneralNominalVersionedEvidence231.Frame (removed 8) (after true).core (child true) key p := by
  refine ⟨removed_checked 8 (by decide),?_,no_current_frame 8⟩
  have actual : boundedWire (removed 8) (after true) (child true) = some (wire true (after true)) := by
    unfold boundedWire
    change (if agreement (constructorKeys (current true).state) (removed 8).constructors constructors
      then some _ else none) = _
    rw [ite_eq_left outside_agrees]
    change some { extract (removed 8) (after true) (child true) with
      producers := (([effect true] : List _).filter (fun candidate : Effect roles =>
        agreement (constructorKeys (current true).state) (removed 8).constructors
          candidate.registry.constructors)).map effectSummary } = _
    have ok : (fun candidate : Effect roles => agreement (constructorKeys (current true).state)
        (removed 8).constructors candidate.registry.constructors) (effect true) = true := outside_agrees
    simp only [List.filter_cons,ok,List.filter_nil]
    rfl
  unfold guarded
  rw [actual]
  exact endpoint_decision true

end Yulang.GeneralRebaseReceiptCatalogueFixture289
