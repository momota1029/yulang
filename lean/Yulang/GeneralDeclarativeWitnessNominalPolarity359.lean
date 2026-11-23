import Yulang.GeneralDeclarativeWitnessNominalRecordFixture359
import Yulang.GeneralDeclarativeWitnessNominalCompareExact359

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 45000000
namespace Yulang.GeneralDeclarativeWitnessNominalPolarity359
open GeneralDeclarativeWitnessNominalSource359 (Location Route Compared SlotRead)
open GeneralDeclarativeWitnessNominalCompareExact359 (FitsSource scoped_compares_exact)
open GeneralDeclarativeWitnessNominalRecordFixture359
  (ctor slots first last genuine current common_source_model)
open GeneralDeclarativeWitnessRecordWidthFixture359 (lowTy highTy endpoints_ordered lowRest highRest)
open GeneralDeclarativeWitnessRecordWindowFixture358 (payload strict_original_payload_bounds)
open GeneralDeclarativeWitnessCoverageFixture357 (prepare bundle)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (Models)
open CommonNominalFullCarrier (Subtype model)
open PresenceNormalForm (Atom)

def route (negative : Bool) (name : Nat) : Route := .unary (ctor negative) (.bind name)

def source (negative : Bool) : Declaration :=
  ⟨72,5,[.app (if negative then 42 else 20) [.var 80],
         .app (if negative then 42 else 20) [.var 81]],[],[],[]⟩

def prepared (negative : Bool) : Option Environment :=
  prepare {bundle with roles := ⟨0,[⟨5,2,[]⟩]⟩,declarations := [source negative]}

def call (negative : Bool) (e : Environment) :=
  GeneralDeclarativeWitnessNominalSource359.compare e table slots false first last
    (route negative 80) (route negative 81)

def comparisonAtom (negative : Bool) : Atom Nat :=
  if negative then .tyLe (.var 67) (.var 61) else .tyLe (.var 61) (.var 67)

theorem actual_bare_variance (negative : Bool) :
    ((prepared negative).bind fun e => (call negative e).map (fun w => w.run.rows)) =
      some [comparisonAtom negative] := by cases negative <;> decide +kernel

theorem exact_origin_order {negative : Bool} {e : Environment} (read : prepared negative = some e)
    (m : Assignment) :
    FitsSource e table slots false first last (route negative 80) (route negative 81) m ↔
      (comparisonAtom negative).Holds model m := by
  have ran := actual_bare_variance negative
  rw [read] at ran
  change (call negative e).map (fun w => w.run.rows) = _ at ran
  cases snapshot : call negative e with
  | none => rw [snapshot] at ran; cases ran
  | some c =>
    have rows : c.run.rows = [comparisonAtom negative] := by simpa [snapshot] using ran
    rw [← scoped_compares_exact]
    change (∃ w,call negative e = some w ∧ ∀ atom ∈ w.run.rows,atom.Holds model m) ↔ _
    constructor
    · rintro ⟨found,same,every⟩
      rw [snapshot] at same
      have eq := Option.some.inj same
      subst found
      exact every _ (rows.symm ▸ List.mem_cons_self)
    · intro yes
      refine ⟨c,snapshot,?_⟩
      intro atom mem
      rw [rows] at mem
      cases List.mem_singleton.mp mem
      exact yes

theorem high_is_not_subtype_of_low : ¬Subtype highTy lowTy := by
  intro rev
  exact strict_original_payload_bounds (GeneralNominalStructuralProjectionLaws.record_payload
    7 payload (.base .int) highRest lowRest rev)

theorem bare_declared_modes_separate_actual_centers :
    Models current (genuine false true) ∧ Models current (genuine true false) ∧
    (comparisonAtom false).Holds model (genuine false true) ∧
    ¬(comparisonAtom true).Holds model (genuine false true) ∧
    (comparisonAtom true).Holds model (genuine true false) ∧
    ¬(comparisonAtom false).Holds model (genuine true false) :=
  ⟨common_source_model false true,common_source_model true false,
    endpoints_ordered,high_is_not_subtype_of_low,endpoints_ordered,high_is_not_subtype_of_low⟩

/-- These are model-relative comparison results, not an election, refusal or
entailment of either bare point order by the interval constraints alone. -/
theorem same_current_state_does_not_pick_bare_order :
    ¬ (∀ m,Models current m → (comparisonAtom false).Holds model m) ∧
    ¬ (∀ m,Models current m → (comparisonAtom true).Holds model m) :=
  ⟨fun h => bare_declared_modes_separate_actual_centers.2.2.2.2.2
      (h _ (common_source_model true false)),
    fun h => bare_declared_modes_separate_actual_centers.2.2.2.1
      (h _ (common_source_model false true))⟩

end Yulang.GeneralDeclarativeWitnessNominalPolarity359
