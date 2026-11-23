import Yulang.GeneralDeclarativeWitnessNativeWindowWitness362

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 69000
set_option maxHeartbeats 72000000
namespace Yulang.GeneralDeclarativeWitnessInheritedEnvelope362
open GeneralDeclarativeWitnessThreeNative362 (Run run authority ctor)
open GeneralDeclarativeWitnessOrderedNativeRelease362 (Opened read)
open GeneralDeclarativeWitnessNativeInvariantCut362 (wrap)
open GeneralDeclarativeWitnessNativeOrder362 (atom holds_yields_typed_context)
open GeneralDeclarativeWitnessNativeThreeModel362 (every_fit_retains_source_window)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)
open GeneralDeclarativeWitnessNativeValue360 (Code)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled)
open CommonRecursiveNominalIntervals (Endpoint ContextWellFormed)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (subtype_refl subtype_trans)
open PresenceNormalForm (Atom)

def extract (code : Code) : Option (Nat × Nat) :=
  match code with
  | .unary tag (.leaf payload) => some (tag,payload)
  | _ => none

def payloadLower {contra} (r : Run contra) : Code :=
  if contra then r.upper.write.code else r.lower.write.code
def payloadUpper {contra} (r : Run contra) : Code :=
  if contra then r.lower.write.code else r.upper.write.code

def interval (tag lo hi : Nat) : Endpoint Nat :=
  .nominal tag [.inl (.interval (.ordinary (.var lo)) (.ordinary (.var hi)))]

structure Enveloped {contra : Bool} (r : Run contra) where
  permitted : Opened r authority
  a : Nat
  b : Nat
  c : Nat
  lo : extract (payloadLower r) = some (ctor contra,a)
  mid : extract r.center.write.code = some (ctor contra,b)
  hi : extract (payloadUpper r) = some (ctor contra,c)
  ordered : Compiled r.environment table false (wrap (interval (ctor contra) a b))
    (wrap (interval (ctor contra) b c))

/-- A logical envelope assembled from actual separately released
payloads, not an interval Code purportedly written as a native point.
The source polarity determines which authored endpoint contains the
payload lower bound. The center stays fixed by its own writer receipt. -/
def envelope {contra} (r : Run contra) : Option (Enveloped r) := do
  let author ← read r authority
  match lo : extract (payloadLower r), mid : extract r.center.write.code, hi : extract (payloadUpper r) with
  | some (i,a),some (j,b),some (k,c) =>
    if modes : i = ctor contra ∧ j = ctor contra ∧ k = ctor contra then
      let yes ← GeneralDeclarativeWitnessSparseIntervals357.compile r.environment table false
        (wrap (interval (ctor contra) a b)) (wrap (interval (ctor contra) b c))
      pure ⟨author,a,b,c,by simpa [modes.1] using lo,by simpa [modes.2.1] using mid,
        by simpa [modes.2.2] using hi,yes⟩
    else none
  | _,_,_ => none

def allowed : List (Atom Nat) :=
  [atom 60 60,atom 60 61,atom 60 62,atom 61 61,atom 61 62,atom 62 62]

def exact {contra r} (p : @Enveloped contra r) : Bool :=
  decide (p.a = 60 ∧ p.b = 61 ∧ p.c = 62) &&
  p.ordered.rows.all (fun x => decide (x ∈ allowed)) &&
  decide (atom 60 62 ∈ p.ordered.rows) &&
  (GeneralDeclarativeWitnessSparseIntervals357.compile r.environment table false
    (interval (ctor contra) p.a p.b) (interval (ctor contra) p.b p.c)).isNone &&
  (GeneralDeclarativeWitnessSparseIntervals357.compile r.environment
    (table.set (ctor contra) [⟨.value,.invariant⟩]) false
    (wrap (interval (ctor contra) p.a p.b)) (wrap (interval (ctor contra) p.b p.c))).isNone

theorem actual_inherited_envelope_uses_authored_payload_order (contra : Bool) :
    ((run contra).bind fun r => (envelope r).map exact).getD false = true := by cases contra <;> decide +kernel

theorem overlaps_at_the_separately_authored_center {contra} {r : Run contra} {p : Enveloped r}
    (start : run contra = some r) (made : envelope r = some p)
    (m : Assignment) (v : NativeViews) (fit : Fits r.final m v) :
    p.a = 60 ∧ p.b = 61 ∧ p.c = 62 ∧
    ContextWellFormed table false (wrap (interval (ctor contra) p.a p.b)) ∧
    ContextWellFormed table false (wrap (interval (ctor contra) p.b p.c)) ∧
    ContextDerives table m false (wrap (interval (ctor contra) p.a p.b))
      (wrap (interval (ctor contra) p.b p.c)) := by
  have gate := actual_inherited_envelope_uses_authored_payload_order contra
  rw [start] at gate
  change ((envelope r).map exact).getD false = true at gate
  rw [made] at gate
  have h := Bool.and_eq_true_iff.mp (show exact p = true from gate)
  have h := Bool.and_eq_true_iff.mp h.1
  have h := Bool.and_eq_true_iff.mp h.1
  have h := Bool.and_eq_true_iff.mp h.1
  have keys := of_decide_eq_true h.1
  obtain ⟨_,lo,hi⟩ := every_fit_retains_source_window r m v fit
  have actual : ∀ a ∈ p.ordered.rows,a.Holds CommonNominalFullCarrier.model m := by
    intro a present
    have member := of_decide_eq_true (List.all_eq_true.mp h.2 _ present)
    simp only [allowed,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    · exact subtype_refl _
    · exact lo
    · exact subtype_trans lo hi
    · exact subtype_refl _
    · exact hi
    · exact subtype_refl _
  exact ⟨keys.1,keys.2.1,keys.2.2,holds_yields_typed_context p.ordered m actual⟩

end Yulang.GeneralDeclarativeWitnessInheritedEnvelope362
