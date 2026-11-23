import Yulang.GeneralDeclarativeWitnessNativeLeafClassify361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 62000
set_option maxHeartbeats 60000000
namespace Yulang.GeneralDeclarativeWitnessNativeLeafSound361
open GeneralDeclarativeWitnessNativeDirectSource361 (actualWire)
open GeneralDeclarativeWitnessNativePortTransport361 (Port transport view Part every_projected_endpoint_is_the_released_value)
open GeneralDeclarativeWitnessNativeLeafClassify361 (Choice Local choose declarative_leaf actual_compiler_agrees_on_declaration)
open GeneralDeclarativeWitnessSequentialReceiver361 (Received receive exact_run_is_inhabited read_in_every_final_model model)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence sequence)
open GeneralDeclarativeWitnessNativePipeline360 (authority)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessReleasedForward360 (originalBody)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews interpreted)
open GeneralDeclarativeWitnessReleasedObservation360 (observe actualRead)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeWitnessLiteral349 (preserves_iff)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify)

structure End {negative : Bool} {r : Run negative} (s : Sequence r) where
  port : Port s authority actualWire
  choice : Choice port
  received : Received s
  readChecked : receive s = some received

def terminal {negative} {r : Run negative} (s : Sequence r) : Option (End s) := do
  let port ← transport s authority actualWire
  let chosen ← choose port
  match out : receive s with
  | none => none
  | some last => some ⟨port,chosen,last,out⟩

def record {negative r s} (t : @End negative r s) : Bool :=
  decide (t.choice.impl.id = 75 ∧ t.choice.binder = 92 ∧
    (t.received.span.lower,t.received.span.center,t.received.span.upper) = (116,101,117)) &&
  (t.choice.observed.path ==
    [(55,.invariant),(if negative then 42 else 20,.declaredValue (if negative then .contravariant else .covariant))])

theorem actual_leaf_is_positively_checked (negative : Bool) :
    ((originalBody negative).bind fun r => (sequence r).bind fun s => (terminal s).map record).getD false = true := by
  cases negative <;> decide +kernel

/-- Soundness in an arbitrary single fitted assignment of the actual
returned state, not in separate assignments for native and ordinary
children. The only elected dictionary here is the exact scoped leaf. -/
theorem dictionary_sound {negative} {r : Run negative} {s : Sequence r}
    (root : originalBody negative = some r) (sent : sequence r = some s)
    (t : End s) (m : Assignment) (v : NativeViews) (fit : Fits t.received.world m v) :
    Classify (Local t.port) s.receiver (.selected (.node t.choice.impl.id [])) ∧
    t.received.prepared.impl = t.choice.impl ∧
    (∀ which : Part, view t.port v which = some (r.typed.write.code.eval m)) ∧
    Holds m ⟨105,.variable 61⟩ ∧
    (v t.received.span.center).bind (fun value => observe value (actualRead negative)) = some (m 61).1 ∧
    t.received.body.fixed = [] ∧ t.received.body.kids = [] := by
  have prior : Fits s.final m v :=
    ⟨restrict ((preserves_iff ..).mp t.received.kept) m fit.1,fit.2⟩
  have exact := read_in_every_final_model root sent t.received m v fit
  exact ⟨declarative_leaf t.choice,actual_compiler_agrees_on_declaration rfl t.choice t.received,
    every_projected_endpoint_is_the_released_value t.port m v prior,
    exact.2.1,exact.1,t.received.noWrites,t.received.noKids⟩

theorem real_scoped_leaf_with_one_fitted_model (negative : Bool) :
    ∃ (r : Run negative) (s : Sequence r) (t : End s),
      originalBody negative = some r ∧ sequence r = some s ∧ terminal s = some t ∧
      t.choice.impl.id = 75 ∧ t.choice.binder = 92 ∧
      Classify (Local t.port) s.receiver (.selected (.node 75 [])) ∧
      (∀ upper scalar,Fits t.received.world (model upper scalar)
        (interpreted t.received.world.board (model upper scalar))) ∧
      ∀ m v, Fits t.received.world m v →
        Holds m ⟨105,.variable 61⟩ ∧
        (v t.received.span.center).bind (fun value => observe value (actualRead negative)) = some (m 61).1 := by
  obtain ⟨r,s,out,root,sent,ran,_,_,_,_,fitOld⟩ := exact_run_is_inhabited negative
  have test := actual_leaf_is_positively_checked negative
  rw [root] at test
  change ((sequence r).bind fun s => (terminal s).map record).getD false = true at test
  rw [sent] at test
  change ((terminal s).map record).getD false = true at test
  cases check : terminal s with
  | none => rw [check] at test; cases test
  | some t =>
    rw [check] at test
    have same : t.received = out := Option.some.inj (t.readChecked.symm.trans ran)
    have gates := of_decide_eq_true (Bool.and_eq_true_iff.mp (show record t = true from test)).1
    have fit (u : Bool) (k : Inference.Base) :
        Fits t.received.world (model u k) (interpreted t.received.world.board (model u k)) := by
      rw [same]; exact fitOld u k
    have one := dictionary_sound root sent t _ _ (fit false .int)
    refine ⟨r,s,t,root,sent,check,gates.1,gates.2.1,?_,fit,?_⟩
    · rw [← gates.1]; exact one.1
    · intro m v exactFit
      have direct := dictionary_sound root sent t m v exactFit
      exact ⟨direct.2.2.2.1,direct.2.2.2.2.1⟩

end Yulang.GeneralDeclarativeWitnessNativeLeafSound361
