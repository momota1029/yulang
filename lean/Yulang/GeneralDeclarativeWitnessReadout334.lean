import Yulang.GeneralDeclarativeWitnessReobserve334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessReadout334
open GeneralDeclarations (Registry Declaration Clause Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeWitnessHead334 (Slice Actuals)
open GeneralDeclarativeWitnessNode334 (Generation Witness)
open GeneralDeclarativeWitnessClassify334 (Rule selected_witness)
open GeneralDeclarativeWitnessStopped334 (same_key_of_visible)
open GeneralDeclarativeCurrentReceipt330 (Receipt)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeOpaqueBatch328 (check check_exact)

/-- Executable comparison of a reported key and literal ordered child
requests with the actual ordinary generator. Comparing full requests,
rather than roles or dictionaries alone, checks centers and fixed
logical targets. Source support and current ordinary derivability
remain separately checked propositions. -/
def replay (r : Registry) (i : Interpretation) (d : Demand) (impl : Declaration)
    (named : State) (spans : List (Nat × Capture)) (protect : List Nat)
    (fallback : Nat → Capture) (targets : Clause → Nat → Nat)
    (reportedKey : Nat) (reportedKids : List Demand) : Option State :=
  if reportedKey = impl.id then
    match compileBody r i d impl named spans protect fallback targets with
    | none => none
    | some (ordinary,generated) => if check generated reportedKids then some ordinary else none
  else none

theorem replay_exact :
    replay r i d impl named spans protect fallback targets key kids = some ordinary ↔
      key = impl.id ∧
        compileBody r i d impl named spans protect fallback targets = some (ordinary,kids) := by
  unfold replay
  by_cases chosen : key = impl.id
  · cases answer : compileBody r i d impl named spans protect fallback targets with
    | none => simp [chosen]
    | some packet =>
      rcases packet with ⟨wrote,expected⟩
      by_cases listOK : check expected kids = true
      · have ordered := check_exact.mp listOK
        cases ordered
        simp [chosen,listOK]
      · have wrong : expected ≠ kids := fun h => listOK (check_exact.mpr h)
        simp [chosen,listOK,wrong]
  · simp [chosen]

/-- Accepting the emitted key/list is only useful if the actual head
proof used for this compile and its ordinary write receipt are linked
to the current state. Neither an old report nor a model supplies those
proofs. In particular, success never changes any requested target. -/
theorem selected_from_replay {s : State} {p : Supported s done}
    (chosen : Elected s r i p (candidates p r i waiting) d impl)
    (slice : Slice p)
    (observed : Actuals slice.support r.constructors i protect slice.base
      d.arguments impl.head named spans)
    (replayed : replay r i d impl named spans protect fallback targets key proposed = some ordinary)
    (here : Receipt ordinary s) :
    Rule p r i waiting d (.selected key proposed) := by
  obtain ⟨rfl,generated⟩ := replay_exact.mp replayed
  exact .selected ⟨⟨slice,protect,fallback,targets,named,spans,observed,ordinary,generated,here⟩,chosen⟩

/-- Independent election distinguishes the choice of declaration from
the choice of legal logical names: every true same-state selection
has the same checked declaration, no matter which receipt is used. -/
theorem chosen_declaration {s : State} {p : Supported s done} (checked : Checked r)
    (first : Witness p r i waiting d a xs) (next : Witness p r i waiting d b ys) :
    a = b :=
  same_key_of_visible checked a b first.chosen.viable.1.1 next.chosen.viable.1.1
    (first.chosen.unique _ next.chosen.viable).symm

theorem chosen_key {s : State} {p : Supported s done} (checked : Checked r)
    (x : Rule p r i waiting d (.selected k xs)) (y : Rule p r i waiting d (.selected j ys)) :
    k = j := by
  obtain ⟨a,rfl,⟨first⟩⟩ := selected_witness x
  obtain ⟨b,rfl,⟨second⟩⟩ := selected_witness y
  exact congrArg Declaration.id (chosen_declaration checked first second)

end Yulang.GeneralDeclarativeWitnessReadout334
