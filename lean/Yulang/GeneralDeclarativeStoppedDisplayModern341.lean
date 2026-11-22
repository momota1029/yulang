import Yulang.GeneralStoppedDisplayOriginal335
import Yulang.GeneralDeclarativeTaggedDictionary340

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeStoppedDisplayModern341
open GeneralNominalExamples (registry interpretation intDisplay)
open GeneralDeclarationExamples (display)
open GeneralStoppedDisplayProjection335 (parentDemand listRow scalarRow)
open GeneralStoppedDisplayCut335 (reminted)
open GeneralStoppedDisplayExtended335 (expanded augmented)
open GeneralStoppedDisplayGuard335 (waiting)
open GeneralStoppedDisplayExtendedChoice335 (mark bound_mark src_original elect_parent elect_child)
open GeneralStoppedDisplayChoice335 (right_of_row)
open GeneralStoppedDisplayOriginal335 (rootWitness childWitness)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeTaggedElection340 (Head Match Election Ranked tests)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeWitnessHead334 (Actuals)
open GeneralDeclarativeTaggedInputs340 (Inputs)
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (All₂)

theorem ranked : Ranked expanded mark := by
  refine ⟨fun b => Nat.le_of_eq (bound_mark b),?_,?_⟩
  · intro a b got
    rcases List.mem_cons.mp got with l|tail
    · cases l
    · cases List.mem_singleton.mp tail
  · intro row found n used _
    rcases List.mem_cons.mp found with rfl|tail
    · have which : n = 1 := List.mem_singleton.mp used
      subst n
      change mark 1 < mark 0
      decide +kernel
    · cases List.mem_singleton.mp tail
      cases used

theorem no_tag (h : GeneralDeclarativeTaggedSources340.Read (augmented done) name tag payload) : False := by
  obtain ⟨_,⟨owner,_,row⟩,decoded⟩ := h.source
  rcases right_of_row (src_original row) with ⟨_,rfl⟩|⟨_,rfl⟩ <;> cases decoded

theorem to_prior {arg : GeneralDeclarativeWhere319.Capture}
    (single : d.arguments = [arg])
    (seen : (tests (augmented done) registry interpretation waiting).viable d impl) :
    (candidates (augmented done) registry interpretation waiting).viable d impl := by
  change All₂ (Head (augmented done) registry.constructors interpretation) d.arguments impl.head at seen
  rw [single] at seen
  cases pos : impl.head with
  | nil => rw [pos] at seen; cases seen
  | cons p rest =>
    rw [pos] at seen
    cases seen with
    | cons head tail =>
      cases tail
      change All₂ (GeneralDeclarativeEndpointProbe321.Matches (restriction (augmented done))
        registry.constructors interpretation) d.arguments impl.head ∨
        All₂ (GeneralDeclarativeInlineEndpoint331.Matches (restriction (augmented done))
          registry.constructors interpretation) d.arguments impl.head
      rw [single,pos]
      cases head with
      | merged h =>
        obtain ⟨_,_,_,_,_,_,reads,_,_,_⟩ := h.reads
        exact (no_tag reads.lower).elim
      | old h => exact .inr (.cons h .nil)
      | named h => exact .inl (.cons h .nil)

theorem from_named
    (xs : All₂ (GeneralDeclarativeEndpointProbe321.Matches (restriction (augmented done))
      registry.constructors interpretation) as ps) :
    All₂ (Head (augmented done) registry.constructors interpretation) as ps := by
  induction xs with
  | nil => exact .nil
  | cons h _ ih => exact .cons (.named h) ih

theorem from_inline
    (xs : All₂ (GeneralDeclarativeInlineEndpoint331.Matches (restriction (augmented done))
      registry.constructors interpretation) as ps) :
    All₂ (Head (augmented done) registry.constructors interpretation) as ps := by
  induction xs with
  | nil => exact .nil
  | cons h _ ih => exact .cons (.old h) ih

theorem promote {arg : GeneralDeclarativeWhere319.Capture} (single : d.arguments = [arg]) (chosen : Elected expanded registry interpretation (augmented done)
      (candidates (augmented done) registry interpretation waiting) d impl) :
    Election (augmented done) registry interpretation waiting d impl := by
  refine ⟨fun a used => Or.inl (chosen.ready a used),⟨mark,ranked⟩,chosen.clear,?_,?_⟩
  · refine ⟨chosen.viable.1,?_⟩
    rcases chosen.viable.2 with a|b
    · exact from_named a
    · exact from_inline b
  · intro other viable
    exact chosen.unique other ⟨viable.1,to_prior single viable.2⟩

theorem input_bridge {p : Supported s done}
    (inputs : Actuals p c i keep before as pats after spans) :
    Inputs p c i keep before as pats after spans [] := by
  induction inputs with
  | nil => exact .nil
  | cons first rest ih => exact .cons (.prior (.old first)) ih

def current {p : Supported expanded done} (w : GeneralDeclarativeWitnessNode334.Witness p registry interpretation waiting d impl kids)
    (now : Election p registry interpretation waiting d impl)
    (compiled : GeneralDeclarativeNestedBody332.compileBody registry interpretation d impl w.named w.spans w.protect
      w.fallback w.targets = some (w.ordinary,kids)) :
    Selected p [] registry interpretation waiting d impl kids :=
  ⟨w.slice,w.protect,w.named,w.spans,[],input_bridge w.source,w.fallback,w.targets,w.ordinary,
    compiled,w.receipt,fun _ h => h,now⟩

noncomputable def parent (done : Nat → Prop) :
    Selected (augmented done) [] registry interpretation waiting parentDemand display [reminted] :=
  current (rootWitness done) (promote rfl (elect_parent done)) GeneralStoppedDisplayExtended335.written

def child (done : Nat → Prop) :
    Selected (augmented done) [] registry interpretation waiting reminted intDisplay [] :=
  current (childWitness done) (promote rfl (elect_child done)) GeneralStoppedDisplayExtended335.child_compiles

end Yulang.GeneralDeclarativeStoppedDisplayModern341
