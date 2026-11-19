import Yulang.GeneralRebaseRawBoundedK2269

namespace Yulang.GeneralRebaseRawActualProbe269
open GeneralNominalState (State Models)
open GeneralNominalMixedRecurrence (Edge ActualArgument)
open GeneralRebaseActualArguments269 (actual_of_empty_models)
open GeneralRebaseSlotInequalities269 (Bound)
open GeneralRebaseRawBoundedK2269 (NominalBounded nominal nominal_sound bounded_exact)
open GeneralRebasePartialBool268 (Reflect Answer either neg)
open GeneralRebasePartialFinite268 (transfer)
open GeneralRebaseRawK2Probe268 (Probes Sound bool_reflect)

def fullNominal (state : State) (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (model : Answer) (a b : Fin state.base.slots) : Answer :=
 if (state.nominals a).isSome then either (neg model) (nominal state bound a b)
 else some false

theorem fullNominal_sound (state : State) (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (cert : ∀ a b, Reflect (Bound state a b) (bound a b))
 (model : Answer) (modelSound : Reflect (∃ m, Models state m) model) (a b : Fin state.base.slots) :
 Reflect (ActualArgument state a b) (fullNominal state bound model a b) := by
 unfold fullNominal
 split
 · rename_i existsD
   cases found : state.nominals a with
   | none => simp [found] at existsD
   | some d =>
     apply transfer (p := (¬ ∃ m, Models state m) ∨ NominalBounded state a b)
     · constructor
       · intro help
         rcases help with empty | bounded
         · exact actual_of_empty_models state a b d found empty
         · exact GeneralRebaseRawBoundedK2269.bounded_sound state a b bounded
       · intro actual
         by_cases inhabited : ∃ m, Models state m
         · exact Or.inr ((bounded_exact state inhabited a b).mpr actual)
         · exact Or.inl inhabited
     · exact GeneralRebasePartialBool268.either_sound
         (GeneralRebasePartialBool268.neg_sound modelSound) (nominal_sound state bound cert a b)
 · rename_i missing
   intro actual
   obtain ⟨_,hit,_⟩ := actual
   exact missing (by simp [hit])

def edge (state : State) (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (model : Answer) (a b : Fin state.base.slots) : Answer :=
 either (some (decide (b ∈ CommonRoleRegularGraph.successors state.view.graph a)))
   (fullNominal state bound model a b)

theorem edge_sound (state : State) (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (cert : ∀ a b, Reflect (Bound state a b) (bound a b))
 (model : Answer) (modelSound : Reflect (∃ m, Models state m) model) (a b : Fin state.base.slots) :
 Reflect (Edge state a b) (edge state bound model a b) :=
 GeneralRebasePartialBool268.either_sound
   (bool_reflect _ _ (by simpa only [decide_eq_true_eq] using (GeneralSourceK2.child_graph_iff state.view a b).symm))
   (fullNominal_sound state bound cert model modelSound a b)

def orProbe (built fallback : Answer) : Answer := built.orElse (fun _ => fallback)

theorem orProbe_sound {p : Prop} {first last : Answer}
 (one : Reflect p first) (two : Reflect p last) : Reflect p (orProbe first last) := by
 cases first <;> assumption

def enhance (state : State) (fallback : Probes state)
 (bound : Fin state.base.slots → Fin state.base.slots → Answer) : Probes state :=
 { fallback with edge := fun a b => orProbe (edge state bound fallback.model a b) (fallback.edge a b) }

theorem enhance_sound (state : State) (fallback : Probes state) (valid : Sound state fallback)
 (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (cert : ∀ a b, Reflect (Bound state a b) (bound a b)) : Sound state (enhance state fallback bound) :=
 ⟨fun a b => orProbe_sound (edge_sound state bound cert fallback.model valid.model a b) (valid.edge a b),valid.model⟩

end Yulang.GeneralRebaseRawActualProbe269
