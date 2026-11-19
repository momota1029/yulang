import Yulang.GeneralRebaseRawK2Probe268

namespace Yulang.GeneralRebaseActualArguments269
open GeneralNominalState (State Descriptor Parameter Models Fits FitsAll)
open GeneralNominalProjections (Observes)
open GeneralNominalMixedRecurrence (ActualArgument Edge)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def Member (state : State) (parent child : Fin state.base.slots)
 (d : Descriptor state.base.slots) (i : Nat) : Prop :=
 ∀ model, Models state model →
 ∃ actual, Observes model (.argument (.source (state.base.source parent)) d.declaration.name i) (.inl actual) ∧
   Equivalent actual (model (state.base.source child)).1

def TypeSlots (d : Descriptor n) : List (Fin d.arguments.length) :=
 (List.finRange d.arguments.length).filter fun i => match d.arguments[i.val] with
 | .type _ => true
 | .row _ => false

theorem fits_length {model : Assignment} (fits : FitsAll state model one two) : one.length = two.length := by
 induction fits with
 | nil => rfl
 | cons _ _ ih => exact congrArg Nat.succ ih

theorem bounded_of_observed (state : State) (model : Assignment) (valid : Models state model)
 (parent : Fin state.base.slots) (d : Descriptor state.base.slots) (recorded : state.nominals parent = some d)
 (i : Nat) (actual : Ty)
 (seen : Observes model (.argument (.source (state.base.source parent)) d.declaration.name i) (.inl actual)) :
 ∃ idx ∈ TypeSlots d, (idx : Nat) = i := by
 obtain ⟨values,fits,head⟩ := valid.2.1 parent d recorded
 have bound : i < d.arguments.length := by
   cases seen with
   | argument src witnessed found =>
     cases src
     have sameLength := (nominal_regular_invariant_exact ..).mp (subtype_trans witnessed.2 head.1) |>.2.1
     have atPosition := (List.getElem?_eq_some_iff.mp found).1
     rw [fits_length fits,←sameLength]
     exact atPosition
 let idx : Fin d.arguments.length := ⟨i,bound⟩
 refine ⟨idx,?_,rfl⟩
 have found : d.arguments[i]? = some d.arguments[i] := List.getElem?_eq_getElem bound
 obtain ⟨other,observed,holds⟩ := GeneralNominalProjections.parameter_binding_valid
   state model valid parent d recorded i 0 d.arguments[i] found
 have same := GeneralNominalProjections.observation_unique model _ _ _ seen observed
 cases other with
 | inr => cases same
 | inl value =>
   change Fits state.base model d.arguments[i] (.inl value) at holds
   simp only [TypeSlots,List.mem_filter,List.mem_finRange,true_and]
   dsimp [idx]
   split
   · rfl
   · rename_i row eq
     rw [eq] at holds
     cases holds


/-- Under model inhabitation, only the descriptor's finitely many type
positions can witness the old actual nominal argument edge. A model
witness is essential for the reverse implication. -/
theorem actual_iff (state : State) (parent child : Fin state.base.slots)
 (d : Descriptor state.base.slots) (recorded : state.nominals parent = some d)
 (inhabited : ∃ model, Models state model) :
 ActualArgument state parent child ↔ ∃ i ∈ TypeSlots d, Member state parent child d i.val := by
 constructor
 · rintro ⟨other,found,i,h⟩
   cases Option.some.inj (found.symm.trans recorded)
   obtain ⟨model,valid⟩ := inhabited
   obtain ⟨actual,seen,_⟩ := h model valid
   obtain ⟨idx,listed,same⟩ := bounded_of_observed state model valid parent d recorded i actual seen
   exact ⟨idx,listed,same.symm ▸ h⟩
 · rintro ⟨i,_,h⟩
   exact ⟨d,recorded,i,h⟩

theorem actual_of_empty_models (state : State) (parent child : Fin state.base.slots)
 (d : Descriptor state.base.slots) (recorded : state.nominals parent = some d)
 (empty : ¬ ∃ model, Models state model) : ActualArgument state parent child :=
 ⟨d,recorded,0,fun model models => False.elim (empty ⟨model,models⟩)⟩

end Yulang.GeneralRebaseActualArguments269
