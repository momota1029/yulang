import Yulang.GeneralNominalOrderedInitial248
/-! Actual raw model support excludes reservation bookkeeping. The reduced
state is used only to prove support facts, never as an operational update.
Live packets and public interfaces still require their own protected reads. -/
namespace Yulang.GeneralNominalActiveSupport249
open GeneralNominalState GeneralNominalCommonBridge

def withoutReservations (state : State) : State := { state with reserved := [] }
def activeSources (state : State) : List Nat := sources (withoutReservations state)

theorem models_exact (state : State) (assignment : Assignment) :
 Models (withoutReservations state) assignment ↔ Models state assignment := Iff.rfl

theorem active_sources (state : State) : activeSources state =
 List.ofFn state.base.source ++ List.ofFn state.base.rowSource ++ state.ordinary.flatMap atomSources := by
 simp [activeSources,withoutReservations,sources]

theorem reservation_irrelevant (state : State) (reserved : List Nat) :
 activeSources {state with reserved := reserved} = activeSources state := rfl

theorem allocated_irrelevant (state : State) (allocated : List GeneralNominalIdentities.Origin) :
 activeSources {state with allocated := allocated} = activeSources state := rfl

theorem active_subset_sources (state : State) : activeSources state ⊆ sources state := by
 intro name member
 rw [active_sources] at member
 rcases List.mem_append.mp member with left | right
 · exact List.mem_append_left _ (List.mem_append_left _ left)
 · exact List.mem_append_right _ right

theorem models_of_agrees (state : State) (first last : Assignment)
 (same : ∀ name ∈ activeSources state, first name = last name)
 (valid : Models state first) : Models state last :=
 GeneralNominalCenteredModelExtension.source_models_same (withoutReservations state) same valid

theorem models_iff_of_agrees (state : State) (first last : Assignment)
 (same : ∀ name ∈ activeSources state, first name = last name) :
 Models state first ↔ Models state last :=
 ⟨models_of_agrees state first last same,
  models_of_agrees state last first (fun name member => (same name member).symm)⟩
end Yulang.GeneralNominalActiveSupport249
