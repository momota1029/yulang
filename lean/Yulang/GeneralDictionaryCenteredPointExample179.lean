import Yulang.GeneralDictionaryCenteredPointInstall179
import Yulang.GeneralDictionaryCenteredNominalPointExample178

/-! A real nonpoint-parameter fixture obtains its common centered model from
finite model extension, not a hand-written binder assignment. -/
namespace Yulang.GeneralDictionaryCenteredPointExample179
open GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryCenteredNominalPointExample178 (root start leaf packet plan candidate)
open GeneralDictionaryNominalPairExample178 (state context assignment registry declaration)

 theorem source_below : ∀ name ∈ GeneralNominalState.sources state, name ≤ state.seed := by
  intro name member
  simp [GeneralNominalState.sources,List.ofFn_succ] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

 theorem joint : ∃ extended, Models start extended ∧ plan.Holds extended ∧
    ∀ name ∈ GeneralNominalState.sources state, extended name = assignment false name :=
  GeneralDictionaryCenteredPointCandidate179.initial_joint candidate
    (fun index equal => point_center state.seed root index equal) source_below
    0 0 (fun _ : Fin 1 => 0) (fun i j _ => Subsingleton.elim i j) rfl leaf.query leaf.located
    rfl rfl (assignment false) (GeneralDictionaryNominalPairExample178.source_models false)

 theorem nonpoint_parameters : leaf.bounds 0 ≠ (2,2) ∧ leaf.bounds 0 ≠ (3,3) := by decide +kernel

 theorem enabled
    (selected : GeneralNominalCenteredBoundary.Local registry start root (.selected declaration.id [])) :
    GeneralNominalCenteredBoundary.Installable registry start plan :=
  GeneralDictionaryCenteredPointInstall179.installable candidate selected rfl
    (fun index equal => point_center state.seed root index equal) source_below
    0 0 (fun _ : Fin 1 => 0) (fun i j _ => Subsingleton.elim i j) rfl leaf.query leaf.located rfl rfl

end Yulang.GeneralDictionaryCenteredPointExample179
