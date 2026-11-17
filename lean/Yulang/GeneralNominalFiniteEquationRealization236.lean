import Yulang.GeneralNominalCenteredModelExtension
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalFiniteEquationRealization236
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCenteredModelExtension
open CommonNominalFullCarrier
abbrev Entry := Nat × TyTerm Nat
variable (entries : List Entry)
def names : Fin entries.length → Nat := fun i => entries[i].1
def terms : Fin entries.length → TyTerm Nat := fun i => entries[i].2
noncomputable def patch (model : Assignment) : Assignment :=
  assign model (names entries) (fun i => (terms entries i).eval CommonNominalFullCarrier.model model)

variable {model : Assignment} {pool : List Nat}
theorem outside (absent : ∀ entry ∈ entries, entry.1 ≠ identity) : patch entries model identity = model identity :=
  assign_outside _ _ _ (fun i => absent entries[i] (List.getElem_mem ..))

theorem row (identity) : (patch entries model identity).2 = (model identity).2 := by
  classical
  unfold patch assign
  split <;> rfl

theorem value (coherent : ∀ first ∈ entries, ∀ last ∈ entries, first.1 = last.1 → first.2 = last.2)
    (entry) (member : entry ∈ entries) :
    (patch entries model entry.1).1 = entry.2.eval CommonNominalFullCarrier.model model := by
  obtain ⟨index,bounded,same⟩ := List.mem_iff_getElem.mp member
  have values := assign_value model (names entries)
    (fun i => (terms entries i).eval CommonNominalFullCarrier.model model)
    (fun i j equal => congrArg (fun t => t.eval CommonNominalFullCarrier.model model)
      (coherent entries[i] (List.getElem_mem ..) entries[j] (List.getElem_mem ..) equal)) ⟨index,bounded⟩
  change (patch entries model entries[index].1).1 = entries[index].2.eval CommonNominalFullCarrier.model model at values
  rw [same] at values
  exact values

theorem preserves (fresh : ∀ entry ∈ entries, entry.1 ∉ pool) :
    ∀ identity ∈ pool, patch entries model identity = model identity := by
  intro identity member
  apply outside
  intro entry present same
  exact fresh entry present (same.symm ▸ member)

theorem equations
    (coherent : ∀ first ∈ entries, ∀ last ∈ entries, first.1 = last.1 → first.2 = last.2)
    (fresh : ∀ entry ∈ entries, entry.1 ∉ pool)
    (supported : ∀ entry ∈ entries, ∀ identity ∈ GeneralNominalState.typeSources entry.2, identity ∈ pool) :
    ∀ entry ∈ entries, PresenceNormalForm.All CommonNominalFullCarrier.model (patch entries model)
      (GeneralNominalAllocation.equations entry.1 entry.2) := by
  intro entry member
  apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
  have expression := type_eval_same (first := patch entries model) (last := model) entry.2
    (fun identity present => preserves entries fresh identity (supported entry member identity present))
  rw [value entries coherent entry member,expression]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem raw_models (fresh : ∀ entry ∈ entries, entry.1 ∉ pool)
    (sources : ∀ identity ∈ GeneralNominalState.sources state, identity ∈ pool)
    (valid : GeneralNominalState.Models state model) : GeneralNominalState.Models state (patch entries model) :=
  source_models_same state (fun identity member => (preserves entries fresh identity (sources identity member)).symm) valid
end Yulang.GeneralNominalFiniteEquationRealization236
