import Yulang.GeneralPresenceFixedInline244
import Yulang.GeneralPresenceOwnerTable244

/-! Readback restores a coherent external definition block. The model signature
alone does not require reflexive subtyping, so block satisfaction explicitly
requires that law. This is a one-way model map, not an equivalence of solutions
for arbitrary fresh blocks. -/
namespace Yulang.GeneralPresenceReadback245
open Core.PresenceGeneration
open PresenceNormalForm
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244
open GeneralPresenceFixedInline244
open GeneralPresenceOwnerTable244
variable {Name Owner : Type} [DecidableEq Name]

def readback (entries : List (Entry Name)) (model : Model)
    (assignment : Name → Comp model) : Name → Comp model :=
  fun name => (substitution entries name).eval model assignment

theorem lookup_of_member (entries : List (Entry Name)) (coherent : Coherent entries)
    (entry : Entry Name) (member : entry ∈ entries) :
    lookup entries entry.1 = some entry.2 := by
  induction entries with
  | nil => simp at member
  | cons first rest ih =>
    by_cases same : first.1 = entry.1
    · have rhs := coherent first (by simp) entry member same
      simp [lookup, same, rhs]
    · have tail : entry ∈ rest := by
        rcases List.mem_cons.mp member with equal | present
        · exact False.elim (same (congrArg Prod.fst equal.symm))
        · exact present
      have coherentRest : Coherent rest := fun a ha b hb eq =>
        coherent a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) eq
      simpa [lookup, same] using ih coherentRest tail

theorem row_preserved (entries : List (Entry Name)) (model : Model)
    (assignment : Name → Comp model) (name : Name) :
    (readback entries model assignment name).2 = (assignment name).2 := rfl

theorem outside_preserved (entries : List (Entry Name)) (model : Model)
    (assignment : Name → Comp model) (name : Name)
    (outside : ∀ entry ∈ entries, entry.1 ≠ name) :
    readback entries model assignment name = assignment name := by
  simp [readback, substitution, lookup_outside outside, CompTerm.eval,
    TyTerm.eval, RowTerm.eval]

theorem entry_value (entries : List (Entry Name)) (external : External entries)
    (coherent : Coherent entries) (model : Model) (assignment : Name → Comp model)
    (entry : Entry Name) (member : entry ∈ entries) :
    (readback entries model assignment entry.1).1 =
      entry.2.eval model (readback entries model assignment) := by
  have fixed := type_fixed entries entry.2 (external entry member)
  have evalFixed := congrArg (fun term => term.eval model assignment) fixed
  rw [TyTerm.eval_subst] at evalFixed
  change entry.2.eval model (readback entries model assignment) =
    entry.2.eval model assignment at evalFixed
  rw [evalFixed]
  simp [readback, substitution, lookup_of_member entries coherent entry member,
    CompTerm.eval]

theorem block_holds (entries : List (Entry Name)) (external : External entries)
    (coherent : Coherent entries) (model : Model)
    (subTy_refl : ∀ value, model.subTy value value)
    (assignment : Name → Comp model) :
    All model (readback entries model assignment) (block entries) := by
  intro atom member
  obtain ⟨entry, present, atomMem⟩ := List.mem_flatMap.mp member
  have equal := entry_value entries external coherent model assignment entry present
  simp only [equations, List.mem_cons, List.not_mem_nil, or_false] at atomMem
  rcases atomMem with rfl | rfl
  · change model.subTy (readback entries model assignment entry.1).1
      (entry.2.eval model (readback entries model assignment))
    rw [equal]
    exact subTy_refl _
  · change model.subTy (entry.2.eval model (readback entries model assignment))
      (readback entries model assignment entry.1).1
    rw [equal]
    exact subTy_refl _

variable [DecidableEq Owner]

theorem models_readback (state : State Name Owner) (owner : Owner)
    (fresh : List (Entry Name)) (present : owner ∈ state.owners)
    (disjoint : ∀ other ∈ state.owners, other ≠ owner →
      DisjointTargets (state.entries owner) (state.entries other))
    (external : External (state.entries owner))
    (coherent : Coherent (state.entries owner)) (model : Model)
    (subTy_refl : ∀ value, model.subTy value value)
    (assignment : Name → Comp model)
    (valid : Models (rebase state owner fresh) model assignment) :
    Models state model (readback (state.entries owner) model assignment) := by
  have consumers := ((models_exact state owner fresh present disjoint model assignment).mp valid).2
  refine ⟨consumers.1, ?_⟩
  intro other member
  by_cases same : other = owner
  · subst other
    exact block_holds _ external coherent model subTy_refl assignment
  · exact consumers.2 other member same

end Yulang.GeneralPresenceReadback245
