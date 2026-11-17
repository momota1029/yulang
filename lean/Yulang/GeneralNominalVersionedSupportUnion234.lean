import Yulang.GeneralNominalVersionedSupport233
import Yulang.GeneralNominalCommonTrustedLedger
set_option backward.isDefEq.respectTransparency false
/-! Finite conjunction of independently trusted versioned slices. Neither
cyclic trust nor availability/completeness is assumed or asserted. -/
namespace Yulang.GeneralNominalVersionedSupportUnion234
open GeneralNominalVersionedSupport233
variable {roles : Roles.RoleDecls} {state : GeneralNominalVersionedJournal232.State roles}

theorem models_append : SliceModels state (first ++ last) model ↔
    SliceModels state first model ∧ SliceModels state last model := by
  constructor
  · intro valid
    exact ⟨⟨valid.1,valid.2.1,fun fact member => valid.2.2 fact (List.mem_append_left _ member)⟩,
      ⟨valid.1,valid.2.1,fun fact member => valid.2.2 fact (List.mem_append_right _ member)⟩⟩
  · rintro ⟨one,two⟩
    refine ⟨one.1,one.2.1,?_⟩
    intro fact member
    rcases List.mem_append.mp member with member | member
    · exact one.2.2 fact member
    · exact two.2.2 fact member

theorem trusted_append (one : Trusted state first) (two : Trusted state last) :
    Trusted state (first ++ last) := by
  induction one with
  | source => exact two
  | input plan trusted recorded readback ih =>
    apply Trusted.input plan ih recorded
    intro slot member test observation head model valid
    exact readback slot member test observation head model (models_append.mp valid).1
  | output effect trusted recorded planRecorded input classReadback settled ih =>
    apply Trusted.output effect ih recorded planRecorded (List.mem_append_left _ input) _ settled
    intro site member alias
    exact GeneralNominalCommonTrustedLedger.same_inputs_restrict (classReadback site member alias)
      (fun _ valid => (models_append.mp valid).1)
  | merge a b trusted one two alias atoms grounded compatible ih =>
    apply Trusted.merge a b ih one two alias atoms
    · intro model valid
      exact grounded model (models_append.mp valid).1
    · exact GeneralNominalCommonTrustedLedger.same_inputs_restrict compatible
        (fun _ valid => (models_append.mp valid).1)

theorem jointly_sound (observation : GeneralCanonicalObservations.Observation) (one : Trusted state first) (two : Trusted state last)
    (sound : ∀ model, SliceModels state first model → SliceModels state last model → observation.Holds model) :
    ∃ facts, Trusted state facts ∧ ∀ model, SliceModels state facts model → observation.Holds model :=
  ⟨first ++ last,trusted_append one two,fun model valid => sound model (models_append.mp valid).1 (models_append.mp valid).2⟩

theorem trusted_flatten {families : List (List (Fact roles))} (given : ∀ facts ∈ families, Trusted state facts) :
    Trusted state families.flatten := by
  induction families with
  | nil => exact .source
  | cons first rest ih =>
    exact trusted_append (given first (List.mem_cons_self ..))
      (ih (fun facts member => given facts (List.mem_cons_of_mem first member)))

theorem models_subset (included : first ⊆ last) (valid : SliceModels state last model) :
    SliceModels state first model :=
  ⟨valid.1,valid.2.1,fun fact member => valid.2.2 fact (included member)⟩

theorem flatten_member {families : List (List (Fact roles))} (member : facts ∈ families)
    (valid : SliceModels state families.flatten model) : SliceModels state facts model := by
  apply models_subset _ valid
  intro fact present
  exact List.mem_flatten.mpr ⟨facts,member,present⟩

end Yulang.GeneralNominalVersionedSupportUnion234
