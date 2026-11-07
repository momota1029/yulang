import Yulang.ProducerRanked

/-!
# Expressiveness boundary of the current rigid demand observations

The candidate demand environment maps variables to finite conjunctions of
`Observation`s. It does not allow an arbitrary symbolic type constraint or an
arbitrary producer type as the interpretation of a demand variable.

Under exactly these definitions, two distinct base alternatives have no common
nontrivial observation. Their union is therefore producer-equivalent to `top`,
at every negative-context rank, for every row type and relation. This is a
theorem about the candidate observer grammar, not a decision that the language
must identify `int | str` with `any`. It records the boundary without changing
the existing definitions or the constructor-grouping theorems.
-/

namespace Yulang.ProducerDemandExpressiveness

open Inference StructuralBase ProducerRanked

universe u
variable {Row : Type u} (leRow : Row → Row → Prop)

/-- Distinct base alternatives share only the trivial observation. No row
reflexivity/transitivity, rank bound, environment bound or solver premise is
assumed. -/
theorem distinct_bases_union_equivalent_top (first last : Base) (different : first ≠ last) :
    ProducerEq leRow (.union (.base first) (.base last)) .top := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank obs
  cases rank <;> cases obs <;> simp [ProbeAt, ProbeStep]
  all_goals
    intro left right
    exact different (left.trans right.symm)

/-- The concrete mixed-base example holds uniformly over every row relation. -/
theorem mixed_union_equivalent_top :
    ProducerEq leRow (.union (.base .int) (.base .str)) .top :=
  distinct_bases_union_equivalent_top leRow .int .str (by intro impossible; cases impossible)

/-- Demand variables, intersections, every syntactically available mask and
every finite negative-context rank cannot distinguish this union from top in
the current candidate semantics. The environment remains arbitrary within
its actual finite-conjunction type. -/
theorem mixed_union_accept_iff (rank : Nat) (environment : ProducerDemand.Environment Row)
    (demand : ProducerDemand.Demand Row) :
    AcceptAt leRow rank environment (.union (.base .int) (.base .str)) demand ↔
      AcceptAt leRow rank environment .top demand := by
  have equivalent := mixed_union_equivalent_top leRow
  exact ⟨equivalent.2 rank environment demand, equivalent.1 rank environment demand⟩

end Yulang.ProducerDemandExpressiveness
