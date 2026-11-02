import YulangClosure.SimpleSubConstraintSyntax

/-!
R235 tests a quotient-based reading of reciprocal Simple-sub bounds for the
literal case of the unchanged SourceProblem.InferenceSoundness parent.

The quotient below identifies terms related by mutual structural `Sub`; it
does not identify them syntactically. This proves only the abstract quotient
leaf. The selected source/algorithm authorities must still justify literal
constraint generation, a typed allocation, and a denotation into the original
PaperTypes descriptor/effect carriers before this can be applied to the source
parent. No such bridge is assumed here.
-/
namespace YulangClosure.OriginalLiteralConstraintModelR235

open YulangClosure.SimpleSub

def ValueEquivalent (a b : Term .value) : Prop := Sub a b ∧ Sub b a

def valueSetoid : Setoid (Term .value) where
  r := ValueEquivalent
  iseqv := {
    refl := by intro a; exact ⟨Sub.refl a, Sub.refl a⟩
    symm := by intro a b h; exact ⟨h.2, h.1⟩
    trans := by
      intro a b c hab hbc
      exact ⟨Sub.trans hab.1 hbc.1, Sub.trans hbc.2 hab.2⟩
  }

abbrev ValueMeaning := Quotient valueSetoid

def observe (t : Term .value) : ValueMeaning := Quotient.mk valueSetoid t

/-- Reciprocal structural subtyping gives equality of semantic observations,
without claiming equality of the source terms. -/
theorem observe_eq_of_mutual_sub (a b : Term .value)
    (forward : Sub a b) (backward : Sub b a) : observe a = observe b := by
  apply Quotient.sound
  exact ⟨forward, backward⟩

/-- Every valuation satisfying the reciprocal literal base bounds identifies
the inferred value term with its base atom in the mutual-Sub quotient. -/
theorem reciprocal_base_bounds_readout (ρ : Valuation) (coordinate base : Nat)
    (lower_bound : Sub ((Term.var coordinate : Term .value).subst ρ)
      ((Term.atom base : Term .value).subst ρ))
    (upper_bound : Sub ((Term.atom base : Term .value).subst ρ)
      ((Term.var coordinate : Term .value).subst ρ)) :
    observe (ρ .value coordinate) = observe (.atom base) := by
  simpa [Term.subst] using
    (observe_eq_of_mutual_sub (ρ .value coordinate) (.atom base)
      lower_bound upper_bound)

/-- The quotient readout preserves the R232 union countermodel's intended
distinction: it accepts mutual-sub equivalence but never asserts syntactic
identity. -/
theorem union_self_observation (base : Term .value) :
    observe (.union base base) = observe base := by
  apply observe_eq_of_mutual_sub
  · exact Sub.unionElim (Sub.refl base) (Sub.refl base)
  · exact Sub.unionLeft base base

#check @observe_eq_of_mutual_sub
#print axioms observe_eq_of_mutual_sub
#check @reciprocal_base_bounds_readout
#print axioms reciprocal_base_bounds_readout
#check @union_self_observation
#print axioms union_self_observation
#print YulangClosure.SourceProblem.InferenceSoundness

end YulangClosure.OriginalLiteralConstraintModelR235
