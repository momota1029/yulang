import Yulang.GeneralDeclarativeI65Body367

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessCompiler350 (Context Finished preparation whereBatch fixedBatch execute placed portNames)
open GeneralDeclarativeWitnessDeclaredState357 (WrittenBody context)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarations (Declaration)

/-- The given actual body execution supplies exact clause and root
segments in its state, with no ordinary constraints added afterward. -/
theorem finished_equation_segments (c : Context) {f : Finished}
    (ran : execute c = some f) :
    ∃ before ports ws rs,
      preparation c = some (before,ports) ∧ whereBatch c ports = some ws ∧
      fixedBatch c ports = some rs ∧ f.fixed = rs ∧
      f.state.normal = before.normal ∧
      f.state.equations = before.equations ++ ws ++ rs := by
  unfold execute at ran
  cases first : preparation c with
  | none => simp [first] at ran
  | some prep =>
    obtain ⟨before,ports⟩ := prep
    cases second : whereBatch c ports with
    | none => simp [first,second] at ran
    | some ws =>
      cases third : fixedBatch c ports with
      | none => simp [first,second,third] at ran
      | some rs =>
        have eq : (⟨appendFacts before ws,rs,
            GeneralDeclarativeEmissionForest322.children c.decl (portNames c ports) (placed c ports)⟩ :
            Finished) = f := by
          simpa [first,second,third] using ran
        cases eq
        exact ⟨before,ports,ws,rs,rfl,second,third,rfl,rfl,rfl⟩

/-- Two names in this list may denote equal rows; prior position, not
the equality or membership of the row value, supplies the index. -/
theorem retained_body_at_suffix_offset {A : Type} (prior xs : List A)
    (j : Nat) : (prior ++ xs)[prior.length+j]? = xs[j]? := by
  induction prior with
  | nil => simp
  | cons a rest ih =>
    simpa [Nat.succ_add] using ih

def retained_body_facts_at_same_current {s : State} {q : Request} {row : Declaration}
    {named spans keep fallback targets} {f : Finished}
    (ran : execute (context s.current q.demand row named spans keep fallback targets) = some f)
    (atoms : f.state.normal.ordinary ⊆ s.current.ordinary.normal.ordinary)
    (intervals : f.state.normal.intervals ⊆ s.current.ordinary.normal.intervals)
    (later : List Equation)
    (prior : s.current.ordinary.equations = f.state.equations ++ later) :
    BodyFacts s q row (children q f.kids) := by
  have retained : Extends f.state s.current.ordinary := ⟨atoms,intervals,by
    intro e written
    rw [prior]
    exact List.mem_append_left _ written⟩
  exact ⟨spans,f.kids,⟨named,keep,fallback,targets,f,ran,rfl,
    GeneralDeclarativeCurrentReceipt330.literal retained⟩,rfl⟩

end Yulang.GeneralDeclarativeI65
