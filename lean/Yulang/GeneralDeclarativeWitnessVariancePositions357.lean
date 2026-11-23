import Yulang.GeneralDeclarativeWitnessSparseVariance357
import Yulang.CommonRoleOutermostResolver
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessVariancePositions357
open GeneralDeclarativeWitnessSparseVariance357 (Header Source Made entry variance modeOf parameters lookup lookup_authored kindAt)
open CommonDeclaredNominalInspection (Kind Parameter)
open CommonDeclaredNominalVariance (Variance)
open CommonDeclarationVarianceTable (TableJudgment Mode)
open CommonRoleOutermostResolver (All₂)

theorem judgment_mem {I P : Type} {program : CommonDeclarationVarianceSyntax.Program I P}
    {slots table} (judgment : TableJudgment program slots table) :
    ∀ (p : P) (mode : Variance), (p,mode) ∈ table → Mode program p mode := by
  induction slots generalizing table with
  | nil => cases table with
    | nil => intro p v absent; cases absent
    | cons h t => cases judgment
  | cons x xs ih => cases table with
    | nil => cases judgment
    | cons y rest =>
      rcases y with ⟨written,kind⟩
      rcases judgment with ⟨rfl,found,remaining⟩
      intro p v here
      rcases List.mem_cons.mp here with eq|tail
      · cases eq
        exact found
      · exact ih remaining _ _ tail

theorem positionMode {count : Nat} {vs : List (Fin count × Variance)} {p mode}
    (selected : modeOf vs p = some mode) : (p,mode) ∈ vs := by
  unfold modeOf at selected
  obtain ⟨found,atRow,eq⟩ := Option.map_eq_some_iff.mp selected
  have test : (found.1 == p) = true :=
    List.find?_some (p := fun q : Fin count × Variance => q.1 == p) atRow
  have exactRow : found = (p,mode) := Prod.ext (beq_iff_eq.mp test) eq
  rw [← exactRow]
  exact List.mem_of_find?_eq_some atRow

def sourced {I count : Nat} (p : CommonDeclarationVarianceSyntax.Program (Fin I) (Fin count))
    (written : Kind × Fin count) (mode : Parameter) : Prop :=
  mode.kind = written.1 ∧ Mode p written.2 mode.variance

theorem parameters_sound {I count : Nat} {p : CommonDeclarationVarianceSyntax.Program (Fin I) (Fin count)}
    {order table} (valid : TableJudgment p order table) (xs : List (Kind × Fin count))
    {out} (read : parameters table xs = some out) : All₂ (sourced p) xs out := by
  induction xs generalizing out with
  | nil =>
    simp [parameters] at read
    subst out
    exact .nil
  | cons a rest ih =>
    rcases a with ⟨kind,slot⟩
    rw [parameters] at read
    cases hv : modeOf table slot with
    | none => simp [hv] at read
    | some mode =>
      cases ht : parameters table rest with
      | none => simp [hv,ht] at read
      | some more =>
        simp [hv,ht] at read
        subst out
        exact .cons ⟨rfl,judgment_mem valid _ _ (positionMode hv)⟩ (ih ht)

theorem authored_modes_exact {nodes types rows} {s : Source nodes types rows}
    (c : Made s) {name computed} (found : lookup c name = some computed) :
    ∃ h ∈ s.headers, h.name = name ∧
      All₂ (sourced c.program) h.written computed := by
  obtain ⟨h,member,nameEq,_,run⟩ := lookup_authored c found
  exact ⟨h,member,nameEq,parameters_sound (GeneralDeclarativeWitnessSparseVariance357.modes_from_source c) _ run⟩

end Yulang.GeneralDeclarativeWitnessVariancePositions357
