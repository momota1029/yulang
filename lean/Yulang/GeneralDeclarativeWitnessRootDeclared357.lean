import Yulang.GeneralDeclarativeWitnessVarianceReport357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRootDeclared357
open GeneralDeclarativeWitnessDeclaredState357 (Current WrittenBody ModelsCurrent authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (Rule Evidence roleView roleView_span)
open GeneralDeclarativeWitnessVarianceReport357 (Leaf exact_leaf_certificate)
open GeneralDeclarativeWitnessCompiler350 (Context Finished execute fixedBatch)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDictionaryAssociatedProvenance (lookup Supplies lookup_exact)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (Classify)

theorem compiled_requests {c : Context} {f : Finished} (ok : execute c = some f) :
    ∀ out ∈ c.demand.outputs,∃ body,lookup c.registry.roles c.decl out.name = some body := by
  unfold execute at ok
  cases prep : GeneralDeclarativeWitnessCompiler350.preparation c with
  | none => simp [prep] at ok
  | some front =>
    rcases front with ⟨s,p⟩
    cases preFixed : GeneralDeclarativeWitnessCompiler350.whereBatch c p with
    | none => simp [prep,preFixed] at ok
    | some afterWhere =>
      cases fixed : fixedBatch c p with
      | none => simp [prep,preFixed,fixed] at ok
      | some equations =>
        intro out seen
        obtain ⟨localRows,known,_⟩ := GeneralDeclarativeBatch320.collect_sound fixed out seen
        cases lookup_ : lookup c.registry.roles c.decl out.name with
        | none => simp [one,lookup_] at known
        | some body => exact ⟨body,rfl⟩

theorem written_root_declared {s : Current} {d impl spans kids}
    (b : WrittenBody s d impl spans kids)
    (signature : impl.Signature (authoredRegistry s).roles)
    (unique : (impl.associated.map GeneralDeclarations.Equation.name).Nodup)
    (role : impl.role = d.role) : Declared (authoredRegistry s) d := by
  intro out member
  obtain ⟨body,actual⟩ := compiled_requests b.run out member
  have sourced := (lookup_exact (authoredRegistry s).roles impl unique out.name body).mp actual
  cases sourced with
  | explicit eq listed exactName =>
    have declared := signature.2.1 eq listed
    simpa only [GeneralDeclarations.Declared,role,exactName] using declared
  | default rhs _ chosen =>
    exact ⟨some rhs,role ▸ chosen⟩

theorem receipt_has_its_own_declared {s : Current} {d w r} (a : Leaf s d w r) :
    Declared (authoredRegistry s) d := by
  have inRole : a.answer.impl ∈ (roleView s d.role).declarations := by
    rw [a.answer.localRead.single]
    exact List.mem_cons_self
  have ⟨visible,role⟩ := (roleView_span s d.role a.answer.impl).mp inRole
  have legal := a.soundSource.2 a.answer.impl visible
  exact written_root_declared a.answer.localRead.body legal.signature legal.identified.2.2.1 role

theorem exact_s2_without_external_declared {s : Current} {d w r} (a : Leaf s d w r)
    (m : Assignment) (v : GeneralDeclarativeWitnessDeclaredState357.Views) (fit : ModelsCurrent s m v) :
    Declared (authoredRegistry s) d ∧
    r.tree = .selected a.answer.impl.id [] ∧
    r.result = .selected (.node a.answer.impl.id []) ∧
    r.outputs = d.outputs ∧
    Classify (Rule s) d r.result ∧ Evidence s m v d (.node a.answer.impl.id []) ∧
    w.outputRows.map Equation.left = d.outputs.map GeneralSourceState.Output.target ∧
    ∀ eq ∈ w.outputRows,Holds m eq :=
  ⟨receipt_has_its_own_declared a,exact_leaf_certificate a (receipt_has_its_own_declared a) m v fit⟩

end Yulang.GeneralDeclarativeWitnessRootDeclared357
