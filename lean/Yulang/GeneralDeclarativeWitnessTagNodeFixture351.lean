import Yulang.GeneralDeclarativeWitnessTagNode351

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTagNodeFixture351
open GeneralDeclarativeWitnessTagFixture351
open GeneralDeclarativeWitnessTagConcrete351 (model fitted some_checked)
open GeneralDeclarativeWitnessTagNode351 (leaf_evidence)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarativeTaggedFixture340 (registry d chosen checked covered wanted keep fallback targets)
open GeneralDeclarativeHiddenDecl324 (interpretation)
open GeneralDeclarativeTaggedFixtureModel340 (entire)

/-- The recursively named input yields real C340-style evidence for
this leaf and the exact fixed whole-payload output in a single model.
This is not a decision about any competing candidate or raw solver. -/
theorem named_leaf_dictionary :
    ∃ r f, namedRun = some (r,f) ∧ Models f.state model ∧
      Evidence registry interpretation model d (.node 97 []) ∧ (model 6).1 = entire := by
  have ok := checked_named_compiler
  cases ran : namedRun with
  | none => simp [ran] at ok
  | some data =>
    obtain ⟨r,f⟩ := data
    have fit := fitted ran
    obtain ⟨wire,⟨cert⟩⟩ := some_checked ran
    have expected := genuine_named_write
    rw [ran] at expected
    have empty : f.kids = [] :=
      List.isEmpty_iff.mp (GeneralDeclarativeWitnessProblem349.splitAnd
        (show writeFits r f = true from expected)).2
    have actualRun : GeneralDeclarativeWitnessCompiler350.execute r.ctx = some f := by
      unfold namedRun at ran
      obtain ⟨readBack,_,here⟩ := GeneralSourceMetadataExprDomain291.bind_success ran
      obtain ⟨produced,computed,written⟩ := GeneralSourceMetadataExprDomain291.bind_success here
      cases Option.some.inj written
      exact computed
    have exactF := Option.some.inj (cert.run.symm.trans actualRun)
    have leaf : cert.compiled.kids = [] := exactF.symm ▸ empty
    have proven := leaf_evidence (r := registry) (d := d) (impl := chosen)
      (.named r.bounds) r.parsed (keep := keep) (fallback := fallback) (targets := targets)
      cert checked covered List.mem_cons_self rfl wanted rfl rfl leaf model fit
    exact ⟨r,f,rfl,fit,proven,rfl⟩

end Yulang.GeneralDeclarativeWitnessTagNodeFixture351
