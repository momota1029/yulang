import Yulang.GeneralDeclarativeWitnessCompletion351
import Yulang.GeneralDeclarativeWitnessFreshFixture351

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralDeclarativeWitnessCompletionFixture351
open GeneralDeclarativeWitnessAuthFixture351 (setup problem state answer originRows)
open GeneralDeclarativeWitnessAuthModel351 (model fixed_shared_model setup_runs)
open GeneralDeclarativeWitnessWriterFixture351 (stamp key out)
open GeneralDeclarativeWitnessFreshFixture351 (fresh actually_fresh)
open GeneralDeclarativeWitnessAuthWhole351 (Accepted Wire decode)
open GeneralDeclarativeWitnessCompiler350 (Finished)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessCompletion351 (both)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralSourceMetadataBundle291 (registry)
open GeneralDeclarativeHead320 (Models Equation)

def labels (f : Finished) (w : Wire) : Bool :=
  ((decode (problem (state f) [key]) w answer).map fun a =>
    decide (a.writer.owned = [⟨key,out⟩] ∧
      a.writer.producer.diagnostic.fixed.map Fixed.path = [[]] ∧
      a.diagnostic.fixed.map Fixed.path = [[],[0],[1]])).getD false

theorem exact_trace : (setup.map (fun (f,w) => labels f w)).getD false = true := by decide +kernel

theorem never_promoted : out ∉ originRows := by decide +kernel

/-- The producer and the consuming tree's dictionaries really coexist
in one specified ordinary model. Both outputs come from replay, not
an accepted reference to a solver's report. -/
theorem two_dictionaries :
    ∃ (f : Finished) (w : Wire) (a : Accepted (problem (state f) [key]) w answer),
      Models (state f) model ∧
      Evidence (registry a.writer.producer.global.table)
        (interpretation a.writer.producer.global.table.snapshot) model
        GeneralDeclarativeWitnessWriterFixture351.demand (.node 190 []) ∧
      Evidence (registry a.env.bundle) (interpretation a.env.bundle.snapshot) model
        GeneralDeclarativeWitnessOrderedFixture350.root (.node 92 [.node 93 [],.node 94 []]) := by
  have ok := actually_fresh
  unfold fresh at ok
  cases done : setup with
  | none => simp [done] at ok
  | some result =>
    obtain ⟨f,w⟩ := result
    have passing : GeneralDeclarativeWitnessFreshness351.check [stamp]
        (problem (state f) [key]) w answer = true := by simpa [done] using ok
    obtain ⟨a,p,c,hp,hc,_,accepted⟩ := both passing
    have full : Models (state f) model := fixed_shared_model (setup_runs done)
    have correct : c = .node 92 [.node 93 [],.node 94 []] := by
      exact (CommonRoleOutermostResolver.Result.selected.inj hc).symm
    have reportShape : w.priorReport = GeneralDeclarativeWitnessWriterFixture351.answer := by
      unfold setup at done
      obtain ⟨_,_,rest⟩ := GeneralSourceMetadataExprDomain291.bind_success done
      obtain ⟨_,_,rest⟩ := GeneralSourceMetadataExprDomain291.bind_success rest
      obtain ⟨_,_,rest⟩ := GeneralSourceMetadataExprDomain291.bind_success rest
      obtain ⟨_,_,rest⟩ := GeneralSourceMetadataExprDomain291.bind_success rest
      obtain ⟨_,_,rest⟩ := GeneralSourceMetadataExprDomain291.bind_success rest
      obtain ⟨_,_,rest⟩ := GeneralSourceMetadataExprDomain291.bind_success rest
      obtain ⟨_,_,rest⟩ := GeneralSourceMetadataExprDomain291.bind_success rest
      obtain ⟨_,_,rest⟩ := GeneralSourceMetadataExprDomain291.bind_success rest
      exact (congrArg (fun pair : Finished × Wire => pair.2.priorReport)
        (Option.some.inj rest)).symm
    have publisher : p = .node 190 [] := by
      rw [reportShape] at hp
      exact (CommonRoleOutermostResolver.Result.selected.inj hp).symm
    subst p
    subst c
    have both := accepted model full
    exact ⟨f,w,a,full,both.1,both.2.1⟩


theorem wrong_release_role :
    GeneralDeclarativeWitnessAuthFixture351.test [{key with role := 20}] = false := by decide +kernel

theorem wrong_release_ordinal :
    GeneralDeclarativeWitnessAuthFixture351.test [{key with write := 1}] = false := by decide +kernel

theorem duplicated_real_writer_key_is_not_a_catalogue :
    GeneralDeclarativeWitnessAuthFixture351.test [key] (fun p =>
      {p with writer := {p.writer with required := [⟨stamp,0⟩,⟨stamp,0⟩]}}) = false := by
  decide +kernel

theorem stale_record_does_not_harm_independently_released_current_version :
    GeneralDeclarativeWitnessAuthFixture351.test [{key with version := 6},key] = true := by
  decide +kernel

end Yulang.GeneralDeclarativeWitnessCompletionFixture351
