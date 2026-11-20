import Yulang.GeneralRebasePackedAnswers298

namespace Yulang.GeneralRebasePackedSource298
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseSourceWitnessProgram297 (Holds Question)
open GeneralRebaseSymbolicQuestions298 (compile)
open GeneralRebaseExecutableJournal298 renaming compile → journal
open GeneralRebaseQuestionFootprint298 (question prior)
open GeneralRebasePackedAnswers298 (Vector fill asked_iff valid_prior_iff)
open Core.PresenceGeneration (CompTerm)

def reduced (s : State roles) (q : Question roles) (fallback : Assignment) :
    Vector (question (journal s CompTerm.var) (compile s CompTerm.var q)) → Prop :=
  fun v => (compile s CompTerm.var q).Holds (journal s CompTerm.var)
    (fill (question (journal s CompTerm.var) (compile s CompTerm.var q)) v fallback)

theorem source_question {r : Registry} {s : State roles} {root : Occurrence roles}
    (reached : B4TargetV8.Reachable (Boundary roles) r root s)
    (q : Question roles) (fallback : Assignment) :
    (∃ m, Holds s q m) ↔ ∃ v, reduced s q fallback v :=
  (exists_congr (GeneralRebaseSymbolicQuestions298.compile_holds reached CompTerm.var q)).symm.trans
    (asked_iff _ _ fallback)

theorem empty_source {r : Registry} {s : State roles} {root : Occurrence roles}
    (reached : B4TargetV8.Reachable (Boundary roles) r root s) (fallback : Assignment) :
    (¬ ∃ m, Models s m) ↔ ¬ ∃ v : Vector (prior (journal s CompTerm.var)),
      (journal s CompTerm.var).Models (fill (prior (journal s CompTerm.var)) v fallback) :=
  not_congr ((exists_congr (GeneralRebaseExecutableJournal298.source_models reached CompTerm.var)).symm.trans
    (valid_prior_iff _ fallback))

theorem reduced_independent (s : State roles) (q : Question roles) (a b : Assignment) (v) :
    reduced s q a v ↔ reduced s q b v :=
  GeneralRebaseQuestionFootprint298.question_exact _ _ _ _
    (GeneralRebasePackedAnswers298.fallback_irrelevant _ v a b)

end Yulang.GeneralRebasePackedSource298
