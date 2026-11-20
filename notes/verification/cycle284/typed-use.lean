import Yulang.GeneralRebaseNoLiteralTrim284

open Yulang
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralRebaseHistoryOrder282 (history decode)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseRoundMicro278 (Tick)
open GeneralRebaseWindowPaths284 (roundFuture)
open GeneralRebaseWholeRow282 (Keeps initialNames)
open GeneralRebasePrivateStore282 (Joint)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseEpochWindow284 (view)

example (n : Nat) (watch : List Nat)
    (c : journalReads (GeneralDictionaryVersionLoopIteration239.state n) ⊆ watch) :
    2*n ≤ watch.length := GeneralRebaseVersionWatchLower284.no_short_watch n watch c

example (n : Nat) (watch : List Nat)
    (c : journalReads (GeneralDictionaryLooseIterationIteration240.state n) ⊆ watch) :
    2*n ≤ watch.length := GeneralRebaseLooseWatchLower284.no_short_watch n watch c

example (n : Nat) (watch : List Nat)
    (row : GeneralPresenceDefinitionRewrite244.Entry Nat)
    (h : row ∈ history (GeneralDictionaryLooseIterationIteration240.state n))
    (dropped : row.1 ∉ watch) :
    ∃ base : Assignment, Models (GeneralDictionaryLooseIterationIteration240.state n)
      (decode (GeneralDictionaryLooseIterationIteration240.state n) base) ∧
      ¬ Models (GeneralDictionaryLooseIterationIteration240.state n)
        (GeneralPresenceOrderedBlock247.solve CommonNominalFullCarrier.model
          (GeneralRebaseFutureWatch284.trim watch (history (GeneralDictionaryLooseIterationIteration240.state n))) base) :=
  GeneralRebaseLooseErasureFailure284.any_omitted_counterexample n watch row h dropped

example (t : Tick) (ex : Assignment) (p : Payload) :
    (∃ a, Keeps (initialNames 3) a ex ∧ ∀ n,
      Joint (GeneralRebaseVersionMicro278.raw (roundFuture t n))
        GeneralDictionaryVersionLoopSource237.registry GeneralDictionaryVersionLoopSource237.root p a) ↔
    GeneralRebaseVersionWindow284.Observe (view t) ex p :=
  GeneralRebaseVersionWindow284.exact_unbounded_future t ex p

example (t : Tick) :
    GeneralRebaseEpochWindow284.canInstall (view t) = true ↔
      ∃ s, GeneralRebaseTerminalAbsorb278.InstallTransition GeneralDictionaryLooseLoopSource240.registry
        GeneralDictionaryLooseLoopSource240.root (GeneralRebaseLooseMicro278.raw t) s :=
  GeneralRebaseLooseWindow284.readiness t

example : GeneralRebaseWatchedEvidenceAt284.CheckedEvidenceAt GeneralRebaseDisplayWatch284.watch
    GeneralRebaseDisplayWatch284.stored.kept GeneralNominalExamples.registry
    GeneralRebaseCompiledDisplay277.after GeneralNominalExamples.displayRoot :=
  GeneralRebaseDisplayEvidenceWatch284.evidence_at

example : GeneralRebaseMixedCounts277.Actual GeneralDictionaryDefaultGap206Source.registry
    GeneralDictionaryDefaultGap206Source.root GeneralDictionaryVersionedGap206Install233.installed
    GeneralDictionaryVersionedGap206Feedback234.feedback :=
  GeneralRebaseDefaultFeedback284.actual_feedback

example :
    ∃ current : GeneralRebaseCertifiedWatchDriver284.Node GeneralDictionaryJournalRefinement228Source.roles,
      current.raw = GeneralDictionaryVersionedSecondInstall233.installed ∧
      GeneralRebaseCertifiedWatchDriver284.Step GeneralDictionaryOptionalInitial229.sourceRegistry
        GeneralDictionaryJournalRefinement228Source.root
        ⟨GeneralDictionaryVersionedPointStage233.point,GeneralRebaseOptionalWatch284.saved⟩ current :=
  GeneralRebaseCertifiedWatchFixtures284.Optional.accepted

example (n : Nat) (watch : List Nat) (row : GeneralPresenceDefinitionRewrite244.Entry Nat)
    (stored : row ∈ history (GeneralDictionaryVersionLoopIteration239.state n)) (missing : row.1 ∉ watch) :
    ∃ p, Joint (GeneralDictionaryVersionLoopIteration239.state n) GeneralDictionaryVersionLoopSource237.registry
      GeneralDictionaryVersionLoopSource237.root (.node 0 []) (decode (GeneralDictionaryVersionLoopIteration239.state n) p) ∧
      ¬ Joint (GeneralDictionaryVersionLoopIteration239.state n) GeneralDictionaryVersionLoopSource237.registry
        GeneralDictionaryVersionLoopSource237.root (.node 0 [])
        (GeneralPresenceOrderedBlock247.solve CommonNominalFullCarrier.model
          (GeneralRebaseFutureWatch284.trim watch (history (GeneralDictionaryVersionLoopIteration239.state n))) p) :=
  GeneralRebaseNoLiteralTrim284.Version.joint_counter n watch row stored missing
