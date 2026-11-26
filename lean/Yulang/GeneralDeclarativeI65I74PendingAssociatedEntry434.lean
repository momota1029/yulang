import Yulang.GeneralDeclarativeI65I74PendingAssociatedRead434

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
open GeneralDeclarativeI65 StructuralWhere428
open Checker408 (Problem Result)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

def R17 : SourcePrimitives .withEndpoint := pendingAssociatedKernel434

def pendingReport : Result := ⟨.pending,.pending,[]⟩

/-- Only the proof-carrying original source re-read creates this
pending rule. No child selection or output needs are inserted. -/
def exactPendingTrace434 {p : Problem} (o : Replay434 p) :
    SourceTrace R17.named426 p.state p.root .pending none :=
  .other .pending o.rootSafe (.inr ⟨rfl,rfl,⟨o.original⟩⟩) .nil

theorem exact_pending_has_same_state_original_trace434 {p : Problem} (o : Replay434 p) :
    Classifies R17 p.state p.root .pending ∧ namedTraceWrites428 (exactPendingTrace434 o) = [] :=
  ⟨legacy_classification_included426 ⟨.pending,none,⟨exactPendingTrace434 o⟩,.pending⟩, rfl⟩

theorem dictionary_sound_R17 : DictionarySound R17 :=
  dictionary_sound_for_pending_associated434

def ClassifiedAs (s : I72.State) (q : Request) (r : Result) : Prop :=
  WhereAssociated432.ClassifiedAs s q r ∨
  ∃ o : Replay434 ⟨s,q⟩, r = pendingReport ∧
    Classifies R17 s q r.verdict ∧ r.writes = namedTraceWrites428 (exactPendingTrace434 o)

def ReportEvidence (s : I72.State) (m : I72.Model) (q : Request) (r : Result) : Prop :=
  WhereAssociated432.ReportEvidence s m q r ∨
  ∃ o : Replay434 ⟨s,q⟩, r = pendingReport ∧
    ¬ HasEpisodeFact434 o.original.episode.seed.slot o.original.episode.a .parentDone ∧
    ¬ HasEpisodeFact434 o.original.episode.seed.slot o.original.episode.a (.head o.original.episode.a)

inductive Witness where
  | previous (old : WhereAssociated432.Witness)
  | pendingAssociated (data : Wire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous old => WhereAssociated432.check p r old
  | .pendingAssociated data => (replay434 p data).isSome && Check408.matchesNoWrites r .pending .pending
  | .unsupported => false

theorem previous_R16_entry_is_unchanged434 (p : Problem) (r : Result)
    (old : WhereAssociated432.Witness) : check p r (.previous old) = WhereAssociated432.check p r old := rfl

theorem checked_pending_reads_actual_original_episode434 {p : Problem} {r : Result} {w : Wire}
    (yes : check p r (.pendingAssociated w) = true) :
    ∃ o : Replay434 p, replay434 p w = some o ∧ r = pendingReport := by
  obtain ⟨proof,res⟩ := splitAnd yes
  cases found : replay434 p w with
  | none => simp [found] at proof
  | some o =>
    obtain ⟨tree,verdict,writes⟩ := Check408.matchesNoWrites_exact408.mp res
    refine ⟨o,rfl,?_⟩
    cases r
    simp only at tree verdict writes
    subst_vars
    rfl

theorem check_sound (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧
    ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  cases w with
  | previous old =>
    obtain ⟨prior,exact⟩ := WhereAssociated432.check_sound p r old yes
    exact ⟨.inl prior,fun m fit => .inl (exact m fit)⟩
  | pendingAssociated data =>
    obtain ⟨o,_,rfl⟩ := checked_pending_reads_actual_original_episode434 yes
    have trace := exact_pending_has_same_state_original_trace434 o
    have noSupport := pending_episode_cannot_use_its_own_produced_head434 o.original.episode
    exact ⟨.inr ⟨o,rfl,trace.1,trace.2.symm⟩,
      fun _ _ => .inr ⟨o,rfl,noSupport.2.1,noSupport.1⟩⟩
  | unsupported => simp [check] at yes

theorem all_prior_R16_verdicts_in_R17_434 {s q r}
    (before : Classifies WhereAssociated432.R16 s q r) : Classifies R17 s q r := by
  rcases classification_has_exact_lane_rule426 before with named|endpoint
  · obtain ⟨t,e,⟨trace⟩,summary⟩ := named
    let lift := mapNamedTrace428 (left_named_rule_map428 WhereAssociated432.R16.named426
      pendingAssociatedLocal434) trace
    exact legacy_classification_included426 ⟨t,e,⟨lift.val⟩,summary⟩
  · exact endpoint_classification_included426 endpoint

theorem verified_R17_result_classifies_in_same_State434 (p : Problem) (r : Result)
    (w : Witness) (good : check p r w = true) :
    Classifies R17 p.state p.root r.verdict ∧
      ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  cases w with
  | previous old =>
    exact ⟨all_prior_R16_verdicts_in_R17_434
      (WhereAssociated432.verified_R16_result_classifies_in_same_State432 p r old good).1,
      (check_sound p r (.previous old) good).2⟩
  | pendingAssociated data =>
    obtain ⟨o,_,same⟩ := checked_pending_reads_actual_original_episode434 good
    exact ⟨same ▸ (exact_pending_has_same_state_original_trace434 o).1,
      (check_sound p r (.pendingAssociated data) good).2⟩
  | unsupported => simp [check] at good

theorem real_raw_K2_refuses_pending_witness434 {p : Problem} {r : Result} {w : Wire}
    (cyc : RootCycle p.state p.root) :
    check p r (.pendingAssociated w) = false ∧ Classifies R17 p.state p.root .rejected := by
  refine ⟨?_,root_k2_is_rejected_for_every_primitive_system cyc⟩
  cases result : check p r (.pendingAssociated w) with
  | false => rfl
  | true =>
    obtain ⟨o,_,_⟩ := checked_pending_reads_actual_original_episode434 result
    exact (o.rootSafe cyc).elim

end Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
