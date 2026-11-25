import Yulang.GeneralDeclarativeI65I72GroundedProducerReplay405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Result Summarizes Tree)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeInspect321 (Visit)
open GeneralDeclarativeHead320 (Equation)

/-- Exact address of the first actually inspected value child of the
completed lower, independent upper rule, not a lookup by equality of
declared ids. A full native scan is not claimed. -/
structure NativeEntryAddress405 (s : State) (q : Request) (row : Declaration) (need : OutputNeed s) where
  entry : CompletedUnaryEntry404 s q row need
  visibleOrdinal : Nat
  visitedRow : (visible s.core q)[visibleOrdinal]? = some row
  rawOrdinal : Nat
  fromVisible : unfilterOrdinal395 (fun d : Declaration => d.role == q.demand.role)
    (authoredRegistry s.core.current).declarations visibleOrdinal = some rawOrdinal
  visitedOriginal : (authoredRegistry s.core.current).declarations[rawOrdinal]? = some row

def NativeEntryAddress405.site {s q row need} (observed : NativeEntryAddress405 s q row need) :
    CandidateVisit :=
  ⟨observed.rawOrdinal,0,[0],.value,false,observed.entry.lowerChild⟩

theorem derive_native_entry_address405 {s q row need}
    (read : CompletedUnaryEntry404 s q row need) :
    Nonempty (NativeEntryAddress405 s q row need) := by
  obtain ⟨i,seen⟩ := List.mem_iff_getElem?.mp read.visibleRow
  obtain ⟨j,unfilter,orig⟩ := unfilterOrdinal395_exact (fun d : Declaration => d.role == q.demand.role)
    (authoredRegistry s.core.current).declarations i seen
  exact ⟨⟨read,i,seen,j,unfilter,orig⟩⟩

theorem native_entry_uses_exact_complete_rhs_and_position405 {s q row need needs}
    (address : NativeEntryAddress405 s q row need)
    (support : SupportForest completedChoiceSource404 s needs) (i : Nat)
    (atI : needs[i]? = some need) :
    (⟨address.entry.input.lower,.nominal address.entry.key [.variable address.entry.lowerChild]⟩ : Equation) ∈
      s.core.current.ordinary.equations ∧
    (authoredRegistry s.core.current).declarations[address.site.declarationOrdinal]? = some row ∧
    q.demand.arguments[address.site.argumentOrdinal]? = some address.entry.input ∧
    row.head[address.site.argumentOrdinal]? = some address.entry.written ∧
    address.site.path = [0] ∧
    Visit (GeneralDeclarativeGraphRows321.structural s.core.current.ordinary)
      address.entry.lowerChild address.entry.query address.site.site := by
  have enters := completed_lower_justifies_entered_native_child404 address.entry
    completed_choice_keeps_fixed_rows404 support i atI
  exact ⟨enters.1,address.visitedOriginal,by simp [NativeEntryAddress405.site,address.entry.exactInput],
    by simp [NativeEntryAddress405.site,address.entry.exactHead],rfl,enters.2.2⟩

/-- The actual rule is data before erasure to C402. When raw root K2
wins there is no candidate visit. The entered constructor records
the first lower child of *this candidate*, not a total ordering of
all other candidates before a rejecting diagnosis. -/
inductive GroundedK2Rejection405 (s : State) (q : Request) : Type where
  | raw (cycle : RootCycle s q)
  | entered {needs : List (OutputNeed s)} (safe : ¬ RootCycle s q)
      (support : SupportForest completedChoiceSource404 s needs) {row : Declaration} {need : OutputNeed s}
      (index : Nat) (atIndex : needs[index]? = some need)
      (address : NativeEntryAddress405 s q row need)
      (cycle : CurrentCycleAt s address.entry.lowerChild)

def GroundedK2Rejection405.visits {s q} (run : GroundedK2Rejection405 s q) : List CandidateVisit :=
  match run with
  | .raw _ => []
  | .entered _ _ _ _ address _ => [address.site]

def GroundedK2Rejection405.source {s q} (run : GroundedK2Rejection405 s q) :
    SourceTrace completedChoiceSource404 s q .rejected none :=
  match run with
  | .raw cycle => .rootK2 cycle
  | .entered safe support i there address cycle =>
    .other .rejected safe (.inl (.inr ⟨rfl,⟨⟨_,i,there,_,address.entry,cycle⟩⟩⟩)) support

theorem k2_replay_rejects_without_model405 {s q} (run : GroundedK2Rejection405 s q) :
    Classifies completedChoiceSource404 s q .rejected :=
  ⟨.rejected,none,⟨run.source⟩,.rejected⟩

theorem k2_replay_visits_are_justified405 {s q} (run : GroundedK2Rejection405 s q) :
    (RootCycle s q ∧ run.visits = []) ∨
    (¬ RootCycle s q ∧ ∃ (row : Declaration) (need : OutputNeed s)
        (address : NativeEntryAddress405 s q row need),
      run.visits = [address.site] ∧ CurrentCycleAt s address.site.site ∧
      Visit (GeneralDeclarativeGraphRows321.structural s.core.current.ordinary)
        address.entry.lowerChild address.entry.query address.site.site) := by
  cases run with
  | raw cycle => exact .inl ⟨cycle,rfl⟩
  | entered safe support i there address cycle =>
    exact .inr ⟨safe,_,_,address,rfl,cycle,
      (native_entry_uses_exact_complete_rhs_and_position405 address support i there).2.2.2.2.2⟩

theorem k2_replay_cannot_relabel_as_selected405 {s q} (run : GroundedK2Rejection405 s q) :
    ∀ d, ¬Classifies completedChoiceSource404 s q (.selected d) := by
  intro d
  cases run with
  | raw cycle => exact root_k2_never_selects cycle
  | entered safe support i there address cycle =>
    intro chosen
    exact completed_structural_input_never_silently_dropped404
      ⟨_,i,there,_,address.entry,cycle⟩ (completed_ambiguity_preserves_exact_selection404.mp chosen)

/-- The unfinished inner edge still participates in raw K2; that
same edge is absent from the support restriction. The outer visit
has the original producer's separate completed finite derivation. -/
theorem original_completed_support_then_pending_inner_k2405 {s producer consumer t e dict row}
    (source : SourceTrace variableWithNativeK2403 s producer t (some e))
    (done : Summarizes t (.selected dict)) (i : Fin producer.demand.outputs.length)
    (address : NativeEntryAddress405 s consumer row (needOfSelected404 e dict i))
    (rawSafe : ¬ RootCycle s consumer)
    {completed : Nat → Prop} (authority : GeneralDeclarativeOrigins321.Supported s.core.current.ordinary completed)
    (tag owner : Nat)
    (observed : authority.derivesFrom
      (⟨address.entry.lowerChild,.nominal tag [.variable address.entry.lowerChild]⟩ : Equation) (.output owner))
    (pending : ∀ o, authority.derivesFrom
      (⟨address.entry.lowerChild,.nominal tag [.variable address.entry.lowerChild]⟩ : Equation) o →
        ∃ n, o = .output n ∧ ¬ completed n) :
    (⟨address.entry.lowerChild,.nominal tag [.variable address.entry.lowerChild]⟩ : Equation)
      ∉ (GeneralDeclarativeOrigins321.restriction authority).equations ∧
    ∃ run : GroundedK2Rejection405 s consumer,
      run.visits = [address.site] ∧ Classifies completedChoiceSource404 s consumer .rejected := by
  let exactSupport : SupportForest completedChoiceSource404 s [needOfSelected404 e dict i] :=
    .cons (preserve_completed_native_sources404
      (preserve_completed_lower_when_admitting_native404 (preserve_c403_derivation404 source))) done rfl .nil
  have unfiltered := GeneralDeclarativeK2Alias321.cycle_in_alias_graph
    (GeneralDeclarativeGraphRows321.pending_nominal_self_cycle authority owner observed)
  let run := GroundedK2Rejection405.entered rawSafe exactSupport 0 rfl address unfiltered
  exact ⟨GeneralDeclarativeOrigins321.pending_only authority _ pending,run,rfl,k2_replay_rejects_without_model405 run⟩

end Yulang.GeneralDeclarativeI65.I72
