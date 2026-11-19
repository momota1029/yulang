import Yulang.GeneralRebaseRefreshRank275
import Yulang.GeneralRebaseTerminalBridge274

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 21000
set_option maxHeartbeats 6800000
namespace Yulang.GeneralRebaseMixedReplay275
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralRebaseTerminalMachine274 (owner firstBindings pointBindings)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseAllWidthRealized275 (successor)

inductive Stage where
 | rebase (stage : GeneralRebaseTerminalMachine274.Stage)
 | stable
 deriving DecidableEq, Repr

inductive Event where
 | rebase (event : GeneralRebaseTerminalMachine274.Event)
 | exposeKnownWidths

def next : Stage → Event → Option Stage
 | .rebase stage,.rebase event => (GeneralRebaseTerminalMachine274.next stage event).map .rebase
 | .rebase .terminal,.exposeKnownWidths => some .stable
 | _,_ => none

def replay : Stage → List Event → Option Stage
 | stage,[] => some stage
 | stage,event :: rest => (next stage event).bind fun after => replay after rest

def Transition (before after : Stage) : Prop := ∃ event, next before event = some after

def rank : Stage → Nat
 | .rebase stage => GeneralRebaseTerminalMachine274.rank stage + 1
 | .stable => 0

noncomputable def raw : Stage → State roles
 | .rebase stage => GeneralRebaseTerminalBridge274.raw stage
 | .stable => successor

def Public : Stage → Assignment → Prop
 | .rebase stage => GeneralRebaseTerminalMachine274.Public stage
 | .stable => GeneralRebaseTerminalMachine274.Public .terminal

theorem cases_of_next {before after : Stage} (s : Transition before after) :
 (∃ a b, before = .rebase a ∧ after = .rebase b ∧ GeneralRebaseTerminalMachine274.Step a b) ∨
 (before = .rebase .terminal ∧ after = .stable) := by
 obtain ⟨e,accepted⟩ := s
 cases before with
 | stable => cases e <;> cases accepted
 | rebase stage =>
   cases e with
   | rebase event =>
     cases seen : GeneralRebaseTerminalMachine274.next stage event with
     | none => simp [next,seen] at accepted
     | some b =>
       have same : Stage.rebase b = after := by simpa only [next,seen,Option.map_some,Option.some.injEq] using accepted
       subst after
       exact Or.inl ⟨stage,b,rfl,rfl,event,seen⟩
   | exposeKnownWidths =>
     cases stage <;> cases accepted
     exact Or.inr ⟨rfl,rfl⟩

theorem rank_drop {before after : Stage} (s : Transition before after) : rank after < rank before := by
 rcases cases_of_next s with ⟨_,_,rfl,rfl,prior⟩|⟨rfl,rfl⟩
 · exact Nat.succ_lt_succ (GeneralRebaseTerminalMachine274.strict prior)
 · decide

theorem accessible (stage : Stage) : Acc (fun after before => Transition before after) stage :=
 (Subrelation.wf (fun hop => rank_drop hop) (measure rank).wf).apply stage

theorem realized {before after : Stage} (s : Transition before after) :
 GeneralNominalVersionedMixedKernel234.Step registry root (raw before) (raw after) := by
 rcases cases_of_next s with ⟨_,_,rfl,rfl,prior⟩|⟨rfl,rfl⟩
 · exact GeneralRebaseTerminalBridge274.mixed_realized prior
 · exact GeneralRebaseAllWidthRealized275.realized

theorem trace_realized (begin : Stage) (events : List Event) (finish : Stage)
 (done : replay begin events = some finish) :
 B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) (raw begin) (raw finish) := by
 induction events generalizing begin with
 | nil =>
   cases Option.some.inj done
   exact .refl
 | cons e rest ih =>
   cases found : next begin e with
   | none => simp [replay,found,Option.bind] at done
   | some middle =>
     have remainder : replay middle rest = some finish := by simpa [replay,found,Option.bind] using done
     exact GeneralRebaseWeakTerminal268.append (.tail .refl (realized ⟨e,found⟩)) (ih middle remainder)

theorem public_exact (stage : Stage) (boundary : Assignment) :
 Public stage boundary ↔ GeneralRebaseCompoundRowsMeaning273.Public (raw stage) boundary := by
 cases stage with
 | rebase old => exact GeneralRebaseTerminalBridge274.public_agrees old boundary
 | stable =>
   change GeneralRebaseTerminalMachine274.Public .terminal boundary ↔ _
   refine (GeneralRebaseTerminalBridge274.public_agrees .terminal boundary).trans ?_
   constructor
   · rintro ⟨m,agree,models⟩
     exact ⟨m,agree,(GeneralRebaseAllWidthRealized275.model_exact m).mpr models⟩
   · rintro ⟨m,agree,models⟩
     exact ⟨m,agree,(GeneralRebaseAllWidthRealized275.model_exact m).mp models⟩

theorem stable_payload (boundary : Assignment) (allowed : Public .stable boundary) :
 ∃ m, Agrees m boundary ∧ Models successor m ∧
   GeneralNominalVersionedEvidence231.Evidence registry successor.core m root (.node declaration.id []) := by
 obtain ⟨m,agree,models⟩ := (public_exact .stable boundary).mp allowed
 exact ⟨m,agree,models,GeneralRebaseAllWidthStable275.evidence m models⟩

def canonical : List Event :=
 [.rebase (.install owner firstBindings 2),
  .rebase (.observe owner pointBindings 2),.rebase (.service owner),.exposeKnownWidths]

theorem run : replay (.rebase .source) canonical = some .stable := rfl

theorem actual_kernel_stops : ∀ after, ¬ GeneralNominalVersionedMixedKernel234.Step registry root (raw .stable) after :=
 GeneralRebaseAllWidthStable275.halted

end Yulang.GeneralRebaseMixedReplay275
