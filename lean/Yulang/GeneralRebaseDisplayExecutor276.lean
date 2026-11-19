import Yulang.GeneralRebaseDisplayAcc276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralRebaseDisplayExecutor276
open GeneralNominalExamples (registry state context displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralRebaseDisplayFrame276 (before after after_models)
open GeneralRebaseDisplayAcc276 (only_step)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)

inductive Phase where | source | settled
 deriving DecidableEq, Repr
inductive Goal where | parent | child
 deriving DecidableEq, Repr

def rank : Phase → Nat
 | .source => 1
 | .settled => 0

def height : Goal → Nat
 | .parent => 2
 | .child => 1

def invocation : Goal → GeneralSourceDictionaries.Occurrence roles
 | .parent => displayRoot
 | .child => displayChild

def localTable : Goal → Nat × List Goal
 | .parent => (1,[.child])
 | .child => (3,[])

def emit : Nat → Goal → Option Payload
 | 0,_ => none
 | fuel+1,goal => do
   let sub ← (localTable goal).2.mapM (emit fuel)
   pure (.node (localTable goal).1 sub)

def step (phase : Phase) (key : Nat) : Option Phase :=
 match phase with
 | .source => if key = (localTable .parent).1 then some .settled else none
 | .settled => none

def run (key : Nat) : Option (Phase × Payload) := do
 let phase ← step .source key
 let dictionary ← emit (height .parent) .parent
 pure (phase,dictionary)

noncomputable def raw : Phase → State roles
 | .source => before
 | .settled => after

theorem phase_distinct : before ≠ after := by
 intro same
 have routes := congrArg (fun (s : State roles) => s.core.erased.current.edges) same
 change [] = after.core.erased.current.edges at routes
 rw [GeneralRebaseDisplayFrame276.actual_edges] at routes
 cases routes

theorem exact_steps (a b : Phase) :
 (∃ key, step a key = some b) ↔ Step registry displayRoot (raw a) (raw b) := by
 cases a <;> cases b
 · constructor
   · rintro ⟨key,valid⟩
     by_cases h : key = 1 <;> simp [step,localTable,h] at valid
   · intro real
     exact False.elim (phase_distinct (only_step _ real))
 · exact ⟨fun _ => GeneralRebaseDisplayStep276.actual_step,fun _ => ⟨1,rfl⟩⟩
 · constructor
   · rintro ⟨_,impossible⟩
     cases impossible
   · intro forbidden
     exact False.elim (GeneralRebaseDisplayStable276.halted _ forbidden)
 · constructor
   · rintro ⟨_,impossible⟩
     cases impossible
   · intro forbidden
     exact False.elim (GeneralRebaseDisplayStable276.halted _ forbidden)

theorem complete (state : State roles) (reached : B4Target.Steps (Step registry displayRoot) before state) :
 ∃ phase, raw phase = state := by
 rcases GeneralRebaseDisplayAcc276.exact_reached state reached with rfl|rfl
 · exact ⟨.source,rfl⟩
 · exact ⟨.settled,rfl⟩

theorem model_exact (phase : Phase) (m : Assignment) :
 Models (raw phase) m ↔ GeneralNominalState.Models (state true) m := by
 cases phase
 · exact (GeneralNominalVersionedJournal232.initial_models _ _ _).trans
     ⟨And.left,fun raw => ⟨raw,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩⟩
 · exact after_models m

theorem table_exact (goal : Goal) :
 GeneralNominalVersionedMixedBoundary234.Local registry after (invocation goal)
   (.selected (localTable goal).1 ((localTable goal).2.map invocation)) := by
 cases goal
 · exact GeneralRebaseDisplaySelection276.picked_parent
 · exact GeneralRebaseDisplaySelection276.picked_child

theorem child_smaller (a b : Goal) (found : b ∈ (localTable a).2) :
 height b < height a := by
 cases a
 · cases List.mem_singleton.mp found
   decide
 · cases found

theorem canonical : run 1 = some (.settled,.node 1 [.node 3 []]) := rfl

theorem underfuel : emit 1 .parent = none := rfl
theorem wrong_key : run 3 = none := rfl

theorem run_exact (key : Nat) (phase : Phase) (data : Payload) :
 run key = some (phase,data) ↔ key = 1 ∧ phase = .settled ∧ data = .node 1 [.node 3 []] := by
 by_cases h : key = 1
 · subst key
   rw [canonical]
   simp [eq_comm]
 · simp [run,step,localTable,h]

theorem readback (key : Nat) (phase : Phase) (data : Payload) (m : Assignment)
 (valid : GeneralNominalState.Models (state true) m) (found : run key = some (phase,data)) :
 Models (raw phase) m ∧ GeneralNominalVersionedEvidence231.Evidence registry (raw phase).core m displayRoot data := by
 obtain ⟨_,rfl,rfl⟩ := (run_exact key phase data).mp found
 exact ⟨(model_exact _ m).mpr valid,GeneralRebaseDisplayEvidence276.source_nonleaf m valid⟩

end Yulang.GeneralRebaseDisplayExecutor276
