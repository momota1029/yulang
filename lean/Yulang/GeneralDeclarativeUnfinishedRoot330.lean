import Yulang.GeneralDeclarativeOverlap321
import Yulang.GeneralDeclarativeCurrentReceipt330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeUnfinishedRoot330
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeLowerKnown321 (Alias Knows Ready Delayed constructorTag alias_refl)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativePriority321 (Local RootRecurs Recurs overlap_outside_fragment selected_generated)
open CommonRoleOutermostResolver (Frontier Classify)

/-- I-59: for the *same* unexpandable argument, the ordinary root is
on a structural cycle and an unfinished producer has supplied its
only available kind of head evidence (no authorized head at this
argument, though the ordinary row is real). No candidate inspection
or where-generation premise appears in this reason. -/
def UnfinishedRoot {s : State} (p : Supported s done) (d : Demand) : Prop :=
  ∃ arg ∈ d.arguments,
    (∀ tag, ¬Knows (restriction p) arg.lower tag) ∧
    AliasCycle s (observed s) arg.lower ∧
    ∃ row : Equation, ∃ owner tag,
      p.derivesFrom row (.output owner) ∧ ¬done owner ∧
      Alias s arg.lower row.left ∧ constructorTag row.right = some tag

theorem blocked_and_cyclic {s : State} {p : Supported s done} (reason : UnfinishedRoot p d) :
    Delayed p d ∧ RootRecurs s d := by
  obtain ⟨arg,used,none,cycle,_⟩ := reason
  exact ⟨⟨arg,used,none⟩,⟨arg,used,cycle⟩⟩

/-- Conservative extension of the pre-I-59 declarative slice only.
This adds an explicit rejection reason; it does not pretend that
every other raw diagnostic has already been made complete. -/
inductive Local59 (s : State) (r : GeneralDeclarations.Registry) (i : GeneralNominalInspection.Interpretation)
    {done : Nat → Prop} (p : Supported s done) (tests : GeneralDeclarativePriority321.Candidates)
    (generate : Demand → GeneralDeclarations.Declaration → List Demand → Prop) :
    Demand → Frontier Demand → Prop where
  | prior : Local s r i p tests generate d outcome → Local59 s r i p tests generate d outcome
  | rootK2 : UnfinishedRoot p d → Local59 s r i p tests generate d .rejected

theorem priority {s : State} {p : Supported s done} {d : Demand} (reason : UnfinishedRoot p d)
    (oldOrNew : Local59 s r i p tests generate d out) : out = .rejected := by
  cases oldOrNew with
  | prior old =>
    have both := blocked_and_cyclic reason
    exact False.elim (overlap_outside_fragment both.1 (.inl both.2) old)
  | rootK2 => rfl

theorem reject_without_children {s : State} {p : Supported s done} {d : Demand}
    (reason : UnfinishedRoot p d) :
    Classify (Local59 s r i p tests generate) d .rejected :=
  ⟨.rejected,.rejected (.rootK2 reason),.rejected⟩

theorem selected_old_exact {s : State} {p : Supported s done} :
    Local59 s r i p tests generate d (.selected key kids) ↔
      Local s r i p tests generate d (.selected key kids) :=
  ⟨fun h => by cases h with | prior old => exact old, .prior⟩

open GeneralDeclarativeCurrentReceipt330 (Staged local_witness)
open GeneralDeclarativeEvidenceFold325 (same_model LocalWitness)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeHead320 (Models)

theorem receipt_witness {s : State} {p : Supported s done}
    (checked : GeneralDeclarations.Checked r) (coverage : Coverage r i) :
    LocalWitness r i s (Local59 s r i p tests (Staged s r i)) := by
  intro m fit d isDeclared key kids selected
  exact local_witness (p := p) (tests := tests) checked coverage m fit d isDeclared key kids
    (selected_old_exact.mp selected)

theorem dictionary_sound {s : State} {p : Supported s done}
    (checked : GeneralDeclarations.Checked r) (coverage : Coverage r i)
    (named : Declared r d) (fit : Models s m)
    (chosen : Classify (Local59 s r i p tests (Staged s r i)) d (.selected dictionary)) :
    Evidence r i m d dictionary :=
  same_model (receipt_witness checked coverage) fit named chosen

open GeneralDeclarativeOverlap321 (state support input self no_independent_head)
open GeneralDeclarativeGraphRows321 (pending_nominal_self_cycle)
open GeneralDeclarativeK2Alias321 (cycle_in_alias_graph)

/-- Uses the exact C321 fixture, not a synthetic precedence flag.
A single unsettled nominal row is ordinary, forbidden for probing,
and already closes the unnamed recursive root. -/
theorem cycle321_exact : UnfinishedRoot (support False) input := by
  refine ⟨⟨0,0,0⟩,List.mem_cons_self,?_,?_,self,1,.nominal 0 1,⟨rfl,.inl rfl⟩,
    (fun impossible => impossible),alias_refl _,rfl⟩
  · intro tag known
    have no := no_independent_head
    obtain ⟨arg,inInput,cannot⟩ := no
    cases List.mem_singleton.mp inInput
    exact cannot tag known
  · exact cycle_in_alias_graph (pending_nominal_self_cycle (support False) 1 ⟨rfl,.inl rfl⟩)

theorem actual_i59 (r : GeneralDeclarations.Registry) (i : GeneralNominalInspection.Interpretation)
    (tests : GeneralDeclarativePriority321.Candidates) :
    Classify (Local59 state r i (support False) tests (fun _ _ _ => False)) input .rejected :=
  reject_without_children cycle321_exact


/-- The added exception does not affect ordinary delayed expansion
in the absence of the root cycle, nor does it inspect deeper candidate
positions to find one. -/
theorem unchanged_without_root {s : State} {p : Supported s done}
    (safeRoot : ¬ RootRecurs s d) :
    Local59 s r i p tests generate d verdict ↔ Local s r i p tests generate d verdict := by
  constructor
  · intro after
    cases after with
    | prior before => exact before
    | rootK2 new => exact False.elim (safeRoot (blocked_and_cyclic new).2)
  · exact .prior

theorem no_emission_needed {s : State} {p : Supported s done} {d : Demand}
    (reason : UnfinishedRoot p d) :
    Classify (Local59 s r i p tests (fun _ _ _ => False)) d .rejected :=
  reject_without_children reason

end Yulang.GeneralDeclarativeUnfinishedRoot330
