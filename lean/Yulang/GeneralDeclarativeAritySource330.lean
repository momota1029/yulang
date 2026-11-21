import Yulang.GeneralDeclarativeArityRun330
import Yulang.GeneralDeclarativeStableTrace329
import Yulang.GeneralDeclarativeStableAssemble329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAritySource330
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarativeStableReads329 (One Heads)
open GeneralDeclarativeStableTrace329 (Actual Aligned from_trace)
open GeneralDeclarativeArityPlan330 (Plan Shape Reads extract grow)
open GeneralDeclarativeOpaqueConserve328 (Retains refl chain)
open GeneralDeclarativeGrowth327 (Extends fits derives)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEndpointProbe321 (Matches)
open GeneralDeclarativeStableInputs329 (demandNames)
open GeneralDeclarativeStableAssemble329 (Span)
open GeneralDeclarativeArityRun330 (build)
open CommonRoleOutermostResolver (All₂)

inductive Task where
  | actual (spans : List Span)
  | project (arg : Capture) (plan : Plan)

inductive Source (s : State) (c : Constructors) (i : Interpretation)
    {done : Nat → Prop} (p : Supported s done) :
    List Capture → List Pattern → Prop where
  | nil : Source s c i p [] []
  | actual : Actual s c i p arg pat spans → Source s c i p args pats →
      Source s c i p (arg::args) (pat::pats)
  | concealed : Matches (restriction p) c i arg pat →
      (∀ code, translate c i (normalize pat) = some code → Shape code) →
      Source s c i p args pats → Source s c i p (arg::args) (pat::pats)

inductive Certified (s : State) (c : Constructors) (i : Interpretation) :
    List Capture → List Pattern → List Task → Prop where
  | nil : Certified s c i [] [] []
  | actual : One s c i a p spans → (∀ u ∈ spans, Bounds s u.2) →
      Certified s c i args pats more → Certified s c i (a::args) (p::pats) (.actual spans :: more)
  | project : Bounds s a → translate c i (normalize p) = some plan.code →
      Reads s a.lower a.upper plan → Certified s c i args pats more →
      Certified s c i (a::args) (p::pats) (.project a plan :: more)

theorem certify {s : State} {p : Supported s done} (read : Source s c i p args pats) :
    ∃ tasks, Certified s c i args pats tasks := by
  induction read with
  | nil => exact ⟨[],.nil⟩
  | actual set _ ih =>
    obtain ⟨_,_,print,real,spots⟩ := set.reads
    obtain ⟨one,ranges⟩ := from_trace set.args print real spots
    obtain ⟨tasks,rest⟩ := ih
    exact ⟨.actual _ :: tasks,.actual one ranges rest⟩
  | concealed matchOk fragment _ ih =>
    obtain ⟨range,code,_,_,printed,lo,hi⟩ := matchOk
    obtain ⟨plan,reread,current⟩ := extract (fragment code printed) lo hi
    obtain ⟨tasks,rest⟩ := ih
    exact ⟨.project _ plan :: tasks,.project range (reread ▸ printed) current rest⟩

theorem transport_one {s t : State} (more : Extends s t) (known : One s c i a p spans) :
    One t c i a p spans := by
  obtain ⟨code,form,print,read,walk⟩ := known.actual
  exact ⟨fits more known.fits,code,form,print,derives more read,walk⟩

theorem transport {s t : State} (more : Extends s t) (jobs : Certified s c i args pats tasks) :
    Certified t c i args pats tasks := by
  induction jobs with
  | nil => exact .nil
  | actual here range _ later => exact .actual (transport_one more here) (fun u h => fits more (range u h)) later
  | project range written found _ later => exact .project (fits more range) written (grow more found) later

def run (keep : List Nat) (s : State) : List Task → GeneralDeclarativeStableInputs329.Built
  | [] => ⟨s,[]⟩
  | .actual here :: rest =>
    let out := run keep s rest
    ⟨out.state,here ++ out.spans⟩
  | .project arg plan :: rest =>
    let named := GeneralDeclarativeArityRun330.run keep s arg plan
    let out := run keep named.state rest
    ⟨out.state,named.binds ++ out.spans⟩

theorem replay_inputs {s : State} (keep : List Nat) (jobs : Certified s c i args pats tasks) :
    let out := run keep s tasks
    Retains s out.state keep ∧ Heads out.state c i args pats out.spans ∧
      ∀ u ∈ out.spans, Bounds out.state u.2 := by
  induction tasks generalizing s args pats with
  | nil => cases jobs; exact ⟨refl s keep,.nil,fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons first rest ih =>
    cases jobs with
    | actual slice bounded later =>
      obtain ⟨lift,observed,hs⟩ := ih later
      refine ⟨lift,.cons (transport_one lift.grows slice) observed,?_⟩
      intro a seen
      rcases List.mem_append.mp seen with one|tail
      · exact fits lift.grows (bounded a one)
      · exact hs a tail
    | project bounded translated read later =>
      have one := build keep _ _ bounded read
      obtain ⟨lift,observed,hs⟩ := ih (transport one.modeled.grows later)
      have liftAll := chain one.modeled lift
      refine ⟨liftAll,.cons ⟨fits liftAll.grows bounded,_,_,translated,
        derives lift.grows one.center,one.walks⟩ observed,?_⟩
      intro a seen
      rcases List.mem_append.mp seen with oneSeen|tail
      · exact fits lift.grows (one.bounds a oneSeen)
      · exact hs a tail

/-- One input can use a fully actual supported observation (without
a constructor restriction) while another requires a checked opaque
projection. The same ordered occurrence list drives the later
I-58 writes. Nothing equates repeated positions at this stage. -/
theorem ordered {s : State} {p : Supported s done} {d : Demand} {impl : GeneralDeclarations.Declaration}
    (visible : Source s c i p d.arguments impl.head) (keep : List Nat) :
    ∃ tasks, let input := run (demandNames d ++ keep) s tasks
      Certified s c i d.arguments impl.head tasks ∧
      Retains s input.state (demandNames d ++ keep) ∧ Heads input.state c i d.arguments impl.head input.spans ∧
      ∀ u ∈ input.spans, Bounds input.state u.2 := by
  obtain ⟨tasks,ready⟩ := certify visible
  exact ⟨tasks,ready,replay_inputs (demandNames d ++ keep) ready⟩

end Yulang.GeneralDeclarativeAritySource330
