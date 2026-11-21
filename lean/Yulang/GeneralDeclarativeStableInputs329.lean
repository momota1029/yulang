import Yulang.GeneralDeclarativeStableMerge329
import Yulang.GeneralDeclarativeEndpointProbe321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableInputs329
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarativeOpaquePlan328 (Plan Shape Read extract grows)
open GeneralDeclarativeOpaqueNested328 (build)
open GeneralDeclarativeOpaqueConserve328 (Retains chain refl)
open GeneralDeclarativeGrowth327 (Extends fits derives)
open GeneralDeclarativeStableReads329 (Heads One weakened)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEndpointProbe321 (Matches HeadMatches)
open CommonRoleOutermostResolver (All₂)

abbrev Job := Capture × Plan

inductive Jobs (s : State) (c : Constructors) (i : Interpretation) :
    List Capture → List Pattern → List Job → Prop where
  | nil : Jobs s c i [] [] []
  | cons : Bounds s a → translate c i (normalize p) = some plan.code →
      Read s a.lower a.upper plan → Jobs s c i args pats rest →
      Jobs s c i (a :: args) (p :: pats) ((a,plan) :: rest)

theorem transport {s t : State} (more : Extends s t) (known : Jobs s c i args pats plans) :
    Jobs t c i args pats plans := by
  induction known with
  | nil => exact .nil
  | cons bounds print read _ after =>
    exact .cons (fits more bounds) print (grows more read) after

structure Built where
  state : State
  spans : List (Nat × Capture)

def run (keep : List Nat) (s : State) : List Job → Built
  | [] => ⟨s,[]⟩
  | (arg,plan) :: rest =>
    let one := GeneralDeclarativeOpaqueNested328.run keep s arg plan
    let tail := run keep one.state rest
    ⟨tail.state,one.binds ++ tail.spans⟩

/-- Reassemble the genuine supported lower/upper traces across the
whole ordered head, not one independently chosen binder table per
argument. Repeated keys remain visibly repeated in the compiled list. -/
theorem source {s : State} {p : Supported s done}
    (visible : ∀ raw ∈ pats, ∃ code, translate c i (normalize raw) = some code ∧ Shape code)
    (reads : All₂ (Matches (restriction p) c i) args pats) :
    ∃ jobs, Jobs s c i args pats jobs := by
  induction reads with
  | nil => exact ⟨[],.nil⟩
  | @cons a raw args pats early other ih =>
    obtain ⟨bounds,code,_,_,print,lo,hi⟩ := early
    obtain ⟨use,known,shape⟩ := visible raw List.mem_cons_self
    cases Option.some.inj (known.symm.trans print)
    obtain ⟨plan,codeEq,seen⟩ := extract shape lo hi
    obtain ⟨more,prepared⟩ := ih (fun p h => visible p (List.mem_cons_of_mem _ h))
    exact ⟨(a,plan)::more,.cons bounds (codeEq ▸ known) seen prepared⟩

theorem build_all {s : State} (keep : List Nat) (known : Jobs s c i args pats jobs) :
    let out := run keep s jobs
    Retains s out.state keep ∧ Heads out.state c i args pats out.spans ∧
      ∀ use ∈ out.spans, Bounds out.state use.2 := by
  induction jobs generalizing s args pats with
  | nil => cases known; exact ⟨refl s keep,.nil,fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons task jobs ih =>
    obtain ⟨a,plan⟩ := task
    cases known with
    | cons range translated uses more =>
      let one := GeneralDeclarativeOpaqueNested328.run keep s a plan
      have b := build keep plan a range uses
      have other := transport b.modeled.grows more
      obtain ⟨carry,read,knownRange⟩ := ih other
      have all := chain b.modeled carry
      refine ⟨all,.cons ⟨fits all.grows range,plan.code,one.form,translated,
        derives carry.grows b.center,b.ordered⟩ read,?_⟩
      intro entry listed
      change entry ∈ one.binds ++ (run keep one.state jobs).spans at listed
      rcases List.mem_append.mp listed with seen|after
      · exact fits carry.grows (b.bounds entry seen)
      · exact knownRange entry after

def demandNames (d : Demand) : List Nat :=
  (d.arguments.flatMap fun cap => [cap.lower,cap.center,cap.upper]) ++ d.outputs.map (·.target)

theorem for_head {s : State} {p : Supported s done} {d : Demand}
    (visible : ∀ raw ∈ impl.head, ∃ code, translate c i (normalize raw) = some code ∧ Shape code)
    (reads : HeadMatches (restriction p) c i d impl) (keep : List Nat) :
    ∃ jobs, let found := run (demandNames d ++ keep) s jobs
      Jobs s c i d.arguments impl.head jobs ∧
      Retains s found.state (demandNames d ++ keep) ∧
      Heads found.state c i d.arguments impl.head found.spans ∧
      ∀ use ∈ found.spans, Bounds found.state use.2 := by
  obtain ⟨plan,seen⟩ := source visible reads
  exact ⟨plan,seen,build_all (demandNames d ++ keep) seen⟩

end Yulang.GeneralDeclarativeStableInputs329
