import Yulang.GeneralDeclarativeVersionedRootGuard342

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15500
set_option maxHeartbeats 8500000
namespace Yulang.GeneralDeclarativeVersionedRootShape342
open GeneralWhereOriginSingleSource318 (declaration sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot actualDemand original_arguments ready_iff)
open GeneralDeclarativeVersionedRootRead342 (publicRow)
open GeneralDeclarativeVersionedChildWitness342 (waiting)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported Backed backed_iff restriction)
open GeneralDeclarativeStableTrace329 (Actual)
open GeneralDeclarativeTrace321 (Trace Occurrence)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeTaggedElection340 (Election Ranked)
open GeneralDeclarativeTaggedInputs340 (Inputs)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)

abbrev point : Capture := ⟨0,0,0⟩
abbrev typePoint : Capture := ⟨2,2,2⟩
abbrev spans : List (Nat × Capture) := [(0,typePoint),(1,typePoint)]
abbrev uses : List Occurrence := [⟨0,.actual,2⟩,⟨1,.actual,2⟩]

theorem read_modes {done : Nat → Prop} (p : Supported observedRoot done)
    (backed : Backed p publicRow) (mode : GeneralNominalMaterialization.Mode) :
    Trace (restriction p) mode 0 (.nominal 0 [.variable 0,.variable 1]) uses := by
  exact Trace.nominal (args := [2,2]) (alias_refl _) ((backed_iff p publicRow).mpr backed)
    (.cons .capture (.cons .capture .nil))

theorem exact_inputs {done : Nat → Prop} (p : Supported observedRoot done)
    (backed : Backed p publicRow) (keep : List Nat) :
    Inputs p sourceRegistry.constructors interpretation keep observedRoot
      actualDemand.arguments declaration.head observedRoot spans [] := by
  have exact : Actual observedRoot sourceRegistry.constructors interpretation p point
      (.app 0 [.var 0,.var 1]) spans := by
    exact ⟨point_bounded _ _,.nominal 0 [.variable 0,.variable 1],uses,
      rfl,read_modes p backed .actual,
      .cons ⟨rfl,rfl,point_bounded _ _⟩ (.cons ⟨rfl,rfl,point_bounded _ _⟩ .nil)⟩
  rw [original_arguments]
  exact .cons (.prior (.old (.named exact))) .nil

theorem current_bindings :
    spans.map (fun pair => (pair.1,pair.2.lower,pair.2.upper)) =
      GeneralDeclarativeVersionedPhysical342.current.packet.bindings := by
  rw [GeneralRebaseRetarget275.packet_bindings (after := GeneralWherePhysicalActive319.ctx)
    GeneralWherePhysicalCurrentRead319.plan GeneralWherePhysicalActive319.refines rfl
    GeneralDeclarativeVersionedPhysical342.observed,GeneralWherePhysicalCurrentRead319.bindings]
  rfl

def level (name : Nat) : Nat := if name = 0 then 1 else 0

theorem ranked : Ranked observedRoot level := by
  refine ⟨?_,?_,?_⟩
  · intro _ _ sub
    induction sub with
    | refl _ => exact Nat.le_refl _
    | interval h => cases h
    | constraint h => cases h
    | trans _ _ a b => exact Nat.le_trans a b
  · intro a b one
    have no := List.mem_singleton.mp one
    cases congrArg Equation.right no
  · intro row one n seen _
    cases List.mem_singleton.mp one
    change n ∈ [2,2] at seen
    have eq : n = 2 := (List.mem_cons.mp seen).elim id List.mem_singleton.mp
    subst n
    decide

/-- For the observed C319 root and its literal declared nominal head,
independent support of the protected physical row is sufficient for
the existing endpoint election and produces the exact two named
input captures. This is not yet its checked ordered body receipt. -/
theorem root_election {done : Nat → Prop} (p : Supported observedRoot done)
    (backed : Backed p publicRow) :
    Election p sourceRegistry interpretation waiting actualDemand declaration := by
  refine ⟨(ready_iff p).mpr backed,⟨level,ranked⟩,fun ⟨_,_,h⟩ => h,?_,?_⟩
  · refine ⟨⟨List.mem_cons_self,rfl⟩,?_⟩
    change CommonRoleOutermostResolver.All₂ (GeneralDeclarativeTaggedElection340.Head p sourceRegistry.constructors interpretation)
      actualDemand.arguments declaration.head
    rw [original_arguments]
    exact .cons (.named ⟨point_bounded _ _,.nominal 0 [.variable 0,.variable 1],uses,uses,rfl,
      read_modes p backed .lower,read_modes p backed .upper⟩) .nil
  · intro other possible
    rcases List.mem_cons.mp possible.1.1 with same|tail
    · cases same
      rfl
    · cases List.mem_singleton.mp tail
      cases possible.1.2

end Yulang.GeneralDeclarativeVersionedRootShape342
