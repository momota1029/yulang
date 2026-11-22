import Yulang.GeneralDeclarativeWitnessPointInput349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessPointEvidence349
open GeneralDeclarativeWitnessPointInput349 (PointProblem lit pick picked printed head_exact pointArgs args_exact)
open GeneralDeclarativeWitnessGround349 (row occurs occurrence safeRows ranked)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeHead320 (Equation State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeLowerKnown321 (alias_refl knows_row)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeStableTrace329 (Actual)
open GeneralDeclarativeWitnessHead334 (Actuals full)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalMaterialization (Mode)
open CommonRoleOutermostResolver (All₂)

def support (p : PointProblem)
    (accepted : occurs p.problem.state p.atName p.kind = true) :
    Supported p.problem.state (fun _ => False) where
  derivesFrom e origin := e = row p.atName p.kind ∧ origin = .source
  ordinary := by
    rintro _ _ ⟨rfl,_⟩
    exact occurrence.mp accepted

theorem source_row (p : PointProblem) (accepted : occurs p.problem.state p.atName p.kind = true) :
    row p.atName p.kind ∈ (restriction (support p accepted)).equations :=
  from_source _ ⟨rfl,rfl⟩

theorem traced (p : PointProblem) (accepted : occurs p.problem.state p.atName p.kind = true) (mode : Mode) :
    Trace (restriction (support p accepted)) mode p.atName (.primitive p.kind []) [] :=
  .primitive (args := []) (alias_refl _) (source_row p accepted) .nil

/-- Positive point fragment only: a still-unrecognized endpoint probe
blocks. The only declaration at the checked role has an actual
positive endpoint probe, so this predicate cannot hide a competitor. -/
def waiting (p : PointProblem) (s : SourceBundle)
    (accepted : occurs p.problem.state p.atName p.kind = true) (d : Demand) (impl : Declaration) : Prop :=
  ¬ HeadMatches (restriction (support p accepted)) (registry s).constructors (interpretation s.snapshot) d impl

theorem matching {p : PointProblem} {s : SourceBundle} {impl : Declaration}
    (accepted : occurs p.problem.state p.atName p.kind = true)
    (point : pointArgs p = true) {ctor : Nat} (head : printed p s impl = some ctor) :
    HeadMatches (restriction (support p accepted)) (registry s).constructors (interpretation s.snapshot)
      p.problem.demand impl := by
  obtain ⟨pattern,code⟩ := head_exact head
  unfold HeadMatches
  rw [args_exact point,pattern]
  exact .cons ⟨point_bounded _ _,_,[],[],code,traced p accepted .lower,traced p accepted .upper⟩ .nil

theorem actual_source {p : PointProblem} {s : SourceBundle} {impl : Declaration}
    (accepted : occurs p.problem.state p.atName p.kind = true)
    (point : pointArgs p = true) {ctor : Nat} (head : printed p s impl = some ctor) :
    Actuals (support p accepted) (registry s).constructors (interpretation s.snapshot) []
      p.problem.state p.problem.demand.arguments impl.head p.problem.state [] := by
  obtain ⟨pattern,code⟩ := head_exact head
  rw [args_exact point,pattern]
  exact .cons (.named ⟨point_bounded _ _,_,[],code,traced p accepted .actual,.nil⟩) .nil

theorem choice {p : PointProblem} {s : SourceBundle} {impl : Declaration}
    (accepted : occurs p.problem.state p.atName p.kind = true)
    (point : pointArgs p = true) (shape : safeRows p.problem.state = true)
    (only : pick p s = some impl) {ctor : Nat} (head : printed p s impl = some ctor) :
    Elected p.problem.state (registry s) (interpretation s.snapshot) (support p accepted)
      (candidates (support p accepted) (registry s) (interpretation s.snapshot) (waiting p s accepted))
      p.problem.demand impl := by
  obtain ⟨member,role,unique⟩ := picked only
  have matchHere := matching accepted point head
  refine ⟨?_,GeneralDeclarativeTaggedElection340.safe (ranked shape),?_,
    ⟨⟨member,role⟩,.inl matchHere⟩,?_⟩
  · intro a found
    rw [args_exact point] at found
    cases List.mem_singleton.mp found
    exact ⟨_,knows_row (source_row p accepted) rfl⟩
  · rintro ⟨other,visible,blocked⟩
    have same := unique other visible.1 visible.2
    subst other
    exact blocked matchHere
  · intro other survives
    exact congrArg Declaration.id (unique other survives.1.1 survives.1.2)

end Yulang.GeneralDeclarativeWitnessPointEvidence349
