import Yulang.CommonRolePotentialChildClosure
import Yulang.CommonRoleOrdinaryKnownness
import Yulang.CommonRoleOpenRecursivePass

/-! Finite work domain for state-dependent int-only source templates.
This is an overapproximation, not general interval inference: non-int and
unmaterialized slots remain unknown. Dynamically creating templates is excluded. -/
namespace Yulang.CommonRoleMaterializedDomain
open CommonRoleSettledSyntax CommonRoleOpenProducer
open CommonRolePotentialChildClosure
open CommonRoleSettledConstraints (State)

/-- Slots preserve source indices; equal Ty values do not identify source slots. -/
inductive Endpoint (n : Nat) where
  | fixed (t : Ty)
  | slot (i : Fin n)
  | wrap (c : Constructor) (inner : Endpoint n)

def Endpoint.eval (s : State n) : Endpoint n → Ty
  | .fixed t => t
  | .slot i => if CommonRoleOrdinaryKnownness.materialize s.atoms i =
      some Roles.Examples.int then .atom .int else .unknown
  | .wrap c e => .wrap c (e.eval s)

/-- Independent slot choices intentionally overapproximate shared-slot consistency. -/
def Endpoint.variants : Endpoint n → List Ty
  | .fixed t => [t]
  | .slot _ => [.unknown, .atom .int]
  | .wrap c e => e.variants.map (.wrap c)

theorem eval_present (s : State n) (e : Endpoint n) : e.eval s ∈ e.variants := by
  induction e with
  | fixed t => simp [Endpoint.eval, Endpoint.variants]
  | slot i => simp only [Endpoint.eval]; split <;> simp [Endpoint.variants]
  | wrap c e ih => exact List.mem_map.mpr ⟨_, ih, rfl⟩

theorem int_materialized (s : State n) (i : Fin n) :
    (Endpoint.slot i).eval s = .atom .int ↔
      CommonRoleOrdinaryKnownness.materialize s.atoms i = some Roles.Examples.int := by
  simp [Endpoint.eval]

/-- Consistent ordinary evidence fixes the int encoding, independently of candidate order. -/
theorem evidence_int_materializes (s : State n) (i : Fin n)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model)
    (models : PresenceNormalForm.All Common.model assignment s.atoms)
    (evidence : CommonRoleOrdinaryKnownness.Evidence s.atoms i .int) :
    CommonRoleOrdinaryKnownness.materialize s.atoms i = some Roles.Examples.int := by
  obtain ⟨base, found⟩ := (CommonRoleOrdinaryKnownness.detect_exists s.atoms i).mpr
    ⟨.int, evidence⟩
  have same := CommonRoleOrdinaryKnownness.evidence_unique s.atoms i assignment models
    base .int (CommonRoleOrdinaryKnownness.detect_evidence s.atoms i base found) evidence
  subst base
  simp [CommonRoleOrdinaryKnownness.materialize, found,
    CommonRoleOrdinaryKnownness.encode, Roles.Examples.int]

/-- Once int is materialized, adding ordinary constraints cannot erase it provided
there is a model of the later state. No consistency is inferred from solver syntax. -/
theorem materialized_int_persists (before after : State n) (i : Fin n)
    (included : ∀ atom ∈ before.atoms, atom ∈ after.atoms)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model)
    (models : PresenceNormalForm.All Common.model assignment after.atoms)
    (known : CommonRoleOrdinaryKnownness.materialize before.atoms i =
      some Roles.Examples.int) :
    CommonRoleOrdinaryKnownness.materialize after.atoms i = some Roles.Examples.int := by
  obtain ⟨base, found, encoded⟩ := Option.bind_eq_some_iff.mp known
  have same : base = Inference.Base.int := by
    cases base <;> simp [CommonRoleOrdinaryKnownness.encode, Roles.Examples.int] at encoded ⊢
  subst base
  obtain ⟨upper, lower⟩ := CommonRoleOrdinaryKnownness.detect_evidence before.atoms i .int found
  exact evidence_int_materializes after i assignment models ⟨included _ upper, included _ lower⟩

structure SourceRequest (n : Nat) where
  role : Nat
  lower : Endpoint n
  upper : Endpoint n

def SourceRequest.eval (s : State n) (source : SourceRequest n) : Request :=
  ⟨source.role, source.lower.eval s, source.upper.eval s⟩

def SourceRequest.variants (source : SourceRequest n) : List Request :=
  source.lower.variants.flatMap fun lo =>
    source.upper.variants.map fun hi => ⟨source.role, lo, hi⟩

theorem root_present (s : State n) (source : SourceRequest n) :
    source.eval s ∈ source.variants := by
  exact List.mem_flatMap.mpr ⟨_, eval_present s source.lower,
    List.mem_map.mpr ⟨_, eval_present s source.upper, rfl⟩⟩

def roots (sources : List (SourceRequest n)) : List Request :=
  sources.flatMap SourceRequest.variants

def domain (registry : Registry) (sources : List (SourceRequest n)) : List Request :=
  (roots sources).flatMap (closure registry)

/-- Declarative reachability; it does not mention executable closure. -/
def InDomain (registry : Registry) (sources : List (SourceRequest n)) (q : Request) : Prop :=
  ∃ root ∈ roots sources, Reach registry root q

theorem domain_exact (registry : Registry) (sources : List (SourceRequest n)) (q : Request) :
    q ∈ domain registry sources ↔ InDomain registry sources q := by
  simp only [domain, List.mem_flatMap, closure_exact, InDomain]

theorem materialized_root_present (registry : Registry) (sources : List (SourceRequest n))
    (s : State n) (source : SourceRequest n) (member : source ∈ sources) :
    source.eval s ∈ domain registry sources := by
  apply (domain_exact registry sources _).mpr
  exact ⟨_, List.mem_flatMap.mpr ⟨source, member, root_present s source⟩, .refl⟩

/-- At any state, all finite descendants of the materialized root are retained.
The state is universally quantified; the domain does not depend on it. -/
theorem materialized_reach_present (registry : Registry) (sources : List (SourceRequest n))
    (s : State n) (source : SourceRequest n) (member : source ∈ sources) (q : Request)
    (reachable : Reach registry (source.eval s) q) : q ∈ domain registry sources := by
  apply (domain_exact registry sources q).mpr
  exact ⟨_, List.mem_flatMap.mpr ⟨source, member, root_present s source⟩, reachable⟩

/-- Candidate filtering can change at every visit; the computed domain is closed. -/
theorem filtered_child_closed (registry : Registry) (sources : List (SourceRequest n))
    (visible : List Declaration) (subset : ∀ d ∈ visible, d ∈ registry.declarations)
    (q child : Request) (member : q ∈ domain registry sources)
    (edge : CommonRoleOutermostResolver.Child (Local visible) child q) :
    child ∈ domain registry sources := by
  obtain ⟨root, rootMember, reachable⟩ := (domain_exact registry sources q).mp member
  apply (domain_exact registry sources child).mpr
  exact ⟨root, rootMember, reach_trans registry root q child reachable
    (.step (filtered_child_step registry visible subset q child edge) .refl)⟩

/-- The actual solver-gated producer, with arbitrary state and allocation, stays
inside the same domain; this does not assert that allocation preserves identity. -/
theorem state_child_closed (registry : Registry) (sources : List (SourceRequest n))
    (visible : List Declaration) (subset : ∀ d ∈ visible, d ∈ registry.declarations)
    (allocate : Ty → Fin m) (gateState : State m) (q child : Request)
    (member : q ∈ domain registry sources)
    (generated : child ∈ CommonRoleOpenPropagation.childList
      (CommonRoleOpenPropagation.produce visible allocate q gateState)) :
    child ∈ domain registry sources := by
  exact filtered_child_closed registry sources visible subset q child member
    (CommonRoleOpenRecursivePass.child_origin visible allocate q gateState child generated)

/-- Complete source-to-child domain bridge for this int-materializing fragment.
No externally provided closure, accessibility proof, or finite bound is needed. -/
theorem materialized_child_present (registry : Registry) (sources : List (SourceRequest n))
    (sourceState : State n) (source : SourceRequest n) (sourceMember : source ∈ sources)
    (visible : List Declaration) (subset : ∀ d ∈ visible, d ∈ registry.declarations)
    (allocate : Ty → Fin m) (gateState : State m) (child : Request)
    (generated : child ∈ CommonRoleOpenPropagation.childList
      (CommonRoleOpenPropagation.produce visible allocate (source.eval sourceState) gateState)) :
    child ∈ domain registry sources := by
  exact state_child_closed registry sources visible subset allocate gateState _ child
    (materialized_root_present registry sources sourceState source sourceMember) generated

end Yulang.CommonRoleMaterializedDomain
