import Yulang.CommonFiniteBoundInspection

/-!
# Strict source descent of same-depth bound inspection

The optional/default inspector contains both guarded and same-depth edges.
For a non-variable original source, every edge for which the finite proof
can request the current depth starts at a proper original source child, or
at the fixed top/width leaf. It never starts at a required/optional auxiliary
bound. Rigid pair and arrow layers require only guarded comparisons and are
excluded from this current-depth statement.

This is a syntax theorem for the actual shared-node adapter. A same-depth
record tail is measured by its finite source term, not by the size or shape
of its potentially cyclic assigned common type.
-/

namespace Yulang.CommonBoundInspectionDescent

open CommonSymbolicBoundInspection
open CommonFiniteBoundInspection (BoundBranch NeedsCurrent)
open CommonSymbolicConstraints (Check)
open CommonPayloadProjection (Payload)
open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool)
open CommonGeneratedRigidDescent (weight rigid)

def currentSources : Source Rows Node → List (BoundRef Node)
  | .reference node => [node]
  | .union first last => [first, last]
  | .rigid _ | .width | .exactEmpty => []
  | .record _ head tail => [head, tail]
  | .recordDefault _ source fallback => [.top, source, fallback]

private theorem union_sources (first last target : BoundRef Node) :
    ∀ branch ∈ ([[edge first target, edge last target]] : Output Rows Node),
      ∀ source target', edge source target' ∈ branch → source ∈ [first, last] := by
  intro branch returned source target' present
  have same : branch = [edge first target, edge last target] := List.mem_singleton.mp returned
  subst branch
  simp only [List.mem_cons, List.not_mem_nil, or_false, edge,
    Check.childBelow.injEq, Payload.ref.injEq] at present
  rcases present with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp

private theorem default_sources (label : Nat) (base fallback : BoundRef Node) (payload : Option Node) :
    ∀ branch ∈ (defaultBranches label base fallback payload : Output Rows Node),
      ∀ source target, edge source target ∈ branch → source ∈ [.top, base, fallback] := by
  intro branch returned source target present
  simp only [defaultBranches, List.mem_cons, List.not_mem_nil, or_false] at returned
  rcases returned with rfl | rfl | rfl
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false, edge,
    Check.childBelow.injEq, Payload.ref.injEq] at present
  all_goals rcases present with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp

theorem required_current_sources (source : Source Rows Node) (label : Nat) (payload : Option Node) :
    ∀ branch ∈ inspectRequired source label payload,
      ∀ first last, edge first last ∈ branch → first ∈ currentSources source := by
  cases source with
  | reference | width | exactEmpty => simp [inspectRequired, currentSources, edge]
  | union first last => exact union_sources first last (.required label payload)
  | record current head tail =>
      by_cases same : label = current <;> simp [inspectRequired, same, currentSources, edge]
  | recordDefault current source fallback =>
      by_cases same : label = current
      · simpa only [inspectRequired, same, ↓reduceIte, currentSources] using
          default_sources (Rows := Rows) label source fallback payload
      · simp [inspectRequired, same, currentSources, edge]
  | rigid node => cases node <;> simp [inspectRequired]

theorem optional_current_sources (source : Source Rows Node) (label : Nat) (payload : Option Node) :
    ∀ branch ∈ inspectOptional source label payload,
      ∀ first last, edge first last ∈ branch → first ∈ currentSources source := by
  cases source with
  | reference | width | exactEmpty => simp [inspectOptional, currentSources, edge]
  | union first last => exact union_sources first last (.optional label payload)
  | record current head tail =>
      by_cases same : label = current <;> simp [inspectOptional, same, currentSources, edge]
  | recordDefault current source fallback =>
      by_cases same : label = current
      · simpa only [inspectOptional, same, ↓reduceIte, currentSources] using
          default_sources (Rows := Rows) label source fallback payload
      · simp [inspectOptional, same, currentSources, edge]
  | rigid node => cases node <;> simp [inspectOptional]

theorem width_current_sources (source : Source Rows Node) :
    ∀ branch ∈ inspectWidth source,
      ∀ first last, edge first last ∈ branch → first ∈ currentSources source := by
  cases source with
  | reference | width | exactEmpty | record | recordDefault => simp [inspectWidth, currentSources, edge]
  | union first last => exact union_sources first last .width
  | rigid node => cases node <;> simp [inspectWidth]

theorem rigid_current_sources (source : Source Rows Node) (target : Rigid Rows Node)
    (targetRef : BoundRef Node) (current : NeedsCurrent source = true) :
    ∀ branch ∈ inspectRigid source target targetRef,
      ∀ first last, edge first last ∈ branch → first ∈ currentSources source := by
  cases source with
  | reference => simp [inspectRigid, currentSources, edge]
  | union first last => exact union_sources first last targetRef
  | rigid => cases current
  | width | exactEmpty | record | recordDefault => cases target <;> simp [inspectRigid]

variable {m : Nat}

/-- Only original proper children and the two fixed leaf sources can occur.
The forbidden cases remain false rather than receiving an arbitrary measure. -/
def SmallerSource (pool : Pool m) (source : TyTerm (Fin m)) : BoundRef (Fin pool.size) → Prop
  | .original child => weight (pool.termAt child) < weight source
  | .top | .width => 1 < weight source
  | .exactEmpty | .required _ _ | .optional _ _ => False

theorem weight_positive (term : TyTerm α) : 0 < weight term := by
  cases term <;> simp [weight] <;> omega

theorem node_current_sources_smaller (pool : Pool m) (term : TyTerm (Fin m))
    (member : term ∈ pool.terms) (source : CommonGeneratedBoundInspection.PoolSource pool)
    (found : CommonGeneratedBoundInspection.ofNode pool term member = some source)
    (nonvariable : rigid term) (current : NeedsCurrent source = true) :
    ∀ child ∈ currentSources source, SmallerSource pool term child := by
  cases term with
  | var => cases nonvariable
  | inter => cases found
  | bottom | top | base | pair | variant | arrow =>
      cases found
      cases current
  | emptyRecord | exactEmpty =>
      cases found
      simp [currentSources]
  | union first last =>
      cases found
      simp only [currentSources, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp]
      constructor <;> simp [SmallerSource, Pool.child, weight] <;> omega
  | required label payload =>
      cases found
      simp only [currentSources, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp]
      constructor
      · simp [SmallerSource, Pool.child, weight]
      · simpa [SmallerSource, weight] using weight_positive payload
  | record label head tail =>
      cases found
      simp only [currentSources, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp]
      constructor <;> simp [SmallerSource, Pool.child, weight] <;> omega
  | recordDefault label base fallback =>
      cases found
      simp only [currentSources, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp]
      have positive := weight_positive base
      constructor
      · simp only [SmallerSource, weight]
        omega
      · constructor <;> simp [SmallerSource, Pool.child, weight] <;> omega

theorem required_child_smaller (pool : Pool m) (term : TyTerm (Fin m))
    (member : term ∈ pool.terms) (source : CommonGeneratedBoundInspection.PoolSource pool)
    (found : CommonGeneratedBoundInspection.ofNode pool term member = some source)
    (nonvariable : rigid term) (current : NeedsCurrent source = true)
    (label : Nat) (payload : Option (Fin pool.size)) (branch : BoundBranch _ _)
    (returned : branch ∈ inspectRequired source label payload)
    (first last : BoundRef (Fin pool.size)) (present : edge first last ∈ branch) :
    SmallerSource pool term first :=
  node_current_sources_smaller pool term member source found nonvariable current first
    (required_current_sources source label payload branch returned first last present)

theorem optional_child_smaller (pool : Pool m) (term : TyTerm (Fin m))
    (member : term ∈ pool.terms) (source : CommonGeneratedBoundInspection.PoolSource pool)
    (found : CommonGeneratedBoundInspection.ofNode pool term member = some source)
    (nonvariable : rigid term) (current : NeedsCurrent source = true)
    (label : Nat) (payload : Option (Fin pool.size)) (branch : BoundBranch _ _)
    (returned : branch ∈ inspectOptional source label payload)
    (first last : BoundRef (Fin pool.size)) (present : edge first last ∈ branch) :
    SmallerSource pool term first :=
  node_current_sources_smaller pool term member source found nonvariable current first
    (optional_current_sources source label payload branch returned first last present)

theorem width_child_smaller (pool : Pool m) (term : TyTerm (Fin m))
    (member : term ∈ pool.terms) (source : CommonGeneratedBoundInspection.PoolSource pool)
    (found : CommonGeneratedBoundInspection.ofNode pool term member = some source)
    (nonvariable : rigid term) (current : NeedsCurrent source = true)
    (branch : BoundBranch _ _) (returned : branch ∈ inspectWidth source)
    (first last : BoundRef (Fin pool.size)) (present : edge first last ∈ branch) :
    SmallerSource pool term first :=
  node_current_sources_smaller pool term member source found nonvariable current first
    (width_current_sources source branch returned first last present)

theorem rigid_child_smaller (pool : Pool m) (term : TyTerm (Fin m))
    (member : term ∈ pool.terms) (source : CommonGeneratedBoundInspection.PoolSource pool)
    (found : CommonGeneratedBoundInspection.ofNode pool term member = some source)
    (nonvariable : rigid term) (current : NeedsCurrent source = true)
    (target : CommonGeneratedBoundInspection.PoolRigid pool) (targetRef : BoundRef (Fin pool.size))
    (branch : BoundBranch _ _) (returned : branch ∈ inspectRigid source target targetRef)
    (first last : BoundRef (Fin pool.size)) (present : edge first last ∈ branch) :
    SmallerSource pool term first :=
  node_current_sources_smaller pool term member source found nonvariable current first
    (rigid_current_sources source target targetRef current branch returned first last present)

end Yulang.CommonBoundInspectionDescent
