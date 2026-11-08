import Yulang.CommonRoleOpenProducerAccess

/-! Structural provenance for the actual unary producer. A capture is located
in the parent endpoint, not identified by equality of its Ty value. Literal
sentinels have no capture position. This is not the full source-graph allocator. -/
namespace Yulang.CommonRoleCaptureOrigin
open CommonRoleSettledSyntax CommonRoleOpenProducer
open CommonRoleOpenProducerAccess

/-- Follow exactly n unary constructor edges; regular loops are opaque. -/
def atDepth : Nat → Ty → Option Ty
  | 0, t => some t
  | n + 1, .wrap _ t => atDepth n t
  | _ + 1, _ => none

def captureDepth : Pattern → Option Nat
  | .bind _ _ => some 0
  | .atom _ => none
  | .wrap _ p => (captureDepth p).map Nat.succ

/-- A declarative inspection hit comes from this exact parent position. -/
theorem inspect_origin (p : Pattern) (t payload : Ty) (depth : Nat)
    (located : captureDepth p = some depth) (hit : Inspect p t (.hit payload)) :
    atDepth depth t = some payload := by
  induction p generalizing t depth with
  | bind first more =>
    simp only [captureDepth, Option.some.injEq] at located
    subst depth
    cases hit
    rfl
  | atom a => simp [captureDepth] at located
  | wrap c p ih =>
    cases h : captureDepth p with
    | none => simp [captureDepth, h] at located
    | some n =>
      have eq : n + 1 = depth := by simpa [captureDepth, h] using located
      subst depth
      cases hit with
      | wrap_hit _ inner => exact ih _ n h inner

/-- Successful executable inspection has the same independently checked origin. -/
theorem inspect_origin_exec (p : Pattern) (t payload : Ty) (depth : Nat)
    (located : captureDepth p = some depth) (hit : inspect p t = .hit payload) :
    atDepth depth t = some payload :=
  inspect_origin p t payload depth located ((inspect_exact ..).mp hit)

def variableDepth : Template → Option Nat
  | .var _ => some 0
  | .atom _ => none
  | .wrap _ t => (variableDepth t).map Nat.succ

/-- Substitution preserves the capture at the variable's structural position. -/
theorem instantiate_origin (template : Template) (payload : Ty) (depth : Nat)
    (located : variableDepth template = some depth) :
    atDepth depth (template.instantiate payload) = some payload := by
  induction template generalizing depth with
  | var name =>
    simp only [variableDepth, Option.some.injEq] at located
    subst depth
    rfl
  | atom a => simp [variableDepth] at located
  | wrap c t ih =>
    cases h : variableDepth t with
    | none => simp [variableDepth, h] at located
    | some n =>
      have eq : n + 1 = depth := by simpa [variableDepth, h] using located
      subst depth
      exact ih n h

/-- Both actual selected payloads are located by one head depth in their
respective endpoints. No equality between lower and upper is assumed. -/
theorem production_origin (visible : List Declaration) (q : Request)
    (d : Declaration) (lp hp : Ty) (depth : Nat)
    (produced : production visible q = some (d, lp, hp))
    (located : captureDepth d.head = some depth) :
    atDepth depth q.lower = some lp ∧ atDepth depth q.upper = some hp := by
  have hit : (d, lp, hp) ∈ hits (scan q.role q.lower q.upper visible) :=
    by
      unfold production at produced
      cases hs : hits (scan q.role q.lower q.upper visible) with
      | nil => simp [hs] at produced
      | cons first rest =>
        have equal : first = (d, lp, hp) := by simpa [hs] using produced
        simp [equal]
  obtain ⟨_, _, low, high⟩ := scan_hit_origin _ _ _ _ d lp hp ((mem_hits ..).mp hit)
  exact ⟨inspect_origin _ _ _ _ located low, inspect_origin _ _ _ _ located high⟩

/-- Every variable-bearing actual child has an explicit requirement witness,
and its copied payload is precisely the captured parent subtree. -/
theorem child_origin (visible : List Declaration) (q child : Request)
    (d : Declaration) (lp hp : Ty) (headDepth : Nat)
    (produced : production visible q = some (d, lp, hp))
    (located : captureDepth d.head = some headDepth)
    (member : child ∈ children q d lp hp) :
    ∃ requirement ∈ d.requirements,
      child.role = requirement.1 ∧
      ∀ depth, variableDepth requirement.2 = some depth →
        atDepth depth child.lower = atDepth headDepth q.lower ∧
        atDepth depth child.upper = atDepth headDepth q.upper := by
  obtain ⟨r, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨low, high⟩ := production_origin visible q d lp hp headDepth produced located
  refine ⟨r, present, rfl, ?_⟩
  intro depth position
  exact ⟨(instantiate_origin r.2 lp depth position).trans low.symm,
    (instantiate_origin r.2 hp depth position).trans high.symm⟩


/-- A used head variable always has a capture position; literal sentinels do not. -/
theorem named_capture (p : Pattern) (name : Nat) (used : name ∈ p.names) :
    ∃ depth, captureDepth p = some depth := by
  induction p with
  | bind first more => exact ⟨0, rfl⟩
  | atom a => simp [Pattern.names] at used
  | wrap c p ih =>
    obtain ⟨depth, located⟩ := ih used
    exact ⟨depth + 1, by simp [captureDepth, located]⟩

theorem named_variable (t : Template) (name : Nat) (used : name ∈ t.names) :
    ∃ depth, variableDepth t = some depth := by
  induction t with
  | var n => exact ⟨0, rfl⟩
  | atom a => simp [Template.names] at used
  | wrap c t ih =>
    obtain ⟨depth, located⟩ := ih used
    exact ⟨depth + 1, by simp [variableDepth, located]⟩

/-- Checked declarations derive, rather than assume, both source positions
for every used where variable of an actual production. -/
theorem checked_requirement_origin (visible : List Declaration) (q : Request)
    (d : Declaration) (lp hp : Ty) (r : Nat × Template) (name : Nat)
    (checked : d.check = true)
    (produced : production visible q = some (d, lp, hp))
    (required : r ∈ d.requirements) (used : name ∈ r.2.names) :
    ∃ headDepth childDepth,
      captureDepth d.head = some headDepth ∧ variableDepth r.2 = some childDepth ∧
      atDepth headDepth q.lower = some lp ∧ atDepth headDepth q.upper = some hp ∧
      atDepth childDepth (r.2.instantiate lp) = atDepth headDepth q.lower ∧
      atDepth childDepth (r.2.instantiate hp) = atDepth headDepth q.upper := by
  obtain ⟨hd, headLocated⟩ := named_capture d.head name (checked_names d checked r required name used)
  obtain ⟨cd, childLocated⟩ := named_variable r.2 name used
  obtain ⟨low, high⟩ := production_origin visible q d lp hp hd produced headLocated
  exact ⟨hd, cd, headLocated, childLocated, low, high,
    (instantiate_origin r.2 lp cd childLocated).trans low.symm,
    (instantiate_origin r.2 hp cd childLocated).trans high.symm⟩

end Yulang.CommonRoleCaptureOrigin
