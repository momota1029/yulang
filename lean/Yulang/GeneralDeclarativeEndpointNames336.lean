import Yulang.GeneralDeclarativeEndpointResidual336
import Yulang.GeneralDeclarativeOpaqueNames328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointNames336
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeCaptureClosure320 (withOrdinary atoms ordinary_models)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralDeclarativeNewNames321 (after before_after)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEndpointRecord336 (Read interp field_interval)
open GeneralDeclarativeEndpointResidual336 (exact_residuals)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleCanonicalRows (Row normalize residual)
open CommonNominalFullCarrier (Ty mask)

abbrev Triple := Ty × Ty × Ty

def prior (s : State) (keep : List Nat) := stateNames s ++ keep

/-- Allocate a disjoint logical interval, not a literal center record.
The slots carry derived observation values in the projection receipt. -/
def names (s : State) (keep : List Nat) : Capture :=
  let f := after (prior s keep)
  ⟨f,f+1,f+2⟩

def prepare (s : State) (keep : List Nat) : State :=
  withOrdinary s (atoms (names s keep))

def extend (s : State) (keep : List Nat) (m : Assignment) (v : Triple) : Assignment :=
  let c := names s keep
  fun n => if n = c.lower then (v.1,(m n).2)
    else if n = c.center then (v.2.1,(m n).2)
    else if n = c.upper then (v.2.2,(m n).2) else m n

theorem kept {s : State} {keep : List Nat} (m : Assignment) (v : Triple) {n : Nat}
    (known : n ∈ prior s keep) : extend s keep m v n = m n := by
  have old : n < after (prior s keep) := before_after known
  have one : n ≠ after (prior s keep) := by omega
  have two : n ≠ after (prior s keep)+1 := by omega
  have three : n ≠ after (prior s keep)+2 := by omega
  simp [extend,names,one,two,three]

theorem values (s : State) (keep : List Nat) (m : Assignment) (v : Triple) :
    ((extend s keep m v (names s keep).lower).1,
     (extend s keep m v (names s keep).center).1,
     (extend s keep m v (names s keep).upper).1) = v := by
  let k := after (prior s keep)
  have a : k+1 ≠ k := by omega
  have b : k+2 ≠ k := by omega
  have c : k+2 ≠ k+1 := by omega
  change ((if k = k then (v.1,(m k).2) else _).1,
    (if k+1 = k then (v.1,(m (k+1)).2) else if k+1 = k+1 then (v.2.1,(m (k+1)).2) else _).1,
    (if k+2 = k then (v.1,(m (k+2)).2) else if k+2 = k+1 then (v.2.1,(m (k+2)).2) else
      if k+2 = k+2 then (v.2.2,(m (k+2)).2) else _).1) = v
  simp only [a,b,c,ite_false,ite_true]

theorem ready (s : State) (keep : List Nat) : Bounds (prepare s keep) (names s keep) :=
  ⟨.constraint (List.mem_append_right _ List.mem_cons_self),
   .constraint (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

theorem extension {s : State} {m : Assignment} {v : Triple} (fit : Models s m)
    (inside : InInterval v.1 v.2.2 v.2.1) (keep : List Nat) :
    Models (prepare s keep) (extend s keep m v) ∧
      ∀ n ∈ prior s keep, extend s keep m v n = m n := by
  let ext := extend s keep m v
  refine ⟨(ordinary_models ext).mpr ⟨(preserves_models s
    (fun n old => kept m v (List.mem_append_left _ old))).mpr fit,?_⟩,fun _ h => kept m v h⟩
  intro e active
  have low := congrArg Prod.fst (values s keep m v)
  have mid := congrArg (fun x : Triple => x.2.1) (values s keep m v)
  have high := congrArg (fun x : Triple => x.2.2) (values s keep m v)
  change (ext (names s keep).lower).1 = v.1 at low
  change (ext (names s keep).center).1 = v.2.1 at mid
  change (ext (names s keep).upper).1 = v.2.2 at high
  unfold atoms at active
  rcases List.mem_cons.mp active with rfl|tail
  · change CommonNominalFullCarrier.Subtype (ext (names s keep).lower).1 (ext (names s keep).center).1
    rw [low,mid]
    exact inside.1
  · cases List.mem_singleton.mp tail
    change CommonNominalFullCarrier.Subtype (ext (names s keep).center).1 (ext (names s keep).upper).1
    rw [mid,high]
    exact inside.2

def Field (key : Nat) (a b : Expr) (arg : Capture) (m : Assignment) (v : Triple) : Prop :=
  v.1 = interp m a ∧ project key false [] (m arg.center).1 = some v.2.1 ∧ v.2.2 = interp m b

def Rest (keys : List Nat) (lo hi : Expr) (arg : Capture) (m : Assignment) (v : Triple) : Prop :=
  v = (mask keys (interp m lo),mask keys (m arg.center).1,mask keys (interp m hi))

theorem name_field {s : State} {p : Supported s done}
    (r : Read p arg keys ls us first last le ue) (one : (key,a) ∈ first) (two : (key,b) ∈ last)
    (m : Assignment) (fit : Models s m) (keep : List Nat) :
    ∃ next : Assignment,
      Models (prepare s keep) next ∧ (∀ n ∈ prior s keep, next n = m n) ∧
      Field key a b arg m ((next (names s keep).lower).1,
        (next (names s keep).center).1,(next (names s keep).upper).1) := by
  obtain ⟨payload,printed,bounded⟩ := field_interval r one two m fit
  let v : Triple := (interp m a,payload,interp m b)
  obtain ⟨valid,unchanged⟩ := extension (v := v) fit bounded keep
  refine ⟨extend s keep m v,valid,unchanged,?_⟩
  rw [values]
  exact ⟨rfl,printed,rfl⟩

theorem name_rest {s : State} {p : Supported s done}
    (r : Read p arg keys ls us first last le ue) (m : Assignment) (fit : Models s m) (keep : List Nat) :
    ∃ next : Assignment,
      Models (prepare s keep) next ∧ (∀ n ∈ prior s keep, next n = m n) ∧
      Rest keys (withTail (residual keys (normalize ls)) le)
        (withTail (residual keys (normalize us)) ue) arg m
          ((next (names s keep).lower).1,(next (names s keep).center).1,(next (names s keep).upper).1) := by
  let v : Triple := (mask keys (interp m (withTail (residual keys (normalize ls)) le)),
    mask keys (m arg.center).1,mask keys (interp m (withTail (residual keys (normalize us)) ue)))
  obtain ⟨valid,unchanged⟩ := extension (v := v) fit (exact_residuals r m fit) keep
  refine ⟨extend s keep m v,valid,unchanged,?_⟩
  rw [values]
  rfl

end Yulang.GeneralDeclarativeEndpointNames336
