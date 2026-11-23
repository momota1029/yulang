import Yulang.GeneralDeclarativeWitnessNominalCompareExact359

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessScopedBindings359
open GeneralDeclarativeWitnessNominalSource359 (Location Route SlotRead Built build AtSource)
open GeneralDeclarativeWitnessNominalRelation359 (Reads lower_sound)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled compile)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives compiled_full_exact)
open CommonRecursiveNominalIntervals (Endpoint ContextWellFormed)
open CommonDeclaredNominalInspection (Registry)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)

structure FrameKey where
  occurrence : List Nat
  declaration : Nat
  sourceOrdinal : Nat
  deriving DecidableEq

/-- A table supplied by an independently chosen/compiled source frame.
A raw comparison answer cannot invent the binder's span. Two different
lexical frames may share a numeric binder and even its actual center. -/
structure Frame where
  key : FrameKey
  locals : List (Nat × Capture)

def findFrame (frames : List Frame) (key : FrameKey) : Option Frame :=
  match frames.filter (fun f => decide (f.key = key)) with
  | [found] => some found
  | _ => none

def readLocal (target : Frame) : SlotRead := fun k =>
  match target.locals.filter (fun b => decide (b.1 = k)) with
  | [found] => some found.2
  | _ => none

def slots (frames : List Frame) (owner : FrameKey) : SlotRead := fun binder =>
  (findFrame frames owner).bind fun frame => readLocal frame binder

def attached (key : FrameKey) : Location → Prop
  | .head id ord _ => key.declaration = id ∧ key.sourceOrdinal = ord
  | .requirement id ord _ _ _ => key.declaration = id ∧ key.sourceOrdinal = ord

instance (key : FrameKey) (loc : Location) : Decidable (attached key loc) := by
  cases loc <;> unfold attached <;> infer_instance

theorem read_has_literal_frame {frames owner binder cap}
    (found : slots frames owner binder = some cap) :
    ∃ frame ∈ frames,frame.key = owner ∧ (binder,cap) ∈ frame.locals := by
  unfold slots at found
  have ⟨f,located,part⟩ := Option.bind_eq_some_iff.mp found
  have anchored : f ∈ frames ∧ f.key = owner := by
    unfold findFrame at located
    split at located
    · rename_i selected exact
      cases located
      exact (List.mem_filter.mp (exact.symm ▸ List.mem_cons_self)).imp_right of_decide_eq_true
    · contradiction
  have piece : (binder,cap) ∈ f.locals := by
    unfold readLocal at part
    split at part
    · rename_i bound exact
      have same : bound.2 = cap := Option.some.inj part
      have it : bound ∈ f.locals ∧ decide (bound.1 = binder) = true :=
        List.mem_filter.mp (exact.symm ▸ List.mem_cons_self)
      have equal : bound = (binder,cap) := Prod.ext (of_decide_eq_true it.2) same
      exact equal ▸ it.1
    · contradiction
  exact ⟨f,anchored.1,anchored.2,piece⟩

structure ScopedComparison (e : Environment) (table : Registry) (frames : List Frame)
    (context : Bool) (lkey rkey : FrameKey) (lhs rhs : Location) (l r : Route) where
  leftSite : attached lkey lhs
  rightSite : attached rkey rhs
  left : Built e table (slots frames lkey) context lhs l
  right : Built e table (slots frames rkey) context rhs r
  proof : Compiled e table context left.endpoint right.endpoint

def run (e : Environment) (table : Registry) (frames : List Frame)
    (context : Bool) (lkey rkey : FrameKey) (lhs rhs : Location) (l r : Route) :
    Option (ScopedComparison e table frames context lkey rkey lhs rhs l r) :=
  if firstSite : attached lkey lhs then
    if lastSite : attached rkey rhs then do
      let left ← build e table (slots frames lkey) context lhs l
      let right ← build e table (slots frames rkey) context rhs r
      let proof ← compile e table context left.endpoint right.endpoint
      pure ⟨firstSite,lastSite,left,right,proof⟩
    else none
  else none

theorem every_frame_kept {e table frames context lkey rkey lhs rhs l r}
    (c : ScopedComparison e table frames context lkey rkey lhs rhs l r) (m : Assignment)
    (all : ∀ atom ∈ c.proof.rows,atom.Holds model m) :
    attached lkey lhs ∧ attached rkey rhs ∧ AtSource e lhs l ∧ AtSource e rhs r ∧
      Reads e table (slots frames lkey) context l c.left.endpoint ∧
      Reads e table (slots frames rkey) context r c.right.endpoint ∧
      ContextWellFormed table context c.left.endpoint ∧
      ContextWellFormed table context c.right.endpoint ∧
      ContextDerives table m context c.left.endpoint c.right.endpoint :=
  ⟨c.leftSite,c.rightSite,c.left.source,c.right.source,lower_sound c.left.lowered,lower_sound c.right.lowered,
    (compiled_full_exact table m context c.left.endpoint c.right.endpoint).mp
      ⟨c.proof.rows,c.proof.exact,all⟩⟩

end Yulang.GeneralDeclarativeWitnessScopedBindings359
