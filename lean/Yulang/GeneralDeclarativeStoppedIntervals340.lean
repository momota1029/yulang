import Yulang.GeneralDeclarativeStoppedLower339

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedIntervals340
open GeneralNominalState (Parameter Descriptor State Fits FitsAll Denotes)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Argument Equivalent Subtype nominal)

inductive SlotEnd where
  | ty (lower upper : Nat)
  | row (lower upper : Nat)
  deriving DecidableEq

def endpoints (base : GeneralSourceState.State) : Parameter base.slots → SlotEnd
  | .type (l,h) => .ty (base.source l) (base.source h)
  | .row (l,h) => .row (base.rowSource l) (base.rowSource h)

def Limits (m : Assignment) : SlotEnd → Argument → Prop
  | .ty l h, .inl actual => Subtype (m l).1 actual ∧ Subtype actual (m h).1
  | .row l h, .inr actual => Common.rowLe (m l).2 actual ∧ Common.rowLe actual (m h).2
  | _,_ => False

theorem at_exact (base : GeneralSourceState.State) (m : Assignment) (p : Parameter base.slots) (v : Argument) :
    Limits m (endpoints base p) v ↔ Fits base m p v := by
  cases p with
  | type pair => cases pair; cases v <;> rfl
  | row pair => cases pair; cases v <;> rfl

def Aligned (m : Assignment) : List SlotEnd → List Argument → Prop
  | [],[] => True
  | p::ps,v::vs => Limits m p v ∧ Aligned m ps vs
  | _,_ => False

theorem aligned_exact (base : GeneralSourceState.State) (m : Assignment)
    (ps : List (Parameter base.slots)) (vs : List Argument) :
    Aligned m (ps.map (endpoints base)) vs ↔ FitsAll base m ps vs := by
  induction ps generalizing vs with
  | nil =>
    cases vs with
    | nil => exact ⟨fun _ => .nil,fun _ => trivial⟩
    | cons => exact ⟨False.elim,fun h => by cases h⟩
  | cons p ps ih =>
    cases vs with
    | nil => exact ⟨False.elim,fun h => by cases h⟩
    | cons v vs =>
      exact ⟨fun a => .cons ((at_exact base m p v).mp a.1) ((ih vs).mp a.2),
        fun a => by cases a with | cons h t => exact ⟨(at_exact base m p v).mpr h,(ih vs).mpr t⟩⟩

/-- A literal source address, the authorized constructor identity, and
its invariant parameter bounds. No representative argument is chosen. -/
structure Row where
  name : Nat
  constructor : Nat
  tag : Nat
  limits : List SlotEnd
  deriving DecidableEq

def rowAt (base : GeneralSourceState.State) (slot : Fin base.slots) (desc : Descriptor base.slots) : Row :=
  ⟨base.source slot,desc.constructor,desc.declaration.name,desc.arguments.map (endpoints base)⟩

def Holds (m : Assignment) (row : Row) : Prop :=
  ∃ args, Aligned m row.limits args ∧ Equivalent (m row.name).1 (nominal row.tag args)

theorem denotes_exact (base : GeneralSourceState.State) (slot : Fin base.slots)
    (d : Descriptor base.slots) (m : Assignment) :
    Holds m (rowAt base slot d) ↔ Denotes base m slot d :=
  ⟨fun ⟨a,fit,nom⟩ => ⟨a,(aligned_exact base m d.arguments a).mp fit,nom⟩,
   fun ⟨a,fit,nom⟩ => ⟨a,(aligned_exact base m d.arguments a).mpr fit,nom⟩⟩

def table (raw : State) : List Row :=
  (List.ofFn fun slot : Fin raw.base.slots => slot).filterMap
      (fun slot => (raw.nominals slot).map (rowAt raw.base slot))

theorem mem_table (raw : State) (e : Row) : e ∈ table raw ↔
    ∃ slot desc, raw.nominals slot = some desc ∧ rowAt raw.base slot desc = e := by
  unfold table
  constructor
  · intro found
    obtain ⟨slot,_,defined⟩ := List.mem_filterMap.mp found
    obtain ⟨desc,there,exact⟩ := Option.map_eq_some_iff.mp defined
    exact ⟨slot,desc,there,exact⟩
  · rintro ⟨slot,desc,there,rfl⟩
    exact List.mem_filterMap.mpr ⟨slot,List.mem_ofFn.mpr ⟨slot,rfl⟩,by simp [there]⟩

theorem table_exact (raw : State) (m : Assignment) :
    (∀ row ∈ table raw, Holds m row) ↔
      ∀ slot desc, raw.nominals slot = some desc → Denotes raw.base m slot desc := by
  constructor
  · intro all slot desc found
    exact (denotes_exact raw.base slot desc m).mp (all _ ((mem_table raw _).mpr ⟨slot,desc,found,rfl⟩))
  · intro all row present
    obtain ⟨slot,desc,there,rfl⟩ := (mem_table raw row).mp present
    exact (denotes_exact raw.base slot desc m).mpr (all slot desc there)

end Yulang.GeneralDeclarativeStoppedIntervals340
