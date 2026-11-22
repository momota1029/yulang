import Yulang.GeneralDeclarativeWhereNominal346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNominalIntervals347
open GeneralNominalState (State Models Parameter Fits FitsAll Descriptor)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Argument Equivalent Subtype nominal)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)

/-- The names in a nominal parameter use their respective physical
namespaces. Nonpoint bounds are retained; neither endpoint is passed off
as the invariant parameter's actual inhabitant. -/
inductive Named where
  | type (lower upper : Nat)
  | row (lower upper : Nat)
  deriving DecidableEq

def encode (base : GeneralSourceState.State) : Parameter base.slots → Named
  | .type (l,u) => .type (base.source l) (base.source u)
  | .row (l,u) => .row (base.rowSource l) (base.rowSource u)

def fits (m : Assignment) : Named → Argument → Prop
  | .type l u, .inl x => Subtype (m l).1 x ∧ Subtype x (m u).1
  | .row l u, .inr x => Common.rowLe (m l).2 x ∧ Common.rowLe x (m u).2
  | _, _ => False

inductive FitList (m : Assignment) : List Named → List Argument → Prop
  | nil : FitList m [] []
  | cons : fits m x a → FitList m xs as → FitList m (x::xs) (a::as)

theorem fits_exact (base : GeneralSourceState.State) (m : Assignment) (p : Parameter base.slots) (a : Argument) :
    Fits base m p a ↔ fits m (encode base p) a := by
  cases p with
  | type pair => obtain ⟨l,u⟩ := pair; cases a <;> exact Iff.rfl
  | row pair => obtain ⟨l,u⟩ := pair; cases a <;> exact Iff.rfl

theorem fits_list_exact (base : GeneralSourceState.State) (m : Assignment) (ps : List (Parameter base.slots)) (as : List Argument) :
    FitsAll base m ps as ↔ FitList m (ps.map (encode base)) as := by
  induction ps generalizing as with
  | nil =>
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; exact .nil
  | cons p ps ih =>
    constructor
    · intro h
      cases h with
      | cons first rest => exact .cons ((fits_exact ..).mp first) ((ih _).mp rest)
    · intro h
      cases h with
      | cons first rest => exact .cons ((fits_exact ..).mpr first) ((ih _).mpr rest)

def read (s : State) (target : Nat) : Option (Nat × List Named) := do
  let i ← sourceSlot s.base target
  let d ← s.nominals i
  pure (d.declaration.name,d.arguments.map (encode s.base))

theorem read_exact {s : State} {target key : Nat} {args : List Named} :
    read s target = some (key,args) ↔ ∃ (i : Fin s.base.slots) (d : Descriptor s.base.slots),
      sourceSlot s.base target = some i ∧ s.nominals i = some d ∧
      d.declaration.name = key ∧ d.arguments.map (encode s.base) = args := by
  constructor
  · intro h
    obtain ⟨i,atI,next⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨d,atD,last⟩ := Option.bind_eq_some_iff.mp next
    have pair : (d.declaration.name,d.arguments.map (encode s.base)) = (key,args) :=
      Option.some.inj last
    exact ⟨i,d,atI,atD,congrArg Prod.fst pair,congrArg Prod.snd pair⟩
  · rintro ⟨i,d,atI,atD,rfl,rfl⟩
    simp [read,atI,atD]

theorem observes {s : State} {target key : Nat} {args : List Named}
    (actual : read s target = some (key,args)) (m : Assignment) (model : Models s m) :
    ∃ vals, FitList m args vals ∧ Equivalent (m target).1 (nominal key vals) := by
  obtain ⟨i,d,atI,atD,rfl,rfl⟩ := read_exact.mp actual
  obtain ⟨vals,fit,eq⟩ := model.2.1 i d atD
  exact ⟨vals,(fits_list_exact ..).mp fit,(sourceSlot_exact ..).mp atI ▸ eq⟩

end Yulang.GeneralDeclarativeNominalIntervals347
