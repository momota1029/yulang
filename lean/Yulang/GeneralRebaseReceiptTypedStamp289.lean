import Yulang.GeneralRebaseReceiptAnchorExport289

/-! Source-indexed finite stamp data. A row coordinate and a type
coordinate with the same numeric ID are different ports. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseReceiptTypedStamp289
open GeneralNominalState (State Parameter Descriptor)
open GeneralNominalRefinements (Refines renameParameter renameDescriptor)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralRebaseReceiptOccurrence289 (Key encode)
open GeneralSourceDictionaries (Occurrence)

inductive Port where
  | type (lo hi : Nat)
  | row (lo hi : Nat)
  deriving Repr, DecidableEq

def port (s : GeneralSourceState.State) : Parameter s.slots → Port
  | .type (a,b) => .type (s.source a) (s.source b)
  | .row (a,b) => .row (s.rowSource a) (s.rowSource b)

structure HeadCode where
  source : Nat
  catalogueKey : Nat
  name : Nat
  args : List Port
  deriving Repr, DecidableEq

def head (s : State) (slot : Fin s.base.slots) (d : Descriptor s.base.slots) : HeadCode :=
  ⟨s.base.source slot,d.constructor,d.declaration.name,d.arguments.map (port s.base)⟩

def heads (s : State) : List HeadCode :=
  (List.ofFn fun slot => (s.nominals slot).map (head s slot)).filterMap id

structure Stamp where
  offer : Offer
  parent : Key
  child : Key
  snapshot : List HeadCode
  deriving Repr, DecidableEq

def capture (s : State) (up down : Occurrence roles) (ask : Offer) : Stamp :=
  ⟨ask,encode up,encode down,heads s⟩

theorem port_renamed {old new : State} (refines : Refines old new)
    (parameter : Parameter old.base.slots) :
    port new.base (renameParameter refines.base.embed parameter) = port old.base parameter := by
  cases parameter <;> simp only [port,renameParameter,refines.base.source,refines.base.rowSource]

theorem head_renamed {old new : State} (refines : Refines old new)
    (slot : Fin old.base.slots) (descriptor : Descriptor old.base.slots) :
    head new (refines.base.embed slot) (renameDescriptor refines.base.embed descriptor) =
      head old slot descriptor := by
  unfold head renameDescriptor
  rw [refines.base.source,List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  exact port_renamed refines p

theorem recorded_head_in_stamp (s : State) (slot : Fin s.base.slots) (d : Descriptor s.base.slots)
    (visible : s.nominals slot = some d) : head s slot d ∈ heads s := by
  unfold heads
  apply List.mem_filterMap.mpr
  refine ⟨some (head s slot d),List.mem_ofFn.mpr ⟨slot,?_⟩,rfl⟩
  rw [visible,Option.map_some]

theorem retained_head {old new : State} (refines : Refines old new)
    (slot : Fin old.base.slots) (descriptor : Descriptor old.base.slots)
    (visible : old.nominals slot = some descriptor) :
    head old slot descriptor ∈ heads new := by
  rw [← head_renamed refines]
  exact recorded_head_in_stamp _ _ _ (refines.nominals slot descriptor visible)

end Yulang.GeneralRebaseReceiptTypedStamp289
