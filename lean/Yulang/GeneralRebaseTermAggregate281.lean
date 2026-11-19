import Yulang.GeneralRebaseTermCopy281

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
namespace Yulang.GeneralRebaseTermAggregate281
open GeneralNominalSaturationState (Packet)
open GeneralNominalIdentities (Origin source source_identity)
open GeneralNominalAllocation (occurrences lower upper equations)
open GeneralNominalVersionedAllocation231 (merges)
open GeneralRebaseAggregateSupport281 (endKey)
open GeneralRebaseAggregateTags281 (fixedOrigin)
open GeneralRebaseAggregateLift281 (sourceView)
open GeneralRebaseTermCopy281 (Write Unique Reads Respects)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (typeSources)
open PresenceNormalForm (All)
open Core.PresenceGeneration (TyTerm)

def active (p : Packet roles) (binder : Nat) : List (Nat × Bool) :=
  match occurrences p.bindings binder with
  | [_] => []
  | _ => [(binder,false),(binder,true)]

def keys (p : Packet roles) : List (Nat × Bool) := p.declaration.inputNames.flatMap (active p)

def expression (p : Packet roles) (key : Nat × Bool) : TyTerm Nat :=
  let terms := occurrences p.bindings key.1
  if key.2 then upper terms else lower terms

def address (p : Packet roles) (fixed : Bool) (key : Nat × Bool) : Nat :=
  source p.context.state.seed (if fixed then
    fixedOrigin p.site.occurrence.identity p.declaration.id ⟨key.1,key.2,0⟩
    else endKey p key.1 key.2)

def writes (p : Packet roles) (stable : Bool) : List Write :=
  (keys p).map fun key => (address p stable key,expression p key)

theorem address_injective (p : Packet roles) (stable : Bool) : Function.Injective (address p stable) := by
  rintro ⟨first,a⟩ ⟨last,b⟩ same
  have key := (source_identity _ _ _).mp same
  have binder := congrArg (fun x : Origin => x.2.2.2.1) key
  have polarity := congrArg (fun x : Origin => x.2.2.1) key
  have firstLast : first = last := by
    cases stable <;> exact binder
  have side : (if a then (1 : Nat) else 0) = (if b then 1 else 0) := by
    cases stable <;> exact polarity
  exact Prod.ext firstLast (by cases a <;> cases b <;> simp_all)

theorem unique (p : Packet roles) (stable : Bool) : Unique (writes p stable) := by
  intro x belongs y present equal
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp belongs
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp present
  cases address_injective p stable equal
  rfl

theorem reads (p : Packet roles) (stable : Bool) : Reads (sourceView p) (writes p stable) := by
  intro row listed
  obtain ⟨⟨binder,up⟩,_,rfl⟩ := List.mem_map.mp listed
  have endpoints := GeneralNominalAllocationSupport.report_endpoints p.context.state (GeneralNominalPacketSupport.report p)
  have member := GeneralNominalAllocationSupport.occurrences_endpoints endpoints binder
  cases up
  · exact GeneralNominalAllocationSupport.lower_sources _ member
  · exact GeneralNominalAllocationSupport.upper_sources _ member

def atoms (ws : List Write) : List (PresenceNormalForm.Atom Nat) :=
  ws.flatMap (fun row => equations row.1 row.2)

theorem atoms_exact (ws : List Write) (m : Assignment) :
    All CommonNominalFullCarrier.model m (atoms ws) ↔ Respects ws m := by
  constructor
  · intro all row seen
    apply (GeneralNominalCaptureMerges.equations_exact m row.1 row.2).mp
    intro atom listed
    exact all atom (List.mem_flatMap.mpr ⟨row,seen,listed⟩)
  · intro valid atom seen
    obtain ⟨row,member,listed⟩ := List.mem_flatMap.mp seen
    exact (GeneralNominalCaptureMerges.equations_exact m row.1 row.2).mpr (valid row member) atom listed

theorem active_atoms (p : Packet roles) (binder : Nat) :
    ((active p binder).map (fun key => (address p false key,expression p key))).flatMap
      (fun row => equations row.1 row.2) =
    (match occurrences p.bindings binder with
      | [_] => []
      | bounds =>
        equations ((GeneralNominalVersionedAllocation231.capture p.context.state p.registry
          p.site.occurrence.identity p.declaration.id p.bindings).inputs binder).1 (lower bounds) ++
        equations ((GeneralNominalVersionedAllocation231.capture p.context.state p.registry
          p.site.occurrence.identity p.declaration.id p.bindings).inputs binder).2 (upper bounds)) := by
  unfold active
  cases found : occurrences p.bindings binder with
  | nil => simp [address,expression,GeneralNominalVersionedAllocation231.capture,found,endKey,GeneralNominalAggregateVersion231.slot]
  | cons a rest =>
    cases rest
    · rfl
    · simp [address,expression,GeneralNominalVersionedAllocation231.capture,found,endKey,GeneralNominalAggregateVersion231.slot]

theorem versioned_atoms (p : Packet roles) :
    atoms (writes p false) =
      merges p.context.state p.registry p.site.occurrence.identity p.declaration p.bindings := by
  unfold atoms writes keys merges
  simp only [List.map_flatMap,List.flatMap_assoc,active_atoms]
  rfl

end Yulang.GeneralRebaseTermAggregate281
