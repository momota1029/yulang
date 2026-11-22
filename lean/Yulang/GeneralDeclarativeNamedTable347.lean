import Yulang.GeneralDeclarativeNominalTransport347
import Yulang.GeneralStoppedLower335

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNamedTable347
open GeneralNominalState (State Models Denotes Descriptor)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeNominalIntervals347 (Named encode FitList fits_list_exact read_exact)
open GeneralDictionaryBinderLocations (sourceSlot_exact)
open CommonNominalFullCarrier (Equivalent nominal)

structure Entry where
  root : Nat
  tag : Nat
  bounds : List Named

def printAt (s : State) (i : Fin s.base.slots) : Option Entry :=
  (s.nominals i).map fun d => ⟨s.base.source i,d.declaration.name,d.arguments.map (encode s.base)⟩

def table (s : State) : List Entry := (List.finRange s.base.slots).filterMap (printAt s)

def Entry.Holds (m : Assignment) (e : Entry) : Prop :=
  ∃ values, FitList m e.bounds values ∧ Equivalent (m e.root).1 (nominal e.tag values)

theorem location {s : State} {e : Entry} :
    e ∈ table s ↔ GeneralDeclarativeNominalIntervals347.read s e.root = some (e.tag,e.bounds) := by
  constructor
  · intro used
    obtain ⟨i,_,there⟩ := List.mem_filterMap.mp used
    obtain ⟨d,saved,rfl⟩ := Option.map_eq_some_iff.mp there
    exact read_exact.mpr ⟨i,d,(sourceSlot_exact ..).mpr rfl,saved,rfl,rfl⟩
  · intro existsRead
    obtain ⟨i,d,atRoot,atD,tag,bounds⟩ := read_exact.mp existsRead
    have root := (sourceSlot_exact ..).mp atRoot
    exact List.mem_filterMap.mpr ⟨i,List.mem_finRange i,by cases e; simp_all [printAt]⟩

theorem exact_nominals (s : State) (m : Assignment) :
    (∀ e ∈ table s, e.Holds m) ↔
      (∀ i d, s.nominals i = some d → Denotes s.base m i d) := by
  constructor
  · intro all i d atD
    let e : Entry := ⟨s.base.source i,d.declaration.name,d.arguments.map (encode s.base)⟩
    have used : e ∈ table s := location.mpr (read_exact.mpr ⟨i,d,(sourceSlot_exact ..).mpr rfl,atD,rfl,rfl⟩)
    obtain ⟨args,typed,head⟩ := all e used
    exact ⟨args,(fits_list_exact ..).mpr typed,head⟩
  · intro all e haveE
    obtain ⟨i,d,atRoot,atD,tag,bounds⟩ := read_exact.mp (location.mp haveE)
    obtain ⟨args,typed,head⟩ := all i d atD
    have root := (sourceSlot_exact ..).mp atRoot
    exact ⟨args,bounds ▸ (fits_list_exact ..).mp typed,root ▸ tag ▸ head⟩

end Yulang.GeneralDeclarativeNamedTable347
