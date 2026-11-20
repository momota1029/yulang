import Yulang.GeneralSourceMetadataPublicationFixture291

/-! Reindex the old inspector's report through the identical base slots.
This is a checked wrapper conversion, not a flattening to diagnostic bits. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralSourceMetadataReport291
open GeneralNominalState (State)
open GeneralNominalInspection (Bounds)
open GeneralNominalRecursiveInspection (Capture Report Origin Test block)
open GeneralSourceMetadataRows291 (Source)
open GeneralSourceMetadataSnapshot291 (Fits retag)

variable (s : State) (src : Source) (fit : Fits s src)

def lowerCapture (c : Capture (retag s src fit)) : Capture s := ⟨c.name,c.bounds,c.origin⟩

def lower (value : Report (retag s src fit)) : Report s :=
  ⟨value.captures.map (lowerCapture s src fit),value.inspected,value.checked,value.blocked,
   value.conflicts,value.arity,value.anchors,value.tests⟩

@[simp] theorem lower_append (a b : Report (retag s src fit)) :
    lower s src fit (a.append b) = (lower s src fit a).append (lower s src fit b) := by
  simp [lower,Report.append,List.map_append]

@[simp] theorem lower_visit (b : Bounds s) (o : Option Origin) (test : Test)
    (r : Report (retag s src fit)) :
    lower s src fit (r.visit b o test) = (lower s src fit r).visit b o test := rfl

@[simp] theorem lower_block (b : Bounds s) :
    lower s src fit (block b) = block b := rfl

@[simp] theorem identical_nominals : (retag s src fit).nominals = s.nominals := rfl
@[simp] theorem identical_view : (retag s src fit).view = s.view := rfl
@[simp] theorem identical_base : (retag s src fit).base = s.base := rfl

end Yulang.GeneralSourceMetadataReport291
