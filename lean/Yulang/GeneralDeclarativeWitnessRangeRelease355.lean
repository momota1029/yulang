import Yulang.GeneralDeclarativeWitnessTypedReemitPayload354
import Yulang.GeneralDeclarativeWitnessTypedIndex354
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRangeRelease355
open GeneralDeclarativeWitnessTypedReemit354 (Linked)
open GeneralDeclarativeWitnessTypedReemitPayload354 (Carry check exact_same_model)
open GeneralDeclarativeWitnessTypedRelease354 (Location Stamp Key Authority position)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Output)

/-- Typed re-emission occurs at the actual compiler-selected child path.
The active incarnation and release key come from independent authority,
not from the diagnostic or from equality of payloads. -/
def stamp {i s w} (a : Linked i s w) (version : Nat) : Stamp :=
  ⟨i.location.path ++ [i.childOrdinal],a.child.role,a.receiver.compiled.readFrom.center.decl.id,version⟩

def address {i s w} (a : Linked i s w) (version ordinal : Nat) (out : Output) : Key :=
  ⟨stamp a version,ordinal,out.name,out.target⟩

structure Released {i s w} (a : Linked i s w) (auth : Authority) (loc : Location) (ordinal : Nat) where
  body : Carry a ordinal
  exactSite : loc.path = i.location.path ++ [i.childOrdinal]
  active : stamp a loc.version ∈ auth.active
  oneActive : (auth.active.map position).Nodup
  granted : address a loc.version ordinal body.indexed.demand ∈ auth.released

def read {i s w} (a : Linked i s w) (auth : Authority) (loc : Location) (ordinal : Nat) :
    Option (Released a auth loc ordinal) := do
  if same : loc.path = i.location.path ++ [i.childOrdinal] then
    let body ← check a ordinal
    if alive : stamp a loc.version ∈ auth.active then
      if unique : (auth.active.map position).Nodup then
        if allowed : address a loc.version ordinal body.indexed.demand ∈ auth.released then
          pure ⟨body,same,alive,unique,allowed⟩
        else none
      else none
    else none
  else none

theorem exact_site {i s w} {a : Linked i s w} {auth loc ordinal} (r : Released a auth loc ordinal) :
    (stamp a loc.version).path = loc.path ∧
    (stamp a loc.version).role = a.child.role ∧
    (stamp a loc.version).declarationId = a.receiver.compiled.readFrom.center.decl.id ∧
    (stamp a loc.version).version = loc.version ∧
    a.writer.output.children[i.childOrdinal]? = some a.child :=
  ⟨r.exactSite.symm,rfl,rfl,rfl,a.actual⟩

theorem no_conflicting_version {i s w} {a : Linked i s w} {auth loc ordinal} (r : Released a auth loc ordinal)
    {competing : Stamp} (seen : competing ∈ auth.active)
    (sameSite : position competing = position (stamp a loc.version)) :
    competing = stamp a loc.version :=
  GeneralDeclarativeWitnessTypedIndex354.unique_position r.oneActive seen r.active sameSite

theorem exact_payload {i s w} {a : Linked i s w} {auth loc ordinal} (r : Released a auth loc ordinal)
    (m : Assignment) (fit : Models s m) :
    a.child.outputs[ordinal]? = some r.body.indexed.demand ∧
    w.receiver.trace[ordinal]? = some (.typed r.body.indexed.typed.row) ∧
    r.body.indexed.typed.row.root = (address a loc.version ordinal r.body.indexed.demand).target ∧
    CommonNominalFullCarrier.Equivalent (m r.body.indexed.typed.row.valueName).1
      (.union (m a.writer.output.source.anchor.first.valueName).1 (m a.writer.output.source.anchor.last.valueName).1) :=
  exact_same_model r.body m fit

end Yulang.GeneralDeclarativeWitnessRangeRelease355
