import Yulang.GeneralDeclarativeWitnessTypedPacket354
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedRelease354
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Wire Row assigned)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralDeclarativeWitnessTypedPacket354 (Accepted Report At typedAt)
open GeneralDeclarativeWitnessCompiler350 (portNames)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeWitnessLiteral349 (preserves preserves_iff)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralSourceState (Output)

structure Stamp where
  path : List Nat
  role : Nat
  declarationId : Nat
  version : Nat
  deriving DecidableEq

def position (s : Stamp) : List Nat × Nat := (s.path,s.role)

structure Key where
  stamp : Stamp
  ordinal : Nat
  name : Nat
  target : Nat
  deriving DecidableEq

structure Authority where
  active : List Stamp
  released : List Key

structure Location where
  path : List Nat
  version : Nat

def stamp {p w s report} (a : Accepted p w s report) (loc : Location) : Stamp :=
  ⟨loc.path,p.demand.role,a.output.source.decl.id,loc.version⟩

def address {p w s report} (a : Accepted p w s report) (loc : Location) (i : Nat) (out : Output) : Key :=
  ⟨stamp a loc,i,out.name,out.target⟩

structure Released {p w s report} (a : Accepted p w s report) (loc : Location) (u : Authority) (i : Nat) where
  atWrite : At p a.output.source.ctx (portNames a.output.source.ctx a.output.ports).input p.demand.outputs i
  inTrace : a.output.writes.trace[i]? = some (.typed atWrite.typed.row)
  active : stamp a loc ∈ u.active
  distinct : (u.active.map position).Nodup
  release : address a loc i atWrite.demand ∈ u.released
  payload : atWrite.typed.row.valueName = a.output.source.anchor.current.valueName
  prior : preserves p.stage s = true

def select {p w s report} (a : Accepted p w s report) (loc : Location) (u : Authority) (i : Nat) :
    Option (Released a loc u i) := do
  let atWrite ← typedAt a.output.writes i
  if live : stamp a loc ∈ u.active then
    if distinct : (u.active.map position).Nodup then
      if granted : address a loc i atWrite.1.demand ∈ u.released then
        if slot : atWrite.1.typed.row.valueName = a.output.source.anchor.current.valueName then
          if prior : preserves p.stage s = true then
            some ⟨atWrite.1,atWrite.2,live,distinct,granted,slot,prior⟩
          else none
        else none
      else none
    else none
  else none

theorem exact_ordinal {p w s report} {a : Accepted p w s report} {loc u i} (b : Released a loc u i) :
    p.demand.outputs[i]? = some b.atWrite.demand ∧
    report.trace[i]? = some (.typed b.atWrite.typed.row) ∧
    b.atWrite.typed.row.root = (address a loc i b.atWrite.demand).target ∧
    (address a loc i b.atWrite.demand).name = b.atWrite.demand.name := by
  exact ⟨b.atWrite.indexed,a.trace.symm ▸ b.inTrace,rfl,rfl⟩

theorem actual_payload {p w s report} {a : Accepted p w s report} {loc u i} (b : Released a loc u i)
    (m : Assignment) (fit : Models s m) :
    CommonNominalFullCarrier.Equivalent (m b.atWrite.typed.row.valueName).1
      (.union (m a.output.source.anchor.first.valueName).1 (m a.output.source.anchor.last.valueName).1) := by
  rw [b.payload]
  exact GeneralDeclarativeWitnessCovariantOrigin353.whole_full a.output.source.anchor m
    (restrict ((preserves_iff ..).mp b.prior) m fit)

end Yulang.GeneralDeclarativeWitnessTypedRelease354
