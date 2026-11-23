import Yulang.GeneralDeclarativeWitnessModeDeclaration357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessJoinedCheck357
open GeneralDeclarativeWitnessDeclaredState357
  (Current AuthoredNominal Joined WrittenBody observed point pointSpans centerEq context)
open GeneralDeclarativeWitnessClassifyVariance357 (JoinedLocal Rule roleView)
open GeneralDeclarativeWitnessConstructorModes357 (readUse Mode)
open GeneralDeclarativeWitnessCompiler350 (Wire decode retained printDemand)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarationPatterns (Pattern normalize)

def unaryCode (x : AuthoredNominal) : Option (Nat × Nat × Nat × Nat) :=
  match x.arguments with
  | [.value (.var n)] => some (x.place,x.tag,x.name,n)
  | _ => none

theorem unary_exact {x : AuthoredNominal} {r t k v} :
    unaryCode x = some (r,t,k,v) → x = observed r t k v := by
  cases x with
  | mk pos tag name args =>
    unfold unaryCode
    split
    · rename_i _ _ writtenArgs
      simp only [Option.some.injEq,Prod.mk.injEq]
      rintro ⟨rfl,rfl,rfl,rfl⟩
      change args = _ at writtenArgs
      rw [writtenArgs]
      rfl
    · intro none
      cases none

def found (s : Current) (place tag name slot : Nat) : Bool :=
  (s.visible.map unaryCode).contains (some (place,tag,name,slot))

theorem find_exact {s : Current} {r t k v} (yes : found s r t k v = true) :
    observed r t k v ∈ s.visible := by
  have got := List.contains_iff_mem.mp (show (s.visible.map unaryCode).contains (some (r,t,k,v)) = true from yes)
  obtain ⟨entry,inList,same⟩ := List.mem_map.mp got
  rwa [unary_exact same] at inList

structure Recipe where
  tag : Nat
  name : Nat
  bindL : Nat
  bindR : Nat
  physicalL : Nat
  physicalR : Nat
  physical : Nat
  valueL : Nat
  valueR : Nat
  value : Nat
  written : Pattern

def checkJoin (s : Current) (d : Demand) (impl : Declaration) (a : Recipe) :
    Option (Joined s d impl) := do
  let use ← readUse s.environment a.name 1
  match mode : use.mode with
  | .declared parameters =>
    if sign : parameters = [⟨.value,.covariant⟩] then
      if law : a.bindL ≠ a.bindR ∧ impl.head = [a.written] ∧ normalize a.written =
          .variant a.tag (.join (.app a.name [.var a.bindL]) (.app a.name [.var a.bindR])) then
        if phys : d.arguments.map GeneralDeclarativeWitnessCompiler350.trip =
            [GeneralDeclarativeWitnessCompiler350.trip (point a.physical)] then
          if first : found s a.physicalL a.tag a.name a.valueL = true then
            if last : found s a.physicalR a.tag a.name a.valueR = true then
              if exact : found s a.physical a.tag a.name a.value = true then
                if written : centerEq a.value a.valueL a.valueR ∈ s.ordinary.equations then
                  some ⟨a.tag,a.name,a.bindL,a.bindR,law.1,a.written,law.2.1,law.2.2,use,
                    mode.trans (congrArg Mode.declared sign),a.physicalL,a.physicalR,a.physical,a.valueL,
                    a.valueR,a.value,GeneralDeclarativeWitnessCompiler350.map_injective
                      (fun h => GeneralDeclarativeWitnessCompiler350.trip_injective h) phys,
                    find_exact first,find_exact last,find_exact exact,written⟩
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  | _ => none

structure Layout where
  named : State
  keep : List Nat
  fallback : Nat → Capture
  via : Clause → Nat → Nat

structure Answer (s : Current) (d : Demand) (wire : Wire) where
  impl : Declaration
  kids : List Demand
  localRead : JoinedLocal s d impl kids
  actualChildren : wire.children = kids.map printDemand
  actualWrites : wire.outputRows = localRead.body.finished.fixed

def replay (s : Current) (d : Demand) (recipe : Recipe) (layout : Layout) (wire : Wire) :
    Option (Answer s d wire) :=
  match wholeRole : (roleView s d.role).declarations with
  | [impl] => do
    let j ← checkJoin s d impl recipe
    let spans := pointSpans j.firstBinder j.lastBinder j.actualValue
    let c := context s d impl layout.named spans layout.keep layout.fallback layout.via
    let a ← decode c s.ordinary wire
    let wb : WrittenBody s d impl spans a.compiled.kids :=
      ⟨layout.named,layout.keep,layout.fallback,layout.via,a.compiled,a.run,rfl,retained a⟩
    pure ⟨impl,a.compiled.kids,⟨wholeRole,j,wb⟩,a.printed,a.fixed⟩
  | _ => none

theorem replay_rule {s : Current} {d wire} (a : Answer s d wire) :
    Rule s d (.selected a.impl.id a.kids) :=
  .join a.localRead

end Yulang.GeneralDeclarativeWitnessJoinedCheck357
