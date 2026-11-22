import Yulang.GeneralDeclarativeWitnessHeader349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessFixture349
open GeneralSourceMetadataRows291 (Source)
open GeneralSourceMetadataBareRole291 (BareRow)
open GeneralSourceMetadataBareBundle291 (InputBundle compile)
open GeneralDeclarativeWitnessProblem349 (Problem declared first)
open GeneralDeclarativeWitnessHeader349 (Header replay check)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State)
open GeneralSourceState (Output)

def tables : Source := ⟨.absent,[]⟩
def state : State := ⟨⟨[],[]⟩,[]⟩
def decl : Declaration := ⟨8,7,[.var 3],[],[⟨0,1,.var 3⟩],[]⟩
def role : BareRow := ⟨7,1,[(0,some (.var 0)),(1,none)]⟩
def ignored : BareRow := ⟨91,0,[]⟩
def invalidDefault : BareRow := ⟨91,0,[(9,some (.app 44 []))]⟩
def source (last : BareRow) : InputBundle :=
  ⟨tables,tables,⟨0,[role,last]⟩,[decl]⟩

def a : Output := ⟨0,4⟩
def b : Output := ⟨1,17⟩
def demand : Demand := ⟨7,[⟨0,0,0⟩],[a,a,b]⟩
def problem (last : BareRow) : Problem := ⟨source last,state,demand⟩
def genuine : Header := ⟨[a,a,b]⟩

theorem good : check (problem ignored) genuine = true := rfl

theorem target_changed : check (problem ignored) ⟨[a,⟨0,5⟩,b]⟩ = false := rfl

theorem order_changed : check (problem ignored) ⟨[b,a,a]⟩ = false := rfl

theorem duplicate_omitted : check (problem ignored) ⟨[a,b]⟩ = false := rfl

theorem ignored_default :
    (compile (source invalidDefault)).isSome = true ∧ first (problem invalidDefault) = none ∧
      check (problem invalidDefault) genuine = false := ⟨rfl,rfl,rfl⟩

def askedNotDeclared : Problem :=
  ⟨source ignored,state,{demand with outputs := [⟨2,4⟩]}⟩

theorem undeclared : first askedNotDeclared = none ∧ check askedNotDeclared ⟨[⟨2,4⟩]⟩ = false :=
  ⟨rfl,rfl⟩

end Yulang.GeneralDeclarativeWitnessFixture349
