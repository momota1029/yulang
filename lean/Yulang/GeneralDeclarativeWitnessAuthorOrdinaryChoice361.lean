import Yulang.GeneralDeclarativeWitnessMixedForwardSound361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65000
set_option maxHeartbeats 68000000
namespace Yulang.GeneralDeclarativeWitnessAuthorOrdinaryChoice361
open GeneralDeclarativeWitnessMixedForwardChoice361 (OrdinarySupported checkOrdinary source_inputs_exact)
open GeneralDeclarativeWitnessNestedInstall360 (Run written requested layout)
open GeneralDeclarativeWitnessNativeBodyFixture360 (childDecl)
open GeneralDeclarativeWitnessJointObservation359 (authored firstLo firstHi parentScope)
open GeneralDeclarativeWitnessSourceEndpoint359 (Read check_exact endpoint_in_model)
open GeneralDeclarativeWitnessNativeSnapshot360 (commit)
open GeneralDeclarativeWitnessNativePipeline360 (gate wire)
open GeneralDeclarativeWitnessNativePreparation360 (prepare shape)
open GeneralDeclarativeWitnessModeCoverage357 (checkDecl)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessNativeLowerCut361 (levels)
open GeneralDeclarativeWitnessRank350 (check)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open PresenceNormalForm (Atom)
open GeneralDeclarations (Declaration)

def aligned (negative : Bool) : Declaration :=
  {written negative with head := [.var 80,.var 81]}

def roleView (e : Environment) (role : Nat) : List Declaration :=
  e.source.declarations.filter (fun decl => decl.role == role)

def firstCheck (s : State) : Bool :=
  GeneralDeclarativeWitnessSourceEndpoint359.check authored s 60 firstLo &&
  GeneralDeclarativeWitnessSourceEndpoint359.check authored s 62 firstHi &&
  decide ((60,61) ∈ s.normal.intervals ∧ (61,62) ∈ s.normal.intervals)

structure FirstSource (s : State) : Prop where
  lower : Read authored s 60 firstLo
  upper : Read authored s 62 firstHi
  lowerKnown : (GeneralDeclarativeLowerKnown321.constructorTag (firstLo.code 60)).isSome = true
  upperKnown : (GeneralDeclarativeLowerKnown321.constructorTag (firstHi.code 62)).isSome = true
  left : Bound s.normal 60 61
  right : Bound s.normal 61 62

theorem first_source_exact {s} (checked : firstCheck s = true) : FirstSource s := by
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨lo,hi⟩ := Bool.and_eq_true_iff.mp a
  have pair := of_decide_eq_true b
  exact ⟨check_exact.mp lo,check_exact.mp hi,rfl,rfl,.interval pair.1,.interval pair.2⟩

structure Author (e : Environment) (negative : Bool) : Prop where
  visible : roleView e 5 = [aligned negative]
  atSource : e.source.declarations[parentScope.sourceOrdinal]? = some (aligned negative)
  initialFirst : FirstSource layout.named
  initialSecond : OrdinarySupported layout.named
  rank : GeneralDeclarativeWitnessRank350.check layout.named levels = true
  covered : checkDecl e (aligned negative) = true
  sourceShape : shape e.source (aligned negative) = true
  demand : GeneralDeclarativeWitnessProblem349.declared e.source requested = true

def Author.check (e : Environment) (negative : Bool) : Bool :=
  decide (roleView e 5 = [aligned negative] ∧ e.source.declarations[parentScope.sourceOrdinal]? = some (aligned negative)) &&
    ((firstCheck layout.named && checkOrdinary layout.named) && GeneralDeclarativeWitnessRank350.check layout.named levels) &&
    ((checkDecl e (aligned negative) && shape e.source (aligned negative)) &&
      GeneralDeclarativeWitnessProblem349.declared e.source requested)

theorem author_checked {e negative} (valid : Author.check e negative = true) : Author e negative := by
  obtain ⟨origins,authoring⟩ := Bool.and_eq_true_iff.mp valid
  obtain ⟨located,stage⟩ := Bool.and_eq_true_iff.mp origins
  obtain ⟨actual,knownRank⟩ := Bool.and_eq_true_iff.mp stage
  obtain ⟨first,second⟩ := Bool.and_eq_true_iff.mp actual
  obtain ⟨source,request⟩ := Bool.and_eq_true_iff.mp authoring
  obtain ⟨types,descent⟩ := Bool.and_eq_true_iff.mp source
  have chosen := of_decide_eq_true located
  exact ⟨chosen.1,chosen.2,first_source_exact first,source_inputs_exact second,knownRank,types,descent,request⟩

def directBound (s : State) (a b : Nat) : Bool :=
  decide ((Atom.tyLe (.var a) (.var b) : Atom Nat) ∈ s.normal.ordinary)

def directAlias (s : State) (a b : Nat) : Bool := directBound s a b && directBound s b a

theorem directs_alias {s a b} (passes : directAlias s a b = true) : Alias s a b := by
  obtain ⟨there,back⟩ := Bool.and_eq_true_iff.mp passes
  exact .bounds (.constraint (of_decide_eq_true there)) (.constraint (of_decide_eq_true back))

structure OrdinaryChild {negative : Bool} (r : Run negative) (d : Demand) : Prop where
  selected : roleView r.env 6 = [childDecl]
  atSource : r.env.source.declarations[1]? = some childDecl
  exactDemand : printDemand d = (6,[(106,61,107)],[(0,105)])
  authored : FirstSource r.final.ordinary
  originLo : Alias r.final.ordinary 106 60
  originHi : Alias r.final.ordinary 107 62
  rank : GeneralDeclarativeWitnessRank350.check r.final.ordinary levels = true
  request : GeneralDeclarativeWitnessProblem349.declared r.env.source d = true

def OrdinaryChild.check {negative} (r : Run negative) (d : Demand) : Bool :=
  (decide (roleView r.env 6 = [childDecl] ∧ r.env.source.declarations[1]? = some childDecl ∧
    printDemand d = (6,[(106,61,107)],[(0,105)])) && firstCheck r.final.ordinary) &&
  ((directAlias r.final.ordinary 106 60 && directAlias r.final.ordinary 107 62) &&
    (GeneralDeclarativeWitnessRank350.check r.final.ordinary levels && GeneralDeclarativeWitnessProblem349.declared r.env.source d))

theorem child_checked {negative} {r : Run negative} {d : Demand}
    (passes : OrdinaryChild.check r d = true) : OrdinaryChild r d := by
  obtain ⟨scope,after⟩ := Bool.and_eq_true_iff.mp passes
  obtain ⟨selected,source⟩ := Bool.and_eq_true_iff.mp scope
  obtain ⟨edges,inner⟩ := Bool.and_eq_true_iff.mp after
  obtain ⟨lo,hi⟩ := Bool.and_eq_true_iff.mp edges
  obtain ⟨safe,asked⟩ := Bool.and_eq_true_iff.mp inner
  have located := of_decide_eq_true selected
  exact ⟨located.1,located.2.1,located.2.2,first_source_exact source,directs_alias lo,directs_alias hi,safe,asked⟩

theorem alias_read_witness {s : State} {a b} (same : Alias s a b) (m : Assignment) (fit : Models s m) :
    Equivalent (m a).1 (m b).1 := by
  induction same with
  | bounds lo hi => exact ⟨bound_sound m fit.1 lo,bound_sound m fit.1 hi⟩
  | forward row => exact fit.2 _ row
  | backward row => exact (fit.2 _ row).symm
  | trans _ _ i j => exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans i j

end Yulang.GeneralDeclarativeWitnessAuthorOrdinaryChoice361
