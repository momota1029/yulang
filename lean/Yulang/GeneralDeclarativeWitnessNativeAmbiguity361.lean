import Yulang.GeneralDeclarativeWitnessWholeSound361
import Yulang.GeneralDeclarativeWitnessNestedReflection361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 66000
set_option maxHeartbeats 70000000
namespace Yulang.GeneralDeclarativeWitnessNativeAmbiguity361
open GeneralDeclarativeWitnessNativeNestedMatch361 (Matches Captures)
open GeneralDeclarativeWitnessNestedLeaf361 (writerSlots elect)
open GeneralDeclarativeWitnessNestedFixture361 (nestedHead receiver)
open GeneralDeclarativeWitnessNativeLeafClassify361 (visible)
open GeneralDeclarativeWitnessNativePortTransport361 (Port transport)
open GeneralDeclarativeWitnessNativeDirectSource361 (Wire actualWire)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)
open GeneralDeclarativeWitnessMixedDependency361 (Path exactGraph no_strict_loop board_checked)
open GeneralDeclarativeWitnessRank350 (sound)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence)
open GeneralDeclarativeWitnessAuthorBeforeRelease361 (Started Prefix beforeGrant close source)
open GeneralDeclarativeWitnessAuthorOrdinaryChoice361 (Author author_checked)
open GeneralDeclarativeWitnessNativePreparation360 (prepare)
open GeneralDeclarativeWitnessNestedInstall360 (Run requested layout)
open GeneralDeclarativeWitnessNativePipeline360 (wire gate authority)
open GeneralDeclarativeWitnessNativeSnapshot360 (commit)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessJointObservation359 (parentScope)
open GeneralDeclarativeWitnessModeCoverage357 (checkDecl)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (Frontier Classify)

structure Candidate {negative : Bool} (r : Run negative) (d : Demand) (impl : Declaration) where
  pattern : Pattern
  written : impl.head.map normalize = [pattern]
  caps : Captures
  matched : Matches r.env (writerSlots r) (wire negative).route r.typed.write.code pattern caps
  checked : checkDecl r.env impl = true
  terminal : impl.requirements = [] ∧ impl.associated = [] ∧ d.outputs = []

def inspect {negative} (r : Run negative) (d : Demand) (impl : Declaration) : Option (Candidate r d impl) :=
  match head : impl.head.map normalize with
  | [pattern] =>
    if checked : checkDecl r.env impl = true then
      if body : impl.requirements = [] ∧ impl.associated = [] ∧ d.outputs = [] then do
        let matched ← GeneralDeclarativeWitnessNativeNestedMatch361.read r.env (writerSlots r)
          (wire negative).route r.typed.write.code pattern
        some ⟨pattern,head,matched.1,matched.2,checked,body⟩
      else none
    else none
  | _ => none

/-- Both currently visible declarations actually match the same backed
native port; there is no precedence based on declaration id or the
compiler's supplied frame. This handles this two-candidate fragment only. -/
structure Two {negative : Bool} {r : Run negative} {s : Sequence r}
    {gate : ReleaseAuthority} {io : Wire} (port : Port s gate io) where
  first : Declaration
  last : Declaration
  allVisible : visible s = [first,last]
  unequal : first.id ≠ last.id
  firstMatch : Candidate r s.receiver first
  lastMatch : Candidate r s.receiver last
  safe : ∀ projection n,¬Path s.final projection true n n

def compare {negative} {r : Run negative} {s : Sequence r} {gate io} (port : Port s gate io) : Option (Two port) :=
  match listed : visible s with
  | [a,b] =>
    if distinct : a.id ≠ b.id then
      if graph : exactGraph s then do
        let first ← inspect r s.receiver a
        let second ← inspect r s.receiver b
        have h := Bool.and_eq_true_iff.mp graph
        some ⟨a,b,listed,distinct,first,second,fun _ => no_strict_loop (sound h.1) (board_checked h.2)⟩
      else none
    else none
  | _ => none

inductive Local {negative : Bool} {r : Run negative} {s : Sequence r} {gate io}
    (port : Port s gate io) : Demand → Frontier Demand → Prop where
  | competing : Two port → Local port s.receiver .ambiguous

theorem two_supported_candidates_are_ambiguous {negative} {r : Run negative} {s : Sequence r} {gate io}
    {port : Port s gate io} (witness : Two port) : Classify (Local port) s.receiver .ambiguous :=
  ⟨.ambiguous,.ambiguous (.competing witness),.ambiguous⟩

def competitor (negative : Bool) : Declaration :=
  ⟨76,8,[.app 55 [.app (if negative then 42 else 20) [.var 93]]],[],[],[]⟩

def exampleStart (negative : Bool) : Option (Started negative) := do
  let env ← GeneralDeclarativeWitnessCoverageFixture357.prepare
    { GeneralDeclarativeWitnessCoverageFixture357.bundle with
      roles := ⟨0,[⟨5,2,[(0,none)]⟩,⟨6,1,[(0,none)]⟩,⟨7,2,[]⟩,⟨8,1,[]⟩]⟩
      declarations := [GeneralDeclarativeWitnessAuthorOrdinaryChoice361.aligned negative,
        GeneralDeclarativeWitnessNativeBodyFixture360.childDecl,
        GeneralDeclarativeWitnessMixedForwardChoice361.aligned,receiver negative false,competitor negative] }
  if checked : Author.check env negative then
    let proof := author_checked checked
    let p ← prepare env parentScope requested layout
    let compiled ← GeneralDeclarativeWitnessNativeValue360.compile p table (wire negative) 3
    match saved : commit p compiled ⟨layout.named,gate⟩ with
    | none => none
    | some final =>
      some ⟨⟨env,p,compiled,final,saved⟩,proof,Option.some.inj (p.authored.symm.trans proof.atSource)⟩
  else none

def exactCheck {negative r} (s : @Sequence negative r) : Bool :=
  ((transport s authority actualWire).map fun p =>
    (elect p).isNone && ((compare p).map fun both => decide (both.first.id = 75 ∧ both.last.id = 76)).getD false).getD false

theorem actual_additional_visible_source_overlaps (negative : Bool) :
    ((exampleStart negative).bind fun r => (beforeGrant r.root).bind fun p =>
      (close p).map fun continued => exactCheck continued.actual).getD false = true := by
  cases negative <;> decide +kernel


theorem actual_conflict_produces_no_scoped_dictionary {negative : Bool}
    {r : Started negative} {p : Prefix r.root}
    {cont : GeneralDeclarativeWitnessAuthorBeforeRelease361.Continued p}
    {port : Port cont.actual authority actualWire}
    (written : exampleStart negative = some r) (ordinary : beforeGrant r.root = some p)
    (passed : close p = some cont) (anchored : transport cont.actual authority actualWire = some port) :
    Classify (Local port) cont.actual.receiver .ambiguous ∧ elect port = none ∧
    ∀ dict,¬Classify (Local port) cont.actual.receiver (.selected dict) := by
  have test := actual_additional_visible_source_overlaps negative
  rw [written] at test
  change ((beforeGrant r.root).bind fun p =>
    (close p).map fun cont => exactCheck cont.actual).getD false = true at test
  rw [ordinary] at test
  change ((close p).map fun cont => exactCheck cont.actual).getD false = true at test
  rw [passed] at test
  change exactCheck cont.actual = true at test
  unfold exactCheck at test
  rw [anchored] at test
  have accepted := Bool.and_eq_true_iff.mp (show
    (elect port).isNone &&
      ((compare port).map fun both => decide (both.first.id = 75 ∧ both.last.id = 76)).getD false = true from test)
  have amb : Classify (Local port) cont.actual.receiver .ambiguous := by
    cases matched : compare port with
    | none => rw [matched] at accepted; exact False.elim (Bool.noConfusion accepted.2)
    | some h => exact two_supported_candidates_are_ambiguous h
  refine ⟨amb,Option.isNone_iff_eq_none.mp accepted.1,?_⟩
  intro dict conflict
  obtain ⟨_,ways,summary⟩ := conflict
  cases ways with
  | pending h => cases h
  | selected h _ => cases h
  | rejected h => cases h
  | ambiguous _ => cases summary

end Yulang.GeneralDeclarativeWitnessNativeAmbiguity361
