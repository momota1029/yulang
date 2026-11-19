import Yulang.GeneralRebaseTreeStructural272

namespace Yulang.GeneralRebaseTreeInterpreter272
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Cyclic RootCycle)
open GeneralNominalFiniteMeaning (At)
open GeneralSourceDictionaries (Occurrence)
open GeneralRebaseFiniteTree272 (Tree Canonical value)
open GeneralRebaseTreeReadbackState272 (Result Meaning decision decision_sound)
open GeneralRebasePartialBool268 (Answer Reflect)

abbrev Source := Nat → Option Tree

def Certified (m : Assignment) (source : Source) : Prop :=
 ∀ id t, source id = some t → Canonical t ∧ Equivalent (m id).1 (value t)

def run (source : Source) : Origin → Result
 | .source id =>
   match source id with
   | some tree => .found tree
   | none => .unknown
 | .nominal parent n idx => GeneralRebaseTreeNominal272.step n idx (run source parent)
 | .structural parent s idx => GeneralRebaseTreeStructural272.step s idx (run source parent)

theorem run_sound (m : Assignment) (source : Source) (cert : Certified m source) (o : Origin) :
 Meaning m o (run source o) := by
 induction o with
 | source id =>
   unfold run
   split
   · rename_i t h
     have valid := cert id t h
     exact ⟨valid.1,GeneralRebaseInstalledReadback271.source_at m id _ valid.2⟩
   · trivial
 | nominal parent name idx ih =>
   exact GeneralRebaseTreeNominal272.sound m parent name idx _ ih
 | structural parent shape idx ih =>
   exact GeneralRebaseTreeStructural272.sound m parent shape idx _ ih

def inspect (source : Source) (o : Origin) : Answer := decision (run source o)

theorem inspect_sound (state : State roles) (m : Assignment) (valid : Models state m)
 (source : Source) (cert : Certified m source) (o : Origin) :
 Reflect (Cyclic state o) (inspect source o) :=
 decision_sound m valid o _ (run_sound m source cert o)

def inspectRoot (source : Source) (state : State roles) (focus : Occurrence roles) : Answer :=
 GeneralRebaseVersionedK2Probe268.rootOrigin state focus (inspect source)

theorem inspectRoot_sound (state : State roles) (m : Assignment) (valid : Models state m)
 (source : Source) (cert : Certified m source) (focus : Occurrence roles) :
 Reflect (RootCycle state focus) (inspectRoot source state focus) :=
 GeneralRebaseVersionedK2Probe268.rootOrigin_sound state focus _ (inspect_sound state m valid source cert)

theorem inspectK2_sound (registry : GeneralDeclarations.Registry) (state : State roles) (m : Assignment)
 (valid : Models state m) (source : Source) (cert : Certified m source) (focus : Occurrence roles) :
 Reflect ((GeneralRebaseSourceSurvivor267.Boundary roles).RootK2 registry state focus) (inspectRoot source state focus) :=
 GeneralRebasePartialFinite268.transfer (GeneralRebaseRawIntoFull271.root_exact registry state ⟨m,valid⟩ focus).symm
   (inspectRoot_sound state m valid source cert focus)

end Yulang.GeneralRebaseTreeInterpreter272
