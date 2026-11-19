import Yulang.GeneralRebaseTreeAuto272
import Yulang.GeneralRebaseRecordRecursiveFixture271

namespace Yulang.GeneralRebaseTreeHybrid272
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Cyclic RootCycle)
open GeneralNominalRecursiveInspection (Origin)
open GeneralSourceDictionaries (Occurrence)
open GeneralRebasePartialBool268 (Answer Reflect)

theorem fallback_sound (p : Prop) (a b : Answer) (one : Reflect p a) (two : Reflect p b) :
 Reflect p (a.or b) := by
 cases a with
 | none => exact two
 | some v => exact one

theorem finite_never_positive (state : State roles) (fuel : Nat) (o : Origin) :
 GeneralRebaseTreeAuto272.check state fuel o ≠ some true := by
 unfold GeneralRebaseTreeAuto272.check GeneralRebaseTreeInterpreter272.inspect
 cases known : GeneralRebaseTreeInterpreter272.run (GeneralRebaseTreeAuto272.source state fuel) o <;>
   intro impossible <;> cases impossible

theorem cycle_forces_abstain (state : State roles) (fuel : Nat) (o : Origin) (recurrent : Cyclic state o) :
 GeneralRebaseTreeAuto272.check state fuel o = none := by
 cases result : GeneralRebaseTreeAuto272.check state fuel o with
 | none => rfl
 | some b =>
   cases b with
   | true => exact False.elim (finite_never_positive state fuel o result)
   | false =>
     obtain ⟨m,valid⟩ := recurrent.2
     have checked := GeneralRebaseTreeAuto272.check_sound state m valid fuel o
     rw [result] at checked
     exact False.elim (checked recurrent)

def inspect (state : State roles) (fuel : Nat) (o : Origin) : Answer :=
 (GeneralRebaseTreeAuto272.check state fuel o).or (GeneralRebaseLocalOriginPocket271.inspect state o)

theorem inspect_sound (state : State roles) (m : GeneralNominalCommonBridge.Assignment) (full : Models state m)
 (fuel : Nat) (o : Origin) : Reflect (Cyclic state o) (inspect state fuel o) :=
 fallback_sound _ _ _ (GeneralRebaseTreeAuto272.check_sound state m full fuel o)
   (GeneralRebaseLocalOriginPocket271.inspect_sound state ⟨m,full⟩ o)

theorem retains_positive (state : State roles) (m : GeneralNominalCommonBridge.Assignment) (full : Models state m)
 (o : Origin) (pocket : GeneralRebaseLocalOriginPocket271.inspect state o = some true) (fuel : Nat) :
 inspect state fuel o = some true := by
 have checked := GeneralRebaseLocalOriginPocket271.inspect_sound state ⟨m,full⟩ o
 rw [pocket] at checked
 unfold inspect
 rw [cycle_forces_abstain state fuel o checked,pocket]
 rfl

def root (state : State roles) (fuel : Nat) (focus : Occurrence roles) : Answer :=
 GeneralRebaseVersionedK2Probe268.rootOrigin state focus (inspect state fuel)

theorem root_sound (registry : GeneralDeclarations.Registry) (state : State roles)
 (m : GeneralNominalCommonBridge.Assignment) (full : Models state m) (fuel : Nat) (focus : Occurrence roles) :
 Reflect ((GeneralRebaseSourceSurvivor267.Boundary roles).RootK2 registry state focus) (root state fuel focus) :=
 GeneralRebasePartialFinite268.transfer (GeneralRebaseRawIntoFull271.root_exact registry state ⟨m,full⟩ focus).symm
   (GeneralRebaseVersionedK2Probe268.rootOrigin_sound state focus _ (inspect_sound state m full fuel))

namespace GuardedRecord
open GeneralRebaseRecordRecursiveFixture271 (journal model full_model)

theorem actual_pocket : GeneralRebaseLocalOriginPocket271.inspect journal (.source 0) = some true := by decide +kernel

theorem every_fuel (n : Nat) : inspect journal n (.source 0) = some true :=
 retains_positive journal model full_model _ actual_pocket n

end GuardedRecord

namespace Installed252
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralDictionaryOutputDepth252 (model)

theorem actual_pocket_missing : GeneralRebaseLocalOriginPocket271.inspect installed (.source 3) = none := by decide +kernel

theorem auto_works : inspect installed 2 (.source 3) = some false := by decide +kernel

theorem automated_negative : ¬ Cyclic installed (.source 3) := by
 have known := inspect_sound installed model installed_model 2 (.source 3)
 rw [auto_works] at known
 exact known

end Installed252
end Yulang.GeneralRebaseTreeHybrid272
