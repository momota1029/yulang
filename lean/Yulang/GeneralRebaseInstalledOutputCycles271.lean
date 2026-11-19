import Yulang.GeneralRebaseUnaryReadback271

namespace Yulang.GeneralRebaseInstalledOutputCycles271
open CommonNominalFullCarrier
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalVersionedCycles232 (Cyclic RootCycle)
open GeneralDictionaryOutputDepth252 (model root sourceRegistry)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralRebaseUnaryRank271 (Unary value)
open GeneralRebaseUnaryReadback271 (Result run cycle stepNom stepStruct)

def term : Nat → Unary
 | 0 | 1 => .scalar .int
 | 2 => .wrapper 0 (.scalar .int)
 | 3 => .wrapper 0 (.wrapper 0 (.wrapper 0 (.scalar .int)))
 | _ => .wrapper 0 (.scalar .int)

theorem known (n : Nat) : Equivalent (model n).1 (value (term n)) := by
 cases n with
 | zero => exact ⟨subtype_refl _,subtype_refl _⟩
 | succ n =>
   rcases n with _ | _ | _ | n <;> exact ⟨subtype_refl _,subtype_refl _⟩

def source (id : Nat) : Option Unary := some (term id)

theorem total (o : Origin) : run source o ≠ .unknown := by
 induction o with
 | source n => simp [run,source]
 | nominal p n j ih =>
   have sure : ∀ r, r ≠ .unknown → stepNom n j r ≠ .unknown := by
     intro r h
     cases r with
     | unknown => exact False.elim (h rfl)
     | absent => intro clash; cases clash
     | found data =>
       cases data with
       | scalar b => intro contradiction; cases contradiction
       | wrapper name child =>
         change (if n = name ∧ j = 0 then Result.found child else Result.absent) ≠ Result.unknown
         split <;> intro contradiction <;> cases contradiction
   exact sure _ ih
 | structural p s i ih =>
   have sure : ∀ r, r ≠ .unknown → stepStruct r ≠ .unknown := by
     intro r h
     cases r with
     | unknown => exact False.elim (h rfl)
     | absent | found _ => intro clash; cases clash
   exact sure _ ih

theorem computed (o : Origin) : cycle source o = some false := by
 have t := total o
 unfold cycle
 split
 · exact False.elim (t (by assumption))
 · rfl

theorem no_cycle (o : Origin) : ¬ Cyclic installed o := by
 have yes := GeneralRebaseUnaryReadback271.cycle_sound installed model installed_model source
   (fun n shape h => Option.some.inj h ▸ known n) o
 rw [computed] at yes
 exact yes

theorem deep_readback :
 run source (.nominal (.nominal (.nominal (.source 3) 0 0) 0 0) 0 0) = .found (.scalar .int) := rfl

theorem malformed_readback :
 run source (.nominal (.nominal (.source 3) 9 0) 0 0) = .absent := rfl

theorem combined_root_clear :
 ¬ (GeneralRebaseSourceSurvivor267.Boundary GeneralDictionaryOutputDepth252.roles).RootK2 sourceRegistry installed root := by
 intro denied
 have cyc := (GeneralRebaseRawIntoFull271.root_exact sourceRegistry installed ⟨model,installed_model⟩ root).mp denied
 rcases cyc with ⟨_,v⟩ | ⟨_,_,_,_,v⟩
 · exact no_cycle _ v
 · exact no_cycle _ v

end Yulang.GeneralRebaseInstalledOutputCycles271
