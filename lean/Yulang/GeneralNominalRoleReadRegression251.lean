import Yulang.GeneralNominalRoleSchema251
import Yulang.GeneralNominalPostInstallRegression250
/-! Historical origin2 and current aggregate2 are deliberately different.
This is a materialized head fixture, not a reachable source packet. -/
namespace Yulang.GeneralNominalRoleReadRegression251
open Core.PresenceGeneration
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalRoleSchema251 (Holds UseHolds)
open GeneralNominalMixedSchema251 (OriginValue)
open CommonNominalFullCarrier

def assignment : Assignment := fun name => (if name = 0 then model.exactEmpty else .emptyRecord,Common.rowEmpty)
def env : Syntax :=
 ⟨fun name => if name = 2 then .var 0 else .var name,
 fun _ => ⟨.var 2,.var 2⟩,fun _ => .var 0,CompTerm.var⟩
def schema : GeneralNominalMaterialization.Schema :=
 ⟨[⟨7,.source 2,.actual⟩,⟨7,.source 1,.lower⟩],[],false⟩

theorem actual_use : UseHolds [] (read env assignment) ⟨7,.source 2,.actual⟩ := by
 change OriginValue _ (.source 2) _
 constructor
 · exact ⟨_,.source 2⟩
 · intro value seen
   cases seen
   exact ⟨subtype_refl _,subtype_refl _⟩

theorem lower_use : UseHolds [] (read env assignment) ⟨7,.source 1,.lower⟩ := by
 change (∃ actual, GeneralNominalRecursiveInspection.Observes _ (.source 1) actual) ∧ _
 constructor
 · exact ⟨_,.source 1⟩
 · intro actual seen
   cases seen
   exact ⟨subtype_refl _,subtype_refl _⟩

theorem head_valid : (GeneralNominalRoleSchema251.compile [] env schema).Holds assignment := by
 apply (GeneralNominalRoleSchema251.compile_exact ..).mpr
 refine ⟨by simp [schema],?_⟩
 intro entry member
 simp only [schema,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl
 · exact actual_use
 · exact lower_use

/-- Replacing the historical origin map by identity breaks this head. -/
def wrong : Syntax := { env with old := CompTerm.var }

theorem wrong_head_invalid : ¬ (GeneralNominalRoleSchema251.compile [] wrong schema).Holds assignment := by
 intro held
 have interpreted := (GeneralNominalRoleSchema251.compile_exact ..).mp held
 have actual := interpreted.2 ⟨7,.source 2,.actual⟩ (by simp [schema])
 have equality := actual.2 _ (GeneralNominalRecursiveInspection.Observes.source 2)
 exact width_not_below_exactEmpty equality.1

theorem no_single_value : ¬ ∃ value : Ty, value = (assignment 0).1 ∧ value = (assignment 2).1 := by
 rintro ⟨value,old,current⟩
 have equal : (assignment 2).1 = (assignment 0).1 := current.symm.trans old
 have impossible : Subtype (assignment 2).1 (assignment 0).1 := equal ▸ subtype_refl _
 exact width_not_below_exactEmpty impossible
end Yulang.GeneralNominalRoleReadRegression251
