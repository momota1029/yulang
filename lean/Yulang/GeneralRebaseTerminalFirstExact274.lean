import Yulang.GeneralRebaseTerminalFirstSupport274

set_option maxRecDepth 24000
set_option maxHeartbeats 7600000
namespace Yulang.GeneralRebaseTerminalFirstExact274
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryVersionedInitialFrame233 (before)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryOptionalInstall229 (actual)
open GeneralDictionaryVersionedSecondRaw233 (oldLo oldHi)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseCompoundSourceTypes273 (PublicSource Body)
open GeneralRebaseTerminalPublic274 (first first_fixed final_to_first)
open GeneralRebaseTerminalDecode274 (decode agrees terminal)
open GeneralRebaseTerminalFirstSupport274 (pool complete)
open GeneralRebaseTerminalPointExact274 (NewFacts)
open GeneralRebaseSemanticSupport274 (Agreement extend_support)
open GeneralRebaseCompoundOwnerCapture273 (PairFacts read_pair)

def OldFacts (m : Assignment) : Prop :=
 Equivalent (m oldLo).1 (m 4).1 ∧ Equivalent (m oldHi).1 (m 2).1 ∧
 Equivalent (m actual).1 (m 2).1

theorem old_aggregates (m : Assignment) (valid : Models first m) :
 PairFacts m oldLo oldHi 4 2 := by
 have raw := (GeneralRebaseTerminalRowFrame274.first_raw_exact m).mp valid.1.1
 have merges := raw.2.2.1
 rw [GeneralDictionaryOptionalInstall229.bindings_exact] at merges
 exact ((PresenceNormalForm.all_append ..).mp merges).1

theorem old_facts (m : Assignment) (valid : Models first m) : OldFacts m := by
 have aggregate := read_pair m oldLo oldHi 4 2 (old_aggregates m valid)
 have observed := (GeneralDictionaryVersionedPointStage233.models_iff m).mpr valid
 exact ⟨aggregate.1,aggregate.2,GeneralRebaseTerminalPointExact274.old_actual_width m observed⟩

theorem decoded_actual (m : Assignment) : (decode m actual).1 = (m 2).1 := rfl
theorem decoded_lo (m : Assignment) : (decode m oldLo).1 = (m 4).1 := rfl
theorem decoded_hi (m : Assignment) : (decode m oldHi).1 = (m 2).1 := rfl

theorem aliases (m : Assignment) (known : OldFacts m) : Agreement pool m (decode m) := by
 intro id member
 refine ⟨?_,rfl⟩
 simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · rw [(agrees m).1 0 (by decide)]; exact ⟨subtype_refl _,subtype_refl _⟩
 · rw [(agrees m).1 1 (by decide)]; exact ⟨subtype_refl _,subtype_refl _⟩
 · rw [(agrees m).1 2 (by decide)]; exact ⟨subtype_refl _,subtype_refl _⟩
 · rw [(agrees m).1 3 (by decide)]; exact ⟨subtype_refl _,subtype_refl _⟩
 · rw [(agrees m).1 4 (by decide)]; exact ⟨subtype_refl _,subtype_refl _⟩
 · rw [decoded_actual]; exact known.2.2
 · rw [decoded_lo]; exact known.1
 · rw [decoded_hi]; exact known.2.1

theorem first_legacy_empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty first := ⟨rfl,rfl⟩

theorem first_exact (m : Assignment) : Models first m ↔ Fixed m ∧ OldFacts m := by
 constructor
 · intro valid
   exact ⟨first_fixed m valid,old_facts m valid⟩
 · rintro ⟨fixed,old⟩
   have valid := final_to_first _ (terminal m fixed)
   exact (extend_support first first_legacy_empty pool complete _ _ (aliases m old)).mpr valid

theorem point_exact (m : Assignment) : Models point m ↔ Fixed m ∧ OldFacts m :=
 (GeneralDictionaryVersionedPointStage233.models_iff m).trans (first_exact m)

theorem all_terminal_fields (m : Assignment) :
 Models installed m ↔ Fixed m ∧ OldFacts m ∧ NewFacts m := by
 rw [GeneralRebaseTerminalPointExact274.exact,point_exact,and_assoc]

theorem initial_to_first (m : Assignment) :
 Models first m ↔ Models before m ∧ Body m ∧ OldFacts m := by
 rw [first_exact,GeneralRebaseCompoundSourceTypes273.restricted_exact,
     GeneralRebaseTerminalRows274.before_models,and_assoc]

end Yulang.GeneralRebaseTerminalFirstExact274
