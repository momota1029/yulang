import Yulang.GeneralRebaseTerminalFreshSupport274

set_option maxRecDepth 19000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6600000
namespace Yulang.GeneralRebaseTerminalRepair274
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryVersionedSecondRaw233 (newLo newHi)
open GeneralRebaseTerminalPublic274 (first point_fixed)
open GeneralRebaseTerminalPointExact274 (NewFacts)
open GeneralRebaseTerminalFreshSupport274 (first_support)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)

def write (m : Assignment) (lo hi : Ty) : Assignment :=
 fun id => (if id = newLo then lo else if id = newHi then hi else (m id).1,(m id).2)

theorem distinct : newLo ≠ newHi := by decide +kernel

theorem low_large : 4 < newLo := GeneralDictionaryVersionedNames231.fresh_above 0
theorem high_large : 4 < newHi := GeneralDictionaryVersionedNames231.fresh_above 1

theorem write_lo (m : Assignment) (lo hi : Ty) : (write m lo hi newLo).1 = lo := by simp [write]

theorem write_hi (m : Assignment) (lo hi : Ty) : (write m lo hi newHi).1 = hi := by
 simp [write,Ne.symm distinct]

theorem unchanged (m : Assignment) (lo hi : Ty) (id : Nat) (a : id ≠ newLo) (b : id ≠ newHi) :
 write m lo hi id = m id := by simp [write,a,b]

theorem public_preserved (m : Assignment) (lo hi : Ty) : Agrees (write m lo hi) m :=
 ⟨fun id small => unchanged m lo hi id (by have h := low_large; omega) (by have h := high_large; omega),fun _ => rfl⟩

theorem write_point (m : Assignment) (valid : Models point m) (lo hi : Ty) :
 Models point (write m lo hi) := by
 have final := (GeneralDictionaryVersionedPointStage233.models_iff m).mp valid
 apply (GeneralDictionaryVersionedPointStage233.models_iff _).mpr
 apply (GeneralNominalVersionedJournalFrame236.models_iff first ?_).mp final
 intro id read
 exact (unchanged m lo hi id (fun e => first_support.1 (e ▸ read))
  (fun e => first_support.2 (e ▸ read))).symm

def repair (m : Assignment) : Assignment := write m (m 2).1 (m 2).1

theorem repair_new (m : Assignment) : NewFacts (repair m) := by
 have two := (public_preserved m (m 2).1 (m 2).1).1 2 (by decide)
 unfold NewFacts repair
 rw [write_lo,write_hi,two]
 exact ⟨⟨subtype_refl _,subtype_refl _⟩,subtype_refl _,subtype_refl _⟩

theorem repairs (m : Assignment) (valid : Models point m) :
 Models installed (repair m) :=
 (GeneralRebaseTerminalPointExact274.exact _).mpr ⟨write_point m valid _ _,repair_new m⟩

theorem continued_leaf (m : Assignment) (valid : Models point m) :
 GeneralRebaseTerminalRows274.HasLeaf (repair m) :=
 GeneralDictionaryVersionedSecondInstall233.evidence (repairs m valid)

theorem not_equivalent_endpoints (m : Assignment) (valid : Models point m) :
 ¬ Equivalent (m 4).1 (m 2).1 := by
 intro eq
 have fixed := point_fixed m valid
 have optional : Equivalent (m 4).1 GeneralDictionaryOptionalOutput229.value := fixed 4 (by decide)
 have width : Equivalent (m 2).1 .emptyRecord := fixed 2 (by decide)
 exact GeneralDictionaryOptionalOutput229.not_width
   (equivalent_trans ⟨optional.2,optional.1⟩ (equivalent_trans eq width))

theorem bad_lo (m : Assignment) (valid : Models point m) :
 Models point (write m (m 4).1 (m 2).1) ∧ ¬ Models installed (write m (m 4).1 (m 2).1) := by
 refine ⟨write_point m valid _ _,?_⟩
 intro final
 have low := ((GeneralRebaseTerminalPointExact274.exact _).mp final).2.1
 rw [write_lo,(public_preserved m _ _).1 2 (by decide)] at low
 exact not_equivalent_endpoints m valid low

theorem bad_hi (m : Assignment) (valid : Models point m) :
 Models point (write m (m 2).1 (m 4).1) ∧ ¬ Models installed (write m (m 2).1 (m 4).1) := by
 refine ⟨write_point m valid _ _,?_⟩
 intro final
 have high := ((GeneralRebaseTerminalPointExact274.exact _).mp final).2.2
 rw [write_hi,(public_preserved m _ _).1 2 (by decide)] at high
 exact not_equivalent_endpoints m valid high

end Yulang.GeneralRebaseTerminalRepair274
