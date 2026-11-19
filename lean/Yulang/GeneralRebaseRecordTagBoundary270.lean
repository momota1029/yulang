import Yulang.GeneralRebaseStructuralOrigin270
import Yulang.GeneralNominalRecordInversion
import Yulang.CommonNominalFinitePresence

namespace Yulang.GeneralRebaseRecordTagBoundary270
open CommonNominalFullCarrier
open GeneralNominalRecursiveInspection (Origin Observes shapeValue)
open GeneralNominalCommonBridge (Assignment)

theorem duplicate_hidden (label : Nat) (visible hidden : Ty) :
 Equivalent (record label visible (record label hidden emptyRecord)) (record label visible emptyRecord) := by
 have law (depth rank : Nat) (env : CommonNominalFullDemand.Environment Row)
   (obs : CommonNominalFullDemand.Observation Row) :
   CommonNominalFullDemand.ProbeAt Common.rowLe rank env
     (.record label (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node visible)) (.record label (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node hidden)) .emptyRecord)) obs ↔
   CommonNominalFullDemand.ProbeAt Common.rowLe rank env
     (.record label (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node visible)) .emptyRecord) obs := by
   cases rank <;> cases obs <;>
     simp [CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep]
   all_goals split <;> simp_all
 constructor <;> intro depth <;> apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
 · intro rank env obs accepted
   exact (law depth rank env obs).mpr accepted
 · intro rank env obs accepted
   exact (law depth rank env obs).mp accepted

theorem duplicate_shape (label : Nat) (visible hidden : Ty) :
 Equivalent (shapeValue (.record [label, label]) [visible,hidden]) (record label visible emptyRecord) := by
 have displayed :
   shapeValue (.record [label,label]) [visible,hidden] = record label visible (record label hidden emptyRecord) := by
   rw [GeneralNominalRecordInversion.record_shape]
   · rfl
   · rfl
 rw [displayed]
 exact duplicate_hidden label visible hidden

theorem duplicate_observes_arbitrary (m : Assignment) (parent label : Nat) (visible arbitrary : Ty)
 (isRecord : Equivalent (m parent).1 (record label visible emptyRecord)) :
 Observes m (.structural (.source parent) (.record [label,label]) 1) arbitrary :=
 .structural (.source _) (by rfl)
   ⟨subtype_trans isRecord.1 (duplicate_shape label visible arbitrary).2,
     subtype_trans (duplicate_shape label visible arbitrary).1 isRecord.2⟩ rfl

theorem duplicate_tests_not_same (label : Nat) :
 GeneralNominalRecursiveInspection.Test.structural (.record [label,label]) ≠ .structural (.record [label]) := by
 intro equal
 cases equal

theorem duplicate_same_coarse_tag (label : Nat) :
 GeneralNominalFiniteHeadInversion.head (.structural (.record [label,label])) =
 GeneralNominalFiniteHeadInversion.head (.structural (.record [label])) := rfl

theorem duplicate_head (m : Assignment) (parent label : Nat) (visible : Ty)
 (known : Equivalent (m parent).1 (record label visible emptyRecord)) :
 GeneralNominalOriginTerms.Head m (.source parent) (.structural (.record [label,label])) := by
 refine ⟨⟨_,.source _⟩,?_⟩
 intro value actual
 cases actual
 have alternate := duplicate_shape label visible (.base .int)
 exact ⟨[visible,.base .int],rfl,⟨subtype_trans known.1 alternate.2,subtype_trans alternate.1 known.2⟩⟩

/-- An arbitrary hidden payload cannot be a semantic successor under
the existing all-observations equality. No revised language rule is needed
to exclude this particular extra position. -/
theorem duplicate_slot_not_live (m : Assignment) (parent label : Nat) (visible : Ty) (target : Origin)
 (known : Equivalent (m parent).1 (record label visible emptyRecord)) :
 ¬ GeneralNominalOriginTerms.Same m (.structural (.source parent) (.record [label,label]) 1) target := by
 intro equal
 obtain ⟨y,seen⟩ := equal.2.1
 have first := equal.2.2 _ y (duplicate_observes_arbitrary m parent label visible (.base .int) known) seen
 have last := equal.2.2 _ y (duplicate_observes_arbitrary m parent label visible (.base .str) known) seen
 have impossible := GeneralDictionaryInspectionHeads215.tag_subtype
   (GeneralDictionaryInspectionHeads215.tagged_scalar .int) (GeneralDictionaryInspectionHeads215.tagged_scalar .str)
   (subtype_trans first.1 last.2)
 cases impossible

theorem duplicate_not_live_full (state : GeneralNominalVersionedJournal232.State roles)
 (parent label : Nat) (inhabited : ∃ m, GeneralNominalVersionedJournal232.Models state m)
 (known : ∀ m, GeneralNominalVersionedJournal232.Models state m →
   ∃ visible, Equivalent (m parent).1 (record label visible emptyRecord)) (target : Origin) :
 ¬ GeneralNominalVersionedCycles232.Equal state (.structural (.source parent) (.record [label,label]) 1) target := by
 obtain ⟨m,valid⟩ := inhabited
 obtain ⟨visible,recorded⟩ := known m valid
 exact fun same => duplicate_slot_not_live m parent label visible target recorded (same m valid)

end Yulang.GeneralRebaseRecordTagBoundary270
