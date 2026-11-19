import Yulang.GeneralRebaseCompoundOwnerDelta273

set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
namespace Yulang.GeneralRebaseCompoundPairedCompletion273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundPointModel238 (extended)
open GeneralDictionaryCompoundFrame238 (installed)
open GeneralRebaseCompoundReplacement273 (patch lower shape)
open GeneralRebaseCompoundReplacementFrame273 (Meaning)
open GeneralRebaseCompoundReplacementPublic273 (complete completed)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)

noncomputable def oldTypes (boundary : Assignment) : Assignment :=
 fun id => (if id ≤ 4 then (boundary id).1 else (extended id).1,(extended id).2)

noncomputable def old (boundary : Assignment) : Assignment :=
 fun id => ((oldTypes boundary id).1,(boundary id).2)

theorem old_agrees (boundary : Assignment) : Agrees (old boundary) boundary := by
 refine ⟨?_,fun _ => rfl⟩
 intro id small
 simp [old,oldTypes,small]

theorem old_model_before_rows (boundary : Assignment) (known : Fixed boundary) :
 Models installed (oldTypes boundary) := by
 have base := (GeneralDictionaryCompoundPoint238.models_iff extended).mp GeneralDictionaryCompoundPointModel238.model
 have agree : GeneralNominalAssignmentCongruence238.Same extended (oldTypes boundary) := by
   intro id
   refine ⟨?_,rfl⟩
   by_cases small : id ≤ 4
   · simp only [oldTypes,small,ite_true]
     have canonical := GeneralRebaseCompoundPublic273.fixed extended base id small
     have actual := known id small
     exact equivalent_trans canonical ⟨actual.2,actual.1⟩
   · simp only [oldTypes,small,ite_false]
     exact ⟨subtype_refl _,subtype_refl _⟩
 exact (GeneralNominalVersionedSourceCongruence238.source_models_iff agree
   GeneralDictionaryCompoundStep238.reachable).mp base

theorem old_model (boundary : Assignment) (known : Fixed boundary) : Models point (old boundary) := by
 have same : GeneralRebaseRowIrrelevance273.SameTypes (oldTypes boundary) (old boundary) := fun _ => rfl
 exact (GeneralDictionaryCompoundPoint238.models_iff _).mpr
  ((GeneralRebaseCompoundRows273.installed_row_free same).mp (old_model_before_rows boundary known))

theorem compiler_is_patch (boundary : Assignment) :
 complete boundary = patch (old boundary) := by
 funext id
 by_cases small : id ≤ 4
 · have cannot : id ≠ lower := by
     have high : 4 < lower := GeneralDictionaryCompoundPacket238.fresh_large 3
     omega
   rw [GeneralRebaseCompoundReplacement273.untouched _ _ cannot,
       (old_agrees boundary).1 id small,
       (GeneralRebaseCompoundReplacementPublic273.agrees boundary).1 id small]
 · apply Prod.ext
   · by_cases edited : id = lower
     · subst id
       simp [complete,GeneralRebaseCompoundReplacementPublic273.updateTypes,small,patch]
       rfl
     · simp [complete,GeneralRebaseCompoundReplacementPublic273.updateTypes,small,patch,old,oldTypes,edited]
   · rfl

/-- For every accepted boundary there is a paired choice of witnesses. A
single type-cell overwrite transports the selected old completion to the
current certificate while literally fixing everything else and all rows. -/
theorem paired (boundary : Assignment) (known : Fixed boundary) :
 Models point (old boundary) ∧ Meaning (patch (old boundary)) ∧
 Agrees (old boundary) boundary ∧ Agrees (patch (old boundary)) boundary ∧
 (∀ id ≠ lower, patch (old boundary) id = old boundary id) :=
 ⟨old_model boundary known,compiler_is_patch boundary ▸ completed boundary known,old_agrees boundary,
   compiler_is_patch boundary ▸ GeneralRebaseCompoundReplacementPublic273.agrees boundary,
   GeneralRebaseCompoundReplacement273.untouched (old boundary)⟩

end Yulang.GeneralRebaseCompoundPairedCompletion273
