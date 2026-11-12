import Yulang.GeneralDictionaryOutputMergeContextComplete
import Yulang.GeneralDictionaryTerminalRefresh

/-! Separating assignments exclude any further exact refresh of other source
identities in this concrete journal. No whole Stable theorem is asserted. -/
namespace Yulang.GeneralDictionaryOutputMergeRefreshClosure
open GeneralDictionaryOutputMergeSuccess GeneralDictionaryOutputMergeRefresh
open GeneralNominalExamples (model)
open GeneralNominalSaturationState CommonNominalFullCarrier
abbrev varying := GeneralDictionaryTerminalRefresh.varying

theorem varying_raw (name : Nat) (zero : name ≠ 0) (one : name ≠ 1)
    (left : name ≠ outputTarget 10) (right : name ≠ outputTarget 11) :
    GeneralNominalState.Models snapshot (varying name) := by
  have low (slot : Fin 4) : varying name (base.source slot) = model (base.source slot) := by
    have different : base.source slot ≠ name := by
      change (if slot.val < 2 then slot.val else if slot.val = 2 then outputTarget 10 else outputTarget 11) ≠ name
      split
      · omega
      · split
        · exact Ne.symm left
        · exact Ne.symm right
    exact ite_eq_right different
  have rows (slot : Fin 4) : (varying name (base.rowSource slot)).2 = (model (base.rowSource slot)).2 := by
    unfold varying GeneralDictionaryTerminalRefresh.varying
    split <;> rfl
  have assigned : GeneralNominalCommonBridge.assignment base (varying name) =
      GeneralNominalCommonBridge.assignment base model := by
    funext slot
    change ((varying name (base.source slot)).1,(varying name (base.rowSource slot)).2) = _
    rw [low slot,rows slot]
    rfl
  have original : GeneralNominalState.Models snapshot model := inhabited.1
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · change PresenceNormalForm.All CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment base (varying name)) _
    rw [assigned]
    exact original.1.1
  · intro slot term recorded
    change Equivalent (varying name (base.source slot)).1 (term.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment base (varying name)))
    rw [low slot,assigned]
    exact original.1.2.1 slot term recorded
  · intro pair member
    change Subtype (varying name (base.source pair.1)).1 (varying name (base.source pair.2)).1
    rw [low pair.1,low pair.2]
    exact original.1.2.2 pair member
  · intro slot descriptor recorded
    obtain ⟨values,fits,equal⟩ := original.2.1 slot descriptor recorded
    refine ⟨values,?_,?_⟩
    · have transform : ∀ parameters values, GeneralNominalState.FitsAll base model parameters values →
          GeneralNominalState.FitsAll base (varying name) parameters values := by
        intro parameters values fits
        induction fits with
        | nil => exact .nil
        | @cons parameter value parameters values head tail ih =>
          refine .cons ?_ ih
          cases parameter <;> cases value <;> first | exact head | simpa only [GeneralNominalState.Fits,low,rows] using head
      exact transform _ _ fits
    · change Equivalent (varying name (base.source slot)).1 _
      rw [low slot]
      exact equal
  · have shape : snapshot.ordinary =
        [.tyLe (.var 1) (.var 1),.tyLe (.var 0) (.var 0),.tyLe (.var 0) (.var 0),
         .tyLe (.var 1) (.var 1),.tyLe (.var (outputTarget 10)) (.var (outputTarget 11)),
         .tyLe (.var (outputTarget 11)) (.var (outputTarget 10)),
         .tyLe (.var (outputTarget 10)) (.var 1),.tyLe (.var 1) (.var (outputTarget 10))] := by decide +kernel
    rw [shape]
    intro atom member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      change Subtype _ _
      simp only [Core.PresenceGeneration.TyTerm.eval]
      first | exact subtype_refl _ |
        simpa [varying,GeneralDictionaryTerminalRefresh.varying,Ne.symm left,Ne.symm right,Ne.symm one,
          GeneralNominalExamples.model,output_nonzero] using (subtype_refl (.base .int))

theorem varying_journal (name : Nat) (zero : name ≠ 0) (one : name ≠ 1)
    (left : name ≠ outputTarget 10) (right : name ≠ outputTarget 11) :
    Models refreshed.current (varying name) :=
  GeneralDictionaryOutputMergeContextComplete.context_complete _ (varying_raw name zero one left right)

theorem refresh_other_unknown (next : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalCycleSteps.Refresh refreshed.current next)
    (name : Nat) (zero : name ≠ 0) (one : name ≠ 1)
    (left : name ≠ outputTarget 10) (right : name ≠ outputTarget 11) :
    ¬ GeneralNominalState.Known next.state name :=
  GeneralDictionaryTerminalRefresh.no_known_distinct next.state model (varying name) name
    (by change (if name = 0 then nominal 0 [.inl (.base .int)] else .base .int) = .base .int; exact ite_eq_right zero)
    (by simp only [varying,GeneralDictionaryTerminalRefresh.varying,ite_true]; rfl)
    (certificate.exact _ inhabited) (certificate.exact _ (varying_journal name zero one left right))
end Yulang.GeneralDictionaryOutputMergeRefreshClosure
