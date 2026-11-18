import Yulang.GeneralDictionaryUniformJournal258
namespace Yulang.GeneralDictionaryUniformAlias258
open Core.PresenceGeneration
open GeneralDictionaryFamilyRecognition258
open GeneralDictionaryUniformFill258 (fill)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def target (name : Nat) : Nat :=
 if isLower name = true then 2 else if isUpper name = true then 4 else name

def mapping (name : Nat) : CompTerm Nat := ⟨.var (target name),.var name⟩

theorem read_exact (assignment : Assignment) :
 GeneralNominalRebaseRawView243.read mapping assignment = fill assignment := by
 funext name
 change ((assignment (target name)).1,(assignment name).2) = fill assignment name
 unfold target fill
 split <;> first | rfl | split <;> rfl

theorem initial (name : Nat) (bound : name ≤ 4) : target name = name := by
 obtain ⟨lo,hi⟩ := small name bound
 simp only [target,lo,hi,Bool.false_eq_true,ite_false]

theorem actual_fixed : target GeneralDictionaryLooseLoopPacket240.actual = GeneralDictionaryLooseLoopPacket240.actual := by
 obtain ⟨lo,hi⟩ := GeneralDictionaryUniformFill258.actual_tags
 simp only [target,lo,hi,Bool.false_eq_true,ite_false]

theorem idempotent (name : Nat) : target (target name) = target name := by
 unfold target
 split
 · exact initial 2 (by decide)
 · split
   · exact initial 4 (by decide)
   · rfl

theorem type_exact (term : TyTerm Nat) (assignment : Assignment) :
 (term.subst mapping).eval model assignment = term.eval model (fill assignment) := by
 rw [TyTerm.eval_subst]
 exact congrArg (term.eval model) (read_exact assignment)

theorem row_exact (term : RowTerm Nat) : term.subst mapping = term := by
 induction term with
 | join a b ihA ihB => simp only [RowTerm.subst,ihA,ihB]
 | var | empty => rfl

theorem atom_exact (atom : PresenceNormalForm.Atom Nat) (assignment : Assignment) :
 (GeneralNominalRebaseRawView243.atom mapping atom).Holds model assignment ↔
 atom.Holds model (fill assignment) := by
 rw [GeneralNominalRebaseRawView243.atom_exact]
 change atom.Holds model (GeneralNominalRebaseRawView243.read mapping assignment) ↔ _
 rw [read_exact]
end Yulang.GeneralDictionaryUniformAlias258
