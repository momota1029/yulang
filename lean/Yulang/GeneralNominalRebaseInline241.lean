import Yulang.GeneralNominalRebaseDefinitions241
/-! Simultaneous inlining of finite definition entries into live ordinary
consumers. This preserves their meaning under the same finite patch, including
row constraints. It is not a cyclic-definition solver or full journal rewrite. -/
namespace Yulang.GeneralNominalRebaseInline241
open Core.PresenceGeneration
open GeneralNominalFiniteEquationRealization236
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm
noncomputable def substitution (entries : List Entry) (name : Nat) : CompTerm Nat := by
 classical
 exact if found : ∃ entry ∈ entries, entry.1 = name then
   ⟨(Classical.choose found).2,.var name⟩ else CompTerm.var name

theorem substitution_eval
 (coherent : ∀ first ∈ entries, ∀ last ∈ entries, first.1 = last.1 → first.2 = last.2)
 (model : Assignment) (name : Nat) :
 (substitution entries name).eval CommonNominalFullCarrier.model model = patch entries model name := by
 classical
 unfold substitution
 split
 · rename_i found
   have member := (Classical.choose_spec found).1
   have identity := (Classical.choose_spec found).2
   apply Prod.ext
   · change (Classical.choose found).2.eval CommonNominalFullCarrier.model model = _
     exact (value entries coherent _ member).symm.trans
       (congrArg (fun key => (patch entries model key).1) identity)
   · exact (row entries name).symm
 · rename_i absent
   have untouched : patch entries model name = model name := outside entries (by
     intro entry member equal
     exact absent ⟨entry,member,equal⟩)
   simpa only [CompTerm.eval_var] using untouched.symm

def atomSubst (mapping : Nat → CompTerm Nat) : Atom Nat → Atom Nat
 | .tyLe left right => .tyLe (left.subst mapping) (right.subst mapping)
 | .rowLe left right => .rowLe (left.subst mapping) (right.subst mapping)

theorem atom_subst (mapping : Nat → CompTerm Nat) (atom : Atom Nat) (model : Assignment) :
 (atomSubst mapping atom).Holds CommonNominalFullCarrier.model model ↔
 atom.Holds CommonNominalFullCarrier.model (fun name => (mapping name).eval CommonNominalFullCarrier.model model) := by
 cases atom <;> simp only [atomSubst,Atom.Holds,TyTerm.eval_subst,RowTerm.eval_subst]

theorem atom_inline
 (coherent : ∀ first ∈ entries, ∀ last ∈ entries, first.1 = last.1 → first.2 = last.2)
 (atom : Atom Nat) (model : Assignment) :
 (atomSubst (substitution entries) atom).Holds CommonNominalFullCarrier.model model ↔
 atom.Holds CommonNominalFullCarrier.model (patch entries model) := by
 rw [atom_subst]
 have same : (fun name => (substitution entries name).eval CommonNominalFullCarrier.model model) = patch entries model :=
   funext (substitution_eval coherent model)
 rw [same]

theorem all_inline
 (coherent : ∀ first ∈ entries, ∀ last ∈ entries, first.1 = last.1 → first.2 = last.2)
 (atoms : List (Atom Nat)) (model : Assignment) :
 All CommonNominalFullCarrier.model model (atoms.map (atomSubst (substitution entries))) ↔
 All CommonNominalFullCarrier.model (patch entries model) atoms := by
 unfold All
 simp only [List.forall_mem_map]
 apply forall_congr'; intro atom
 apply forall_congr'; intro member
 exact atom_inline coherent atom model
end Yulang.GeneralNominalRebaseInline241
