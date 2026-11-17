import Yulang.GeneralNominalRebaseRawView243
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseViewSubst243
open GeneralNominalRebaseRawView243
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration (CompTerm TyTerm RowTerm)
open CommonNominalFullCarrier

def parameter (mapping : Nat → CompTerm Nat) : Parameter → Parameter
 | .type lo hi => .type (lo.subst mapping) (hi.subst mapping)
 | .row lo hi => .row (lo.subst mapping) (hi.subst mapping)

def descriptor (mapping : Nat → CompTerm Nat) (d : Descriptor) : Descriptor :=
 ⟨d.name,d.arguments.map (parameter mapping)⟩

def subst (view : View) (mapping : Nat → CompTerm Nat) : View where
 slots := view.slots
 slot := fun index => (view.slot index).subst mapping
 ordinary := view.ordinary.map (atom mapping)
 heads := fun index => (view.heads index).map (fun term => term.subst mapping)
 intervals := view.intervals
 nominals := fun index => (view.nominals index).map (descriptor mapping)

theorem parameter_exact (mapping : Nat → CompTerm Nat) (model : Assignment) (p : Parameter) (value : Argument) :
 (parameter mapping p).Fits model value ↔ p.Fits (read mapping model) value := by
 cases p <;> cases value <;> simp only [parameter,Parameter.Fits,TyTerm.eval_subst,RowTerm.eval_subst] <;> rfl

theorem fitsAll_exact (mapping : Nat → CompTerm Nat) (model : Assignment) (parameters : List Parameter) (values : List Argument) :
 FitsAll model (parameters.map (parameter mapping)) values ↔ FitsAll (read mapping model) parameters values := by
 constructor
 · intro valid
   generalize eq : parameters.map (parameter mapping) = translated at valid
   induction valid generalizing parameters with
   | nil => cases parameters <;> simp_all; exact .nil
   | cons fit rest ih =>
     cases parameters with
     | nil => simp at eq
     | cons p ps =>
       simp only [List.map_cons,List.cons.injEq] at eq
       exact .cons ((parameter_exact mapping model p _).mp (eq.1 ▸ fit)) (ih ps eq.2)
 · intro valid
   induction valid with
   | nil => exact .nil
   | cons fit rest ih => exact .cons ((parameter_exact mapping model _ _).mpr fit) ih

theorem descriptor_exact (mapping : Nat → CompTerm Nat) (model : Assignment) (target : TyTerm Nat) (d : Descriptor) :
 (descriptor mapping d).Denotes model (target.subst mapping) ↔ d.Denotes (read mapping model) target := by
 simp only [Descriptor.Denotes,descriptor,fitsAll_exact,TyTerm.eval_subst]
 rfl

theorem exact (view : View) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (subst view mapping).Models model ↔ view.Models (read mapping model) := by
 unfold View.Models subst
 simp only [all_exact,CompTerm.subst,TyTerm.eval_subst]
 apply and_congr Iff.rfl
 apply and_congr
 · constructor
   · intro valid index term found
     have h := valid index (term.subst mapping) (by simp [found])
     rw [TyTerm.eval_subst] at h
     exact h
   · intro valid index term found
     obtain ⟨original,recorded,rfl⟩ := Option.map_eq_some_iff.mp found
     rw [TyTerm.eval_subst]
     exact valid index original recorded
 apply and_congr Iff.rfl
 constructor
 · intro valid index d found
   exact (descriptor_exact mapping model (view.slot index).1 d).mp (valid index _ (by simp [found]))
 · intro valid index d found
   obtain ⟨original,recorded,rfl⟩ := Option.map_eq_some_iff.mp found
   exact (descriptor_exact mapping model (view.slot index).1 original).mpr (valid index original recorded)

def inline (view : View) (entries : List GeneralNominalFiniteEquationRealization236.Entry) : View :=
 subst view (GeneralNominalRebaseLookup242.substitution entries)

theorem inline_exact (view : View) (entries : List GeneralNominalFiniteEquationRealization236.Entry)
 (coherent : GeneralNominalRebaseEscapedProjection242.Coherent entries) (model : Assignment) :
 (inline view entries).Models model ↔ view.Models (GeneralNominalFiniteEquationRealization236.patch entries model) := by
 rw [inline,exact]
 change view.Models (GeneralNominalRebaseLookup242.patch entries model) ↔ _
 rw [GeneralNominalRebaseLookup242.patch_exact entries coherent model]

/-- Rewriting an already materialized view is exact at every further step.
This theorem is not a finite bound on the size of a rewrite sequence. -/
theorem repeated (view : View) (first last : Nat → CompTerm Nat) (model : Assignment) :
 (subst (subst view first) last).Models model ↔ view.Models (read first (read last model)) :=
 (exact (subst view first) last model).trans (exact view first (read last model))
end Yulang.GeneralNominalRebaseViewSubst243
