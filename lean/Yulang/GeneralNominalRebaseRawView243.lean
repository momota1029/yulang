import Yulang.GeneralNominalRebaseLookup242
import Yulang.GeneralNominalRawCongruence238
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseRawView243
open Core.PresenceGeneration (CompTerm TyTerm RowTerm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
abbrev Atom := PresenceNormalForm.Atom Nat

def read (mapping : Nat → CompTerm Nat) (model : Assignment) : Assignment :=
 fun name => (mapping name).eval CommonNominalFullCarrier.model model

def atom (mapping : α → CompTerm Nat) : PresenceNormalForm.Atom α → Atom
 | .tyLe a b => .tyLe (a.subst mapping) (b.subst mapping)
 | .rowLe a b => .rowLe (a.subst mapping) (b.subst mapping)

theorem atom_exact (mapping : α → CompTerm Nat) (a : PresenceNormalForm.Atom α) (model : Assignment) :
 (atom mapping a).Holds CommonNominalFullCarrier.model model ↔
 a.Holds CommonNominalFullCarrier.model (fun name => (mapping name).eval CommonNominalFullCarrier.model model) := by
 cases a <;> simp only [atom,PresenceNormalForm.Atom.Holds,TyTerm.eval_subst,RowTerm.eval_subst]

theorem all_exact (mapping : α → CompTerm Nat) (atoms : List (PresenceNormalForm.Atom α)) (model : Assignment) :
 PresenceNormalForm.All CommonNominalFullCarrier.model model (atoms.map (atom mapping)) ↔
 PresenceNormalForm.All CommonNominalFullCarrier.model (fun name => (mapping name).eval CommonNominalFullCarrier.model model) atoms := by
 simp only [PresenceNormalForm.All,List.forall_mem_map,atom_exact]

inductive Parameter where
 | type (lower upper : TyTerm Nat)
 | row (lower upper : RowTerm Nat)

def Parameter.Fits (model : Assignment) : Parameter → Argument → Prop
 | .type lower upper,.inl value => Subtype (lower.eval CommonNominalFullCarrier.model model) value ∧ Subtype value (upper.eval CommonNominalFullCarrier.model model)
 | .row lower upper,.inr value => Common.rowLe (lower.eval CommonNominalFullCarrier.model model) value ∧ Common.rowLe value (upper.eval CommonNominalFullCarrier.model model)
 | _,_ => False

inductive FitsAll (model : Assignment) : List Parameter → List Argument → Prop
 | nil : FitsAll model [] []
 | cons : parameter.Fits model value → FitsAll model parameters values → FitsAll model (parameter :: parameters) (value :: values)

structure Descriptor where
 name : Nat
 arguments : List Parameter

def Descriptor.Denotes (model : Assignment) (target : TyTerm Nat) (descriptor : Descriptor) : Prop :=
 ∃ values, FitsAll model descriptor.arguments values ∧ Equivalent (target.eval CommonNominalFullCarrier.model model) (nominal descriptor.name values)

structure View where
 slots : Nat
 slot : Fin slots → CompTerm Nat
 ordinary : List Atom
 heads : Fin slots → Option (TyTerm Nat)
 intervals : List (Fin slots × Fin slots)
 nominals : Fin slots → Option Descriptor

def View.Models (view : View) (model : Assignment) : Prop :=
 PresenceNormalForm.All CommonNominalFullCarrier.model model view.ordinary ∧
 (∀ index term, view.heads index = some term → Equivalent ((view.slot index).1.eval CommonNominalFullCarrier.model model) (term.eval CommonNominalFullCarrier.model model)) ∧
 (∀ pair ∈ view.intervals, Subtype ((view.slot pair.1).1.eval CommonNominalFullCarrier.model model) ((view.slot pair.2).1.eval CommonNominalFullCarrier.model model)) ∧
 (∀ index descriptor, view.nominals index = some descriptor → descriptor.Denotes model (view.slot index).1)

def slot (state : GeneralSourceState.State) (mapping : Nat → CompTerm Nat) (index : Fin state.slots) : CompTerm Nat :=
 ⟨(mapping (state.source index)).1,(mapping (state.rowSource index)).2⟩

def parameter (state : GeneralSourceState.State) (mapping : Nat → CompTerm Nat) : GeneralNominalState.Parameter state.slots → Parameter
 | .type bounds => .type (slot state mapping bounds.1).1 (slot state mapping bounds.2).1
 | .row bounds => .row (slot state mapping bounds.1).2 (slot state mapping bounds.2).2

def descriptor (state : GeneralSourceState.State) (mapping : Nat → CompTerm Nat) (d : GeneralNominalState.Descriptor state.slots) : Descriptor :=
 ⟨d.declaration.name,d.arguments.map (parameter state mapping)⟩

def compile (raw : GeneralNominalState.State) (mapping : Nat → CompTerm Nat) : View where
 slots := raw.base.slots
 slot := slot raw.base mapping
 ordinary := raw.base.ordinary.map (atom (slot raw.base mapping)) ++ raw.ordinary.map (atom mapping)
 heads := fun index => (raw.base.heads index).equation.map (fun term => term.subst (slot raw.base mapping))
 intervals := raw.base.intervals
 nominals := fun index => (raw.nominals index).map (descriptor raw.base mapping)

theorem slot_eval (state : GeneralSourceState.State) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (fun index => (slot state mapping index).eval CommonNominalFullCarrier.model model) = GeneralNominalCommonBridge.assignment state (read mapping model) := rfl

theorem parameter_exact (state : GeneralSourceState.State) (mapping : Nat → CompTerm Nat) (model : Assignment) (p : GeneralNominalState.Parameter state.slots) (value : Argument) :
 (parameter state mapping p).Fits model value ↔ GeneralNominalState.Fits state (read mapping model) p value := by
 cases p <;> cases value <;> rfl

theorem fitsAll_exact (state : GeneralSourceState.State) (mapping : Nat → CompTerm Nat) (model : Assignment) (parameters : List (GeneralNominalState.Parameter state.slots)) (values : List Argument) :
 FitsAll model (parameters.map (parameter state mapping)) values ↔ GeneralNominalState.FitsAll state (read mapping model) parameters values := by
 constructor
 · intro valid
   generalize eq : parameters.map (parameter state mapping) = translated at valid
   induction valid generalizing parameters with
   | nil => cases parameters <;> simp_all; exact .nil
   | cons fit rest ih =>
     cases parameters with
     | nil => simp at eq
     | cons p ps =>
       simp only [List.map_cons,List.cons.injEq] at eq
       exact .cons ((parameter_exact state mapping model p _).mp (eq.1 ▸ fit)) (ih ps eq.2)
 · intro valid
   induction valid with
   | nil => exact .nil
   | cons fit rest ih => exact .cons ((parameter_exact state mapping model _ _).mpr fit) ih

theorem descriptor_exact (state : GeneralSourceState.State) (mapping : Nat → CompTerm Nat) (model : Assignment) (index : Fin state.slots) (d : GeneralNominalState.Descriptor state.slots) :
 (descriptor state mapping d).Denotes model (slot state mapping index).1 ↔ GeneralNominalState.Denotes state (read mapping model) index d := by
 unfold Descriptor.Denotes GeneralNominalState.Denotes descriptor
 simp only [fitsAll_exact]
 rfl

theorem compile_exact (raw : GeneralNominalState.State) (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (compile raw mapping).Models model ↔ GeneralNominalState.Models raw (read mapping model) := by
 unfold View.Models compile GeneralNominalState.Models GeneralNominalCommonBridge.Models
 simp only [PresenceNormalForm.all_append,all_exact,slot_eval]
 have headExact : (∀ index term, Option.map (fun t => t.subst (slot raw.base mapping)) (raw.base.heads index).equation = some term → Equivalent ((slot raw.base mapping index).1.eval CommonNominalFullCarrier.model model) (term.eval CommonNominalFullCarrier.model model)) ↔
   (∀ index term, (raw.base.heads index).equation = some term → Equivalent ((read mapping model) (raw.base.source index)).1 (term.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment raw.base (read mapping model)))) := by
   constructor
   · intro valid index term found
     have h := valid index (term.subst (slot raw.base mapping)) (by simp [found])
     rw [TyTerm.eval_subst,slot_eval] at h
     exact h
   · intro valid index term found
     obtain ⟨original,recorded,rfl⟩ := Option.map_eq_some_iff.mp found
     rw [TyTerm.eval_subst,slot_eval]
     exact valid index original recorded
 have nominalExact : (∀ index d, Option.map (descriptor raw.base mapping) (raw.nominals index) = some d → d.Denotes model (slot raw.base mapping index).1) ↔
   (∀ index d, raw.nominals index = some d → GeneralNominalState.Denotes raw.base (read mapping model) index d) := by
   constructor
   · intro valid index d found
     exact (descriptor_exact raw.base mapping model index d).mp (valid index _ (by simp [found]))
   · intro valid index d found
     obtain ⟨original,recorded,rfl⟩ := Option.map_eq_some_iff.mp found
     exact (descriptor_exact raw.base mapping model index original).mpr (valid index original recorded)
 rw [headExact,nominalExact]
 constructor
 · rintro ⟨⟨a,b⟩,c,d,e⟩; exact ⟨⟨a,c,d⟩,e,b⟩
 · rintro ⟨⟨a,c,d⟩,e,b⟩; exact ⟨⟨a,b⟩,c,d,e⟩
end Yulang.GeneralNominalRebaseRawView243
