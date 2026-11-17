import Yulang.GeneralNominalRebaseEffectView243
import Yulang.GeneralNominalVersionedEffects231
set_option backward.isDefEq.respectTransparency false
/-! Finite class-effect equations. Translation failure contributes no equation,
matching BodyHolds; readiness remains a distinct obligation. -/
namespace Yulang.GeneralNominalRebaseClassView243
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralDictionaryAssociatedProvenance (lookup Body)
open GeneralNominalRebaseEffectView243 (Equation body)
open GeneralNominalRebaseRawView243 (read Atom)
open CommonNominalFullCarrier

structure View where
 equations : List Equation
 equalities : List Atom

def View.Holds (view : View) (model : Assignment) : Prop :=
 (∀ equation ∈ view.equations, equation.Holds model) ∧
 PresenceNormalForm.All CommonNominalFullCarrier.model model view.equalities

def equations (plan : Plan roles) (mapping : Nat → CompTerm Nat)
 (outputs : List GeneralSourceState.Output) : List Equation :=
 outputs.flatMap fun output => (lookup roles plan.packet.declaration output.name).toList.flatMap
   fun source => (body plan mapping output.target source).toList

def equalities (mapping : Nat → CompTerm Nat) (outputs : List GeneralSourceState.Output) : List Atom :=
 outputs.flatMap fun first => outputs.flatMap fun last =>
 if first.name = last.name then [.tyLe (mapping first.target).1 (mapping last.target).1,
 .tyLe (mapping last.target).1 (mapping first.target).1] else []

noncomputable def compile (state : GeneralNominalCenteredSteps.State roles)
 (root : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles) (mapping : Nat → CompTerm Nat) : View :=
 ⟨equations plan mapping (requests state root),equalities mapping (requests state root)⟩

theorem body_list_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment)
 (target : Nat) (source : Body) :
 (∀ equation ∈ (body plan mapping target source).toList, equation.Holds model) ↔
 GeneralNominalCenteredHeadMatEffects.BodyHolds plan target (read mapping model) source := by
 cases found : GeneralNominalCenteredHeadMatEffects.compileBody plan source with
 | none => simp [body,found,GeneralNominalCenteredHeadMatEffects.BodyHolds,
     GeneralNominalCenteredHeadMatEffects.bodySchema,GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
 | some expression =>
   simpa [body,found] using GeneralNominalRebaseEffectView243.body_exact plan mapping model target source found

theorem equations_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment)
 (outputs : List GeneralSourceState.Output) :
 (∀ equation ∈ equations plan mapping outputs, equation.Holds model) ↔
 (∀ output ∈ outputs, ∀ source, lookup roles plan.packet.declaration output.name = some source →
 GeneralNominalCenteredHeadMatEffects.BodyHolds plan output.target (read mapping model) source) := by
 simp only [equations,List.forall_mem_flatMap]
 constructor
 · intro valid output member source found
   apply (body_list_exact plan mapping model output.target source).mp
   exact valid output member source (by simpa using found)
 · intro valid output member source found
   exact (body_list_exact plan mapping model output.target source).mpr
     (valid output member source (by simpa using found))

theorem equalities_exact (mapping : Nat → CompTerm Nat) (model : Assignment)
 (outputs : List GeneralSourceState.Output) :
 PresenceNormalForm.All CommonNominalFullCarrier.model model (equalities mapping outputs) ↔
 (∀ first ∈ outputs, ∀ last ∈ outputs, first.name = last.name →
 Equivalent ((read mapping model) first.target).1 ((read mapping model) last.target).1) := by
 unfold equalities PresenceNormalForm.All
 simp only [List.forall_mem_flatMap]
 have pair (first last : GeneralSourceState.Output) :
   (∀ atom ∈ (if first.name = last.name then
     [PresenceNormalForm.Atom.tyLe (mapping first.target).1 (mapping last.target).1,
      .tyLe (mapping last.target).1 (mapping first.target).1] else []),
     atom.Holds CommonNominalFullCarrier.model model) ↔
   (first.name = last.name → Equivalent
     ((GeneralNominalRebaseRawView243.read mapping model) first.target).1
     ((GeneralNominalRebaseRawView243.read mapping model) last.target).1) := by
   by_cases h : first.name = last.name
   · simp only [h,ite_true,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,true_implies]
     rfl
   · simp [h]
 simp only [pair]


theorem compile_exact (state : GeneralNominalCenteredSteps.State roles)
 (root : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles)
 (mapping : Nat → CompTerm Nat) (model : Assignment) :
 (compile state root plan mapping).Holds model ↔
 GeneralNominalVersionedEffects231.ClassEffects state root plan (read mapping model) := by
 rw [GeneralNominalVersionedEffects231.class_effects_iff]
 exact and_congr (equations_exact plan mapping model _) (equalities_exact mapping model _)
end Yulang.GeneralNominalRebaseClassView243
