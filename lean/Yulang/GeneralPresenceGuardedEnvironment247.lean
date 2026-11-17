import Yulang.GeneralPresenceGuardedAbsorption247
/-! Explicit finite guarded closure environments for Presence consumers.
This is a new expression representation, not the existing journal/cache state.
Environment lists have no asserted finite bound over an operational run. -/
namespace Yulang.GeneralPresenceGuardedEnvironment247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceGuardedBlock246
open GeneralPresenceModelCongruence245
open CommonNominalFullCarrier
variable {Name : Type} [DecidableEq Name]

structure Closure (Name : Type) where
 nodes : Nat
 parameters : Nat
 body : Body Name nodes parameters
 targets : Fin nodes → Name
 parametersAt : Fin parameters → Name
 injective : Function.Injective targets
 separate : ∀ index parameter, targets index ≠ parametersAt parameter

def Closure.read (closure : Closure Name) (assignment : Name → Comp model) : Name → Comp model :=
 extend closure.body closure.targets closure.parametersAt assignment

def Closure.atoms (closure : Closure Name) : List (Atom Name) :=
 block (entries closure.body closure.targets closure.parametersAt)

theorem Closure.models (closure : Closure Name) (assignment : Name → Comp model) :
 All model (closure.read assignment) closure.atoms :=
 block_satisfied closure.body closure.targets closure.injective closure.parametersAt closure.separate assignment

theorem Closure.rows (closure : Closure Name) (assignment : Name → Comp model) (name : Name) :
 (closure.read assignment name).2 = (assignment name).2 := rfl

theorem Closure.outside (closure : Closure Name) (assignment : Name → Comp model) (name : Name)
 (outside : ∀ index, closure.targets index ≠ name) : closure.read assignment name = assignment name :=
 extend_outside closure.body closure.targets closure.parametersAt assignment name outside

omit [DecidableEq Name] in
theorem values_congr (body : Body Name nodes parameters) (parametersAt : Fin parameters → Name)
 (first last : Name → Comp model) (same : Compatible model first last) (index : Fin nodes) :
 Equivalent (values body parametersAt first index) (values body parametersAt last index) := by
 have rows : compiled body first = compiled body last := by
   funext index
   exact GeneralPresenceGuardedLayer246.lower_rows first last (fun name => (same name).2) (body index)
 unfold values
 rw [rows]
 exact CommonNominalFullGuardedClosure.parameter_congr _ _ _ (fun parameter => (same (parametersAt parameter)).1) index

theorem Closure.compatible (closure : Closure Name) (first last : Name → Comp model)
 (same : Compatible model first last) : Compatible model (closure.read first) (closure.read last) := by
 intro name
 refine ⟨?_,(same name).2⟩
 by_cases inside : ∃ index, closure.targets index = name
 · obtain ⟨index,rfl⟩ := inside
   change Equivalent (extend closure.body closure.targets closure.parametersAt first (closure.targets index)).1
     (extend closure.body closure.targets closure.parametersAt last (closure.targets index)).1
   rw [extend_at closure.body closure.targets closure.injective,extend_at closure.body closure.targets closure.injective]
   exact values_congr closure.body closure.parametersAt first last same index
 · have outside : ∀ index, closure.targets index ≠ name := fun index equal => inside ⟨index,equal⟩
   rw [closure.outside first name outside,closure.outside last name outside]
   exact (same name).1

theorem Closure.recovered (closure : Closure Name) (assignment : Name → Comp model)
 (valid : All model assignment closure.atoms) : Compatible model (closure.read assignment) assignment :=
 GeneralPresenceGuardedRecovery247.extend_compatible closure.body closure.targets closure.injective closure.parametersAt assignment valid

def read (environment : List (Closure Name)) (assignment : Name → Comp model) : Name → Comp model :=
 match environment with
 | [] => assignment
 | closure :: rest => closure.read (read rest assignment)

theorem read_append (first last : List (Closure Name)) (assignment : Name → Comp model) :
 read (first ++ last) assignment = read first (read last assignment) := by
 induction first with
 | nil => rfl
 | cons closure rest ih => simp only [List.cons_append,read,ih]

theorem read_compatible (environment : List (Closure Name)) (first last : Name → Comp model)
 (same : Compatible model first last) : Compatible model (read environment first) (read environment last) := by
 induction environment with
 | nil => exact same
 | cons closure rest ih => exact closure.compatible _ _ ih

theorem read_rows (environment : List (Closure Name)) (assignment : Name → Comp model) (name : Name) :
 (read environment assignment name).2 = (assignment name).2 := by
 induction environment with
 | nil => rfl
 | cons closure rest ih => exact ih

theorem all_compatible (environment : List (Closure Name)) (atoms : List (Atom Name))
 (first last : Name → Comp model) (same : Compatible model first last) :
 All model (read environment first) atoms ↔ All model (read environment last) atoms :=
 GeneralPresenceModelCongruence245.all_iff GeneralPresenceCommonLaws245.common_laws
   (read_compatible environment first last same) atoms
end Yulang.GeneralPresenceGuardedEnvironment247
