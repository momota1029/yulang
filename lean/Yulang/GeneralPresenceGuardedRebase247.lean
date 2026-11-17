import Yulang.GeneralPresenceGuardedEnvironment247
/-! Semantics of a finite closure-environment rebase representation. Ordinary
Presence atoms are retained with explicit old guarded environments, so private
cyclic reads are not silently redirected to fresh definitions. This is not
an adapter for actual journal/inspection/cache states or a termination result. -/
namespace Yulang.GeneralPresenceGuardedRebase247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceGuardedBlock246 GeneralPresenceGuardedEnvironment247
open CommonNominalFullCarrier
variable {Name : Type} [DecidableEq Name]

structure State (Name : Type) where
 current : Closure Name
 environment : List (Closure Name)
 atoms : List (Atom Name)

def Models (state : State Name) (assignment : Name → Comp model) : Prop :=
 All model (read state.environment assignment) state.atoms ∧ All model assignment state.current.atoms

def freshClosure (old : Closure Name) (fresh : Body Name old.nodes parameters)
 (parametersAt : Fin parameters → Name) (separate : ∀ index parameter, old.targets index ≠ parametersAt parameter) : Closure Name :=
 ⟨old.nodes,parameters,fresh,old.targets,parametersAt,old.injective,separate⟩

def rebase (state : State Name) (fresh : Body Name state.current.nodes parameters)
 (parametersAt : Fin parameters → Name) (separate : ∀ index parameter, state.current.targets index ≠ parametersAt parameter) : State Name where
 current := freshClosure state.current fresh parametersAt separate
 environment := state.environment ++ [state.current]
 atoms := state.atoms

theorem closure_absorbs (old : Closure Name) (fresh : Body Name old.nodes parameters)
 (parametersAt : Fin parameters → Name) (separate : ∀ index parameter, old.targets index ≠ parametersAt parameter)
 (assignment : Name → Comp model) :
 old.read ((freshClosure old fresh parametersAt separate).read assignment) = old.read assignment :=
 GeneralPresenceGuardedAbsorption247.extend_absorbs old.body old.parametersAt fresh old.targets old.injective parametersAt old.separate assignment

theorem models_forward (state : State Name) (fresh : Body Name state.current.nodes parameters)
 (parametersAt : Fin parameters → Name) (separate : ∀ index parameter, state.current.targets index ≠ parametersAt parameter)
 (assignment : Name → Comp model) (valid : Models state assignment) :
 Models (rebase state fresh parametersAt separate) ((freshClosure state.current fresh parametersAt separate).read assignment) := by
 constructor
 · change All model (read (state.environment ++ [state.current]) _) state.atoms
   rw [read_append]
   change All model (read state.environment (state.current.read ((freshClosure state.current fresh parametersAt separate).read assignment))) state.atoms
   rw [closure_absorbs]
   exact (all_compatible state.environment state.atoms _ _ (state.current.recovered assignment valid.2)).mpr valid.1
 · exact (freshClosure state.current fresh parametersAt separate).models assignment

theorem models_backward (state : State Name) (fresh : Body Name state.current.nodes parameters)
 (parametersAt : Fin parameters → Name) (separate : ∀ index parameter, state.current.targets index ≠ parametersAt parameter)
 (assignment : Name → Comp model) (valid : Models (rebase state fresh parametersAt separate) assignment) :
 Models state (state.current.read assignment) := by
 refine ⟨?_,state.current.models assignment⟩
 have consumers := valid.1
 change All model (read (state.environment ++ [state.current]) assignment) state.atoms at consumers
 rw [read_append] at consumers
 exact consumers

def Agrees (sharedNames : Name → Prop) (first last : Name → Comp model) : Prop :=
 ∀ name, sharedNames name → first name = last name

/-- Public coordinates here are the live assignment coordinates. No claim is
made that an arbitrary environment leaves those names untouched. -/
theorem public_models_iff (state : State Name) (fresh : Body Name state.current.nodes parameters)
 (parametersAt : Fin parameters → Name) (separate : ∀ index parameter, state.current.targets index ≠ parametersAt parameter)
 (sharedNames : Name → Prop) (privateTargets : ∀ name, sharedNames name → ∀ index, state.current.targets index ≠ name)
 (boundary : Name → Comp model) :
 (∃ assignment, Models state assignment ∧ Agrees sharedNames assignment boundary) ↔
 (∃ assignment, Models (rebase state fresh parametersAt separate) assignment ∧ Agrees sharedNames assignment boundary) := by
 constructor
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨(freshClosure state.current fresh parametersAt separate).read assignment,
     models_forward state fresh parametersAt separate assignment valid,?_⟩
   intro name shared
   rw [(freshClosure state.current fresh parametersAt separate).outside assignment name (privateTargets name shared)]
   exact agree name shared
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨state.current.read assignment,models_backward state fresh parametersAt separate assignment valid,?_⟩
   intro name shared
   rw [state.current.outside assignment name (privateTargets name shared)]
   exact agree name shared

def Protected (sharedNames : Name → Prop) (environment : List (Closure Name)) : Prop :=
 ∀ closure ∈ environment, ∀ name, sharedNames name → ∀ index, closure.targets index ≠ name

theorem protected_read (sharedNames : Name → Prop) (environment : List (Closure Name))
 (kept : Protected sharedNames environment) (assignment : Name → Comp model) :
 Agrees sharedNames (read environment assignment) assignment := by
 induction environment with
 | nil => exact fun _ _ => rfl
 | cons closure rest ih =>
   intro name shared
   change closure.read (read rest assignment) name = assignment name
   rw [closure.outside _ name (kept closure (by simp) name shared)]
   exact ih (fun c cm => kept c (List.mem_cons_of_mem _ cm)) name shared

omit [DecidableEq Name] in
theorem rebase_protected (state : State Name) (fresh : Body Name state.current.nodes parameters)
 (parametersAt : Fin parameters → Name) (separate : ∀ index parameter, state.current.targets index ≠ parametersAt parameter)
 (sharedNames : Name → Prop) (kept : Protected sharedNames state.environment)
 (privateTargets : ∀ name, sharedNames name → ∀ index, state.current.targets index ≠ name) :
 Protected sharedNames (rebase state fresh parametersAt separate).environment := by
 intro closure member
 rcases List.mem_append.mp member with old | new
 · exact kept closure old
 · have same : closure = state.current := by simpa using new
   subst closure
   exact privateTargets
end Yulang.GeneralPresenceGuardedRebase247
